/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>

#include <signal.h>
#include <zlib.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/Solver.h"
#include "Solver.h"
#include "../mtl/Vec.h"
#include "SolverTypes.h"

#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <fstream>
#include <mpi.h>

int myMPI_rank  = -1;
int num_mpi_ranks = 0;

using namespace Minisat;
using namespace std;
static BoolOption optfixFirstLayer("MAIN", "fixFirst", "fix first layer", false);
static BoolOption opt_prefLayer("MAIN", "usePrefFile", "Use a prefix file", false);
static BoolOption opt_someStartValues("MAIN", "useSomeValues", "Add some values and continue iteratively", false);
static BoolOption opt_lastLayerConstraints("MAIN", "lastLayerConstraints", "Use constraints on last layers", true);

static BoolOption opt_lastLayerHC("MAIN", "llCleaner", "Use half cleaner as last layer", false);

static BoolOption opt_optEncoding("MAIN", "betterEncoding", "Use faster encoding", false);
static IntOption opt_minNumInputs("MAIN", "minNumInputs", "Minimum number of inputs to use", 0, IntRange(0, INT32_MAX));
static IntOption opt_row("MAIN", "row", "Row in File to use", 0, IntRange(0, INT32_MAX));
static IntOption shrinkGen("MAIN", "shrink", "Shrink generated formula by this number of bits.\n", 0,
                           IntRange(0, INT32_MAX));
static StringOption prefFileName("MAIN", "prefFile", "Name of prefix file");
static BoolOption opt_create_splitter("MAIN", "splitter", "Create a network which only sorts inputs with n/2 ones", false);

static BoolOption opt_llGuess("MAIN", "llGuess", "Make the guess that the last layer is similar to a half cleaner", false);
static IntOption opt_maxPrefLayer("MAIN", "maxPrefLayer", "Max layer to use from input.\n", 10,
                           IntRange(0, INT32_MAX));
static BoolOption opt_mpi("MAIN", "useMPI", "Use the parallel version", true);


static BoolOption opt_shortComps("MAIN", "shortComps", "Add clauses which enfoce each comparator (i,i+1) to be used", true);

//=================================================================================================

void printStats(Solver &solver) {
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("restarts              : %"
    PRIu64
    "\n", solver.starts);
    printf("conflicts             : %-12"
    PRIu64
    "   (%.0f /sec)\n", solver.conflicts, solver.conflicts / cpu_time);
    printf("decisions             : %-12"
    PRIu64
    "   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float) solver.rnd_decisions * 100 /
                                                            (float) solver.decisions, solver.decisions / cpu_time);
    printf("propagations          : %-12"
    PRIu64
    "   (%.0f /sec)\n", solver.propagations, solver.propagations / cpu_time);
    printf("conflict literals     : %-12"
    PRIu64
    "   (%4.2f %% deleted)\n", solver.tot_literals, (solver.max_literals - solver.tot_literals) * 100 /
                                                    (double) solver.max_literals);
    if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
    printf("CPU time              : %g s\n", cpu_time);
}


static Solver *solver;

// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int signum) { solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum) {
    printStats(*solver);
    printf("\n");
    printf("*** INTERRUPTED ***\n");
    _exit(1);
}

vec<Lit> firstCubes;
/**********************************************************************
* The comparator class
*/

struct comparator {
    int layer, minchan, maxchan;

    comparator(int l, int minc, int maxc) : layer(l), minchan(minc), maxchan(maxc) { }

    bool operator<(const comparator &other) const {
        if (other.layer != layer)
            return layer < other.layer;
        if (other.minchan != minchan)
            return minchan < other.minchan;
        return maxchan < other.maxchan;
    }
};

/**********************************************************************
 * Compute the rating of an input, i.e. the number of leading zeros + tailing ones
 */
int getRating(int val, int n) {
    int rVal = 0;
    int m = 1;
    for (int i = 0; i < n; i++) {
        if (!(val & m))
            rVal++;
        else
            break;
        m <<= 1;
    }
    m = 1 << (n - 1);
    for (int i = 0; i < n; i++) {
        if (val & m)
            rVal++;
        else
            break;
        m >>= 1;
    }
    return rVal;
}

int getNumLeadingZeros(int val, int n) {
    int rVal = 0;
    for (int i = 0; i < n; i++) {
        if (val & (1 << i))
            return rVal;
        rVal++;
    }
    return rVal;
}

int getNumTailingOnes(int val, int n) {
    int mask = 1 << (n - 1);
    int rVal = 0;
    for (int i = 0; i < n; i++) {
        if (!(val & mask))
            return rVal;
        mask >>= 1;
        rVal++;
    }
    return rVal;
}

/**********************************************************************
 * Perform the compare&swap of a comparator between channels i and j*/
/* Precondition: i < j*/
int comp(int val, int i, int j) {
    if ((val & (1 << i)) && !(val & (1 << j))) {
        val ^= ((1 << i) | (1 << j));
    }
    return val;
}

int evalParberry(int val, int bits) {
    for (int i = 0; i < bits; i += 2) {
        if (i + 1 < bits)
            val = comp(val, i, i + 1);
    }
    return val;
}

/**********************************************************************
 * Given an input "val", compute the output of a prefix */
/* inputs: 
 *      - val : The input to be "presorted"
 *      - bits: The number of channels 
 *      - comps: a vector of triples (d, i, j) containing the comparators and their respective layers
 * */
int eval(int val, vector<comparator> &comps) {
    unsigned used = 0;
    int layer = 0;
    while (used < comps.size()) {
        for (unsigned i = 0; i < comps.size(); i++) {
            if (comps[i].layer == layer) {
                int a = comps[i].minchan;
                int b = comps[i].maxchan;
                val = comp(val, min(a, b), max(a, b));
                used++;
            }
        }
        layer++;
    }
    return val;
}


typedef map<comparator, Var> triVarMap;

void reifyAnd(Solver & s, Lit l, vec<Lit> & rhs){
    // l -> rhs[i]
    for(int i = 0 ; i < rhs.size() ; i++){
        vec<Lit> ps;
        ps.push(~l);
        ps.push(rhs[i]);
        s.addClause(ps);
    }
    // ~l -> ~rhs[i]
    vec<Lit> ps;
    for(int i = 0 ; i < rhs.size() ; i++){
        ps.push(~rhs[i]);
    }
    ps.push(l);
    s.addClause(ps);
}

void printComps(vector<comparator> & comps, int n, int d){
    for(int i = 0 ; i < d ; i++){
        printf("\\addtocounter{sncolumncounter}{1}\n");
        vector<comparator> usedComps;
        for(int j = 0 ; j < comps.size();j++){
            if(comps[j].layer == i)
                usedComps.push_back(comps[j]);
        }

        // Group these comparators:
        map<int, vector<comparator> > miniLayers;
        set<pair<int, int> > usedChannels;
        for(int j = 0 ; j < usedComps.size();j++){


            comparator c = usedComps[j];
            for(int myLayer = 0 ; myLayer < usedComps.size();myLayer++){
                bool found = true;
                for(int k = c.minchan; k <= c.maxchan ; k++){
                    if(usedChannels.count(make_pair(myLayer, k)))
                        found = false;
                }
                if(found){
                    for(int k = c.minchan; k <= c.maxchan ; k++){
                        assert(usedChannels.count(make_pair(myLayer, k)) == 0);
                        usedChannels.insert(make_pair(myLayer, k));
                    }
                    miniLayers[myLayer].push_back(c);
                    break;
                }
            }
        }
        for(map<int, vector<comparator> >::iterator it = miniLayers.begin() ; it != miniLayers.end();it++){
            printf("\\nodeconnection{");
            vector<comparator> & v = it->second;
            for(int j = 0 ; j < v.size();j++){
                printf("{%d,%d}", n-v[j].minchan, n-v[j].maxchan);
                if(j +1 < v.size())
                    printf(",");
            }
            printf("}\n");
        }
        // print them:
        //printf("\\nodeconnection{ {%d,%d}}\n", n-j, n-k);
    }
}

void printNetwork(Solver & netWorkCreate, int n, int d,triVarMap &compVarsInCreatedNW ){
    vector<comparator> allComps;
    for(int i = 0 ; i < d ; i++){


        for (int j = 0; j < n; j++) {
            for (int k = j + 1; k < n; k++) {
                if (netWorkCreate.modelValue(compVarsInCreatedNW[comparator(i, j, k)]) == l_True) {
                    allComps.push_back(comparator(i,j,k));
                }
            }
        }
        /*
        // Group these comparators:
        map<int, vector<comparator> > miniLayers;
        set<pair<int, int> > usedChannels;
        for(int j = 0 ; j < usedComps.size();j++){


            comparator c = usedComps[j];
            for(int myLayer = 0 ; myLayer < usedComps.size();myLayer++){
                bool found = true;
                for(int k = c.minchan; k <= c.maxchan ; k++){
                    if(usedChannels.count(make_pair(myLayer, k)))
                        found = false;
                }
                if(found){
                    for(int k = c.minchan; k <= c.maxchan ; k++){
                        assert(usedChannels.count(make_pair(myLayer, k)) == 0);
                        usedChannels.insert(make_pair(myLayer, k));
                    }
                    miniLayers[myLayer].push_back(c);
                    break;
                }
            }
        }
        for(map<int, vector<comparator> >::iterator it = miniLayers.begin() ; it != miniLayers.end();it++){
            printf("\\nodeconnection{");
            vector<comparator> & v = it->second;
            for(int j = 0 ; j < v.size();j++){
                printf("{%d,%d}", n-v[j].minchan, n-v[j].maxchan);
                if(j +1 < v.size())
                    printf(",");
            }
            printf("}\n");
        }*/
        // print them:
        //printf("\\nodeconnection{ {%d,%d}}\n", n-j, n-k);
    }
    printComps(allComps, n, d);
}

/**********************************************************************
 * a <=> b or c 
 */
void add_a_equals_b_or_c(Solver &s, Var &a, Var &b, Var &c) {
    vec<Lit> ps;
    //  A implies B or C
    ps.push(~mkLit(a));
    ps.push(mkLit(b));
    ps.push(mkLit(c));
    s.addClause(ps);
    ps.clear();
    // Not A implies (Not B and Not C)
    ps.push(mkLit(a));
    ps.push(~mkLit(b));
    s.addClause(ps);
    ps.clear();
    ps.push(mkLit(a));
    ps.push(~mkLit(c));
    s.addClause(ps);
    ps.clear();
}

/**********************************************************************
 * a <=> b and c 
 */
void add_a_equals_b_and_c(Solver &s, Var &a, Var &b, Var &c) {
    vec<Lit> ps;
    //  not A implies (not B or not C)
    ps.push(mkLit(a));
    ps.push(~mkLit(b));
    ps.push(~mkLit(c));
    s.addClause(ps);
    ps.clear();
    //  A implies (B and  C)
    ps.push(~mkLit(a));
    ps.push(mkLit(b));
    s.addClause(ps);
    ps.clear();
    ps.push(~mkLit(a));
    ps.push(mkLit(c));
    s.addClause(ps);
    ps.clear();
}

/**********************************************************************
 * x <=> y, i.e. x => y and (not x) => (not y) 
 */
void addEquals(Solver &s, Var &x, Var &y) {
    vec<Lit> ps;
    ps.push(mkLit(x));
    ps.push(~mkLit(y));
    s.addClause(ps);
    ps.clear();
    ps.push(~mkLit(x));
    ps.push(mkLit(y));
    s.addClause(ps);
    ps.clear();
}

/********************************************************************** 
 * Create a reference-network which computes a sorted output for variable input- and output-vectors. 
 * This is done as a "bubble sort" network.
 * */
void createRefNetwork(Solver &s, vector<Var> &inputVars, vector<Var> &outputVars, int numBits, int numLayers,
                      map<pair<int, int>, Var> &innerVars) {
    Var varsInNetwork[numLayers - 1][numBits];
    for (int i = 0; i < numLayers - 1; i++) {
        for (int j = 0; j < numBits; j++) {
            varsInNetwork[i][j] = s.newVar();
            innerVars[make_pair(i, j)] = varsInNetwork[i][j];
        }
    }

    for (int i = 0; i < numLayers; i++) {
        /* If there is no comparator on the first channel, copy its value for the next layer*/
        if (i % 2 == 1) {
            addEquals(s, varsInNetwork[i - 1][0], i < numLayers - 1 ? varsInNetwork[i][0] : outputVars[0]);
        }
        for (int j = (i % 2); j < numBits; j += 2) {
            if (j + 1 < numBits) {
                // move "one" to line with higher index, i.e. v_{i, j+1} = v_{i-1, j+1} \vee v_{i-1, j+1}
                add_a_equals_b_or_c(s, i < numLayers - 1 ? varsInNetwork[i][j + 1] : outputVars[j + 1],
                                    i > 0 ? varsInNetwork[i - 1][j] : inputVars[j],
                                    i > 0 ? varsInNetwork[i - 1][j + 1] : inputVars[j + 1]);
                add_a_equals_b_and_c(s, i < numLayers - 1 ? varsInNetwork[i][j] : outputVars[j],
                                     i > 0 ? varsInNetwork[i - 1][j] : inputVars[j],
                                     i > 0 ? varsInNetwork[i - 1][j + 1] : inputVars[j + 1]);
            }
        }
        /* If there is no comparator on the last channel, copy its value for the next layer*/
        if (i % 2 != numBits % 2) {
            addEquals(s, i > 0 ? varsInNetwork[i - 1][numBits - 1] : inputVars[numBits - 1],
                      i < numLayers - 1 ? varsInNetwork[i][numBits - 1] : outputVars[numBits - 1]);
        }
    }
    if(opt_create_splitter){
        assert(numBits % 2 == 0);
        s.addClause(~mkLit(outputVars[numBits/2 - 1]));
        s.addClause(mkLit(outputVars[numBits/2 ]));
    }
}

/**********************************************************************
 * v <=> C, where C is a clause. 
 * This is, if v is true, at least one of the literals in C must be true. 
 * If v is false, ALL literals in C must be false
 */
void addEqual(Solver &s, Var &v, vec<Lit> &clause) {
    vec<Lit> ps;
    /* v implies clause */
    for (int i = 0; i < clause.size(); i++)
        ps.push(clause[i]);
    ps.push(~mkLit(v));
    s.addClause(ps);
    ps.clear();
    /* not v implies not clause */
    for (int i = 0; i < clause.size(); i++) {
        ps.push(mkLit(v));
        ps.push(~clause[i]);
        s.addClause(ps);
        ps.clear();
    }
}

/**********************************************************************
 * Avoid Tseitin-encoding for this case, which appears quite often in a comparator network. 
 * */
void add_a_implies_b_equal_c_or_d(Solver &s, Var a, Var b, Var c, Var d) {
    vec<Lit> ps;
    ps.push(~mkLit(a));
    ps.push(mkLit(b));
    ps.push(~mkLit(c)); // (a and not b) implies not c
    s.addClause(ps);
    ps.clear();
    ps.push(~mkLit(a));
    ps.push(mkLit(b));
    ps.push(~mkLit(d)); // (a and not b) implies not d
    s.addClause(ps);
    ps.clear();
    ps.push(~mkLit(a));
    ps.push(~mkLit(b));
    ps.push(mkLit(c));
    ps.push(mkLit(d));  // (a and  b) implies  c or d
    s.addClause(ps);
    ps.clear();
}

/**********************************************************************
 * Avoid Tseitin-encoding for this case, which appears quite often in a comparator network. 
 * */
void add_a_implies_b_equal_c_and_d(Solver &s, Var a, Var b, Var c, Var d) {
    vec<Lit> ps;
    ps.push(~mkLit(a));
    ps.push(~mkLit(b));
    ps.push(mkLit(c)); // (a and b) implies c
    s.addClause(ps);
    ps.clear();
    ps.push(~mkLit(a));
    ps.push(~mkLit(b));
    ps.push(mkLit(d)); // (a and b) implies d
    s.addClause(ps);
    ps.clear();
    ps.push(~mkLit(a));
    ps.push(mkLit(b));
    ps.push(~mkLit(c));
    ps.push(~mkLit(d));  // (a and not b) implies (not c or not d)
    s.addClause(ps);
    ps.clear();
}

/**********************************************************************
 * Avoid Tseitin-encoding for this case, which appears quite often in a comparator network. 
 * */
void add_a_implies_b_equal_c(Solver &s, Lit a, Lit b, Lit c) {
    vec<Lit> ps;
    ps.push(~a);
    ps.push(~b);
    ps.push(c); // (a and b) imply c
    s.addClause(ps);
    ps.clear();
    ps.push(~a);
    ps.push(b);
    ps.push(~c); // (a and not b) imply (not c)
    s.addClause(ps);
}

/******************************************************************************
 * Create a test-network. 
 * For each possible comparator, a variable is created and stored in "compVars"
 * This does NOT test whether the network is correct!
 */
void createTestNetWork(Solver &s, vector<Var> &inputVars, vector<Var> &outputVars, int numBits, int numLayers,
                       map<comparator, Var> &compVars, map<pair<int, int>, Var> &internalVars) {
    // create variables for inner states: 
    Var varsInNetwork[numLayers - 1][numBits];
    for (int i = 0; i < numLayers - 1; i++) {
        for (int j = 0; j < numBits; j++) {
            varsInNetwork[i][j] = s.newVar();
            internalVars[make_pair(i, j)] = varsInNetwork[i][j];
        }
    }
    // Create variables to describe which comparators are selected
    for (int i = 0; i < numLayers; i++) {
        for (int j = 0; j < numBits; j++) {
            for (int k = j + 1; k < numBits; k++) {
                Var c = s.newVar();
                compVars[comparator(i, j, k)] = c;
            }
        }
    }
    // compute dependency between inner states and comparators
    for (int i = 0; i < numLayers; i++) {
        for (int j = 0; j < numBits; j++) {
            // create unused-variable: 
            Var u = s.newVar();
            vec<Lit> compLits;
            for (int k = 0; k < numBits; k++) {
                if (j != k) {
                    Var v = compVars[comparator(i, min(j, k), max(j, k))];
                    compLits.push(mkLit(v));
                }
            }
            addEqual(s, u, compLits);
            // if there is no comparator for this line, the the output will be equal to the input
            add_a_implies_b_equal_c(s, ~mkLit(u), mkLit(i > 0 ? varsInNetwork[i - 1][j] : inputVars[j]),
                                    mkLit(i < numLayers - 1 ? varsInNetwork[i][j] : outputVars[j]));
            for (int k = j + 1; k < numBits; k++) {
                if (j != k) {
                    int max = j > k ? j : k;
                    int min = j < k ? j : k;
                    add_a_implies_b_equal_c_or_d(s, compVars[comparator(i, min, max)],
                                                 i < numLayers - 1 ? varsInNetwork[i][max] : outputVars[max],
                                                 i > 0 ? varsInNetwork[i - 1][max] : inputVars[max],
                                                 i > 0 ? varsInNetwork[i - 1][min] : inputVars[min]);
                    add_a_implies_b_equal_c_and_d(s, compVars[comparator(i, min, max)],
                                                  i < numLayers - 1 ? varsInNetwork[i][min] : outputVars[min],
                                                  i > 0 ? varsInNetwork[i - 1][max] : inputVars[max],
                                                  i > 0 ? varsInNetwork[i - 1][min] : inputVars[min]);
                }
            }
        }
    }
}

void addAtLeastOneDiffers(Solver &s, vector<Var> &out1, vector<Var> &out2, vector<Var> &diffIndVars) {
    vec<Lit> diffVars;
    for (unsigned i = 0; i < out1.size(); i++) {
        /*
         * hand-crafted: Encode all 4 situations
         * (x and y) => not t
         * (not x and not y) => not t
         * (x and not y) => t
         * (not x and y) => t
         */
        Var t = s.newVar();
        diffIndVars.push_back(t);
        diffVars.push(mkLit(t));
        Var &x = out1[i];
        Var &y = out2[i];

        vec<Lit> ps;
        ps.push(mkLit(t));
        ps.push(~mkLit(x));
        ps.push(mkLit(y));
        s.addClause(ps);
        ps.clear();

        ps.push(mkLit(t));
        ps.push(mkLit(x));
        ps.push(~mkLit(y));
        s.addClause(ps);
        ps.clear();

        ps.push(~mkLit(t));
        ps.push(mkLit(x));
        ps.push(mkLit(y));
        s.addClause(ps);
        ps.clear();

        ps.push(~mkLit(t));
        ps.push(~mkLit(x));
        ps.push(~mkLit(y));
        s.addClause(ps);
        ps.clear();

    }
    s.addClause(diffVars);
}

/******************************************************************************
 * Parse our csv-file 
 */
vector<vector<comparator> > allPrefixes;
void parseSecondlayer(vector<comparator> &out, const char *fileName, int row) {
    FILE *fp = fopen(fileName, "r");
    allPrefixes.clear();
    if(myMPI_rank <= 0) printf("c parse called! \n");
    int BUF_SIZE = 1024;
    char buffer[BUF_SIZE];
    int rowRead = 0;
    while (fp && !feof(fp)) {
        vector<comparator> tmp;
        fscanf(fp, "%s", buffer);
        char *buff = strtok(buffer, ";");
        while (buff) {

            int a, b, c;
            a = atoi(buff);
            if(!buff)
                break;
            buff = strtok(NULL, ";");
            if(!buff)
                break;
            b = atoi(buff);
            buff = strtok(NULL, ";");
            if(!buff)
                break;
            c = atoi(buff);
            buff = strtok(NULL, ";");
            tmp.push_back(comparator(a, b, c));
        }
        //printf("c read row %d\n", rowRead++);
        if(tmp.size() > 0)
            allPrefixes.push_back(tmp);
    }
    if(myMPI_rank <= 0) printf("c Parsed %d prefixes...\n", allPrefixes.size() );
    out.clear();
    vector<comparator> & toAdd = allPrefixes[row];
    for(int i = 0 ; i < toAdd.size();i++){
        if(toAdd[i].layer < opt_maxPrefLayer)
            out.push_back(toAdd[i]);
    }
    //out.insert(out.end(), allPrefixes[row].begin(), allPrefixes[row].end());
}

/******************************************************************************
 * Add once-constraint to the formula, ensuring that every channel is used only
 * once in each layer, i.e. c_{i, j, k} => not c_{i, j, l} forall l != k
 */
void once(Solver &s, int n, int d, map<comparator, Var> &compVars) {
    for (int i = 0; i < d; i++) {
        for (int j = 0; j < n; j++) {
            for (int k = 0; k < n; k++) {
                for (int l = k + 1; l < n; l++) {
                    if (k != l && j != k && j != l) {
                        vec<Lit> ps;
                        ps.push(~mkLit(compVars[comparator(i, min(j, k), max(j, k))]));
                        ps.push(~mkLit(compVars[comparator(i, min(j, l), max(j, l))]));
                        s.addClause(ps);
                    }
                }
            }
        }
    }
}

/******************************************************************************
 * Add variables indicating which channels are used
 */
void createUsedVariables(Solver &s, int n, int d, map<comparator, Var> &compVars, map<pair<int, int>, Var> &used) {
    for (int i = 0; i < d; i++) {
        for (int j = 0; j < n; j++) {
            vec<Lit> ps;
            Var v = s.newVar();
            used[make_pair(i, j)] = v;
            for (int k = 0; k < n; k++) {
                if (k < j)
                    ps.push(mkLit(compVars[comparator(i, k, j)]));
                else if (k > j)
                    ps.push(mkLit(compVars[comparator(i, j, k)]));
            }
            addEqual(s, v, ps);
        }
    }
}


/*
 * For the case of splitters, create a constraint that comparators in the last layer must range from the
 * upper to the lower half of the network
 * */

void createConstraintsForLastSplitLayer(Solver &s, int n, int d, map<comparator, Var> &compVars){

    for(int i = 0 ; i < n ; i++){
        for(int j = i+1 ; j < n ; j++){
            assert(compVars.count(comparator(d-1, i, j)));
            if( j < n/2-1 || i >= n/2){
                printf("c forbidding comparator %d -> %d in last layer! \n", i, j);
                s.addClause(~mkLit(compVars[comparator(d-1, i, j)]));
            }
        }
    }
    printf("c TODO!!! \n");

    if(opt_llGuess){
        // Okay, make a wild guess.
        // we cannot assume the last layer to be a half cleaner, however, maybe it's similar?
        for(int i = 0 ; 2*i < n ; i++){
            vec<Lit> ps;
            int other = n-i-1;
            if(other -1 >= n/2){// one shorter

                assert(compVars.count(comparator(d-1, i, other-1)));
                ps.push(mkLit(compVars[comparator(d-1, i, other-1)]));
            }
            assert(compVars.count(comparator(d-1, i, other)));
            ps.push(mkLit(compVars[comparator(d-1, i, other)]));
            if(other +1 < n){// one shorter

                assert(compVars.count(comparator(d-1, i, other+1)));
                ps.push(mkLit(compVars[comparator(d-1, i, other+1)]));
            }
            s.addClause(ps);
        }
    }
}

/******************************************************************************
 * Every comparator of length 1 has to be used at least in one layer (cf. Knuth, TAOCP)
 */
void createConstraintsForLength1Comparators(Solver &s, int n, int d, map<comparator, Var> &compVars) {
    for (int i = 0; i < n - 1; i++) {
        vec<Lit> ps;
        for (int j = 0; j < d; j++) {
            ps.push(mkLit(compVars[comparator(j, i, i + 1)]));
        }
        s.addClause(ps);
    }
}

/******************************************************************************
 * Add constraints on layer layer
 */
void onlyShortComparatorsInLastLayer(Solver &s, int n, int d, map<comparator, Var> &compVars, vec<Lit> &ps) {
    for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
            /* Handled by Phi2 as well*/
            if (j > i + 1) {
                ps.push(~mkLit(compVars[comparator(d - 1, i, j)]));
                s.addClause(ps);
                ps.clear();
            }
            if (j > i + 3) {
                ps.push(~mkLit(compVars[comparator(d - 2, i, j)]));
                s.addClause(ps);
                ps.clear();
            }
        }
    }
}

/******************************************************************************
 * Add constraint phi_1 to the formula (see the article for more details)
 */
void phi_1(Solver &s, int n, int d, map<comparator, Var> &compVars, map<pair<int, int>, Var> &used) {
    for (int i = d; i < d; i++) {
        for (int j = 0; j < n; j++) {
            for (int k = j + 2; k < n; k++) {
                vec<Lit> ps;
                ps.push(~mkLit(compVars[comparator(i, j, k)]));
                for (int i2 = i + 1; i2 < d; i2++) {
                    ps.push(mkLit(used[make_pair(i2, j)]));
                    ps.push(mkLit(used[make_pair(i2, k)]));
                }
                s.addClause(ps);
            }
        }
    }
}

/******************************************************************************
 * Add constraint phi_3 to the formula (see the article for more details)
 */
void phi_3(Solver &s, int n, int d, map<comparator, Var> &compVars) {
    for (int i = 0; i < n - 3; i++) {
        vec<Lit> ps;
        ps.push(~mkLit(compVars[comparator(d - 2, i, i + 3)]));
        ps.push(mkLit(compVars[comparator(d - 1, i, i + 1)]));
        s.addClause(ps);
        ps.clear();
        ps.push(~mkLit(compVars[comparator(d - 2, i, i + 3)]));
        ps.push(mkLit(compVars[comparator(d - 1, i + 2, i + 3)]));
        s.addClause(ps);
        ps.clear();
    }
}

/******************************************************************************
 * Add constraint phi_4 to the formula (see the article for more details)
 */
void phi_4(Solver &s, int n, int d, map<comparator, Var> &compVars) {
    for (int i = 0; i < n - 2; i++) {
        vec<Lit> ps;
        ps.push(~mkLit(compVars[comparator(d - 2, i, i + 2)]));
        ps.push(mkLit(compVars[comparator(d - 1, i, i + 1)]));
        ps.push(mkLit(compVars[comparator(d - 1, i + 1, i + 2)]));
        s.addClause(ps);
    }
}

/******************************************************************************
 * Add constraint psi_1 to the formula (see the article for more details)
 */
void psi_1(Solver &s, int n, int d, map<pair<int, int>, Var> &used) {
    for (int i = 0; i < n - 1; i++) {
        vec<Lit> ps;
        ps.push(mkLit(used[make_pair(d - 1, i)]));
        ps.push(mkLit(used[make_pair(d - 1, i + 1)]));
        s.addClause(ps);
    }
}

/******************************************************************************
 * Add constraint psi_2a to the formula (see the article for more details)
 */
void psi_2a(Solver &s, int n, int d, map<comparator, Var> &compVars, map<pair<int, int>, Var> &used) {
    for (int i = 0; i < n - 3; i++) {
        vec<Lit> ps;
        ps.push(~mkLit(compVars[comparator(d - 1, i, i + 1)]));
        ps.push(~mkLit(compVars[comparator(d - 1, i + 2, i + 3)]));
        ps.push(mkLit(used[make_pair(d - 2, i)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 2)]));
        s.addClause(ps);
        ps.clear();

        ps.push(~mkLit(compVars[comparator(d - 1, i, i + 1)]));
        ps.push(~mkLit(compVars[comparator(d - 1, i + 2, i + 3)]));
        ps.push(mkLit(used[make_pair(d - 2, i)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 3)]));
        s.addClause(ps);
        ps.clear();

        ps.push(~mkLit(compVars[comparator(d - 1, i, i + 1)]));
        ps.push(~mkLit(compVars[comparator(d - 1, i + 2, i + 3)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 1)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 2)]));
        s.addClause(ps);
        ps.clear();

        ps.push(~mkLit(compVars[comparator(d - 1, i, i + 1)]));
        ps.push(~mkLit(compVars[comparator(d - 1, i + 2, i + 3)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 1)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 3)]));
        s.addClause(ps);
        ps.clear();
    }
}

/******************************************************************************
 * Add constraint psi_2b to the formula (see the article for more details)
 */
void psi_2b(Solver &s, int n, int d, map<comparator, Var> &compVars, map<pair<int, int>, Var> &used) {
    for (int i = 0; i < n - 2; i++) {
        vec<Lit> ps;
        ps.push(~mkLit(compVars[comparator(d - 1, i, i + 1)]));
        ps.push(mkLit(used[make_pair(d - 1, i + 2)]));
        ps.push(mkLit(used[make_pair(d - 2, i)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 2)]));
        s.addClause(ps);
        ps.clear();

        ps.push(~mkLit(compVars[comparator(d - 1, i, i + 1)]));
        ps.push(mkLit(used[make_pair(d - 1, i + 2)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 1)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 2)]));
        s.addClause(ps);
    }
}

/******************************************************************************
 * Add constraint psi_2c to the formula (see the article for more details)
 */
void psi_2c(Solver &s, int n, int d, map<comparator, Var> &compVars, map<pair<int, int>, Var> &used) {
    for (int i = 0; i < n - 2; i++) {
        vec<Lit> ps;
        ps.push(~mkLit(compVars[comparator(d - 1, i + 1, i + 2)]));
        ps.push(mkLit(used[make_pair(d - 1, i)]));
        ps.push(mkLit(used[make_pair(d - 2, i)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 1)]));
        s.addClause(ps);
        ps.clear();

        ps.push(~mkLit(compVars[comparator(d - 1, i + 1, i + 2)]));
        ps.push(mkLit(used[make_pair(d - 1, i)]));
        ps.push(mkLit(used[make_pair(d - 2, i)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 2)]));
        s.addClause(ps);
    }
}

/******************************************************************************
 * Add constraint psi_3a to the formula (see the article for more details)
 */
void psi_3a(Solver &s, int n, int d, map<comparator, Var> &compVars, map<pair<int, int>, Var> &used) {
    for (int i = 0; i < n - 2; i++) {
        vec<Lit> ps;
        ps.push(~mkLit(compVars[comparator(d - 1, i, i + 1)]));
        ps.push(mkLit(used[make_pair(d - 1, i + 2)]));
        ps.push(mkLit(used[make_pair(d - 2, i)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 1)]));
        s.addClause(ps);
    }
}

/******************************************************************************
 * Add constraint psi_3b to the formula (see the article for more details)
 */
void psi_3b(Solver &s, int n, int d, map<comparator, Var> &compVars, map<pair<int, int>, Var> &used) {
    for (int i = 1; i < n - 1; i++) {
        vec<Lit> ps;
        ps.push(~mkLit(compVars[comparator(d - 1, i, i + 1)]));
        ps.push(mkLit(used[make_pair(d - 1, i - 1)]));
        ps.push(mkLit(used[make_pair(d - 2, i)]));
        ps.push(mkLit(used[make_pair(d - 2, i + 1)]));
        s.addClause(ps);
    }
}
vec<Lit> testAssumptions;

void createOnOfThesePrefixes(Solver & s, int n, map<comparator, Var> & compVars, map<pair<int, int>, Var> &used,
                             vector<comparator> & secondLayer){
    vector<Var> prefixVars;
    set<comparator> possComps;
    int maxLayer = -1;
    map<comparator, int> noOccurs;
    for(int i = 0 ; i < allPrefixes.size();i++){
        // Is this compatible?
        bool useThis = true;
        vector<comparator> & thisPrefix = allPrefixes[i];
        set<pair<int, int> > usedChannels;

        if(thisPrefix.size() < secondLayer.size())
            useThis = false;
        //assert(!useThis || thisPrefix.size() >= secondLayer.size());
        for(int j = 0 ; useThis&& j < secondLayer.size();j++){
            assert(j < secondLayer.size());
            assert(j < thisPrefix.size());
            comparator & c1 = secondLayer[j];
            comparator & c2 = thisPrefix[j];
            if(c1.layer != c2.layer || c1.minchan != c2.minchan || c1.maxchan != c2.maxchan){
                useThis = false;
                printf("c skipping prefix %d: l1 %d l2 %d c1.min %d c2.min %d c1.max %d c2.max %d\n",
                       i, c1.layer, c2.layer, c1.minchan, c2.minchan, c1.maxchan, c2.maxchan);
            }

        }
        if(useThis){
            printf("c using prefix %d\n", i);
            Var v = s.newVar();
            vec<Lit> comps;
            for(int j = 0 ; j < thisPrefix.size();j++){
                comparator & c = thisPrefix[j];
                if(c.layer > maxLayer)
                    maxLayer = c.layer;
                usedChannels.insert(make_pair(c.layer, c.minchan));
                usedChannels.insert(make_pair(c.layer, c.maxchan));
                assert(compVars.count(thisPrefix[j]));
                comps.push(mkLit(compVars[thisPrefix[j]]));
                possComps.insert(c);
            }
            for(int j = 0 ; j < maxLayer ; j++)
                for(int k = 0 ; k < n ; k++)
                    if(usedChannels.count(make_pair(j,k)) == 0){
                        assert(used.count(make_pair(j,k)));
                        comps.push(~mkLit(used[make_pair(j,k)]));
                    }
            printf("c and reifying the and\n");
            reifyAnd(s, mkLit(v), comps);
            prefixVars.push_back(v);
        }
    }
    for(int i = 0 ; i < allPrefixes.size();i++){
        vector<comparator> & thisPrefix = allPrefixes[i];
        for(int j = 0 ; j < thisPrefix.size();j++){
            comparator & c = thisPrefix[j];
            if(c.layer == maxLayer)
                noOccurs[c]++;
        }
    }

    // now one of these vars must hold:
    printf("c TODO: CHANGE ME: Naive AMO-Encoding! \n");
    vec<Lit> ps;
    for(int i = 0 ; i < prefixVars.size();i++){
        ps.push(mkLit(prefixVars[i]));
        testAssumptions.push(~mkLit(prefixVars[i]));
    }
    s.addClause(ps);
    for(int i = 0 ; i < prefixVars.size();i++){
        for(int j = i+1 ; j < prefixVars.size();j++)
            s.addClause(~mkLit(prefixVars[i]), ~mkLit(prefixVars[j]));
    }
    int maxOcc = 0;
    for(map<comparator, int>::iterator it = noOccurs.begin() ; it != noOccurs.end();it++){
        if(it->second > 3){
            const comparator & c = it->first;
            printf("c comp %d -> %d occurs %d times\n", c.minchan, c.maxchan, it->second);
            int nbBefore = s.nFreeVars();
            if(it->second == allPrefixes.size()){
                s.checkLiteral(~mkLit(compVars[c]));
            }
            if(s.nFreeVars() != nbBefore){
                printf("c fixed this variable! \n");
            }
            if(it->second > maxOcc && it->second < allPrefixes.size()){
                maxOcc = it->second;
                testAssumptions.clear();
                testAssumptions.push(~mkLit(compVars[c]));
                printf("c pushing assumption NOT %d -> %d\n", c.minchan, c.maxchan);
            }
        }
    }
    /*printf("c testing comps: \n");
    int oldVer = s.verbosity;
    s.verbosity = 0;
    for(int i = 0 ; i < n ; i++){
        for(int j = i+1 ; j < n ; j++){
            comparator c(maxLayer, i, j);
            assert(compVars.count(c));
            if(!possComps.count(c)){
                Var v = compVars[c];
                printf("c verifiying that comp %d -> %d cannot be used! \n", i, j);
                vec<Lit> ps;
                ps.push(mkLit(v));
                int conflBefore = s.conflicts;
                lbool ret = s.solveLimited(ps);
                printf("c solver returned false? %d\n", ret == l_False);
                printf("c conlfs required: %d\n", s.conflicts - conflBefore);
            }
        }
    }
    s.verbosity = oldVer;
*/

}


/******************************************************************************
 * Create a formula for a feasible comparator network. 
 * This can be extended to restrict the network in severals ways.
 */
void createNetWorkFormula(Solver &s, int n, int d, map<comparator, Var> &compVars, map<pair<int, int>, Var> &used,
                          Var &T, Var &F, bool createSplitModule) {
    T = s.newVar();
    vec<Lit> units;
    units.push(mkLit(T));
    s.addClause(units);
    units.clear();
    F = s.newVar();
    units.push(~mkLit(F));
    s.addClause(units);
    units.clear();
    // create a variable for each possible comparator: 
    int minV = 0xFFFFFF;
    int maxV = 0;
    for (int i = 0; i < d; i++) {
        for (int j = 0; j < n; j++) {
            for (int k = j + 1; k < n; k++) {
                Var v = s.newVar();
                minV = min(minV, v);
                maxV = max(maxV, v);
                compVars[comparator(i, j, k)] = v;
            }
        }
    }

    once(s, n, d, compVars);
    createUsedVariables(s, n, d, compVars, used);
    if(!createSplitModule){
        if(opt_shortComps)
            createConstraintsForLength1Comparators(s, n, d, compVars);
    }
    else{
        createConstraintsForLastSplitLayer(s, n, d, compVars);
    }

    /********************************************************************
    * Create first layer (cf. the paper :) )
    */

    bool fixFirst = optfixFirstLayer;
    int maxFixedPrefLayer = -1;
    if (opt_prefLayer) {
        const char *_prefFileName = prefFileName ? (const char *) prefFileName : "layers.txt";
        if(myMPI_rank <= 0) printf("Reading input from %s\n", _prefFileName);
        vector<comparator> secondlayer;
        parseSecondlayer(secondlayer, _prefFileName, opt_row);
        if(myMPI_rank <= 0){
            printf("c prefix: \n");
            printComps(secondlayer, n, d);
        }
        // if nothing was read, try "Parberry" first layer
        if (secondlayer.size() == 0) {
            for (int i = 0; i < n; i += 2) {
                if (i + 1 < n) {
                    vec<Lit> ps;
                    ps.push(mkLit(compVars[comparator(0, i, i + 1)]));
                    s.addClause(ps);
                }
            }
        }
        // Remember which wires are used in which layer. 
        // In case a wire is not used, forbid adding a comparator to it
        set<pair<int, int> > usedWiresInLayer;
        int highestLayerInFile = 0;
        for (vector<comparator>::iterator it = secondlayer.begin(); it != secondlayer.end(); it++) {
            vec<Lit> ps;
            usedWiresInLayer.insert(make_pair(it->layer, it->minchan));
            usedWiresInLayer.insert(make_pair(it->layer, it->maxchan));
            ps.push(mkLit(compVars[*it]));
            s.addClause(ps);
            ps.clear();
            if(myMPI_rank <= 0) printf("Forcing %d: %d -> %d\n", it->layer, it->minchan, it->maxchan);
            highestLayerInFile = max(highestLayerInFile, it->layer);
        }
        maxFixedPrefLayer = highestLayerInFile;
        if(myMPI_rank <= 0) printf("Setting maxFixedPrefLayer=%d\n", maxFixedPrefLayer);
        for (int i = 0; i < d && i <= highestLayerInFile; i++) {
            for (int j = 0; j < n; j++) {
                if (usedWiresInLayer.count(make_pair(i, j)) == 0) {
                    vec<Lit> ps;
                    ps.push(~mkLit(used[make_pair(i, j)]));
                    s.addClause(ps);
                    if(myMPI_rank <= 0) printf("Forcing used[%d,%d]=false  (%d, %d)\n", i, j, used[make_pair(i, j)], ps.size());
                }
            }
        }
        //createOnOfThesePrefixes(s, n, compVars, used, secondlayer);
    } else if (fixFirst) {

        printf("Adding BZ-style first vector...\n");
        for (int j = 0; j < n - j - 1; j++) {
            vec<Lit> ps;
            ps.push(mkLit(compVars[comparator(0, j, n - j - 1)]));
            s.addClause(ps);
        }
        maxFixedPrefLayer = 0;
    }

    if (opt_lastLayerConstraints) {
        assert(!createSplitModule);
        vec<Lit> ps;
        onlyShortComparatorsInLastLayer(s, n, d, compVars, ps);
        phi_1(s, n, d, compVars, used);
        phi_3(s, n, d, compVars);
        phi_4(s, n, d, compVars);
        psi_1(s, n, d, used);
        psi_2a(s, n, d, compVars, used);
        psi_2b(s, n, d, compVars, used);
        psi_2c(s, n, d, compVars, used);
        psi_3a(s, n, d, compVars, used);
        psi_3b(s, n, d, compVars, used);

        // Redundantly add the following constraint:
        // If there is a comparator (l, i, j) and both used(l+1, i) and (l+1, j) are false, add a comparator there
        for (int l = 2; l < d - 2; l++) {
            for (int i = 0; i < n; i++) {
                for (int j = i + 1; j < n; j++) {
                    ps.push(~mkLit(compVars[comparator(l, i, j)]));
                    ps.push(mkLit(used[make_pair(l + 1, i)]));
                    ps.push(mkLit(used[make_pair(l + 1, j)]));
                    s.addClause(ps);
                    ps.clear();
                }
            }
        }
        // If there is a comparator (i,j) in layer l, then there is no comparator (i,j) in layer l+1
        for(int l = maxFixedPrefLayer ; l < d - 1 ; l++){
            for(int i = 0 ; i < n ; i++){
                for(int j = i+1 ; j < n ; j++){
                    if(compVars.count(comparator(l,i,j))){
                        if(compVars.count(comparator(l+1, i,j))){
                            vec<Lit> ps;
                            ps.push(~mkLit(compVars[comparator(l,i,j)]));
                            ps.push(~mkLit(compVars[comparator(l+1,i,j)]));
                            s.addClause(ps);
                        }
                    }
                }
            }
        }
    }
    else if(createSplitModule){
        if(opt_lastLayerHC){
            assert(n%2 == 0);
            for(int i = 0 ; i < n / 2 ; i++){
                s.addClause(mkLit(compVars[comparator(d-1, i, n-i-1)]));
            }
        }
    }

}


void addOneFromToRange(Solver &s, int layer, int from, int to, map<comparator, Var> &compVars,
                       map<comparator, Var> &rangeVars) {

    assert(rangeVars.find(comparator(layer, from, to)) == rangeVars.end());

    vec<Lit> ps;
    if (from < to) {
        if (from == to - 1) {
            rangeVars[comparator(layer, from, to)] = compVars[comparator(layer, from, to)];
        } else {
            Var v = s.newVar();
            for (int i = from + 1; i <= to; i++) {
                ps.push(mkLit(compVars[comparator(layer, from, i)]));
            }
            addEqual(s, v, ps);
            rangeVars[comparator(layer, from, to)] = v;
        }
    } else {
        if (from == to + 1) {
            rangeVars[comparator(layer, from, to)] = compVars[comparator(layer, to, from)];
        } else {
            Var v = s.newVar();
            for (int i = to; i < from; i++) {
                ps.push(mkLit(compVars[comparator(layer, i, from)]));
            }
            addEqual(s, v, ps);
            rangeVars[comparator(layer, from, to)] = v;
        }
    }

}

/******************************************************************************
 * Create the clauses corresponding to an input-vector using the improved encoding
 * presented in the article.
 */
void addInputImprovedEncoding(Solver &s, vector<bool> &newInput, int n, int d, triVarMap &compVarsInCreatedNW,
                              map<pair<int, int>, Var> &used, Var &T, Var &F, triVarMap &intVars,
                              triVarMap &rangeVars) {
    vector<bool> newOutput;
    static int calls = 0;
    calls++;
    map<pair<int, int>, Var> newInternalVars;
    int zeros = 0;
    for (unsigned i = 0; i < newInput.size(); i++) {
        if (!newInput[i]) {
            zeros++;
        }
    }
    for (unsigned i = 0; i < newInput.size(); i++) {
        newOutput.push_back(i < zeros ? false : true);
    }
    int leadingZeros = 0;
    for (unsigned i = 0; i < newInput.size(); i++) {
        if (newInput[i])
            break;
        else
            leadingZeros++;
    }
    int tailingOnes = 0;
    for (unsigned i = newInput.size() - 1; i >= 0; i--) {
        if (!newInput[i])
            break;
        else {
            tailingOnes++;
        }
    }
    /*if(zeros == 9){
        printf("c input %d zeros %d ones %d leading %d trailing\n", zeros, n-zeros, leadingZeros, tailingOnes);
    }*/
    // Create new internal variables
    for (int i = 0; i < d - 1; i++) {
        for (int j = 0; j < n; j++) {
            if (j < leadingZeros) {
                newInternalVars[make_pair(i, j)] = F;
                intVars.insert(make_pair(comparator(calls, i, j), F));
            } else if (j >= n - tailingOnes) {
                newInternalVars[make_pair(i, j)] = T;
                intVars.insert(make_pair(comparator(calls, i, j), T));
            } else {
                Var v = s.newVar();
                newInternalVars[make_pair(i, j)] = v;
                intVars.insert(make_pair(comparator(calls, i, j), v));
            }
        }
    }
    // Add input- and output-variables: 
    for (int j = 0; j < n; j++) {
        newInternalVars[make_pair(-1, j)] = newInput[j] ? T : F;
        assert(newInternalVars.count(make_pair(d - 1, j)) == 0);
        newInternalVars[make_pair(d - 1, j)] = newOutput[j] ? T : F;
    }
    // Add update-rules: 
    for (int i = 0; i < d; i++) {
        for (int j = leadingZeros; j < (n - tailingOnes); j++) {
            // Let us assume that the value on this channel is "1". 
            // Thus, this will stay unless there is a comparator down inside the window,
            // and the other input is "0". 
            vec<Lit> ps;
            // If none of the comparators to higher indices is used...
            if (rangeVars.count(comparator(i, j, n - tailingOnes - 1)) == 0) {
                addOneFromToRange(s, i, j, n - tailingOnes - 1, compVarsInCreatedNW, rangeVars);
            }
            ps.push(mkLit(rangeVars[comparator(i, j, n - tailingOnes - 1)]));
            // And the input is "1"
            ps.push(~mkLit(newInternalVars[make_pair(i - 1, j)]));
            // Then, the output is "1"
            ps.push(mkLit(newInternalVars[make_pair(i, j)]));
            s.addClause(ps);
            ps.clear();

            // Not let us assume there is a comparator to a higher index. 
            // This, this "1" will disappear if the other input is a "0"
            for (int k = j + 1; k < n - tailingOnes; k++) {
                // If the other input is "0"...
                ps.push(~mkLit(compVarsInCreatedNW[comparator(i, j, k)]));
                ps.push(mkLit(newInternalVars[make_pair(i - 1, k)]));
                ps.push(~mkLit(newInternalVars[make_pair(i, j)]));
                s.addClause(ps);
                ps.clear();
                // If both inputs equal "1"
                ps.push(~mkLit(compVarsInCreatedNW[comparator(i, j, k)]));
                ps.push(~mkLit(newInternalVars[make_pair(i - 1, k)]));
                ps.push(~mkLit(newInternalVars[make_pair(i - 1, j)]));
                ps.push(mkLit(newInternalVars[make_pair(i, j)]));
                s.addClause(ps);
                ps.clear();
            }
            // What if the input is "0"? 
            // No comparator to lower indices -> output will be zero
            if (rangeVars.count(comparator(i, j, leadingZeros)) == 0) {
                addOneFromToRange(s, i, j, leadingZeros, compVarsInCreatedNW, rangeVars);
            }
            ps.push(mkLit(rangeVars[comparator(i, j, leadingZeros)]));

            ps.push(mkLit(newInternalVars[make_pair(i - 1, j)]));
            ps.push(~mkLit(newInternalVars[make_pair(i, j)]));
            s.addClause(ps);
            ps.clear();
            for (int k = leadingZeros; k < j; k++) {
                // Comparator chosen, and other value="1" -> swap
                ps.push(~mkLit(compVarsInCreatedNW[comparator(i, k, j)]));
                ps.push(~mkLit(newInternalVars[make_pair(i - 1, k)]));
                ps.push(mkLit(newInternalVars[make_pair(i, j)]));
                s.addClause(ps);
                ps.clear();

                // Comparator chosen, and other value="0" -> still "0"
                ps.push(~mkLit(compVarsInCreatedNW[comparator(i, k, j)]));
                ps.push(mkLit(newInternalVars[make_pair(i - 1, k)]));
                ps.push(mkLit(newInternalVars[make_pair(i - 1, j)]));
                ps.push(~mkLit(newInternalVars[make_pair(i, j)]));
                s.addClause(ps);
                ps.clear();
            }
        }
    }
}

/******************************************************************************
 * Create the clauses for an input vecotr using the "old" encoding, due to Bundala and Zavodny.
 */
void addInputOldEncoding(Solver &s, vector<bool> &newInput, int n, int d, triVarMap &compVarsInCreatedNW,
                         map<pair<int, int>, Var> &used, Var &T, Var &F, triVarMap &intVars) {
    int nbBefore = s.nVars();
    int freeVarsBefore = s.nFreeVars();
    vector<bool> newOutput;
    static int calls = 0;
    calls++;
    map<pair<int, int>, Var> newInternalVars;
    int zeros = 0;
    for (unsigned i = 0; i < newInput.size(); i++) {
        if (!newInput[i]) {
            zeros++;
        }
    }
    for (unsigned i = 0; i < newInput.size(); i++) {
        newOutput.push_back(i < zeros ? false : true);
    }
    int leadingZeros = 0;
    for (int i = 0; i < newInput.size(); i++) {
        if (newInput[i])
            break;
        else
            leadingZeros++;
    }
    int tailingOnes = 0;
    for (unsigned i = newInput.size() - 1; i >= 0; i--) {
        if (!newInput[i])
            break;
        else {
            tailingOnes++;
        }
    }
    // Create new internal variables
    for (unsigned i = 0; i < d - 1; i++) {
        for (int j = 0; j < n; j++) {
            Var v = s.newVar();
            newInternalVars[make_pair(i, j)] = v;
            intVars.insert(make_pair(comparator(calls, i, j), v));
        }
    }
    // add input and output-variables
    for (int j = 0; j < n; j++) {
        newInternalVars[make_pair(-1, j)] = newInput[j] ? T : F;
        assert(newInternalVars.count(make_pair(d - 1, j)) == 0);
        newInternalVars[make_pair(d - 1, j)] = newOutput[j] ? T : F;
    }

    // add update-rules: 
    for (int i = 0; i < d; i++) {
        for (int j = 0; j < n; j++) {
            if (i < d - 1 && j < leadingZeros) {
                vec<Lit> ps;
                ps.push(~mkLit(newInternalVars[make_pair(i, j)]));
                s.addClause(ps);
            } else if (i < d - 1 && j >= n - tailingOnes) {
                vec<Lit> ps;
                ps.push(mkLit(newInternalVars[make_pair(i, j)]));
                s.addClause(ps);
            }
            // not used -> copy
            add_a_implies_b_equal_c(s, ~mkLit(used[make_pair(i, j)]),
                                    mkLit(i > 0 ? newInternalVars[make_pair(i - 1, j)] : newInput[j] ? T : F),
                                    mkLit(i < d - 1 ? newInternalVars[make_pair(i, j)] : newOutput[j] ? T : F));
            for (int k = j + 1; k < n; k++) {
                add_a_implies_b_equal_c_or_d(s, compVarsInCreatedNW[comparator(i, j, k)],
                                             i < d - 1 ? newInternalVars[make_pair(i, k)] : newOutput[k] ? T : F,
                                             i > 0 ? newInternalVars[make_pair(i - 1, k)] : newInput[k] ? T : F,
                                             i > 0 ? newInternalVars[make_pair(i - 1, j)] : newInput[j] ? T : F);
                add_a_implies_b_equal_c_and_d(s, compVarsInCreatedNW[comparator(i, j, k)],
                                              i < d - 1 ? newInternalVars[make_pair(i, j)] : newOutput[j] ? T : F,
                                              i > 0 ? newInternalVars[make_pair(i - 1, k)] : newInput[k] ? T : F,
                                              i > 0 ? newInternalVars[make_pair(i - 1, j)] : newInput[j] ? T : F);
            }
        }
    }

    int nbAfter = s.nVars();
    printf("\n");
    for (int i = 0; i < newInput.size(); i++) {
        printf("%d ", newInput[i] ? 1 : 0);
    }

    s.verbosity = 0;
    for (map<pair<int, int>, Var>::reverse_iterator it = newInternalVars.rbegin(); it != newInternalVars.rend(); it++) {
        s.checkLiteral(mkLit(it->second));
        s.checkLiteral(~mkLit(it->second));
    }
    s.verbosity = 1;

    int zerosInWindow = zeros - leadingZeros;
    int onesInWindow = n - zeros - tailingOnes;
    printf("In windows: %d zeros, %d ones\n", zerosInWindow, onesInWindow);
    printf("And %d more free vars\n", s.nFreeVars() - freeVarsBefore);
    printf("\nleading zeros: %d, tailing ones: %d (%d-%d)\n", leadingZeros, tailingOnes, nbBefore, nbAfter);
}

struct testInput {
    int input;
    int outPutOfPrefix;
    int leadingZeros;
    int tailingOnes;
    int windowSize;

    testInput(int _in, int _out, int _lead, int _tail, int _size) {
        input = _in;
        outPutOfPrefix = _out;
        leadingZeros = _lead;
        tailingOnes = _tail;
        windowSize = _size;
    }
};

bool isSmallerInput(const testInput &ti1, const testInput &ti2) {
    // Inputs of small window size first
    if (ti1.windowSize != ti2.windowSize) {
        return ti1.windowSize < ti2.windowSize;
    }
    // If the window sizes are equal, try to choose input for the middle of the network
    // This is, we multiply the number of leading zeros, and tailing ones
    // 
    int c1 = ti1.leadingZeros * ti1.tailingOnes;
    int c2 = ti2.leadingZeros * ti2.tailingOnes;
    if (c1 != c2) {
        return c1 > c2;
    }
    // Assume that there is only one "input" for each "output"
    return ti1.outPutOfPrefix < ti2.outPutOfPrefix;
}

bool isSet(int val, int bit) {
    return val & (1 << bit);
}

int getNumUnsorted(int val, int n) {
    int leadingZeros = 0, nZeros = 0;
    int tailingOnes = 0, nOnes = 0;
    while (leadingZeros < n && !isSet(val, leadingZeros))
        leadingZeros++;
    while (tailingOnes < n && isSet(val, n - tailingOnes - 1))
        tailingOnes++;

    for (int i = 0; i < n; i++) {
        if (isSet(val, i))
            nOnes++;
        else
            nZeros++;
    }
    return min(nZeros - leadingZeros, nOnes - tailingOnes);
}

int getNumOnes(int val, int n){
    int ret = 0;
    for(int i = 0 ; i <=n ; i++)
        if (val & (1<<i))
            ret++;
    return ret;
}


int countNumOnes(int v){
    int ret = 0;
    for(int i = 0 ; i < 24 ; i++)
        if(v & (1<<i))
            ret++;
    return ret;
}


/**********************************************************************
 * Initialize the solver with some inputs.
 * */
void addSomeInputs(Solver &s, vector<comparator> &compsReadFromFile, int n, int d,
                   map<comparator, Var> &compVarsInCreatedNW, map<pair<int, int>, Var> &used, Var &T, Var &F,
                   map<comparator, Var> &intVars, int k, triVarMap &rangeVars) {

    // intputs with k leading zeros
    int added = 0;
    if(myMPI_rank <= 0) printf("Window size: %d\n", n - k);
    map<comparator, Var> internalVars;
    // map: Input -> Vector after first two layers
    map<int, int> inputsToAdd;

    if(myMPI_rank <= 0) printf("Creating inputs, read %d comparators from file\n", compsReadFromFile.size());
    // Small change: Get ALL possible outputs of the prefix here
    bool useAllPrefixes = false;
    set<int> inputsSeen;
    int multiples = 0;
    for (int i = 0; i < (1 << n); i++) {
        if(! opt_create_splitter || getNumOnes(i, n) == n/2){

            if(useAllPrefixes){
                for(int j = 0 ; j < allPrefixes.size();j++){
                    int tmpStuff = eval(i, allPrefixes[j]);
                    if (inputsToAdd.find(tmpStuff) == inputsToAdd.end()) {
                        if(inputsSeen.count(i)){
                            //printf("c adding input %d, it was added before! \n", i);
                            multiples++;
                        }
                        else{
                            inputsToAdd[tmpStuff] = i;
                            inputsSeen.insert(i);
                        }
                    }
                }
            }
            else{
                int unsorted = getNumUnsorted(i, n);

                int tmpStuff = compsReadFromFile.size() == 0 ? evalParberry(i, n) : eval(i, compsReadFromFile);
                // getRating : num of leading zeros + num of tailing ones


                if (inputsToAdd.find(tmpStuff) == inputsToAdd.end()) {
                    inputsToAdd[tmpStuff] = i;
                } else {
                    // Already found this vector AFTER the first two layers. What does the input for this look like?
                    if (getRating(i, n) > getRating(inputsToAdd[tmpStuff], n)) {
                        inputsToAdd[tmpStuff] = i;
                    }
                }
            }
        }

    }

    vector<testInput> possibleInputs;
    for (map<int, int>::iterator it = inputsToAdd.begin(); it != inputsToAdd.end(); it++) {
        int _out = it->first;
        int _in = it->second;
        int _lead = getNumLeadingZeros(_out, n);
        int _tail = getNumTailingOnes(_out, n);

        testInput t1(_in, _out, _lead, _tail, n - (_lead + _tail));
        possibleInputs.push_back(t1);

    }
    sort(possibleInputs.begin(), possibleInputs.end(), isSmallerInput);

    int windowSize2Add = n - k;
    int toAdd = opt_minNumInputs;
    if(myMPI_rank <= 0) printf("Starting to add inputs, windowSize2Add=%d, opt_minNumInputs=%d\n", windowSize2Add, toAdd);
    if(myMPI_rank <= 0) printf("Chose %d out of %d\n", possibleInputs.size(), inputsToAdd.size());
    int iters = 0;
    vector<int> numOnes(n+1, 0);
    for (vector<testInput>::iterator it = possibleInputs.begin(); it != possibleInputs.end(); it++) {
        iters++;
        //if(iters % 100 == 0){
         //   printf("c added %d inputs, now %d vars, %d clauses! \n", iters, s.nVars(), s.nClauses());
        //}
        if (it->windowSize > windowSize2Add && added >= toAdd)
            break;
        if (it->windowSize > 0) {
            // Skip sorted inputs
            vector<bool> inputs;
            numOnes[countNumOnes(it->input)]++;
            for (int j = 0; j < n; j++) {
                inputs.push_back((it->input & (1 << j)) != 0);
            }

            if (opt_optEncoding) {
                addInputImprovedEncoding(s, inputs, n, d, compVarsInCreatedNW, used, T, F, intVars, rangeVars);
            } else {
                addInputOldEncoding(s, inputs, n, d, compVarsInCreatedNW, used, T, F, intVars);
            }
            added++;
        }
    }

    if(myMPI_rank <= 0) {
        printf("c Added %d inputs\n", added);
        for(int i = 0 ; i < numOnes.size() ; i++)
            printf("c inputs with %d ones: %d\n", i, numOnes[i] );
    }
    bool fCheckDone = false;
    while (!fCheckDone) {
        int freeBefore = s.nFreeVars();
        s.FL_Check_fast();
        //s.failedLiteralCheck();
        fCheckDone = s.nFreeVars() == freeBefore;
    }
    //s.toDimacs("formula.cnf");
}

bool findFeasibleNetwork(Solver &s, int iteration, vec<Lit> &allAssumptions) {

    //s.failedLiteralCheck();
    if (iteration >= 0) {
        double t_failed = cpuTime();
        // Use failed literal check less often if solutions are counted...
        if (iteration % 10 == 1 && (!false || iteration < 1000)) {

           // s.failedLiteralCheck();
            if(myMPI_rank <= 0)printf("Failed literal check took %5.3lf s\n", cpuTime() - t_failed);
        }
    }

    bool done = false;
    bool netWorkCreated = false;
    while (!done) {
        s.budgetForRandom = 0;
        if(opt_mpi ){
            s.mpi_rank = myMPI_rank;
            s.mpi_num_ranks = num_mpi_ranks;
            lbool test = s.mpi_solve(firstCubes); // s.DFS_Solve(firstCubes);
            if(test != l_True)
                return false;
            return true;
        }
        bool solved = s.solve(allAssumptions);
        if (solved) {
            done = true;
            netWorkCreated = true;
        } else if (allAssumptions.size() == 0) {
            done = true;
        } else {
            printf("Assumptions failed, removing one. Now: %d assumptions remaining\n", allAssumptions.size());
            allAssumptions.pop();
            s.addClause(s.conflict);
        }
    }
    return netWorkCreated;
}

bool findFeasibleNetwork(Solver &s, int iteration) {
    if(!s.okay())
        return false;
    vec<Lit> emptyAssumptions;
    for(int i = 0 ; i < testAssumptions.size() ; i++)
        emptyAssumptions.push(testAssumptions[i]);

    return findFeasibleNetwork(s, iteration, emptyAssumptions);
}


/**********************************************
 * Try to find a counter-example of minimum size. 
 * This version is quite dumb and tries ALL O(n^2) possibilities...
 * */
bool findMinSizeCounterExample(Solver &s, vec<Lit> &assumptions, vector<Var> &inputVars, vector<bool> &bestInput, int n,
                               map<pair<int, int>, Var> &innerVars) {
    int bestRating = n + 1;
    bool counterExampleFound = false;
    int iterations = 0;
    for (int lead = 0; lead < n; lead++) {
        for (int tail = 0; tail < n && lead + tail < n; tail++) {
            if (n - (tail + lead) > bestRating)
                continue;
            iterations++;
            vec<Lit> allAssumptions;
            for (int i = 0; i < assumptions.size(); i++) {
                allAssumptions.push(assumptions[i]);
            }
            bool useInnerVars = false;
            if (useInnerVars) {
                // push "lead" nums of zeros
                for (int i = 0; i < lead; i++)
                    allAssumptions.push(~mkLit(innerVars[make_pair(1, i)]));
                for (int i = 0; i < tail; i++)
                    allAssumptions.push(mkLit(innerVars[make_pair(1, n - i - 1)]));
            } else {
                // push "lead" nums of zeros
                for (int i = 0; i < lead; i++)
                    allAssumptions.push(~mkLit(inputVars[i]));
                for (int i = 0; i < tail; i++)
                    allAssumptions.push(mkLit(inputVars[n - i - 1]));
            }
            bool solved = s.solve(allAssumptions);
            if (solved) {
                /* What is the rating of this? */
                int ws;
                if (useInnerVars) {
                    int l = 0;
                    while (l < n && s.modelValue(innerVars[make_pair(1, l)]) == l_False)
                        l++;
                    int t = 0;
                    while (t < n && s.modelValue(innerVars[make_pair(1, n - t - 1)]) == l_True)
                        t++;
                    ws = n - (l + t);
                } else {
                    int l = 0;
                    while (l < n && s.modelValue(inputVars[l]) == l_False)
                        l++;
                    int t = 0;
                    while (t < n && s.modelValue(inputVars[n - t - 1]) == l_True)
                        t++;
                    ws = n - (l + t);
                }
                if (ws < bestRating) {
                    bestRating = ws;
                    bestInput.clear();
                    for (int i = 0; i < inputVars.size(); i++) {
                        bestInput.push_back(s.model[inputVars[i]] == l_True);
                    }
                }
                counterExampleFound = true;
            }
        }
    }
    return counterExampleFound;
}

bool findCounterExample(Solver &testSolver, Solver &creationSolver, map<comparator, Var> &compVarsInCreatedNW,
                        map<comparator, Var> &compVarsInTestNW, int iteration, vector<Var> &inputVars,
                        vector<Var> &outputVars, vector<bool> &newInput, int n, map<pair<int, int>, Var> &innerVars) {
    vec<Lit> assumptions;
    set<Var> test;
    /* Copy the comparators of the given comparator network to the test network*/
    for (map<comparator, Var>::iterator it = compVarsInCreatedNW.begin(); it != compVarsInCreatedNW.end(); it++) {
        assert(compVarsInTestNW.count(it->first) > 0);
        if (creationSolver.modelValue(it->second) == l_True) {
            assumptions.push(mkLit(compVarsInTestNW[it->first]));
        } else {
            assumptions.push(~mkLit(compVarsInTestNW[it->first]));
        }
        test.insert(compVarsInTestNW[it->first]);
    }

    return findMinSizeCounterExample(testSolver, assumptions, inputVars, newInput, n, innerVars);

}

int addSuffixInput(Solver & s, int n, int d,triVarMap &compVarsInCreatedNW,
                   map<pair<int, int>, Var> &used, Var &T, Var &F, triVarMap &intVars,
                   triVarMap &rangeVars, vector<bool> & newInput, int suffDepth){
    vector<bool> newOutput;
    map<pair<int, int>, Var> newInternalVars;
    Var mkConditional = s.newVar();
    int zeros = 0;
    for (unsigned i = 0; i < newInput.size(); i++) {
        if (!newInput[i]) {
            zeros++;
        }
    }
    for (unsigned i = 0; i < newInput.size(); i++) {
        newOutput.push_back(i < zeros ? false : true);
    }
    int leadingZeros = 0;
    for (unsigned i = 0; i < newInput.size(); i++) {
        if (newInput[i])
            break;
        else
            leadingZeros++;
    }
    int tailingOnes = 0;
    for (unsigned i = newInput.size() - 1; i >= 0; i--) {
        if (!newInput[i])
            break;
        else {
            tailingOnes++;
        }
    }
    printf("c have %d leading zeros, and %d trailing ones! \n", leadingZeros, tailingOnes);
    //assert(leadingZeros >= 6);
    //assert(tailingOnes >= 6);

    // Create new internal variables
    for (int i = d-suffDepth; i < d - 1; i++) {
        for (int j = 0; j < n; j++) {
            if (j < leadingZeros) {
                newInternalVars[make_pair(i, j)] = F;
            } else if (j >= n - tailingOnes) {
                newInternalVars[make_pair(i, j)] = T;
            } else {
                Var v = s.newVar();
                newInternalVars[make_pair(i, j)] = v;
            }
        }
    }
    // Add input- and output-variables:
    for (int j = 0; j < n; j++) {
        newInternalVars[make_pair(d-suffDepth-1, j)] = newInput[j] ? T : F;
        assert(newInternalVars.count(make_pair(d - 1, j)) == 0);
        Var newOut = s.newVar();
        newInternalVars[make_pair(d - 1, j)] = newOut;
        // If this input is used, the it must be sorted!
        if(newOutput[j]){
           s.addClause(~mkLit(mkConditional), mkLit(newOut));
        }
        else{
            s.addClause(~mkLit(mkConditional), ~mkLit(newOut));
        }
         //= newOutput[j] ? T : F;
    }
    // Add update-rules:

    for (int i = d-suffDepth; i < d; i++) {
        for (int j = leadingZeros; j < (n - tailingOnes); j++) {
            // Let us assume that the value on this channel is "1".
            // Thus, this will stay unless there is a comparator down inside the window,
            // and the other input is "0".
            vec<Lit> ps;
            // If none of the comparators to higher indices is used...
            if (rangeVars.count(comparator(i, j, n - tailingOnes - 1)) == 0) {
                addOneFromToRange(s, i, j, n - tailingOnes - 1, compVarsInCreatedNW, rangeVars);
            }
            ps.push(mkLit(rangeVars[comparator(i, j, n - tailingOnes - 1)]));
            // And the input is "1"
            ps.push(~mkLit(newInternalVars[make_pair(i - 1, j)]));
            // Then, the output is "1"
            ps.push(mkLit(newInternalVars[make_pair(i, j)]));
            s.addClause(ps);
            ps.clear();

            // Not let us assume there is a comparator to a higher index.
            // This, this "1" will disappear if the other input is a "0"
            for (int k = j + 1; k < n - tailingOnes; k++) {
                // If the other input is "0"...
                ps.push(~mkLit(compVarsInCreatedNW[comparator(i, j, k)]));
                ps.push(mkLit(newInternalVars[make_pair(i - 1, k)]));
                ps.push(~mkLit(newInternalVars[make_pair(i, j)]));
                s.addClause(ps);
                ps.clear();
                // If both inputs equal "1"
                ps.push(~mkLit(compVarsInCreatedNW[comparator(i, j, k)]));
                ps.push(~mkLit(newInternalVars[make_pair(i - 1, k)]));
                ps.push(~mkLit(newInternalVars[make_pair(i - 1, j)]));
                ps.push(mkLit(newInternalVars[make_pair(i, j)]));
                s.addClause(ps);
                ps.clear();
            }
            // What if the input is "0"?
            // No comparator to lower indices -> output will be zero
            if (rangeVars.count(comparator(i, j, leadingZeros)) == 0) {
                addOneFromToRange(s, i, j, leadingZeros, compVarsInCreatedNW, rangeVars);
            }
            ps.push(mkLit(rangeVars[comparator(i, j, leadingZeros)]));

            ps.push(mkLit(newInternalVars[make_pair(i - 1, j)]));
            ps.push(~mkLit(newInternalVars[make_pair(i, j)]));
            s.addClause(ps);
            ps.clear();
            for (int k = leadingZeros; k < j; k++) {
                // Comparator chosen, and other value="1" -> swap
                ps.push(~mkLit(compVarsInCreatedNW[comparator(i, k, j)]));
                ps.push(~mkLit(newInternalVars[make_pair(i - 1, k)]));
                ps.push(mkLit(newInternalVars[make_pair(i, j)]));
                s.addClause(ps);
                ps.clear();

                // Comparator chosen, and other value="0" -> still "0"
                ps.push(~mkLit(compVarsInCreatedNW[comparator(i, k, j)]));
                ps.push(mkLit(newInternalVars[make_pair(i - 1, k)]));
                ps.push(mkLit(newInternalVars[make_pair(i - 1, j)]));
                ps.push(~mkLit(newInternalVars[make_pair(i, j)]));
                s.addClause(ps);
                ps.clear();
            }
        }
    }
    return toInt(mkLit(mkConditional));
}

void testTheseVars(Solver & s, int index, vector<int> & testVars, int numConfls, vec<Lit> & ass){

    if(index < testVars.size()){
        ass.push(toLit(testVars[index]));
        s.setConfBudget(numConfls);
        lbool ret = s.solveLimited(ass);
        if(ret == l_True){
            printf("c this combination of %d cases works...\n", ass.size());
            testTheseVars(s, index+1, testVars, numConfls, ass);
            ass.pop();
            testTheseVars(s, index+1, testVars, numConfls, ass);
        }
        else if (ret == l_False){
            printf("c conflict, %d cases used! \n", ass.size());
            ass.pop();
            testTheseVars(s, index+1, testVars, numConfls, ass);
        }
        else{
            printf("c INDET, recursive call! \n");
            testTheseVars(s, index+1, testVars, numConfls, ass);
            ass.pop();
        }

    }
}

void addTestLiterals_oneIn(int layer, int n, int minFrom, int maxTo, triVarMap &compVarsInCreatedNW){
    for(int i = 0 ; i < n ; i++){
        for(int j = n-1 ; j > i  ; j--){
            int from = i;
            int to = j;
            if((from >= minFrom && from <= maxTo ) || (to >= minFrom && to <= maxTo)){
                if(compVarsInCreatedNW.count(comparator(layer, from, to))){
                    if(myMPI_rank <= 0) printf("c layer %d : %d -> %d varIndex is %d\n", layer, from, to, compVarsInCreatedNW[comparator(layer, from,to)]);
                    firstCubes.push(mkLit(compVarsInCreatedNW[comparator(layer, from, to)]));
                }
            }
        }
    }
}

void addTestLiterals(int layer, int minFrom, int maxTo, int maxLength, triVarMap &compVarsInCreatedNW){
    for(int i = minFrom ; i < maxTo ; i++){
        for(int j = maxLength ; j >= 1  ; j--){
            int from = i;
            int to = i+j;
            if(to <= maxTo && compVarsInCreatedNW.count(comparator(layer, from, to))){
                if(myMPI_rank <= 0) printf("c layer %d : %d -> %d varIndex is %d\n", layer, from, to, compVarsInCreatedNW[comparator(layer, from,to)]);
                firstCubes.push(mkLit(compVarsInCreatedNW[comparator(layer, from, to)]));
            }
        }
    }
}

void testLastLayerStuff(Solver & s, int n, int d,triVarMap &compVarsInCreatedNW,
                        map<pair<int, int>, Var> &used, Var &T, Var &F, triVarMap &intVars,
                        triVarMap &rangeVars){
    assert(n == 18);
    vector<int> testVariables;
    int maskLower = 0x3F;
    int maskUpper = (0x3F)<<12;
    for(int i = 0 ; i < (1<<n) ; i++){
        if(countNumOnes(i) == n/2){
            vector<bool> newInput;
            int tmp = i;
            if (((i & maskLower) == 0) && ((i & maskUpper) == maskUpper)){
                for(int j = 0 ; j < n ; j++)
                    newInput.push_back(i & (1<<j));
                testVariables.push_back(addSuffixInput(s, n, d, compVarsInCreatedNW, used, T, F, intVars, rangeVars, newInput, 2));
            }
        }

    }
    printf("c got %d testVariable! \n", testVariables.size());
    vec<Lit> ass;
    testTheseVars(s, 0, testVariables, 1000, ass);
}

//=================================================================================================
// Main:


int main(int argc, char **argv) {


    setbuf(stdout, NULL);
    try {
        setUsageHelp(
                "USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");

#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        //if(myMPI_rank <= 0) printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption verb("MAIN", "verb", "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        IntOption cpu_lim("MAIN", "cpu-lim", "Limit on CPU time allowed in seconds.\n", INT32_MAX,
                          IntRange(0, INT32_MAX));
        IntOption mem_lim("MAIN", "mem-lim", "Limit on memory usage in megabytes.\n", INT32_MAX,
                          IntRange(0, INT32_MAX));

        IntOption inputBits("MAIN", "input-Bits", "Num input bits for comparator network.\n", 6,
                            IntRange(0, INT32_MAX));
        IntOption numComps("MAIN", "numComps", "Maximum no comparators allowed.\n", 100000, IntRange(0, INT32_MAX));
        IntOption layers("MAIN", "layers", "Num layers for comparator network.\n", 8, IntRange(0, INT32_MAX));
        IntOption opt_thres("MAIN", "threshold",
                            "Threshold for initially forbidding some comparators in the last columns.\n", 0,
                            IntRange(0, INT32_MAX));

        BoolOption encodeAll("MAIN", "encodeAll", "Add all inputs immediately, and write formula", false);
        BoolOption opt_reverse_inputs("MAIN", "revers", "Revert counterexample optimization", false);


        parseOptions(argc, argv, true);

        if(opt_mpi){
            MPI_Init(NULL, NULL);
            MPI_Comm_rank(MPI_COMM_WORLD, &myMPI_rank);
            MPI_Comm_size(MPI_COMM_WORLD, &num_mpi_ranks);
            int buf_size = 100 * 1000 * 1000 * sizeof(int);
            int * my_buffer = (int*) malloc(buf_size);
            assert(my_buffer);
            MPI_Buffer_attach(my_buffer, buf_size);
            printf("c init MPI done, rank %d, numRanks %d\n", myMPI_rank, num_mpi_ranks);
        }
        else{
            myMPI_rank = 0;
            printf("c running without MPI, my rank is %d\n", myMPI_rank);
        }

        double initial_time = cpuTime();
        const char *_prefFileName = prefFileName ? (const char *) prefFileName : "layers.txt";
        /* 
         * standard initialization
         */
        Solver S;
        S.verbosity = verb;

        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU, SIGINT_exit);

        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX) {
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t) cpu_lim < rl.rlim_max) {
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1)
                    printf("WARNING! Could not set resource limit: CPU-time.\n");
            }
        }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX) {
            rlim_t new_mem_lim = (rlim_t) mem_lim * 1024 * 1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max) {
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("WARNING! Could not set resource limit: Virtual memory.\n");
            }
        }


        int n = inputBits;
        int d = layers;
        double overAllTimeForNetworkCheck = 0.0;
        double overAllTimeForNetworkCreation = 0.0;
        if(myMPI_rank <= 0) printf("=========================================================\n");
        if(myMPI_rank <= 0) printf("=== Looking for Sorting networks for %d bits with depth %d\n", n, d);

        /******************************************************
        * create a solver to compare two networks: 
        */
        Solver netWorksCompare;

        // add reference network
        vector<Var> inputVars;
        vector<Var> outputVarsForRev;
        vector<Var> outputVarsForTest;
        map<pair<int, int>, Var> innerVars1;
        map<pair<int, int>, Var> innerVars2;
        map<comparator, Var> internalVarsInCreatedNW;
        for (int i = 0; i < n; i++) {
            inputVars.push_back(netWorksCompare.newVar());
            outputVarsForRev.push_back(netWorksCompare.newVar());
            outputVarsForTest.push_back(netWorksCompare.newVar());
        }
        assert(netWorksCompare.nVars() > 0);
        if(myMPI_rank <= 0) printf("Vectors created, numVars=%d\n", netWorksCompare.nVars());
        /* create a reference-network - in this case, it's simply an odd-even-sort */
        createRefNetwork(netWorksCompare, inputVars, outputVarsForRev, n, n, innerVars1);
        if(myMPI_rank <= 0) printf("First Network created, numVars=%d\n", netWorksCompare.nVars());

        /* create a configurable network */
        map<comparator, Var> compVarsInTestNW;
        map<pair<int, int>, Var> internalTestVars;
        createTestNetWork(netWorksCompare, inputVars, outputVarsForTest, n, d, compVarsInTestNW, internalTestVars);
        //createRefNetwork(netWorksCompare, inputVars, outputVarsForTest, n, n, innerVars2);
        if(myMPI_rank <= 0) printf("Second Network created, numVars=%d\n", netWorksCompare.nVars());
        // create "atLeastOneDiffers"-Constraint: 
        vector<Var> diffVars;
        addAtLeastOneDiffers(netWorksCompare, outputVarsForRev, outputVarsForTest, diffVars);


        if(myMPI_rank <= 0) printf("Got so far, numVars = %d\n", netWorksCompare.nVars());

        /*************************************************************************************
         * Create Solver and formula which create a network which sorts the given inputs
         */

        Solver netWorkCreate;
        solver = &netWorkCreate;
        netWorkCreate.verbosity = verb;
        map<comparator, Var> rangeVars;
        map<comparator, Var> compVarsInCreatedNW;
        map<pair<int, int>, Var> used;
        Var T, F;
        map<Var, vector<Var> > inputVecs;
        createNetWorkFormula(netWorkCreate, n, d, compVarsInCreatedNW, used, T, F, opt_create_splitter);
        netWorkCreate.verbosity = verb;
        vector<comparator> compsReadFromFile;
        if(n == 18){
            //testLastLayerStuff(netWorkCreate, n, d, compVarsInCreatedNW, used, T, F, internalVarsInCreatedNW, rangeVars);
        }
        /*******************************************************
         * Add all inputs that are not equivalent modulo the first layers. 
         */

        {
            bool done = false;
            bool networkFound = false;
            int iterations = 0;

            vector<Var> varsIndicatingPrefix;

            if (opt_someStartValues) {

                if (opt_prefLayer) {
                    parseSecondlayer(compsReadFromFile, _prefFileName, opt_row);
                }
                else if(optfixFirstLayer){
                    for (int j = 0; j < n - j - 1; j++) {
                        compsReadFromFile.push_back(comparator(0, j, n - j - 1));
                    }
                }
                int maxLayerReadFromFile = -1;
                for (vector<comparator>::iterator it = compsReadFromFile.begin(); it != compsReadFromFile.end(); it++) {
                    maxLayerReadFromFile = std::max(maxLayerReadFromFile, it->layer);
                }
                if(myMPI_rank <= 0) printf("Max layer in input: %d\n", maxLayerReadFromFile);
                addSomeInputs(netWorkCreate, compsReadFromFile, n, d, compVarsInCreatedNW, used, T, F,
                              internalVarsInCreatedNW, shrinkGen, rangeVars);

            }


            int maxWindowSoFar = 1;
            if(myMPI_rank <= 0) printf("c starting loop,netWorkCreate.okay = %d\n", netWorkCreate.okay());
            while (!done) {
                // Create network
                if(myMPI_rank <= 0) printf("\n\n================================================================================\n");
                if(myMPI_rank <= 0) printf("Iteration %d\n", ++iterations);
                if(myMPI_rank <= 0) printf("Internal vars: %d and %d\n", compVarsInCreatedNW.size(), compVarsInTestNW.size());
                if(myMPI_rank <= 0) printf("looking for a feasible network: \n");
                double t_ = cpuTime();
                if(myMPI_rank <= 0) netWorkCreate.toDimacs("bla.cnf");
                if(n >= 16 ){
                    int minFrom = 5;
                    int maxTo = n-5;
                    // Last layer:
                    addTestLiterals(d-2, minFrom, maxTo, 3,compVarsInCreatedNW);
                    addTestLiterals(d-1, minFrom, maxTo, 1,compVarsInCreatedNW);
                    addTestLiterals(d-3, minFrom, maxTo, 8,compVarsInCreatedNW);
                    addTestLiterals_oneIn(d-2, n, minFrom, maxTo, compVarsInCreatedNW);
                    addTestLiterals_oneIn(d-3, n, minFrom, maxTo, compVarsInCreatedNW);
                    /*int nStart = n/2 - 3;
                    for(int i = 0 ; i < 4 ; i++){
                        for(int k = 1 ; k <= 3 ; k++){
                            int from = nStart + i;
                            int to = from + k;
                            if(compVarsInCreatedNW.count(comparator(d-2, from ,to))){
                                printf("c %d -> %d varIndex is %d\n", from, to, compVarsInCreatedNW[comparator(d-2, from, to)]);
                                firstCubes.push(mkLit(compVarsInCreatedNW[comparator(d-2, from, to)]));
                            }
                        }


                    }*/
                    //for(int i = 0 ; i < 4 ; i++)
                        //if(compVarsInCreatedNW.count(comparator(d-2, n/2-2+i, n/2+1+i)))
                            //firstCubes.push(mkLit(compVarsInCreatedNW[comparator(d-2, n/2-2+i, n/2+1+i)]));
                    /*if(compVarsInCreatedNW.count(comparator(8, 8, 11))){
                        firstCubes.push(mkLit(compVarsInCreatedNW[comparator(8, 8, 11)]));
                        firstCubes.push(mkLit(compVarsInCreatedNW[comparator(8, 10, 13)]));
                    }*/

                }
                bool newNetWorkCreated = findFeasibleNetwork(netWorkCreate, iterations);

                printf("Network Creation took %lf s\n", cpuTime() - t_);
                overAllTimeForNetworkCreation += cpuTime() - t_;
                if (!newNetWorkCreated) {
                    printf("UNSAT\n");
                    printf("networkCreate.okay()=%d\n", netWorkCreate.okay());
                    printf("MaxWindowSize: %d\n", maxWindowSoFar);
                    done = true;
                } else {
                    /* print this comparator network */
                    for (int i = 0; i < d; i++) {
                        for (int j = 0; j < n; j++) {
                            for (int k = j + 1; k < n; k++) {
                                assert(compVarsInCreatedNW.find(comparator(i, j, k)) != compVarsInCreatedNW.end());

                                if (netWorkCreate.modelValue(compVarsInCreatedNW[comparator(i, j, k)]) == l_True) {
                                    printf("%d-%d, ", j, k);
                                }
                            }
                        }
                        printf("\n");
                    }
                    vector<bool> newInput;
                    bool counterExampleFound = findCounterExample(netWorksCompare, netWorkCreate, compVarsInCreatedNW,
                                                                  compVarsInTestNW, iterations, inputVars,
                                                                  outputVarsForTest, newInput, n, internalTestVars);

                    if (counterExampleFound) {
                        if (!opt_optEncoding) {
                            addInputOldEncoding(netWorkCreate, newInput, n, d, compVarsInCreatedNW, used, T, F,
                                                internalVarsInCreatedNW);
                        } else {
                            addInputImprovedEncoding(netWorkCreate, newInput, n, d, compVarsInCreatedNW, used, T, F,
                                                     internalVarsInCreatedNW, rangeVars);
                        }
                    } else {
                        done = true;
                        networkFound = true;
                        break;
                    }
                }
            }
            if (networkFound) {
                /* print output for the verifyer
                 * */
                printf("VERIFY %d\n", n);
                int numComps = 0;
                for (int i = 0; i < d; i++) {
                    for (int j = 0; j < n; j++) {
                        for (int k = j + 1; k < n; k++) {
                            if (netWorkCreate.modelValue(compVarsInCreatedNW[comparator(i, j, k)]) == l_True) {
                                numComps++;
                            }
                        }
                    }
                }
                printf("VERIFY %d\n", numComps);
                for (int i = 0; i < d; i++) {
                    for (int j = 0; j < n; j++) {
                        for (int k = j + 1; k < n; k++) {
                            if (netWorkCreate.modelValue(compVarsInCreatedNW[comparator(i, j, k)]) == l_True) {
                                printf("VERIFY %d %d\n", j, k);
                            }
                        }
                    }
                }


                /* Give a (ugly) latex-version of the network found*/
                // plot lines: 
                /*for (int i = 0; i < n; i++) {
                    printf("\\draw[color=black] (%d,%d)--(%d,%d);\n", 0, i, d, i);
                }
                for (int i = 0; i < d; i++) {
                    float found = 0;
                    printf("\\addtocounter{sncolumncounter}{1}\n");
                    for (int j = 0; j < n; j++) {
                        for (int k = j + 1; k < n; k++) {
                            if (netWorkCreate.modelValue(compVarsInCreatedNW[comparator(i, j, k)]) == l_True) {
                                printf("\\nodeconnection{ {%d,%d}}\n", n-j, n-k);

                            }
                        }
                    }
                    printf("\n");
                }*/
                netWorkCreate.toDimacs("formula.cnf");
                printNetwork(netWorkCreate, n, d, compVarsInCreatedNW);
            }
        }
        if(myMPI_rank <= 0){
            printf("time was %f s\n", cpuTime() - initial_time);

            printf("Time spent in network creation: %lf\n", overAllTimeForNetworkCreation);
            printf("==============================================\n");
            printf("Comparator stats: \n");
            printStats(netWorksCompare);
            printf("==============================================\n");
            printf("Network creation stats: \n");
            printStats(netWorkCreate);
        }
        lbool ret = l_Undef;
        if(opt_mpi){
            MPI_Barrier(MPI_COMM_WORLD);
            MPI_Finalize();
        }

#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException &) {
        printf("===============================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}
