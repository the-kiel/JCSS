/***************************************************************************************[Solver.cc]
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

#include <math.h>

#include "mtl/Sort.h"
#include "core/Solver.h"
#include "utils/System.h"

#include <vector>
#include <set>
#include <algorithm>

#include <ctime>
#include <cmath>

#include <mpi.h>


using namespace Minisat;
using namespace std;
//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.9999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static BoolOption    opt_randomStart       (_cat, "rndStart",        "Use random decisions at DL0", false);
static IntOption     opt_random_until      (_cat, "rndThreshold",  "Max DL to branch randomly", 0, IntRange(0, INT32_MAX));
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static IntOption     opt_deletion_mode     (_cat, "delMode",      "Mode of deleting clauses (0=standard, 1=removeImplied, 2=old", 0, IntRange(0, 2));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ThresholdPermanent      (_cat, "threshPerm",  "Clauses with LBD at most this value will become permanent", 7, IntRange(0, INT32_MAX));
static DoubleOption  opt_target_rate       (_cat, "targetRate",        "target rate of how many clauses become permanent", 0.2, DoubleRange(0, true, 1, true));

static IntOption     opt_restartInterval     (_cat, "restarts",      "Number of conflicts between restarts", 1024, IntRange(0, INT32_MAX));

static IntOption     opt_numConfls      (_cat, "numConfls",      "Number of conflicts before splitting the cube", 100000, IntRange(1, INT32_MAX));
static IntOption     opt_maxDB          (_cat, "maxDB",      "Size of learnt clause database before clean", 300000, IntRange(1, INT32_MAX));

static BoolOption    opt_subsumptionTests       (_cat, "subTests",        "Use subsumption tests on core learnt clauses", false);

static IntOption     opt_shortCube     (_cat, "shortCube",      "Cubes with this size will be considered small", 6, IntRange(0, INT32_MAX));
//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (0)
  , nextPrintStats(10000)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , del_mode         (opt_deletion_mode)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  //, learntsize_adjust_start_confl (10)
  , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  , restart_interval (opt_restartInterval)
    , maxDB_size(opt_maxDB)
    , conflsPerCube (opt_numConfls)
  , stealRequestPending(false)
  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap         (VarOrderLt(activity))
  , progress_estimate  (0)
  , remove_satisfied   (true)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
  , budgetForRandom    (0)
  , MYFLAG              (0)
{}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    permDiff.push(0);
    permDiff.push(0);
    return v;
}


bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++){
        assert(var(ps[i]) >= 0 && var(ps[i]) <= nVars());
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    }
    ps.shrink(i - j);
       if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    }else{
        
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    
    if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1); 
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
                polarity[x] = sign(trail[c]);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;
    
    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }
    
    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();
    
    return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.learnt()){
            claBumpActivity(c);
            if(!c.isGoodClause()){
                int lbd = computeLBD(c);
                if(lbd < dyn_threshold){
                    c.setGood(true);
                    c.setCanBeDel(false);
                }
            }
//            c.setCanBeDel(false);
            // recompute LBD here???
        }

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel())
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause& c = ca[reason(var(analyze_stack.last()))]; analyze_stack.pop();

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else
                uncheckedEnqueue(first, cr);

        NextClause:;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}

inline unsigned int Solver::computeLBD(const Clause &c) {
    int nblevels = 0;
    MYFLAG++;
    for(int i=0;i<c.size();i++) {
      int l = level(var(c[i]));
      if (permDiff[l] != MYFLAG) {
            permDiff[l] = MYFLAG;
            nblevels++;
        }
    }

  return nblevels;
}

inline unsigned int Solver::computeLBD(const vec<Lit> &c) {
    int nblevels = 0;
    MYFLAG++;
    for(int i=0;i<c.size();i++) {
      int l = level(var(c[i]));
      if (permDiff[l] != MYFLAG) {
            permDiff[l] = MYFLAG;
            nblevels++;
        }
    }

  return nblevels;
}

/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
        return  ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); }
};
void Solver::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity
    
    sort(learnts, reduceDB_lt(ca));
    int middle = learnts.size()/2;
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    if(mpi_rank <= 0) printf("c first clause: size %d, act %lf\n", ca[learnts[0]].size(), ca[learnts[0]].activity());
    int n = learnts.size()-1;
    if(mpi_rank <= 0) printf("c last clause: size %d, act %lf\n", ca[learnts[n]].size(), ca[learnts[n]].activity());
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && c.canBeDel() && i < middle )
            removeClause(learnts[i]);
        else{
            learnts[j++] = learnts[i];
            if(!c.isGoodClause() || assumptions.size() > 0){
                c.setCanBeDel(true);
            }
        }
    }
    learnts.shrink(i - j);
    if(mpi_rank <= 0)
        printf("c reduce DB: %d -> %d clauses\n", i, j);
    checkGarbage();
}

Lit Solver::subsumes_faster    (Clause & c1, Clause & c2){

    Lit ret = lit_Undef;
    if(c1.size() > c2.size() ){
        return lit_Error;
    }


    MYFLAG++;

    // Mark all literals from c2
    for(int i = 0 ; i < c2.size();i++)
        permDiff[c2[i].x] = MYFLAG;
    for(int i = 0 ; i < c1.size();i++){
        if(permDiff[c1[i].x] != MYFLAG){
            // So this literal is not in c2. Is its opposite literal in there?
            if(ret == lit_Undef && permDiff[(~c1[i]).x] == MYFLAG)
                ret = c1[i];
            else
                ret = lit_Error;
        }
    }
    return ret;
}

struct size_lt {
    ClauseAllocator& ca;
    size_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) {
        return  ca[x].size() < ca[y].size() ; }
};


struct ClauseDeleted {
    const ClauseAllocator& ca;
    explicit ClauseDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
    bool operator()(const CRef& cr) const { return ca[cr].mark() == 1; } };

bool Solver::checkSubsumption(Clause & c1, Clause & c2){
    int varsMatch = 0;
    int litsMatch = 0;
    for(int i = 0 ; i < c1.size();i++){
        for(int j = 0 ; j < c2.size();j++){
            if(c1[i] == c2[j])
                litsMatch++;
            if(var(c1[i]) == var(c2[j]))
                varsMatch++;
        }
    }
    if(varsMatch == c1.size() && litsMatch == c1.size()-1){
        return true;
    }
    printf("c something is strange here! \n");
    return false;
}

bool Solver::mySubsumptionTest(){
    double tStart = cpuTime();
    std::vector<std::vector<CRef> > occurs(nVars()+1);
    for(int i = 0 ; i < learnts.size();i++){

        Clause & c = ca[learnts[i]];
        assert(!c.mark());
        CRef cr = learnts[i];
        for(int j = 0 ; j < c.size();j++){
            occurs[var(c[j])].push_back(cr);
        }
    }
    for(int i = 0 ; i < occurs.size();i++)
        std::sort(occurs[i].begin(), occurs[i].end());

    sort(learnts, size_lt(ca));
    int subsumed = 0;
    int couldBeShrinked=0;
    int n = learnts.size();
    std::vector<std::vector<int> > newClauses;
    std::vector<bool> goodClause;
    int goodShrinked = 0;
    for(int i = 0 ; i < n;i++){
        Clause & c = ca[learnts[i]];
        if(!c.mark() && !c.canBeDel() && c.isGoodClause()){
            Lit best1 = occurs[var(c[0])].size() < occurs[var(c[1])].size() ? c[0] : c[1];
            Lit best2 = best1 == c[0] ? c[1] : c[0];
            assert(best1 != best2);

            for(int j = 2 ; j < c.size();j++){
                if(occurs[var(c[j])].size() < occurs[var(best1)].size()){
                    best2 = best1;
                    best1 = c[j];
                }
                else if(occurs[var(c[j])].size() < occurs[var(best2)].size()){
                    best2 = c[j];
                }
            }

            const std::vector<CRef> & others1 = occurs[var(best1)];
            const std::vector<CRef> & others2 = occurs[var(best2)];
            int j1 = 0, j2 = 0;
            for(j1 = j2 = 0 ; j1 < others1.size() && j2 < others2.size();){
                if(others1[j1] < others2[j2]){
                    j1++;
                }
                else if(others2[j2] < others1[j1]){
                    j2++;
                }
                else{
                    if(!ca[others1[j1]].mark() && others1[j1] != learnts[i] && ca[others1[j1]].isGoodClause() && !ca[others1[j1]].canBeDel()){
                        Lit l = subsumes_faster(ca[learnts[i]], ca[others1[j1]]);
                        // ca[learnts[i]].subsumes_learnt(ca[others[j]]);
                        if(l == lit_Error){
                            // Nothing???
                        }
                        else if(l == lit_Undef){
                            subsumed++;
                            ca[others1[j1]].mark(1);
                        }
                        else{
                            checkSubsumption(ca[learnts[i]], ca[others1[j1]]);
                            couldBeShrinked++;
                            std::vector<int> newC;
                            vec<Lit> testStuff;
                            for(int k = 0 ; k < ca[others1[j1]].size();k++)
                                if(var(ca[others1[j1]][k]) != var(l)){
                                    newC.push_back(toInt(ca[others1[j1]][k]));
                                    testStuff.push(ca[others1[j1]][k]);
                                }
                            newClauses.push_back(newC);
                            if(newC.size() + 1 != ca[others1[j1]].size()){
                                printf("c this is weird. size %d -> %d\n", ca[others1[j1]].size(), newC.size());
                            }
                            /*if(!entailed(testStuff)){
                                printf("c okay, clause of size %d is not entail just after I found it??? \n", testStuff.size());
                            }*/
                            goodClause.push_back(ca[others1[j1]].isGoodClause());
                            if(ca[others1[j1]].isGoodClause())
                                goodShrinked++;
                            ca[others1[j1]].mark(1);
                            /*vec<Lit> newClause;
                            Clause & c2 = ca[others[j]];
                            for(int k = 0 ; k < c2.size();k++)
                                if(var(c2[k]) != var(l))
                                    newClause.push(c[k]);
                            //printf("c c.size() %d c2.size() %d newClause.size() %d \n", c.size(), c2.size(), newClause.size());
                            assert(c2.size() == newClause.size()+1);
                            if(newClause.size() > 1){
                                CRef cr = ca.alloc(newClause, true);

                                learnts.push(cr);
                                attachClause(cr);
                                ca[cr].setGood(ca[others[j]].isGoodClause());
                                ca[others[j]].mark(1);
                            }
                            else{
                                printf("c got unit clause by subsumption check??? \n");
                            }*/
                        }
                    }
                    j1++;
                    j2++;
                }
            }
        }
    }

    for(int i = 0 ; i < newClauses.size();i++){
        vec<Lit> ps;
        std::vector<int> & v = newClauses[i];
        for(int j = 0 ; j < v.size();j++)
            ps.push(toLit(v[j]));
        if(ps.size() <= 1){
            printf("c okay, found unit clause???\n");
        }
        bool succ = true; //entailed(ps);
        if(!succ){
            printf("c okay, I got a clause which is not entailed by the formula??? size is %d\n", ps.size());
        }

        CRef cr = ca.alloc(ps, true);

        learnts.push(cr);
        attachClause(cr);
        ca[cr].setGood(goodClause[i]);
    }
    printf("c my subsumption test is done, have %d subsumed clauses and %d which can be shrinked (%d good). times was %lf\n", subsumed, couldBeShrinked, goodShrinked, cpuTime() - tStart);
    int i=0;
    int j = 0;
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if ( !locked(c) && c.mark())
            removeClause(learnts[i]);
        else{
            learnts[j++] = learnts[i];
            c.mark(0);
        }
    }
    learnts.shrink(i - j);
    printf("c after subsumption check DB: %d -> %d clauses\n", i, j);
    checkGarbage();
    return subsumed > 0 || couldBeShrinked > 0;
}

bool clauseExists(Clause & ps, std::set<std::vector<int> > & seenSoFar){
    std::vector<int> v;
    for(int i = 0 ; i < ps.size();i++){
        v.push_back(toInt(ps[i]));
    }
    std::sort(v.begin(), v.end());
    if(seenSoFar.count(v))
        return true;
    seenSoFar.insert(v);
    return false;
}

void Solver::checkDuplicates(){
    std::set<std::vector<int> > duplicates;
    int found = 0;
    for(int i = 0 ; i < learnts.size();i++)
        if(clauseExists(ca[learnts[i]], duplicates))
            found++;
    printf("c found %d duplicate clauses! \n", found);
}

/*
 * Return whether the clause "c" is entailed by this formula by checking that unit-propagation on its negation yields a conflict
 * */
bool Solver::entailed(vec<Lit> & c){
    assert(0 == decisionLevel());
    int tsBefore = trail.size();
    for(int i = 0 ; i < c.size();i++)
        if(value(c[i]) == l_True){
            return true; // propagating the negation will yield a conflict
        }
    newDecisionLevel();
    for(int i = 0 ; i < c.size();i++){
        if(value(c[i]) == l_Undef)
            uncheckedEnqueue(~c[i]);
    }
    CRef confl = propagate();
    bool ret = confl != CRef_Undef;
    cancelUntil(0);
    assert(trail.size() == tsBefore);
    return ret;
}

lbool Solver::checkLearnts(bool fullCheck){
    assert(0 == decisionLevel());
    int n = learnts.size();
    printf("c check called! \n");
    double tStart = cpuTime();
    int checked = 0;
    int numConfls = 0;
    int numReduced = 0;
    sort(learnts, size_lt(ca));

    for(int i = 0 ; i < n && checked < 1000 ; i++){
        Clause & c = ca[learnts[i]];

        bool done = false;
        if(c.isGoodClause() && (fullCheck || !c.wasChecked())){
            c.setChecked(true);
            checked++;
            for(int j = 0 ; j < c.size() && !done;j++){
                if(value(c[j]) == l_Undef){
                    newDecisionLevel();
                    uncheckedEnqueue(~c[j]);
                    CRef confl = propagate();
                    if(confl != CRef_Undef){
                        c.setCanBeDel(true);
                        int         backtrack_level;
                        vec<Lit>    learnt_clause;
                        analyze(confl, learnt_clause, backtrack_level);
                        numConfls++;
                        if(backtrack_level == 0){
                            printf("c got BT to DL 0! \n");
                            cancelUntil(0);
                            uncheckedEnqueue(learnt_clause[0]);
                            confl = propagate();
                            if(confl != CRef_Undef){
                                printf("c got UNSAT \n");
                                return l_False;
                            }
                        }
                        else{
                            CRef cr = ca.alloc(learnt_clause, true);
                            learnts.push(cr);
                            attachClause(cr);
                            ca[cr].setGood(true);
                        }
                        done = true;
                    }
                }
                else if(value(c[j]) == l_True){
                    // Call analyseFinal here!
                    vec<Lit>    learnt_clause;
                    analyzeFinal(c[j], learnt_clause);
                    if(learnt_clause.size() < c.size()){
                        numReduced++;
                        cancelUntil(0);
                        assert(entailed(learnt_clause));
                        CRef cr = ca.alloc(learnt_clause, true);
                        if(learnt_clause.size() == 1){
                            printf("c found unit clause! \n");
                            if(value(learnt_clause[0]) == l_Undef){
                                uncheckedEnqueue(learnt_clause[0]);
                                CRef confl = propagate();
                                if(confl != CRef_Undef){
                                    printf("c got UNSAT \n");
                                    return l_False;
                                }
                            }
                        }
                        else{
                            learnts.push(cr);
                            attachClause(cr);
                            c.setCanBeDel(true);
                            ca[cr].setGood(true);
                        }
                    }
                    done = true;
                }
            }
        }
        cancelUntil(0);
    }
    printf("c checked %d clauses in time %lf had %d confls and %d lifts\n", checked, cpuTime() - tStart, numConfls, numReduced);
    return l_Undef;
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c) || c.canBeDel())
            removeClause(cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);
    
    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}
/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    starts++;
    bool dynRestarts = false;
    int deepestBT = 1<<24;
    for (;;){
        CRef confl = propagate();

        if (confl != CRef_Undef){
            
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 0) return l_False;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);

            unsigned int LBD = computeLBD(learnt_clause);
            cancelUntil(backtrack_level);
            if(backtrack_level < deepestBT){

                deepestBT = backtrack_level;
                if(dynRestarts && conflictC > 100){
                    printf("c bt to %d, increasing number of conflicts remaining! \n", backtrack_level);
                    nof_conflicts += 1024;
                }
            }
            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);
                attachClause(cr);
                claBumpActivity(ca[cr]);
                ca[cr].setGood(LBD <= dyn_threshold);
                updateThreshold(ca[cr].isGoodClause());
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            varDecayActivity();
            claDecayActivity();

            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;


            }
            if(conflicts > nextPrintStats){
                if (verbosity >= 1)
                    printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n",
                           (int)conflicts,
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals,
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
                nextPrintStats += 10000;
            }

        }else{
            // NO CONFLICT
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts || !withinBudget()){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if(learnts.size() > maxDB_size)
                reduceDB();
            //if (learnts.size()-nAssigns() >= max_learnts)
                // Reduce the set of learnt clauses:
              //  reduceDB();

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef){
                    // Model found:
                    lastTrail.clear();
                    for(int i = 0 ; i < trail.size();i++)
                        if(reason(var(trail[i])) == CRef_Undef)
                            lastTrail.push(trail[i]);
                    return l_True;
                }
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}
bool Solver::checkLiteral(Lit p){
    
    assert(decisionLevel()==0);
    if(value(p) != l_Undef)
        return true;
    int tmp = phase_saving;
    phase_saving = 0;
    newDecisionLevel();
    uncheckedEnqueue(p);
    CRef confl = propagate();
    if(confl != CRef_Undef){
        vec<Lit> ps;
        int btLevel;
        analyze(confl, ps, btLevel);
        cancelUntil(0);
        uncheckedEnqueue(ps[0]);
        
        confl = propagate();
        if(confl != CRef_Undef){
            printf("got conflict in checkLiteral, UNSAT\n");
            ok = false;
            phase_saving = tmp;
            return false;
        }
    }
    cancelUntil(0);
    phase_saving = tmp;
    return true;
}

bool Solver::checkLitFast(Lit l, vector<bool> & seenHere){
    if(!ok)
        return false;
    if(value(l) != l_Undef)
        return false;
    if(seenHere[toInt(l)])
        return false;
    newDecisionLevel();
    assert(value(l) == l_Undef);
    uncheckedEnqueue(l);
    CRef confl = propagate();

    if(confl == CRef_Undef){
        for(int i = trail.size()-1 ; i > 0 ; i--){
            seenHere[toInt(trail[i])]=true;
            if(level(var(trail[i])) == 0)
                break;
        }
        cancelUntil(0);
        return false;
    }
    else{
        cancelUntil(0);
        uncheckedEnqueue(~l);
        confl = propagate();
        if(confl != CRef_Undef){
            ok = false;
            return true;
        }
    }
    return false;
}

bool Solver::FL_Check_fast(){
    cancelUntil(0);
    vector<bool> seenHere(2*nVars(), false);
    double t = cpuTime();
    int nBefore = trail.size();
    for(int i = 0 ; i < nVars() && ok;i++){
        assert(0 == decisionLevel());
        if(checkLitFast(mkLit(i), seenHere))
            return false;
        assert(0 == decisionLevel());
        if(checkLitFast(~mkLit(i), seenHere))
            return false;
        assert(0 == decisionLevel());
    }
    if(mpi_rank <= 0)
        printf("c fixed %d variables, time was %lf\n", trail.size()-nBefore, cpuTime()-t);
    return trail.size() != nBefore;
}

bool Solver::failedLiteralCheck(){
    assert(decisionLevel()==0);
    int nbSetBefore=trail.size();
//     int equivsFound = 0;
    set<Lit> lits2Check;
    int maxProps = 0;
    Lit maxLit = lit_Undef;
    /* Turn phase saving off */
    assert(phase_saving == opt_phase_saving);
    int phaseBefore = phase_saving;
    phase_saving = 0;
    double t = cpuTime();
    /* Collect all literals that appear in clauses of size 2, as branching on others will not trigger BCP... */
    for(int i = 0 ; i < clauses.size();i++){
        int trueFound = 0;
        int falseFound=0;
        set<Lit> tmp;
        for(int j =0;j<ca[clauses[i]].size();j++){
            if(value(ca[clauses[i]][j])==l_True){
                trueFound++;
                break;
            }
            else if(value(ca[clauses[i]][j])==l_False){
                falseFound++;
            }
            else
                tmp.insert(ca[clauses[i]][j]);
        }
        if(trueFound==0&&falseFound<=2){
            lits2Check.insert(tmp.begin(),tmp.end());
        }
    }
    for(int i = 0 ; i < learnts.size();i++){
        int trueFound = 0;
        int falseFound=0;
        set<Lit> tmp;
        for(int j =0;j<ca[learnts[i]].size();j++){
            if(value(ca[learnts[i]][j])==l_True){
                trueFound++;
                break;
            }
            else if(value(ca[learnts[i]][j])==l_False){
                falseFound++;
            }
            else
                tmp.insert(ca[learnts[i]][j]);
        }
        if(trueFound==0&&falseFound<=2){
            lits2Check.insert(tmp.begin(),tmp.end());
        }
    }
    /* For each variable x of them: 
        - Branch on x. 
            -If conflict occurs, we can set (not x) at root level.
            -If no conflict occurs, store all literals that were implied
        Branch on (not x)
            -If conflict occurs, we can set ( x) at root level.
            - Compare implied literals to those implied by x: If for some y, x ->* y and (not x) ->* y, then y must be true in either case, thus we can set it.
        Remember all literals that were seen here - they don't need to be checked, as branching on them again will not yield new results
     */
    set<Lit> redundant;
    for(set<Lit>::reverse_iterator it = lits2Check.rbegin();it!=lits2Check.rend();it++){
        
        if(value(*it)==l_Undef && redundant.count(~(*it))==0){
            set<Lit> literalsSet;
            newDecisionLevel();
            uncheckedEnqueue(~(*it));
            CRef confl = propagate();
            if(confl != CRef_Undef){
                vec<Lit> ps;
                int btLevel;
                analyze(confl, ps, btLevel);
                cancelUntil(0);
                uncheckedEnqueue(ps[0]);
                
                confl = propagate();
                if(confl != CRef_Undef){
                    printf("got conflict, UNSAT\n");
                    ok = false;
                    phase_saving = phaseBefore;
                    return false;
                }
            }
            else{
                // no conflict...
                if(trail.size() - trail_lim[0] >= maxProps){
                    maxLit = ~*it;
                    maxProps= trail.size() - trail_lim[0];
                }
                for(int i = trail.size() -1 ; i >trail_lim[0];i--){
                    redundant.insert(trail[i]);
                    literalsSet.insert(trail[i]);
                }
                cancelUntil(0);
                newDecisionLevel();
                uncheckedEnqueue(*it);
                CRef confl = propagate();
                if(confl != CRef_Undef){
                    vec<Lit> ps;
                    int btLevel;
                    analyze(confl, ps, btLevel);
                    cancelUntil(0);
                    uncheckedEnqueue(ps[0]);
                    confl = propagate();
                    if(confl != CRef_Undef){
                        printf("got conflict, UNSAT\n");
                        phase_saving = phaseBefore;
                        return false;
                    }
                }
                else{
                    set<Lit> lit2Add;
                    if(trail.size() - trail_lim[0] >= maxProps){
                        maxLit = *it;
                        maxProps= trail.size() - trail_lim[0];
                    }
                    // Check for literals that were also implied when branching on the opposite case - they are implied in either case!
                    for(int i = trail.size() -1 ; i > trail_lim[0] ; i--){
                        if(literalsSet.count(trail[i]) > 0){
                            lit2Add.insert(trail[i]);
                        }
                    }
                    cancelUntil(0);
                    int trailSizeBefore = trail.size();
                    
                    for(set<Lit>::iterator it = lit2Add.begin();it!=lit2Add.end();it++){
                        uncheckedEnqueue(*it);
                    }
                    CRef confl = propagate();
                    if(confl != CRef_Undef){
                        phase_saving = phaseBefore;
                        return false;
                    }
                    if(lit2Add.size()>0 && verbosity > 1){
                        printf("Fixed %d literals\n", trail.size()-trailSizeBefore);
                        printf("trail.size()=%d\n", trail.size());
                    }
                }
                cancelUntil(0);
            }
        }
    }
    printf("fixed %d variables at DL0 in time %lf\n", trail.size()-nbSetBefore, cpuTime()-t);
    printf("Max # propagations: %d\n", maxProps);
    printf("MaxLit: %d\n", sign(maxLit) ? (- var(maxLit)) : var(maxLit));
    // Restore phase saving
    phase_saving = phaseBefore;
    return true;
}

void Solver::updateThreshold(bool taken){
    double c = 1000;
    double val = taken ? 1 : 0;
    dyn_threshold += (target_rate-val)/c;
}

void Solver::checkClausesUnterAssumptions(vec<Lit> & ass, set<vector<int> > & allClauses, set<pair<int, int> > & binaries, int & duplicates){
    if(!restoreTrail(ass))
        return;
    int equivs = 0;
    int implied = 0;
    for(int i = 0 ; i < clauses.size();i++){
        Clause & c = ca[clauses[i]];
        int nTrue = 0;
        int nFalse = 0;
        vector<int> v;
        for(int j = 0 ; j < c.size();j++){
            if(value(c[j]) == l_True)
                nTrue++;
            else if(value(c[j]) == l_Undef)
                v.push_back(toInt(c[j]));
        }
        if(nTrue == 0){
            sort(v.begin(), v.end());
            if(allClauses.count(v))
                duplicates++;
            else
                allClauses.insert(v);
            if(v.size() == 2){
                binaries.insert(make_pair(v[0], v[1]));
                if(binaries.count(make_pair(v[0]^1, v[1]^1)))
                    equivs++;
                else if(binaries.count(make_pair(v[0]^1, v[1])) || binaries.count(make_pair(v[0], v[1]^1)))
                    implied++;
            }
        }
    }
    for(int i = 0 ; i < learnts.size();i++){
        Clause & c = ca[learnts[i]];
        int nTrue = 0;
        int nFalse = 0;
        vector<int> v;
        for(int j = 0 ; j < c.size();j++){
            if(value(c[j]) == l_True)
                nTrue++;
            else if(value(c[j]) == l_Undef)
                v.push_back(toInt(c[j]));
        }
        if(nTrue == 0){
            sort(v.begin(), v.end());
            if(allClauses.count(v))
                duplicates++;
            else
                allClauses.insert(v);
            if(v.size() == 2){
                binaries.insert(make_pair(v[0], v[1]));
                if(binaries.count(make_pair(v[0]^1, v[1]^1)))
                    equivs++;
                else if(binaries.count(make_pair(v[0]^1, v[1])) || binaries.count(make_pair(v[0], v[1]^1)))
                    implied++;
            }
        }
    }
    printf("c checked clauses, have %d actual clauses left, %d duplicates, %d equivalences, %d implied literals! \n", allClauses.size(), duplicates, equivs, implied);
    cancelUntil(0);
}

bool Solver::check_lit_with_assumptions(Lit l, std::vector<bool> & seenHere, vec<Lit> & ass){
    for(int i = 0 ; i < ass.size();i++){
        if(value(ass[i]) == l_False){
            printf("c got UNSAT during conditional FL check! \n");
            return true;
        }
        else if(value(ass[i]) == l_Undef){
            newDecisionLevel();
            uncheckedEnqueue(ass[i]);
            CRef confl = propagate();
            if(confl != CRef_Undef){
                printf("c got confl while propagating trail! \n");
                return true;
            }
        }
    }
    if(value(l) == l_Undef && !seenHere[toInt(l)] ){
        int dlBefore = decisionLevel();
        newDecisionLevel();
        uncheckedEnqueue(l);
        CRef confl = propagate();
        if(confl == CRef_Undef){
            // mark all seen literals
            for(int i = trail.size()-1 ; i >= 0 ; i--){
                seenHere[toInt(trail[i])]=true;
                if(level(var(trail[i])) < decisionLevel())
                    break;
            }
            cancelUntil(dlBefore);
        }
        else{
            int backtrack_level;
            vec<Lit> learnt_clause;
            analyze(confl, learnt_clause, backtrack_level);
            int startDL = decisionLevel();
            unsigned int LBD = computeLBD(learnt_clause);
            cancelUntil(backtrack_level);
            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
                confl = propagate();
                if(confl != CRef_Undef){
                    printf("c got UNSAT??? \n");
                    return true;
                }
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);
                attachClause(cr);
                claBumpActivity(ca[cr]);
                ca[cr].setGood(LBD <= dyn_threshold);
                updateThreshold(ca[cr].isGoodClause());
                //printf("c got clause of size %d, DL %d, backtrack to %d??? \n", learnt_clause.size(), decisionLevel(), backtrack_level);
                int maxDL = 0;
                for(int i = 0 ; i < learnt_clause.size();i++){
                    if(value(learnt_clause[i]) != l_Undef){
                        if(level(var(learnt_clause[i])) - 1 > maxDL)
                            maxDL = level(var(learnt_clause[i]))-1;
                    }
                }
                cancelUntil(maxDL);
                int numFree = 0;
                for(int i = 0 ; i < learnt_clause.size();i++)
                    if(value(learnt_clause[i]) == l_Undef)
                        numFree++;
                if(numFree <= 1){
                    printf("c this is weird. DL %d -> %d -> %d, clause has %d literals", startDL, backtrack_level, maxDL, learnt_clause.size());
                }
                assert(numFree > 1);
                confl = propagate();
                if(confl != CRef_Undef){
                    printf("c got UNSAT after propagating this clause? this should not happen! \n");
                    return true;
                }
            }
        }
    }
    return false;
}

bool Solver::FL_Check_With_Assumptions(vec<Lit> & ass){
    cancelUntil(0);
    double t = cpuTime();
    if(!restoreTrail(ass)){
        printf("c could not restore trail...\n");
        return false;
    }
    int tsBefore = trail.size();
    vector<bool> seenHere(2*nVars(), false);
    for(int i = 0 ; i < nVars();i++){
        if(check_lit_with_assumptions(mkLit(i), seenHere, ass))
            return false;
        if(check_lit_with_assumptions(~mkLit(i), seenHere, ass))
            return false;
    }
    //printf("c conditional FL check done! \n");
    restoreTrail(ass);
    printf("c solver %d trail size %d -> %d in time %lf\n", mpi_rank, tsBefore, trail.size(), cpuTime()-t);
    cancelUntil(0);
    return true;

}

Lit    Solver::getNextBranchLit(vec<Lit> & ass)
{
    cancelUntil(0);
    for(int i = 0 ; i < ass.size();i++){
        if(value(ass[i]) == l_Undef){
            newDecisionLevel();
            uncheckedEnqueue(ass[i]);
            CRef confl = propagate();
            if(confl != CRef_Undef){
                printf("c got conflict while getting new cube! \n");
                cancelUntil(0);
                return lit_Undef;
            }
        }
        else if(value(ass[i]) == l_False){
            printf("c looking for cube, lit is false??? \n");
            cancelUntil(0);
            return lit_Undef;
        }
    }
    Lit next = pickBranchLit();
    cancelUntil(0);
    return next;
}

Lit Solver::getNextBranchLitFromList(vec<Lit> & ass, vec<Lit> & list){
    assert(0 == decisionLevel());
    cancelUntil(0);
    for(int i = 0 ; i < ass.size();i++){
        if(value(ass[i]) == l_Undef){
            newDecisionLevel();
            uncheckedEnqueue(ass[i]);
            CRef confl = propagate();
            if(confl != CRef_Undef){
                printf("c got conflict while getting new cube! \n");
                cancelUntil(0);
                return lit_Undef;
            }
        }
        else if(value(ass[i]) == l_False){
            printf("c looking for cube, lit is false??? \n");
            cancelUntil(0);
            return lit_Undef;
        }
    }
    Lit rVal = lit_Undef;
    for(int i = 0 ; i < list.size();i++){
        if(value(list[i]) == l_Undef){
            rVal = list[i];
            break;
        }
    }
    cancelUntil(0);
    return rVal;
}

bool    Solver::restoreTrail(vec<Lit> & ass){
    cancelUntil(0);
    for(int i = 0 ; i < ass.size();i++){
        if(value(ass[i]) == l_Undef){
            newDecisionLevel();
            uncheckedEnqueue(ass[i]);
            CRef confl = propagate();
            if(confl != CRef_Undef){
                printf("c got conflict while restoring trail! \n");
                cancelUntil(0);
                return false;
            }
        }
        else if(value(ass[i]) == l_False){
            cancelUntil(0);
            return false;
        }
    }
    return true;
}

void Solver::updateProgress(int length, vector<int> & progress){
    while(progress.size() <= length)
        progress.push_back(0);
    while(length >= 0){
        if(progress[length])
            progress[length]=0;
        else{
            progress[length]=1;
            break;
        }
        length--;
    }
    double sum = 0.0;
    for(int i = 0 ; i < progress.size();i++){
        if(progress[i])
            sum += std::pow(0.5, i);
    }
    printf("c progress: %lf\n", sum);
}

void Solver::initMPIStuff(){
    MPI_Init(NULL, NULL);
    MPI_Comm_rank(MPI_COMM_WORLD, &mpi_rank);
    MPI_Comm_size(MPI_COMM_WORLD, &mpi_num_ranks);
    int buf_size = 100 * 1000 * 1000 * sizeof(int);
    int * my_buffer = (int*) malloc(buf_size);
    assert(my_buffer);
    MPI_Buffer_attach(my_buffer, buf_size);
}

void Solver::initParameters(){
    printf("c TODO: Adjust parameters! \n");
    int tmp = mpi_rank;
    // Restart interval: 1024, 2048 or 4096
    switch(tmp % 3){
    case 0:
        restart_interval = 1024;
        break;
    case 1:
        restart_interval = 2048;
        break;
    default:
        restart_interval = 4096;
    }
    tmp /= 3;
    // conflicts per cube: 50000, 100000, 200000
    switch(tmp % 3){
    case 0:
        conflsPerCube = 50 * 1000;
        break;
    case 1:
        conflsPerCube = 100 * 1000;
        break;
    default:
        conflsPerCube = 250 * 1000;
    }
    tmp /= 3;
    // Max size of clause DB: 200000, 500000, 1000000
    switch(tmp % 3){
    case 0:
        maxDB_size = 200 * 1000;
        break;
    case 1:
        maxDB_size = 500 * 1000;
        break;
    default:
        maxDB_size = 1000 * 1000;
    }
    printf("c configured: myRank %d, restart %d confls %d maxDB %d\n", mpi_rank, restart_interval, conflsPerCube, maxDB_size);
    //assert(false && "TODO");

}

bool Solver::importFailedCubes(){
    bool done = false;
    while(!done){
        MPI_Status s;
        int received;
        MPI_Iprobe(MPI_ANY_SOURCE, TAG_SHARED_FAILED_CUBE, MPI_COMM_WORLD, &received, &s);
        if(received){
            int length;
            MPI_Get_count(&s, MPI_INT, &length);
            int  arr[length];
            MPI_Recv(arr, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
            cancelUntil(0);
            vec<Lit> ps;
            for(int i = 0 ; i < length ; i++)
                ps.push(toLit(arr[i]));
            addClause(ps);
            if(!ok){
                printf("c got conflict while importing shared failed cube of size %d\n", length);
                return false;
            }

        }
        else{
            MPI_Iprobe(MPI_ANY_SOURCE, TAG_STEAL_REQUEST, MPI_COMM_WORLD, &received, &s);
            if(received){
                printf("c slave %d received steal request! \n", mpi_rank);
                stealRequestPending = true;
                int dummy;
                MPI_Recv(&dummy, 0, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
            }
            done = true;
        }
    }
    return true;
}

bool Solver::share_failed_cube(vec<Lit> & ps){
    verbosity = 0;
    lbool ret = solveLimited(ps);
    assert(ret == l_False);
    if(conflict.size() <= 1){
        printf("c master analyzed failed cube of size %d, got conflict of size %d \n", ps.size(), conflict.size());
    }
    bool test = true;
    if(test){
        printf("c master analyzed failed cube of size %d, got conflict of size %d \n", ps.size(), conflict.size());
    }
    addClause(conflict);
    vector<int> confl;
    for(int i = 0 ; i < conflict.size();i++)
        confl.push_back(toInt(conflict[i]));
    if(confl.size() <= 1){
        printf("c master sharing failed cube of size %d! \n", confl.size());
    }
    sort(confl.begin(), confl.end());
    if(master_shared_cubes.count(confl) == 0){
        master_shared_cubes.insert(confl);
        // Send it to all others:
        int arr[confl.size()];
        for(int i = 0 ; i < confl.size();i++)
            arr[i] = confl[i];
        for(int i = 1 ; i < mpi_num_ranks ; i++){
            MPI_Bsend(arr, conflict.size(), MPI_INT, i,TAG_SHARED_FAILED_CUBE , MPI_COMM_WORLD);
        }
    }
    return true;
}

bool Solver::failedCube(int * arr, int n, int sender){
    int cubeLength = arr[0];
    int conflLength = arr[1];
    printf("c received failed cube of size %d, conflict size %d\n", cubeLength, conflLength);
    vec<Lit> failedCube;
    vec<Lit> conflict;
    for(int i = 0 ; i < cubeLength ; i++)
        failedCube.push(toLit(arr[2+i]));
    for(int i = 0 ; i < conflLength ; i++){
        conflict.push(toLit(arr[2+cubeLength+i]));
    }
    addClause(conflict);
    share_failed_cube(failedCube);
    vec<Lit> failedCube2;
    for(int i = failedCube.size()-1 ; i >= 0; i--){
        failedCube2.push(failedCube[i]);
    }
    share_failed_cube(failedCube2);
    return false;
}
void Solver::sendNextJob(vector<vector<int> > & open_cubes, vector<int> & idle_slave_indices, map<int, vector<int> > & lastCubes){
    printf("c looking for job for slave\n");
    int nextSlave = idle_slave_indices.back();
    idle_slave_indices.pop_back();
    // Get the next job:
    int shortestFoundIndex = 0;
    int longestPrefix = -1;
    int bestIndex = -1;

    for(int i = 0 ; i < open_cubes.size();i++){
        if(open_cubes[i].size() < open_cubes[shortestFoundIndex].size())
            shortestFoundIndex = i;
        if(lastCubes.find(nextSlave) != lastCubes.end()){
            int sz = 0;
            vector<int> & lastPref = lastCubes[nextSlave];
            for(int j = 0 ; j < lastPref.size() && j < open_cubes[i].size() && open_cubes[i][j] == lastPref[j] ; j++)
                sz++;
            if(sz > longestPrefix || (sz == longestPrefix && open_cubes[i].size() < open_cubes[bestIndex].size())){
                longestPrefix = sz;
                bestIndex = i;
            }

        }
    }
    printf("c chose slave %d have %d open jobs, shortest %d\n", nextSlave, open_cubes.size(), open_cubes[shortestFoundIndex].size());
    vector<int> nextCube;
    if(open_cubes[shortestFoundIndex].size() <=opt_shortCube  || bestIndex < 0){
        nextCube.insert(nextCube.end(), open_cubes[shortestFoundIndex].begin(), open_cubes[shortestFoundIndex].end());
        open_cubes[shortestFoundIndex] = open_cubes.back();
        open_cubes.pop_back();
    }
    else{
        nextCube.insert(nextCube.end(), open_cubes[bestIndex].begin(), open_cubes[bestIndex].end());
        open_cubes[bestIndex] = open_cubes.back();
        open_cubes.pop_back();
    }
    int arr[nextCube.size()];
    for(int i = 0 ; i < nextCube.size();i++)
        arr[i] = nextCube[i];
    lastCubes[nextSlave] = nextCube;
    printf("c sending cube to %d : ", nextSlave);
    for(int i = 0 ; i < nextCube.size();i++)
        printf("%d ", (nextCube[i] % 2 == 0) ? nextCube[i]/2 : -nextCube[i]/2);
    printf("\n");
    MPI_Bsend(arr, nextCube.size(), MPI_INT, nextSlave, TAG_NEW_CUBE_FOR_SLAVE, MPI_COMM_WORLD);
}

bool Solver::master_solve(){
    vector<vector<int> > open_cubes;
    vector<int> progress;
    open_cubes.push_back(vector<int>());
    vector<int> idle_slave_indices;
    vec<Lit> guide_to_sat;
    map<int, vector<int> > lastCube;
    bool done = false;
    bool foundSAT = false;
    double time_last_steal_request = MPI_Wtime();
    while(!done){
        if(open_cubes.size() > 0 && idle_slave_indices.size() > 0){
            // Pick a solver and send next cube:
            sendNextJob(open_cubes, idle_slave_indices, lastCube);
        }
        if(open_cubes.size() < mpi_num_ranks && MPI_Wtime() > time_last_steal_request + 5){
            printf("c master: have only %d open jobs, sending steal request! \n", open_cubes.size());
            for(int i = 1 ; i < mpi_num_ranks ; i++){
                MPI_Bsend(NULL, 0, MPI_INT, i,TAG_STEAL_REQUEST , MPI_COMM_WORLD);

            }
            time_last_steal_request = MPI_Wtime();
        }
        MPI_Status s;
        int received;
        MPI_Iprobe(MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &received, &s);
        if(received){
            int length;
            switch(s.MPI_TAG){
                case TAG_CUBE_REQUEST:
                    MPI_Get_count(&s, MPI_INT, &length);
                    int dummy;
                    assert(length <= 1);
                    MPI_Recv(&dummy, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
                    //printf("c solver %d requested cube! \n", s.MPI_SOURCE);
                    idle_slave_indices.push_back(s.MPI_SOURCE);
                break;
            case TAG_SAT_ANSWER:{
                MPI_Get_count(&s, MPI_INT, &length);
                int  arr[length]; // = (int*) malloc(length * sizeof(int));
                MPI_Recv(arr, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
                foundSAT = true;
                done = true;
                guide_to_sat.clear();
                for(int i = 0 ; i < length ; i++){
                    Lit l = toLit(arr[i]);
                    assert(var(l) >= 0);
                    assert(var(l) < nVars());
                    guide_to_sat.push(l);
                }
                printf("c received partial solution from %d\n", s.MPI_SOURCE);
                break;
            }
            case TAG_UNSAT_ANSWER:
            {
                MPI_Get_count(&s, MPI_INT, &length);
                int  arr [length]; // = (int*) malloc(length * sizeof(int));
                MPI_Recv(arr, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
                failedCube(arr, length, s.MPI_TAG);
                updateProgress(arr[0], progress);
                break;
            }
            case TAG_NEW_CUBE_FOR_MASTER:
            {
                MPI_Get_count(&s, MPI_INT, &length);
                int  arr [length]; // = (int*) malloc(length * sizeof(int));
                MPI_Recv(arr, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
                vector<int> newCube;
                printf("c master received new cube from %d: ", s.MPI_SOURCE);
                for(int i = 0 ; i < length ; i++){
                    newCube.push_back(arr[i]);
                    printf("%d ", (newCube[i] % 2 == 0) ? newCube[i]/2 : -newCube[i]/2);
                }
                printf("\n");
                open_cubes.push_back(newCube);
                break;
            }
            default:
                printf("c master received weird message: %d\n", s.MPI_TAG);
                // MPI_Get_count(&s, MPI_INT, &length);
                // MPI_Recv(arr, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
            }
        }
        else{
            usleep(2000);
        }
    // Am I done?
        if(idle_slave_indices.size() == mpi_num_ranks-1 && open_cubes.size() == 0 && progress.size() > 0){
            printf("c checking progress...\n");
            assert(progress[0] == 1);
            done = true;
        }
    }
    for(int i = 1 ; i < mpi_num_ranks ; i++)
        MPI_Bsend(NULL, 0, MPI_INT, i, TAG_TERMINATE, MPI_COMM_WORLD);
    MPI_Barrier(MPI_COMM_WORLD);
    printf("c master passed barrier foundSAT=%d\n", foundSAT);
    if(foundSAT){
        usleep(300 * 1000);
        printf("c master tying to restore solution conflicts here: %d\n \n", conflicts);
        usleep(300 * 1000);
        //guide_to_sat.clear();
        lbool restore = solveLimited(guide_to_sat);
        printf("c return was true: %d and conflicts %d\n", restore == l_True, conflicts);
        return true;
    }
    return false;
}

void Solver::slave_solve(vec<Lit> & firstCubes){
    verbosity = 0;
    bool done = false;
    int solveCalls = 0;
    MPI_Bsend(NULL, 0, MPI_INT, 0, TAG_CUBE_REQUEST, MPI_COMM_WORLD);
    while(!done){
        MPI_Status s;
        int received;
        MPI_Iprobe(MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &received, &s);
        if(received){
            int length;
            switch(s.MPI_TAG){
            case TAG_NEW_CUBE_FOR_SLAVE:
            {

                MPI_Get_count(&s, MPI_INT, &length);
                int  arr[length];
                printf("c received cube of size %d\n", length);
                MPI_Recv(arr, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
                vec<Lit> ass;

                bool shortCube = solveCalls < 4 || length <= opt_shortCube;
                for(int i = 0 ; i < length ; i++)
                    ass.push(toLit(arr[i]));
                if(length <= opt_shortCube)
                    setConfBudget(10);
                else{
                    setConfBudget(conflsPerCube);
                }
                //printf("c slave %d calling solve\n",mpi_rank );
                int conflsBefore = conflicts;
                solveCalls++;
                lbool ret ;
                if(shortCube)
                    ret  = solveLimited(ass);
                else{
                    setConfBudget(2000);
                    ret = solveLimited(ass);
                    if(ret == l_Undef){
                        FL_Check_With_Assumptions(ass);
                        setConfBudget(conflsPerCube);
                        ret = solveLimited(ass);
                    }
                }

                if(ret == l_False){
                    printf("c solver %d cube failed after %d conflicts\n", mpi_rank, conflicts - conflsBefore);
                    int arr[2 + conflict.size() + ass.size()];
                    arr[0] = ass.size();
                    arr[1] = conflict.size();
                    for(int i = 0 ; i < ass.size();i++)
                        arr[2+i] = toInt(ass[i]);
                    for(int i = 0 ; i < conflict.size();i++)
                        arr[2+ass.size()+i] = toInt(conflict[i]);
                    MPI_Bsend(arr, ass.size() + conflict.size()+2, MPI_INT, 0, TAG_UNSAT_ANSWER, MPI_COMM_WORLD);
                    MPI_Bsend(NULL, 0, MPI_INT, 0, TAG_CUBE_REQUEST, MPI_COMM_WORLD);

                }
                else if(ret == l_True){
                    printf("c got SAT, lastTrail.size()=%d\n", lastTrail.size());
                    int arr[lastTrail.size()];
                    for(int i = 0 ; i < lastTrail.size();i++)
                        arr[i] = toInt(lastTrail[i]);
                    MPI_Bsend(arr, lastTrail.size() , MPI_INT, 0, TAG_SAT_ANSWER, MPI_COMM_WORLD);
                }
                else{
                    printf("c cube not solved, sending answer to master! \n");
                    Lit next = getNextBranchLitFromList(ass, firstCubes);
                    if(next == lit_Undef)
                        next = getNextBranchLit(ass);
                    if(next == lit_Undef){
                        // Send this cube back to the solver
                        printf("c solver %d could not find branching literal??? \n", mpi_rank);
                        int arr[length];
                        for(int i = 0 ; i < ass.size();i++){
                            arr[i] = toInt(ass[i]);
                            MPI_Bsend(arr, length, MPI_INT, 0, TAG_NEW_CUBE_FOR_MASTER, MPI_COMM_WORLD);
                            MPI_Bsend(NULL, 0, MPI_INT, 0, TAG_CUBE_REQUEST, MPI_COMM_WORLD);
                        }
                    }
                    else{
                        int arr1[length+1];
                        int arr2[length+1];
                        for(int i = 0 ; i < ass.size();i++){
                            arr1[i] = arr2[i] = toInt(ass[i]);
                        }
                        arr1[length] = toInt(mkLit(var(next)));
                        arr2[length] = toInt(~mkLit(var(next)));
                        MPI_Bsend(arr1, length+1, MPI_INT, 0, TAG_NEW_CUBE_FOR_MASTER, MPI_COMM_WORLD);
                        MPI_Bsend(arr2, length+1, MPI_INT, 0, TAG_NEW_CUBE_FOR_MASTER, MPI_COMM_WORLD);
                        MPI_Bsend(NULL, 0, MPI_INT, 0, TAG_CUBE_REQUEST, MPI_COMM_WORLD);
                    }
                }
            }
                break;
            case TAG_TERMINATE:
                done = true;
                break;
            case TAG_SHARED_FAILED_CUBE:
                importFailedCubes();
                break;
            case TAG_STEAL_REQUEST:
            {
                int dummy;
                stealRequestPending = true;
                MPI_Recv(&dummy, 0, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
                break;
            }
            default:
                printf("c received weird tag %d\n", s.MPI_TAG);
                break;
            }
        }
        else{
            usleep(1000);
        }
    }
    printf("c slave %d at barrier! \n", mpi_rank);
    MPI_Barrier(MPI_COMM_WORLD);

}

lbool Solver::mpi_solve(vec<Lit> & firstCubes){
    // init all stuff
    //initMPIStuff();
    // init parameter
    initParameters();
    lbool ret = l_False;
    printf("c mpi_solve, rank=%d\n", mpi_rank);
    if(mpi_rank == 0){
        bool succ = master_solve();
        if(succ){
            ret = l_True;
        }
    }
    else{
        slave_solve(firstCubes);
    }
    MPI_Barrier(MPI_COMM_WORLD);
    return ret;
}

lbool Solver::DFS_Solve(vec<Lit> & firstCubes){
    vector<vector<int> > cubes;
    vector<int> progress;
    /*if(firstCubes.size() > 0){
        for(int i = 0 ; i < (1<<firstCubes.size()) ; i++){
            vector<int> v;
            for(int j = 0 ; j < firstCubes.size();j++){
                if(i & (1<<j))
                    v.push_back(toInt(firstCubes[j]));
                else
                    v.push_back(toInt(~firstCubes[j]));

            }
            cubes.push_back(v);
        }

    }
    else*/
    cubes.push_back(vector<int>());
    bool done = false;
    bool hadUnSAT = false;
    verbosity = 0;
    int numChecked = 0;
    while(!done){
        int bestIndex = cubes.size()-1;
        if(false && numChecked < 128){
            // take shortest cube
            for(int i = 0 ; i < cubes.size();i++){
                if(cubes[i].size() < cubes[bestIndex].size())
                    bestIndex = i;
            }
        }
        else{
            // take last cube
        }
        vector<int> v = cubes[bestIndex];
        cubes.erase(cubes.begin()+bestIndex);
        printf("c checking cube ");
        for(int i = 0 ; i < v.size();i++){
               printf("%d ", (v[i] % 2 == 0) ? v[i]/2 : -v[i]/2);
        }
        printf("\n");
        set<vector<int> > tmpSet;
        set<pair<int, int> > tmpBinaries;
        int numDupl=0;
        numChecked++;
        vec<Lit> ass;
        for(int i = 0 ; i < v.size();i++)
            ass.push(toLit(v[i]));
        int confBudget = opt_numConfls;
        if(getNextBranchLitFromList(ass, firstCubes) != lit_Undef){
            if(!hadUnSAT)
                confBudget = 1000;
            else
                confBudget = opt_numConfls/4;
        }
        else{
            FL_Check_With_Assumptions(ass);
        }
        printf("c setting conf Budget to %d\n", confBudget);
        setConfBudget(confBudget);
        //checkClausesUnterAssumptions(ass, tmpSet, tmpBinaries, numDupl);
        //printf("c calling FL check with assumptions! ")
        double t = cpuTime();
        int conflsBefore = conflicts;
        lbool ret = solveLimited(ass);
        if(ret == l_True)
            return l_True;
        else if(ret == l_False){
            hadUnSAT = true;
            printf("c cube of size %d is UNSAT! ", ass.size());
            for(int i = 0 ; i < v.size();i++){
                printf("%d ", (v[i] % 2 == 0) ? v[i]/2 : -v[i]/2);
            }
            printf("\n");
            printf("c conflict size %d\n", conflict.size());
            printf("c time was %lf, conflicts %d\n", cpuTime()-t, conflicts - conflsBefore);
            if(conflict.size() == 0)
                done = true;
            updateProgress(ass.size(), progress);
            addClause(conflict);
            if(conflict.size() <= 2){
                cancelUntil(0);
                FL_Check_fast();
            }
        }
        else{
            Lit next = getNextBranchLitFromList(ass, firstCubes);
            if(next == lit_Undef)
                next = getNextBranchLit(ass);
            if(next == lit_Undef)
                cubes.push_back(v);
            else{
                vector<int> v2(v.begin(), v.end());
                vector<int> v3(v.begin(), v.end());
                v2.push_back(toInt(~mkLit(var(next))));
                v3.push_back(toInt(mkLit(var(next))));
                cubes.push_back(v2);
                cubes.push_back(v3);
            }
        }
    }
    return l_False;
}

void Solver::reduceDB_with_assumptions(vec<Lit> & ass){
    cancelUntil(0);
    int nbLockedBefore = 0;
    for(int i = 0 ; i < learnts.size();i++){
        Clause & c = ca[learnts[i]];
        if(locked(c))
            nbLockedBefore++;
    }
    for(int i = 0 ; i < ass.size();i++){
        if(value(ass[i]) == l_Undef){
            newDecisionLevel();
            uncheckedEnqueue(ass[i]);
            CRef confl = propagate();
            if(confl != CRef_Undef){
                printf("c got conflict while trying to clean DB! \n");
                cancelUntil(0);
                return;
            }
        }
        else if(value(ass[i]) == l_False){
            printf("c got conflict while trying to clean DB, lit is false??? \n");
            cancelUntil(0);
            return;
        }
    }
    int nbLockedAfter = 0;
    for(int i = 0 ; i < learnts.size();i++){
        Clause & c = ca[learnts[i]];
        if(locked(c))
            nbLockedAfter++;
    }
    printf("c reduce with assumptions, locked: %d vs %d\n", nbLockedBefore, nbLockedAfter);
    reduceDB();
    cancelUntil(0);
    return;
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    int delay_Checks = 10000;
    int delay_counter_asymBranch = 4;
    int conflsNextCheck = delay_Checks;
    solves++;
    if(verbosity >= 1) 
        printf("Solve called, numVars()=%d, assigned at DL0: %d, num Clauses: %d, learnt clauses: %d\n", nVars(), trail.size(), clauses.size(), learnts.size());
    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("===============================================================================\n");
    }

    dyn_threshold = opt_ThresholdPermanent;
    target_rate = opt_target_rate;
    // Search:
    /*if(assumptions.size() > 0){
        reduceDB_with_assumptions(assumptions);
    }*/
    int curr_restarts = 0;
    int calls = 0;
    while (status == l_Undef){
        importFailedCubes();
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        int maxConfls = rest_base * restart_first;
        if(maxConfls > 4000){
            maxConfls = 4000;
        }
        status = search(restart_interval);
        if (!withinBudget()) break;
        curr_restarts++;
        if(conflicts > conflsNextCheck && status == l_Undef && opt_subsumptionTests){
            printf("c running tests, dynThreshold=%lf\n", dyn_threshold);
            delay_counter_asymBranch--;
            if(delay_counter_asymBranch <= 0){
                lbool test = checkLearnts((calls % 10) == 0);
                calls++;
                delay_counter_asymBranch = 4;
                if(test == l_False){
                    status = l_False;
                }
            }
            if(status == l_Undef){
                //checkDuplicates();
                for(int i = 0 ; i < 5 ; i++)
                    if(!mySubsumptionTest())
                        break;
                reduceDB();

            }

            conflsNextCheck = conflicts + delay_Checks;
            delay_Checks *= 1.3;
        }
        else if(!opt_subsumptionTests && conflicts > conflsNextCheck && status == l_Undef && assumptions.size() == 0){
            conflsNextCheck = conflicts + delay_Checks;

            reduceDB();
        }
        if(stealRequestPending){
            stealRequestPending = false;
            if(status == l_Undef){
                return status;
            }
        }
    }

    if (verbosity >= 1)
        printf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0);
    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            //fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
        fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", var(c[i]));
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        //fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", var(assumptions[i]));
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    printf("c reloc called! \n");
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
