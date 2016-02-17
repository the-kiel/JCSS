/*
 * ---------------------------------------------------------------------------
 * "THE BEER-WARE LICENSE" (Revision 42):
 * the and mimu wrote this file.  As long as you retain this notice you can do
 * whatever you want with this stuff. If we meet some day, and you think this 
 * stuff is worth it, you can buy us a beer in return.
 * Mike Mueller, Thorsten Ehlers
 * ---------------------------------------------------------------------------
 */

#include <string.h>
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <algorithm>
using namespace std;

struct comp {
    int layer;
    int from;
    int to;

    comp(int a, int b, int c)
        :layer(a), from(b), to(c) {}

    bool operator<(const comp& c2) const {
    	if (layer < c2.layer)
            return true;
        else if ((layer == c2.layer) && (from < c2.from))
            return true;
        else if ((layer == c2.layer) && (from == c2.from) && (to < c2.to))
            return true;
        else
            return false;
    }
};

bool isSet(int val, int bit){
    return val & (1<<bit);
}
/* Get maximum a and b such that val=0^axb^n */
int getWindowSize(int val, int n){
    int tailingOnes = 0;
    int leadingZeros = 0;
    while(leadingZeros < n && !isSet(val, leadingZeros))
        leadingZeros++;
    while(tailingOnes < n && isSet(val, n-tailingOnes-1))
        tailingOnes++;
    return n - (tailingOnes+leadingZeros);
}

/* Parse csv-file, where each row represents one prefix. */
void parseAllLayers(vector<vector<comp> > & out, char * fileName, int diff){
    FILE * fp = fopen(fileName, "r");
    int BUF_SIZE = 1024;
    char buffer[BUF_SIZE];
    int rowRead = 0;
    while(fp && !feof(fp)){
        int scan = fscanf(fp, "%s", buffer);
        if(scan >= 0){
            char * buff = strtok(buffer, ";");
            vector<comp> tmp;
            while(buff){
                int a, b, c;
                a = atoi(buff);
                buff = strtok(NULL, ";");
                b = atoi(buff);
                buff = strtok(NULL, ";");
                c = atoi(buff);
                buff = strtok(NULL, ";");
                tmp.push_back(comp(a, b-diff, c-diff));
            }
            out.push_back(tmp);
        }
        rowRead++;
    }
}

int swap(int val, int a, int b){
    assert(a < b);
    if(val & (1<<a))
        if(!(val & (1<<b)))
            val ^= ((1<<a) | (1<<b));
    return val;
}

/* A bit smarter version: Should run way faster if the first layer is not empty */
void getAllOutputs(vector<comp> & comps, int index, int currentValue, set<int> & outputs){
    if(index >= comps.size())
        outputs.insert(currentValue);
    else if(comps[index].layer == 0){
        // First layer. 
        int from        = comps[index].from;
        int to          = comps[index].to;
        // Three possible outputs: Both zero, Both one, output on "to"-channel 1, the other 0
        /* both zero */
        getAllOutputs(comps, index+1, currentValue, outputs);
        /* both one */
        getAllOutputs(comps, index+1, currentValue | ((1<<from)|(1<<to)), outputs);
        /* "one" at to-channel, zero at "from"-channel */
        getAllOutputs(comps, index+1, currentValue | (1<<to), outputs);
    }
    else{
        for(int i = index ; i < comps.size() ; i++){
            // Later layer. 
            int from        = comps[i].from;
            int to          = comps[i].to;
            // Is the input of this comparator unsorted?
            if(currentValue&(1<<from) && !(currentValue&(1<<to))){
                 currentValue^= ((1<<from)|(1<<to));
            }
        }
        outputs.insert(currentValue);
    }
}
/* If there are channels which are not used in the first layer, try "0" and "1" here, otherwise take only values available in the resulting poset */
void getAllOutputs(vector<comp> & comps, int index, int currentValue, vector<int> & unused, set<int> & outputs){
    if(index >= unused.size()){
        getAllOutputs(comps, 0, currentValue, outputs);
    }
    else{
        // Value on this channel might be one or zero
        getAllOutputs(comps, index+1, currentValue, unused, outputs);
        getAllOutputs(comps, index+1, currentValue|(1<<unused[index]), unused, outputs);
    }
}
/* Precondition: Comparators are sorted according to their layers */
void getAllOutputs(vector<comp> & comps, set<int> & outputs, int n){
    // Which channels are not used in the first layer?
    set<int> used;
    for(int i = 0 ; i < comps.size() ; i++){
        if(comps[i].layer == 0){
            used.insert(comps[i].from);
            used.insert(comps[i].to);
        }
    }
    vector<int> unUsed;
    for(int i = 0 ; i < n ; i++){
        if(used.count(i) == 0)
            unUsed.push_back(i);
    }
    getAllOutputs(comps, 0, 0, unUsed, outputs);
}

/* Count the costs for adding 2000 different inputs, if they are chosen by ascending window size*/
int minCostFor2000Inputs(vector<comp> & comps, int n){
    set<int> outputs;
    getAllOutputs(comps, outputs, n);
    int sizes[n+1];
    for(int i = 0 ; i < n+1 ; i++)
        sizes[i]=0;
    int rVal = 0;
    for(set<int>::iterator it = outputs.begin() ; it != outputs.end() ; it++){
        sizes[getWindowSize(*it, n)]++;
    }
    int sum = 0;
    for(int i = 0 ; i < n+1 ; i++){
        if(sum >= 2000) break;
        if(sum + sizes[i] >= 2000)
            rVal -= i * (2000-sum);
        else
            rVal -= i*sizes[i];
        sum += sizes[i];
    }
    return rVal;
}
// Swap two channels of the prefix from "in", and untangle the result
int swapAndEval(vector<comp> & in, int (*f) (vector<comp>&comps, int), int n,
    int channel1, int channel2
)
{
    // Search for 2 different channels to swap
    while(channel1 == channel2){
        channel1 = random() % n;
        channel2 = random() % n;
    }
    bool done = false;
    int mapsTo[n];
    for(int i = 0 ; i < n ; i++){
        mapsTo[i] = i;
    }
    mapsTo[channel1] = channel2;
    mapsTo[channel2] = channel1;
    vector<comp> test;
    for(vector<comp>::iterator it = in.begin(); it != in.end() ; it++){
        test.push_back(*it);
    }
    // Swap "channel1" and "channel2" on all comparators
    for(vector<comp>::iterator it = test.begin() ; it != test.end() ; it++){
        if(it->from == channel1)
            it->from = channel2;
        else if(it->from == channel2)
            it->from = channel1;
        if(it->to == channel1)
            it->to= channel2;
        else if(it->to == channel2)
            it->to = channel1;
    }
    // As performance is not a big issue here, try the original algorithm from Searching&Sorting as well (runs in O(n^2) )
    for(int i = 0 ; i < test.size() ; i++){
        if(test[i].from > test[i].to){
            int tmp = test[i].from;
            test[i].from = test[i].to;
            test[i].to = tmp;
            int c1 = test[i].from;
            int c2 = test[i].to;
            for(int j = i+1 ; j < test.size() ; j++){
                if(test[j].from == c1)
                    test[j].from = c2;
                else if(test[j].from == c2)
                    test[j].from = c1;
                if(test[j].to == c1)
                    test[j].to = c2;
                else if(test[j].to == c2)
                    test[j].to = c1;
            }
        }
    }
    // Faster version: Remove slow one, if necessary...
    for(vector<comp>::iterator it = in.begin() ; it != in.end() ; it++){
        int from = mapsTo[it->from];
        int to = mapsTo[it->to];
        if(from > to){
            // All further occurcences of "from" will be replaced by "to", and vice versa
            mapsTo[it->from] = to;
            mapsTo[it->to] = from;
            // Turn direction of comparator
            it->from = to;
            it->to = from;
        }
        else{
            // Correct direction, nothing to do
            it->from = from;
            it->to = to;
        }
        // Make sure they aim in the correct direction
        if(it->from >= it->to){
            printf("This should not happen...\n");
            getchar();
            int tmp = it->to;
            it->to = it->from;
            it->from = tmp;
        }
    }
    for(int i = 0 ; i < test.size() ; i++){
        assert(test[i].layer == in[i].layer);
        assert(test[i].from == in[i].from);
        assert(test[i].to == in[i].to);
    }
    return f ? f(in, n) : 0;
}
int swapAndEval(vector<comp> & in, int (*f) (vector<comp>&comps, int), int n){
    int channel1 = random() % n;
    int channel2 = random() % n;
    return swapAndEval(in, f, n, channel1, channel2);
}
/* Run a small evolutionary algorithm (looks like it's smart enough to find good solutions ;) ) */
void optimizePrefix(vector<comp> & input, int runs, int n, int (*f) (vector<comp>&comps, int),
    vector<comp> & output
){
    // Get some children...
    int popSize = 32;
    multimap<int, vector<comp> > pop;
    int bestRating = 0;
    int worstRating = 1000000;
    int initial = f(input, n);
    pop.insert(make_pair(initial, input));
    /* Get some more population members... Just do 20 random swaps*/
    for(int i = 0 ; i < 10 ; i++){
        vector<comp> tmp;
        for(vector<comp>::iterator it = input.begin() ; it != input.end() ; it++){
            tmp.push_back(*it);
        }
        int e = 0;
        for(int j = 0 ; j < 20 ; j++){
            e = swapAndEval(tmp, f, n);
        }
        pop.insert(make_pair(e, tmp));
    }
    for(int i = 0 ; i < runs ; i++){
        multimap<int, vector<comp> > nextGen;

        for(multimap<int, vector<comp> >::iterator it = pop.begin() ; it != pop.end() ; it++){
            vector<comp> tmp;
            // Store original value
            nextGen.insert(*it);
            for(vector<comp>::iterator it2 = it->second.begin() ; it2 != it->second.end() ; it2++){
                tmp.push_back(*it2);
            }
            int eval = swapAndEval(tmp, f, n);
            bestRating = max(bestRating, eval);
            worstRating = min(worstRating, eval);
            nextGen.insert(make_pair(eval, tmp));
        }
        pop.clear();
        set<vector<comp> > checker;
        for(multimap<int, vector<comp> >::reverse_iterator it = nextGen.rbegin() ; it != nextGen.rend() ; it++){
            if(checker.count(it->second) == 0 && pop.size() < popSize){
                pop.insert(*it);
                checker.insert(it->second);
            }
        }
    }
    multimap<int, vector<comp> >::reverse_iterator r = pop.rbegin();
    printf("Done, Init = %d, Best= %d\n", initial, r->first);
    for(vector<comp>::iterator it = r->second.begin() ; it != r->second.end() ; it++){
        output.push_back(*it);
    }
}


int main(int argc, char ** argv)
{
    if(argc < 5){
        printf("Parameters: inputFile n diff \n");
        printf("n=#channels\n");
        printf("diff= lowest index of a channel (default: 0)\n");
    }
    int n = atoi(argv[2]);
    int diff = argc >= 5 ? atoi(argv[4]) : 0;

    vector<vector<comp> > allLayers;
    parseAllLayers(allLayers, argv[1], diff);

    int iter = 0;
    for(vector<vector<comp> >::iterator it = allLayers.begin() ; it != allLayers.end() ; it++){
        vector<comp> current = *it;
        vector<comp> out;
        optimizePrefix(current, 20, n, minCostFor2000Inputs, out);
        for(vector<comp>::iterator it = out.begin() ; it != out.end() ; it++){
            printf("%d;%d;%d;", it->layer, it->from, it->to);
        }
        printf("\n");

    }
    return 0;
}
