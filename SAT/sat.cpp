#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
#include <map>

using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

typedef vector<int> Clause;

long long int numPropagations = 0;
long long int numDecisions = 0;

vector<Clause> clauses;
uint numVars;
uint numClauses;

vector< vector<Clause> > positive;
vector< vector<Clause> > negative;
vector< vector<Clause> > litToClauses;

vector<int> model;      
uint modelStackCurrentSize = 0;
vector<int> modelStack;

vector< pair<int,int> > litsFreq;
vector< int > indexsOfLitsFreq;

vector<int> litScore;

uint indexOfNextLitToPropagate;
uint decisionLevel;

bool sortByFreq(const pair<int,int>& a, const pair<int,int>& b) {
    return a.second > b.second;
}

void readClauses()
{
    // Skip comments
    char c = cin.get();
    while (c == 'c') {
        while (c != '\n') c = cin.get();
        c = cin.get();
    }

    // Read "cnf numVars numClauses"
    string aux;
    cin >> aux >> numVars >> numClauses;
    positive.resize(numVars);
    negative.resize(numVars);
    litToClauses.resize(numVars);

    litScore = vector<int>(numVars + 1, 0);

    litsFreq.resize(numVars);
    for(uint i = 0; i < numVars; ++i)  {
        litsFreq[i].first = (i+1);
        litsFreq[i].second = 0;
    }

    clauses.resize(numClauses);

    // Read clauses
    for (uint i = 0; i < numClauses; ++i) {
        int lit;
        int lits[3]; int j = 0;
        while (cin >> lit && lit != 0) {
            clauses[i].push_back(lit);
            lits[j++] = lit;
        }
        for(uint k = 0; k < 3; ++k) {
            lit = lits[k];
            litsFreq[abs(lit)-1].second++; //Increase frequency
            if(lit > 0) positive[abs(lit)-1].push_back(clauses[i]);
            else negative[abs(lit)-1].push_back(clauses[i]);
            litToClauses[abs(lit)-1].push_back(clauses[i]);
        }
    }

    std::sort(litsFreq.begin(),litsFreq.end(),sortByFreq);

    indexsOfLitsFreq.resize(numVars+1, 0);
    for(int i = 0; i < litsFreq.size(); ++i) {
        indexsOfLitsFreq[litsFreq[i].first - 1] = i;
    }
}

inline int currentValueInModel(int lit) {
    if (lit >= 0) return model[lit];
    else {
        if (model[-lit] == UNDEF) return UNDEF;
        else return 1 - model[-lit];
    }
}


inline void setLiteralToTrue(int lit) {
    modelStack.push_back(lit);
    if (lit > 0) model[abs(lit)] = (lit > 0);
    else model[-lit] = FALSE;
}


bool propagateGivesConflict() {
    while(indexOfNextLitToPropagate < modelStack.size()) {
        int lit = modelStack[indexOfNextLitToPropagate];
        ++indexOfNextLitToPropagate;
        ++numPropagations;

        //We only care about clauses where lit appears with opposite polarity
        const vector<Clause> &clausesCheckConflict = (currentValueInModel(abs(lit)) == TRUE) ?
                                                           negative[abs(lit)-1] :
                                                           positive[abs(lit)-1];

        for(uint i = 0; i < clausesCheckConflict.size(); ++i) {
            int numUndefs = 0;
            int lastLitUndef = 0;
            bool someLitTrue = false;

            for(uint j = 0; !someLitTrue && j < 3; ++j) {
                const int x = currentValueInModel(clausesCheckConflict[i][j]);
                if (x == UNDEF) {
                    ++numUndefs;
                    lastLitUndef = clausesCheckConflict[i][j];
                }
                else if(x == TRUE) someLitTrue = true;
            }
            if(!someLitTrue) {
                if(numUndefs == 0) {
                    //CONFLICT! All literals are false!
                    return true;
                }
                else if(numUndefs == 1) setLiteralToTrue(lastLitUndef);
            }
        }
    }
    return false;
}


void backtrack()
{
    uint i = modelStack.size() -1;
    int lit = 0;
    while (modelStack[i] != 0) // 0 is the DL mark
    {
        lit = modelStack[i];
        model[abs(lit)] = UNDEF;
        modelStack.pop_back();
        --i;
    }
    // at this point, lit is the last decision
    modelStack.pop_back(); // remove the DL mark
    --decisionLevel;
    indexOfNextLitToPropagate = modelStack.size();
    setLiteralToTrue(-lit);  // reverse last decision
}

// Heuristic for finding the next decision literal:

int getNextDecisionLiteral() {
    //first decision, choose the lit with most freq
    if(decisionLevel == 0) {
        for(uint i = 0; i < numVars; ++i) {
            if(currentValueInModel(litsFreq[i].first) == UNDEF)
                return litsFreq[i].first;
        }
    }
    int maxScore = 0;
    int maxLit = -1;
    ++numDecisions;

    for(int k = 0; k < litScore.size(); ++k)
        litScore[k] = 0;

    for(uint i = 0; i < numClauses; ++i) {
        uint countFalse = 0;
        uint countUndef = 0;
        int lastFalseIndex = -1;
        for (uint j = 0; j < 3; ++j) {
            const int v = currentValueInModel(clauses[i][j]);
            if (v == UNDEF) ++countUndef;
            else if (v == FALSE) {
                ++countFalse;
                lastFalseIndex = j;
            }
            else break;
        }
        if (countFalse == 1 and countUndef == 2) {
            for (uint j = 0; j < 3; ++j) {
                if (j == lastFalseIndex) continue;
                int lit = clauses[i][j];
                ++litScore[abs(lit)];
            }
        }
    }
    for (uint i = 1; i <= numVars; ++i) {
        if(currentValueInModel(i) == UNDEF) {
            if (litScore[i] == maxScore) {
                if(indexsOfLitsFreq[i-1] < indexsOfLitsFreq[maxLit-1]) {
                    maxLit = i;
                }
            }
            else if (litScore[i] > maxScore) {
                maxScore = litScore[i];
                maxLit = i;
            }
        }
    }
    if (maxLit > 0) return maxLit;
    return 0;
}


void checkmodel()
{
    for (int i = 0; i < numClauses; ++i){
        bool someTrue = false;
        for (int j = 0; not someTrue and j < clauses[i].size(); ++j)
            someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
        if (not someTrue) {
            cout << "Error in model, clause is not satisfied:";
            for (int j = 0; j < clauses[i].size(); ++j) cout << clauses[i][j] << " ";
            cout << endl;
            exit(1);
        }
    }
}


inline void debug(clock_t start) {
    double timeTaken = ((double)(clock() - start) / CLOCKS_PER_SEC);
    cout << "Decisions: " << numDecisions << endl << "Propagations: " << numPropagations << endl << "Time: " << timeTaken << endl;
    cout << "Props/time: " << (long long int)(((double) numPropagations) / timeTaken) << endl;
}


int main()
{
    readClauses(); // reads numVars, numClauses and clauses
    model.resize(numVars+1,UNDEF);
    indexOfNextLitToPropagate = 0;
    decisionLevel = 0;

    clock_t start = clock();

    // DPLL algorithm
    while (true) {
        while (propagateGivesConflict()) {
            if (decisionLevel == 0) {
                cout << "UNSATISFIABLE " << endl;
                debug(start);
                return 10;
            }
            backtrack();
        }
        int decisionLit = getNextDecisionLiteral();
        if (decisionLit == 0) {
            checkmodel();
            cout << "SATISFIABLE " << endl;
            debug(start);
            return 20;
        }
        // start new decision level:
        ++decisionLevel;
        ++indexOfNextLitToPropagate;
        modelStack.push_back(0);       // push mark indicating new DL
        setLiteralToTrue(decisionLit); // now push decisionLit on top of the mark
    }
}
