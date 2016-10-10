#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
#include <stack>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

struct info{
    int lit;
    int score;
};

int numPropagations = 0;
int numDecisions = 0;

uint numVars;
uint numClauses;

typedef vector<int> Clause;

vector<Clause> clauses;
vector<vector<Clause> > positive;
vector<vector<Clause> > negative;
vector<vector<Clause> > litClause;
vector<info> litFreq;
vector<info> litScore;

vector<int> model;
vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;

bool desc(info a, info b) {return a.score > b.score;}

inline void debug(clock_t start) {
    //for (int i = 0; i < numVars; ++i) cout << decision[i].lit << " lit, " << decision[i].score << " conf" << endl;
    double timeTaken = ((double)(clock() - start) / CLOCKS_PER_SEC);
    cout << "Decisions: " << numDecisions << endl << "Propagations: " << numPropagations << endl << "Time: " << timeTaken << endl;
    cout << "Props/time: " << ((double) numPropagations) / timeTaken << endl;
}

void readClauses( ){
  // Skip comments
  char c = cin.get();
  while (c == 'c') {
    while (c != '\n') c = cin.get();
    c = cin.get();
  }  
  // Read "cnf numVars numClauses"
  string aux;
  cin >> aux >> numVars >> numClauses;
  clauses.resize(numClauses);

  positive.resize(numVars);
  negative.resize(numVars);
  litClause.resize(numVars);
  litFreq.resize(numVars);
  litScore.resize(numVars+1);

  for (int k = 0; k < numVars; ++k) {
      litFreq[k].lit = k+1;
      litFreq[k].score = 0;
  }

   // Read clauses
  for (uint i = 0; i < numClauses; ++i)
  {
    int lit;
    int lits[3]; int j = 0;
    while (cin >> lit && lit != 0)
    {
        clauses[i].push_back(lit);
        lits[j++] = lit;
    }

    for(uint k = 0; k < 3; ++k)
    {
        lit = lits[k];
        litFreq[abs(lit)-1].lit = lit;
        litFreq[abs(lit)-1].score++; //Increase frequency

        if(lit > 0) positive[abs(lit)-1].push_back(clauses[i]);
        else negative[abs(lit)-1].push_back(clauses[i]);
        litClause[abs(lit)-1].push_back(clauses[i]);
    }
  }
  sort(litFreq.begin(),litFreq.end(),desc);
}

inline int currentValueInModel(int lit){
  if (lit >= 0) return model[lit];
  else {
    if (model[-lit] == UNDEF) return UNDEF;
    else return 1 - model[-lit];
  }
}

inline void setLiteralToTrue(int lit){
  modelStack.push_back(lit);
  if (lit > 0) model[lit] = TRUE;
  else model[-lit] = FALSE;		
}

bool propagateGivesConflict ( ) {
  while ( indexOfNextLitToPropagate < modelStack.size() ) {
    int lit = modelStack[indexOfNextLitToPropagate];
    ++indexOfNextLitToPropagate;
    ++numPropagations;

    //Only care about clauses where lit appears in the opposite state
    const vector<Clause> &checkConflict = (currentValueInModel(abs(lit)) == TRUE) ? negative[abs(lit)-1] : positive[abs(lit)-1];

    for(uint i = 0; i < checkConflict.size(); ++i) {
            int numUndefs = 0;
            int lastLitUndef = 0;
            bool someLitTrue = false;
            for(uint j = 0; !someLitTrue && j < 3; ++j) {
                const int jval = currentValueInModel(checkConflict[i][j]);
                if (jval == UNDEF) {
                    ++numUndefs;
                    lastLitUndef = checkConflict[i][j];
                }
                else if(jval == TRUE) someLitTrue = true;
            }
            if (!someLitTrue) { //for each clause
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

void backtrack(){
  uint i = modelStack.size() -1;
  int lit = 0;
  while (modelStack[i] != 0){ // 0 is the DL mark
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
int getNextDecisionLiteral(){
    ++numDecisions;
  for (uint i = 1; i <= numVars; ++i) // stupid heuristic:
    if (model[i] == UNDEF) return i;  // returns first UNDEF var, positively
  return 0; // reurns 0 when all literals are defined*/
}


void checkmodel(){
  for (int i = 0; i < numClauses; ++i){
    bool someTrue = false;
    for (int j = 0; not someTrue and j < clauses[i].size(); ++j)
      someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
    if (not someTrue) {
      cout << "Error in model, clause is not satisfied:";
      for (int j = 0; j < clauses[i].size(); ++j) cout << clauses[i][j] << " ";
      exit(1);
    }
  }  
}

int main(){ 
  readClauses(); // reads numVars, numClauses and clauses
  model.resize(numVars+1,UNDEF);
  indexOfNextLitToPropagate = 0;  
  decisionLevel = 0;
  
  // DPLL algorithm

  clock_t start = clock();

  while (true) {
    while ( propagateGivesConflict() ) {
      if ( decisionLevel == 0) { cout << "UNSATISFIABLE" << endl; debug(start); return 10; }
      backtrack();
    }
    int decisionLit = getNextDecisionLiteral();
    if (decisionLit == 0) { checkmodel(); cout << "SATISFIABLE " << endl; debug(start); return 20; }
    // start new decision level:
    modelStack.push_back(0);  // push mark indicating new DL
    ++indexOfNextLitToPropagate;
    ++decisionLevel;
    setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
  }
}  
