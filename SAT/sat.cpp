#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
#include <queue>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

struct info{
    int lit;
    float score;
};

int propagations;
int pickVar;

queue<int> conflictClause;

uint numVars;
uint numClauses;
vector<vector<int> > clauses;
vector<vector<int> > negative;
vector<vector<int> > positive;
vector<info> decision;
vector<int> model;
vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;

bool inc(info a, info b) {return a.score > b.score;}

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

  pickVar = 0;
  propagations = 0;

  //UP
  positive.resize(numVars);
  negative.resize(numVars);

  //HE
  decision.resize(numVars);
  for (int k = 0; k < numVars; ++k) {
      decision[k].lit = k+1;
      decision[k].score = 0.0f;
  }

  // Read clauses
  for (uint i = 0; i < numClauses; ++i) {
    int lit;
    while (cin >> lit and lit != 0) {
        clauses[i].push_back(lit);
    	//UP
    	if (lit>0) positive[lit-1].push_back(i);
    	else negative[abs(lit)-1].push_back(i);
    	//HE
    	decision[abs(lit)-1].score += 1.0f;
    }
  }
  sort(decision.begin(), decision.end(), inc);
}

inline void debug(clock_t start) {
    //for (int i = 0; i < numVars; ++i) cout << decision[i].lit << " lit, " << decision[i].score << " conf" << endl;
    double timeTaken = ((double)(clock() - start) / CLOCKS_PER_SEC);
    cout << "Decisions: " << pickVar << endl << "Propagations: " << propagations << endl << "Time: " << timeTaken << endl;
    cout << "Props/time: " << ((double) propagations) / timeTaken << endl;
}

inline void cut(int x) {
    for (int i = 0; i < numVars; ++i)
        //if (i != x) decision[i].score *= 0.95f;
        decision[i].score *= 1.0f/4.0f;
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
    ++indexOfNextLitToPropagate;
    ++propagations;
    for (uint i = 0; i < numClauses; ++i) {
      bool someLitTrue = false;
      int numUndefs = 0;
      int lastLitUndef = 0;
      for (uint k = 0; not someLitTrue and k < clauses[i].size(); ++k){
	int val = currentValueInModel(clauses[i][k]);
	if (val == TRUE) someLitTrue = true;
	else if (val == UNDEF){ ++numUndefs; lastLitUndef = clauses[i][k]; }
      }
      if (not someLitTrue and numUndefs == 0) {
          return true; // conflict! all lits false
      }
      else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);	
    }    
  }
  return false;
}

/* PROPAGATION
 * First look for clauses with the opposite polarity of the literal, then with the same polarity
 * This way we can find conflicts faster
 */

bool propagateGivesConflict2 ( ) {
	while ( indexOfNextLitToPropagate < modelStack.size() ) {
        int auxlit = modelStack[indexOfNextLitToPropagate];
        ++indexOfNextLitToPropagate;
        ++propagations;
        vector<int> auxclause1;
        vector<int> auxclause2;
        if (auxlit > 0) {
            auxclause1 = negative[auxlit-1];
            auxclause2 = positive[auxlit-1];
        }
        else {
            auxclause1 = positive[abs(auxlit)-1];
            auxclause2 = negative[abs(auxlit)-1];
        }
        for (uint i = 0; i < auxclause1.size(); ++i) {
            bool someLitTrue = false;
            int numUndefs = 0;
            int lastLitUndef = 0;
            for (uint j = 0; not someLitTrue and j < clauses[auxclause1[i]].size(); ++j){
                int val = currentValueInModel(clauses[auxclause1[i]][j]);
                if (val == TRUE) someLitTrue = true;
                else if (val == UNDEF){ ++numUndefs; lastLitUndef = clauses[auxclause1[i]][j]; }
            }
            if (not someLitTrue and numUndefs == 0) {
                //Berkmin
                conflictClause.push(auxclause1[i]);
                //VSIDS
                //decision[abs(auxlit)-1].score += 1.0f;
                //cut(abs(auxlit)-1);
                return true; // conflict! all lits false
            }
            else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);
        }
        for (uint i = 0; i < auxclause2.size(); ++i) {
            bool someLitTrue = false;
            int numUndefs = 0;
            int lastLitUndef = 0;
            for (uint j = 0; not someLitTrue and j < clauses[auxclause2[i]].size(); ++j){
                int val = currentValueInModel(clauses[auxclause2[i]][j]);
                if (val == TRUE) someLitTrue = true;
                else if (val == UNDEF){ ++numUndefs; lastLitUndef = clauses[auxclause2[i]][j]; }
            }
            if (not someLitTrue and numUndefs == 0) {
                //Berkmin
                conflictClause.push(auxclause2[i]);
                //VSIDS
                //decision[abs(auxlit)-1].score += 1.0f;
                //cut(abs(auxlit)-1);
                return true; // conflict! all lits false
            }
            else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);
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
    ++pickVar;
  for (uint i = 1; i <= numVars; ++i) // stupid heuristic:
    if (model[i] == UNDEF) return i;  // returns first UNDEF var, positively
  return 0; // reurns 0 when all literals are defined*/
}

/* HEURISTIC: Berkmin SAT (Better VSIDS)
 * Keep a counter for every conflict that a variable has (score).
 * When a conflict appears, put the clause where it appears on top of a list.
 * Select the literal with the highest score from within that clause and pop the clause from the list.
 * Increment score of literal by 1 and multiply rest by 0.95 (this is to penalize older ones).
 * If there are no more clauses then simply chose the undefined literal with highest score.
 */

 int topClauseLit() {
 	while (not conflictClause.empty()) {
        int c = conflictClause.front();
		conflictClause.pop();
 		vector<info> aux(clauses[c].size());
 		for(uint i = 0; i < aux.size(); ++i) {
 			aux[i].lit = abs(clauses[c][i]);
 			aux[i].score = decision[abs(clauses[c][i])-1].score;
 		}
 		sort(aux.begin(),aux.end(),inc);
 		for (uint j = 0; j < aux.size(); ++j) {
        	if (model[aux[j].lit] == UNDEF) {
        		decision[abs(aux[j].lit)-1].score += 1.0f;
				cut(abs(aux[j].lit)-1);
            	return aux[j].lit;
        	}
    	}
	}
    //list has clauses with only defined literals
    sort(decision.begin(), decision.end(), inc);
    for (uint i = 0; i < numVars; ++i) {
       	if (model[decision[i].lit] == UNDEF) {
           	return decision[i].lit;
       	}
    }
    return 0;
 }

int getNextDecisionLiteral2(){
    ++pickVar;
    if (conflictClause.empty()) {
    	sort(decision.begin(), decision.end(), inc);
    	for (uint i = 0; i < numVars; ++i) {
        	if (model[decision[i].lit] == UNDEF) {
            	return decision[i].lit;
        	}
    	}
    	return 0;
	}
	else {
		return topClauseLit();
	}
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
  
  // Take care of initial unit clauses, if any
  for (uint i = 0; i < numClauses; ++i)
    if (clauses[i].size() == 1) {
      int lit = clauses[i][0];
      int val = currentValueInModel(lit);
      if (val == FALSE) {cout << "UNSATISFIABLE" << endl; return 10;}
      else if (val == UNDEF) setLiteralToTrue(lit);
    }
  
  // DPLL algorithm

  clock_t start = clock();

  while (true) {
    while ( propagateGivesConflict2() ) {
      if ( decisionLevel == 0) { cout << "UNSATISFIABLE" << endl; debug(start); return 10; }
      backtrack();
    }
    int decisionLit = getNextDecisionLiteral2();
    if (decisionLit == 0) { checkmodel(); cout << "SATISFIABLE " << endl; debug(start); return 20; }
    // start new decision level:
    modelStack.push_back(0);  // push mark indicating new DL
    ++indexOfNextLitToPropagate;
    ++decisionLevel;
    setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
  }
}  
