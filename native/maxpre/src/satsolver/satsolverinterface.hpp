#include <vector>
#include "../prooflogger.h"

#ifndef SATSOLVERINTERFACE_HPP
#define SATSOLVERINTERFACE_HPP

using namespace std;

class SATSolver {
public:
	virtual void setProofLogger(maxPreprocessor::ProofLogger* plog) = 0;

	virtual void cleanLearntClausesFromProof() = 0;

	virtual void addClause(const vector<int>& clause) = 0;

	virtual void addClause(int lit) = 0;

	virtual void addClause(int lit1, int lit2) = 0;

	virtual void addClause(int lit1, int lit2, int lit3) = 0;

	virtual bool solve(vector<int>& assumptions) = 0; // returns true if SAT, false if UNSAT

	virtual int solveLimited(vector<int>& assumptions, int64_t maxPropagations, int64_t maxConflicts) = 0; // returns 0 if UNSAT, 1 if SAT, -1 if budget

	virtual int solveLimited(vector<int>& assumptions, double time) = 0; // estimated time seconds maximum time

	virtual int solveLimited(double time) {
		vector<int> a;
		return solveLimited(a, time);
	}

	virtual bool solve() = 0; // returns true if SAT, false if UNSAT

	virtual void getCore(vector<int>& retCore) = 0;

	virtual void getModel(vector<bool>& retModel) = 0;

	virtual bool propagate(vector<int>& assumptions, vector<int>& result, int phase_saving = 0) = 0; // does up from assumptions, result contains propagated literals, returns true if SAT, false if UNSAT

	virtual bool testUPConflict(vector<int>& assumptions, int phase_saving = 0) = 0; // returns true if SAT, false if UNSAT

	// statistics
	virtual int numberOfSATcalls() = 0;
	virtual int numberOfUNSATcalls() = 0;

	virtual ~SATSolver() {};
};


#endif
