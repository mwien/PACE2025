#ifndef MAXPP_PROBLEMINSTANCE_HPP
#define MAXPP_PROBLEMINSTANCE_HPP

#include <vector>
#include <cstdint>

#include "clause.hpp"
#include "global.hpp"
#include "touchedlist.hpp"

namespace maxPreprocessor {
class ProblemInstance {
private:
	std::vector<int> isLabel; //
public:
	int objectives;

	// All clauses including removed. Clauses id is its index in this list and it never changes.
	std::vector<Clause> clauses;
	std::vector<std::vector<int> > litClauses;
	// Is clause i removed
	std::vector<int> removedClauses;


	int vars;
	int excessVar;

	TouchedList tl;
private:
	void init(uint64_t topWeight);
public:
	ProblemInstance(const std::vector<std::vector<int> >& clauses_, const std::vector<uint64_t>& weights_, uint64_t topWeight);
	ProblemInstance(const std::vector<std::vector<int> >& clauses_, const std::vector<std::pair<uint64_t, uint64_t> >& weights_, uint64_t topWeight);
	ProblemInstance(const std::vector<std::vector<int> >& clauses_, const std::vector<std::vector<uint64_t> >& weights_, uint64_t topWeight);

	int labelPolarity(int var, int objective) const; // 0 if not a label, VAR_FALSE if its negation is soft, VAR_TRUE otherwise
	int slabelPolarity(int var) const; // returns labels polarity, if label has same polarity for all objectives. returns 0 otherwise
	int labelIndexMask(int var) const; //returns 0 if not label, bitmask of objectives if label
	bool isLabelVar(int var) const; // returns true if var is used as a label, false if not
	bool isLabelVar(int var, int objective) const;
	bool isLitLabel(int lit) const; // returns true if var(lit) is label on polarity litPolarity(lit) for any objective
	bool isLitLabel(int lit, int objective) const; // returns true if var(lit) is label on polarity lit for given objective

	int labelObjectives(int var) const; // returns the number of objectives for which var is a label
	int labelObjective(int var) const;  // returns the objective for which var is a label, if it is a label only for one objective. returns -1 otherwise

	void unLabel(int lbl);
	void unLabelPolarity(int lbl, int polarity);
	void unLabel(int lbl, int objective);
	void mkLabel(int lbl, int objective, int polarity);
	void updateLabelMask(int lbl); // check weights on lbl clauses and update label information accordingly

	bool isClauseRemoved(int clauseId) const;
	bool isVarRemoved(int var) const;
	int litLabelIndexMask(int lit) const; // returns bitmask of objectives where var(lit) is a label pof polarity lit.
	bool isLabelClause(int clauseId) const;
	uint64_t labelWeight(int lbl, int objective) const;
	const std::vector<uint64_t>& labelLitWeights(int lbl) const; // NOTE! in this function parameter lbl is a literal, not variable!

	// functions to check if for each objective w1[objective]>=w2[objective] (wDominates)
	// and  w1[objective]==w2[objective] (wEqual)
	bool wDominates(const std::vector<uint64_t>& w1, const std::vector<uint64_t>& w2) const;
	bool wEqual(const std::vector<uint64_t>& w1, const std::vector<uint64_t>& w2) const;


	void populateLitClauses(int clauseId);

	void removeClauseFromLitClause(int clauseId, int lit);
	void removeClauseFromLitClauses(int clauseId);

	void removeClause(int clauseId);

	void pourAllWeight(int clauseFrom, int clauseTo);
	std::vector<uint64_t> substractWeights(int clause1, int clause2);

	// Literals in clause should be in sorted order
	void addClause(const std::vector<int>& clause, const std::vector<uint64_t>& weight = std::vector<uint64_t>());

	// Returns the index of added variable
	int addVar();

	void addLiteralToClause(int lit, int clause, bool touch = true);

	// The clause must be hard
	void removeLiteralFromClause(int lit, int clause, bool touch = true);

	// lit1 is replaced by lit2
	void replaceLiteralInClause(int lit1, int lit2, int clause, bool touch = true);

	bool canSubsume2(uint64_t h1, uint64_t h2);
	bool canSubsume1(int clause1, int clause2);
	bool canSubsume(int clause1, int clause2);

	int getExcessVar();
	uint64_t getWeightSum(int objective);
	std::vector<uint64_t> getWeightSums();

	// for debugging purposes
	void printClauses(std::ostream& out);
};
}
#endif
