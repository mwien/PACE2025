#include <vector>
#include <cstdint>
#include <cassert>
#include <algorithm>
#include <random>

#include "probleminstance.hpp"
#include "utility.hpp"
#include "global.hpp"
#include "touchedlist.hpp"

using namespace std;
namespace maxPreprocessor{


int ProblemInstance::labelPolarity(int var, int objective) const {
	return ((isLabel[var]>>objective)&1) | ((isLabel[var]>>(objective+15))&2);
}

int ProblemInstance::slabelPolarity(int var) const {
	if ((isLabel[var]&65535) && !((isLabel[var]>>16)&65535)) {
		return VAR_TRUE;
	} else if (!(isLabel[var]&65535) && ((isLabel[var]>>16)&65535)) {
		return VAR_FALSE;
	}
	return 0;
}

int ProblemInstance::labelIndexMask(int var) const {
	return (isLabel[var]&65535) | ((isLabel[var]>>16)&65535);
}

bool ProblemInstance::isLabelVar(int var) const {
	return isLabel[var];
}

bool ProblemInstance::isLabelVar(int var, int objective) const {
	return isLabel[var] & (65537<<objective);
}

void ProblemInstance::unLabel(int lbl) {
	isLabel[lbl] = 0;
}

void ProblemInstance::unLabelPolarity(int lbl, int polarity) {
	if (polarity == VAR_TRUE) {
		isLabel[lbl] &= ~(65535);
	} else {
		isLabel[lbl] &= 65535;
	}
}

void ProblemInstance::unLabel(int lbl, int objective) {
	isLabel[lbl] &= ~(65537<<objective);
}

void ProblemInstance::mkLabel(int lbl, int objective, int polarity) {
	unLabel(lbl, objective);
	if (polarity == VAR_TRUE) {
		isLabel[lbl] |= (1<<objective);
	} else {
		isLabel[lbl] |= (65536<<objective);
	}
}

void ProblemInstance::updateLabelMask(int lbl) {
	unLabel(lbl);
	if (litClauses[negLit(lbl)].size() && !clauses[litClauses[negLit(lbl)][0]].isHard()) {
		int cl = litClauses[negLit(lbl)][0];
		for (unsigned i=0; i<clauses[cl].weights.size(); ++i) {
			if (clauses[cl].weights[i]) {
				isLabel[lbl] |= (65536<<i);
			}
		}
	}
	if (litClauses[posLit(lbl)].size() && !clauses[litClauses[posLit(lbl)][0]].isHard()) {
		int cl = litClauses[posLit(lbl)][0];
		for (unsigned i=0; i<clauses[cl].weights.size(); ++i) {
			if (clauses[cl].weights[i]) {
				isLabel[lbl] |= (1<<i);
			}
		}
	}
	// assert labeling is valid: unique polarity for each objective
	assert( (isLabel[lbl] ^ (isLabel[lbl]>>16)) ==  (isLabel[lbl] | (isLabel[lbl]>>16)));
}

bool ProblemInstance::isClauseRemoved(int clause) const {
	return removedClauses[clause];
}

bool ProblemInstance::isVarRemoved(int var) const {
	if (litClauses[negLit(var)].size() + litClauses[posLit(var)].size() > 0) return false;
	return true;
}


bool ProblemInstance::isLitLabel(int lit) const {
	if (litValue(lit) == VAR_TRUE) {
		return isLabel[litVariable(lit)]&65535;
	} else {
		return isLabel[litVariable(lit)]&(65535<<16);
	}
}

bool ProblemInstance::isLitLabel(int lit, int objective) const {
	if (litValue(lit) == VAR_TRUE) {
		return isLabel[litVariable(lit)]&(1<<objective);
	} else {
		return isLabel[litVariable(lit)]&(65536<<objective);
	}
}

int ProblemInstance::labelObjectives(int var) const {
	return __builtin_popcount(isLabel[var]);
}

int ProblemInstance::labelObjective(int var) const {
	const int m = labelIndexMask(var);
	if (m==1) return 0;
	if (m==2) return 1;
	for (int i=2; i<objectives; ++i) if (m==(1<<i)) return i;
	return -1;
}

bool ProblemInstance::isLabelClause(int clauseId) const {
	if (clauses[clauseId].isHard()) return false;
	if (clauses[clauseId].lit.size() != 1) return false;
	if (!isLitLabel(clauses[clauseId].lit[0])) return false;
	assert(litClauses[clauses[clauseId].lit[0]][0] == clauseId);
	return true;
}

uint64_t ProblemInstance::labelWeight(int lbl, int objective) const {
	if (isLabel[lbl] & (1<<objective) ) {
// 		assert(litClauses[posLit(lbl)].size() == 1);
		return clauses[litClauses[posLit(lbl)][0]].weights[objective];
	}
	else if(isLabel[lbl] & (65536<<objective)) {
// 		assert(litClauses[negLit(lbl)].size() == 1);
		return clauses[litClauses[negLit(lbl)][0]].weights[objective];
	}
	else {
		assert(0);
	}
}

const std::vector<uint64_t>& ProblemInstance::labelLitWeights(int lbl) const {
	assert(litClauses[lbl].size());
	assert(clauses[litClauses[lbl][0]].isHard() == false);
	return clauses[litClauses[lbl][0]].weights;
}


bool ProblemInstance::wDominates(const std::vector<uint64_t>& w1, const std::vector<uint64_t>& w2) const {
	for (unsigned i=0; i<w2.size(); ++i) {
		uint64_t a = (i<w1.size() ? w1[i] : 0);
		uint64_t b = w2[i];
		if (b > a) return false;
	}
	return true;
}

bool ProblemInstance::wEqual(const std::vector<uint64_t>& w1, const std::vector<uint64_t>& w2) const {
	for (unsigned i=0, k = max(w1.size(), w2.size()); i<k; ++i) {
		uint64_t a = (i<w1.size() ? w1[i] : 0);
		uint64_t b = (i<w2.size() ? w2[i] : 0);
		if (b != a) return false;
	}
	return true;
}

void ProblemInstance::init(uint64_t topWeight) {
	int maxVar = 0;
	for (unsigned i = 0; i < clauses.size(); i++) {
		for (int lit : clauses[i].lit) {
			maxVar = max(maxVar, abs(lit) - 1);
		}
	}


	for (unsigned i = 0; i < clauses.size(); i++) {
		for (int& lit : clauses[i].lit) {
			lit=litFromDimacs(lit);
		}

		for (unsigned j = 0; j < clauses[i].weights.size(); ++j){
			if (clauses[i].weights[j] >= topWeight) {
				clauses[i].makeHard();
				break;
			}
		}

		sort(clauses[i].lit.begin(), clauses[i].lit.end());
		clauses[i].lit.erase(unique(clauses[i].lit.begin(), clauses[i].lit.end()), clauses[i].lit.end());
		clauses[i].updateHash();
	}

	vars = maxVar + 1;

	isLabel.resize(vars);
	litClauses.resize(vars*2);
	removedClauses.resize(clauses.size());

	tl.init(vars);

	for (unsigned i = 0; i < clauses.size(); i++) {
		populateLitClauses(i);
	}
}

ProblemInstance::ProblemInstance(const vector<vector<int> >& clauses_, const vector<uint64_t> & weights_, uint64_t topWeight) : tl(*this) {
	assert(clauses_.size() == weights_.size());
	objectives = 1;

	clauses.reserve(clauses_.size());
	for (unsigned i = 0; i < clauses_.size(); i++) {
		if (weights_[i]>=topWeight) {
			clauses.emplace_back(Clause(clauses_[i], {}));
		} else {
			clauses.emplace_back(Clause(clauses_[i], {weights_[i]}));
		}
	}
	init(topWeight);
}

ProblemInstance::ProblemInstance(const vector<vector<int> >& clauses_, const vector<pair<uint64_t, uint64_t> > & weights_, uint64_t topWeight) : tl(*this) {
	assert(clauses_.size() == weights_.size());
	objectives = 2;

	clauses.reserve(clauses_.size());
	for (unsigned i = 0; i < clauses_.size(); i++) {
		if (weights_[i].first>=topWeight || weights_[i].second>=topWeight) {
			clauses.emplace_back(Clause(clauses_[i], {}));
		} else {
			clauses.emplace_back(Clause(clauses_[i], {weights_[i].first, weights_[i].second}));
		}
	}
	init(topWeight);
}

ProblemInstance::ProblemInstance(const vector<vector<int> >& clauses_, const vector<vector<uint64_t> > & weights_, uint64_t topWeight) : tl(*this) {
	assert(clauses_.size() == weights_.size());
	objectives = 0;

	clauses.reserve(clauses_.size());
	for (unsigned i = 0; i < clauses_.size(); i++) {
		assert(weights_[i].size() <= 16); // AT MOST 16 OBJECTIVES
		objectives = max(objectives, (int)weights_[i].size());
		clauses.emplace_back(Clause(clauses_[i], weights_[i]));
	}
	init(topWeight);
}

void ProblemInstance::populateLitClauses(int clause) {
	for (int lit : clauses[clause].lit) {
		litClauses[lit].push_back(clause);
	}
}

void ProblemInstance::removeClauseFromLitClause(int clause, int lit) {
	for (unsigned i = 0; i < litClauses[lit].size(); i++) {
		if (litClauses[lit][i] == clause) {
			litClauses[lit][i] = litClauses[lit][litClauses[lit].size() - 1];
			litClauses[lit].pop_back();
			break;
		}
	}
}

void ProblemInstance::pourAllWeight(int clauseFrom, int clauseTo) {
	if (clauses[clauseFrom].weights.size()>clauses[clauseTo].weights.size()) clauses[clauseTo].weights.resize(clauses[clauseFrom].weights.size());

	for (unsigned i=0; i<clauses[clauseFrom].weights.size(); ++i) {
		clauses[clauseTo].weights[i] += clauses[clauseFrom].weights[i];
		clauses[clauseFrom].weights[i]=0;
	}
}

std::vector<uint64_t> ProblemInstance::substractWeights(int clause1, int clause2) {
	unsigned k = min(clauses[clause1].weights.size(), clauses[clause2].weights.size());
	std::vector<uint64_t> res(k);
	for (unsigned i=0; i<k; ++i) {
		res[i] = min(clauses[clause1].weights[i], clauses[clause2].weights[i]);
		if (res[i]) {
			clauses[clause1].weights[i] -= res[i];
			clauses[clause2].weights[i] -= res[i];
		}
	}
	return res;
}

void ProblemInstance::removeClauseFromLitClauses(int clause) {
	for (int lit : clauses[clause].lit) {
		removeClauseFromLitClause(clause, lit);
	}
}

void ProblemInstance::removeClause(int clause) {
	assert(removedClauses[clause] == false);

	tl.touchClause(clause);

	removedClauses[clause] = true;
	removeClauseFromLitClauses(clause);
}

// Literals in clause should be in sorted order
void ProblemInstance::addClause(const vector<int>& clause, const std::vector<uint64_t>& weight) {
	clauses.push_back(Clause(clause, weight));
	int cId = clauses.size() - 1;
	populateLitClauses(cId);

	removedClauses.push_back(0);

	tl.modClause(cId);
}

// Returns the index of added variable
int ProblemInstance::addVar() {
	litClauses.push_back(vector<int>());
	litClauses.push_back(vector<int>());
	isLabel.push_back(0);
	tl.addVar();
	return vars++;
}

void ProblemInstance::addLiteralToClause(int lit, int clause, bool touch) {
	// Dont add if it already exists
	for (int l : clauses[clause].lit) {
		if (l == lit) return;
		// Tautology -> runtime error
		assert(l != litNegation(lit));
	}
	if (touch) tl.modClause(clause);
	clauses[clause].addLiteral(lit);
	litClauses[lit].push_back(clause);
}

// The clause must be hard
void ProblemInstance::removeLiteralFromClause(int lit, int clause, bool touch) {
	if (touch) {
		tl.modClause(clause);
		tl.touchLiteral(lit);
	}
	clauses[clause].removeLiteral(lit);
	removeClauseFromLitClause(clause, lit);
}

void ProblemInstance::replaceLiteralInClause(int lit1, int lit2, int clause, bool touch) {
	if (touch) {
		tl.modClause(clause);
		tl.touchLiteral(lit1);
		//tl.touchLiteral(lit2); TODO: touch lit2 or not?
	}
	clauses[clause].replaceLiteral(lit1, lit2);
	removeClauseFromLitClause(clause, lit1);
	litClauses[lit2].push_back(clause);
}

bool ProblemInstance::canSubsume2(uint64_t h1, uint64_t h2) {
	uint64_t un = h1 | h2;
	return un == h1 || un == h2;
}

bool ProblemInstance::canSubsume1(int clause1, int clause2) {
	uint64_t un = clauses[clause1].hash | clauses[clause2].hash;
	return un == clauses[clause1].hash || un == clauses[clause2].hash;
}

bool ProblemInstance::canSubsume(int clause1, int clause2) {
	if ((clauses[clause1].hash | clauses[clause2].hash) == clauses[clause2].hash) return true;
	return false;
}

int ProblemInstance::getExcessVar() {
	if (excessVar == 0) excessVar = addVar();
	return excessVar;
}

uint64_t ProblemInstance::getWeightSum(int objective) {
	uint64_t weightSum = 0;
	for (int c = 0; c < (int)clauses.size(); c++) {
		if (!clauses[c].isHard() && !isClauseRemoved(c)) {
			weightSum += clauses[c].weight(objective);
		}
	}
	return weightSum;
}

std::vector<uint64_t> ProblemInstance::getWeightSums() {
	std::vector<uint64_t> weightSums(objectives);
	for (unsigned c = 0, k = clauses.size(); c < k; ++c) {
		if (clauses[c].isHard() || isClauseRemoved(c)) continue;
		for (unsigned objective = 0, kk = clauses[c].weights.size(); objective < kk; ++objective) {
			weightSums[objective] += clauses[c].weights[objective];
		}
	}
	return weightSums;
}

void ProblemInstance::printClauses(std::ostream& out) {
	for (int i=0; i<(int)clauses.size(); ++i) {
		out << "clause #" << i << ": ";
		if (isClauseRemoved(i)) {
			out << "[removed]\n";
			continue;
		}
		out << "( ";
		for (int l : clauses[i].lit) out << litToDimacs(l) << " ";
		out << ") ";
		if (clauses[i].isHard()) {
			out << "[HARD]\n";
		} else {
			out << "weight: ";
			for (int o=0; o<objectives; ++o) out << clauses[i].weight(o) << " ";
			out << "\n";
		}
	}
}

}
