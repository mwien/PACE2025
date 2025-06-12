#include <vector>
#include <queue>
#include <algorithm>
#include <cassert>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <set>
#include <sstream>
#include <stack>


#include "preprocessor.hpp"
#include "trace.hpp"
#include "global.hpp"
#include "utility.hpp"
#include "timer.hpp"
#include "log.hpp"
#include "AMSLEX.hpp"
#include "satlikeinterface.hpp"

#define F first
#define S second

using namespace std;
namespace maxPreprocessor {

void Preprocessor::init() {
	originalVars = pi.vars;
	originalClauses = pi.clauses.size();
	BIGIt = 1;
	BVElocalGrow = 0;
	BVEglobalGrow = 0;

	redSatSolverCalls = 0;

	bestCost = HARDWEIGHT;

	doneUnhiding = false;
	randGen.seed(123);
	flePos = 0;
	fleActiveTechniques = 0;
	rLog.weightRange = pi.getWeightSums();
	rLog.initialWeightRange = rLog.weightRange;

	trace.setNbObjectives(pi.objectives);

	for (int i=0; i<pi.objectives; ++i) {
		stats["original_weight_sum"+std::to_string(i)]=rLog.weightRange[i];
	}
	stats["original_clauses"]=pi.clauses.size();
	stats["original_variables"]=pi.vars;
}

void Preprocessor::logProof(std::ostream& o, int debugLevel) {
	if (pi.objectives > 1) {
		cerr << "c proof logging not supported for multiobjective optimization\n";
		return;
	}
	plogDebugLevel = debugLevel;
	int pcl = 1;
	if (debugLevel>=3) pcl = 2;
	if (debugLevel>=5) pcl = 3;
	plog = new ProofLogger(o, pi.vars, pcl);
}

Preprocessor::Preprocessor(const vector<vector<int> >& clauses, const vector<vector<uint64_t> >& weights, uint64_t topWeight)
	: plog(nullptr), pi(clauses, weights, topWeight), satSolver(0), amsLex(pi) {
		init();
}
Preprocessor::Preprocessor(const vector<vector<int> >& clauses, const vector<uint64_t>& weights, uint64_t topWeight)
	: plog(nullptr), pi(clauses, weights, topWeight), satSolver(0), amsLex(pi) {
		init();
}
Preprocessor::Preprocessor(const vector<vector<int> >& clauses, const vector<pair<uint64_t, uint64_t> >& weights, uint64_t topWeight)
	: plog(nullptr), pi(clauses, weights, topWeight), satSolver(0), amsLex(pi) {
		init();
}


void Preprocessor::prepareSatSolver(ProofLogger* plog) {
	// For now use always glucose 3... and create it every time...
	if (satSolver) {
		delete satSolver;
	}
	satSolver = (SATSolver*) new Glucose3();
	satSolver->setProofLogger(plog);

	for (unsigned c = 0; c<pi.clauses.size(); ++c) {
		if (pi.isClauseRemoved(c)) continue;
		if (!pi.clauses[c].isHard()) continue;

		satSolver->addClause(pi.clauses[c].lit);
	}
}

void Preprocessor::plogLogState() {
	if (!plog) return;
	for (int i=0; i<(int)pi.clauses.size(); ++i) {
		if (pi.isClauseRemoved(i)) continue;
		plog->clause_check(i, pi.clauses[i].lit);
	}
	plog->log_current_objective();
}

bool Preprocessor::isTautology(const Clause& clause) const {
	for (unsigned i = 1; i < clause.lit.size(); i++) {
		if (litNegation(clause.lit[i]) == clause.lit[i - 1]) {
			return true;
		}
	}
	return false;
}

// Returns number of clauses removed
int Preprocessor::setVariable(int lit, int vid) {
	if (plog && plogDebugLevel>=1) plog->comment("setVariable(", lit, " [=", plog->gl(lit), "], ", vid, ")");
	int nlit = litNegation(lit);
	int var = litVariable(lit);

	if (plog && pi.isLabelVar(var)) {
		// when hardening label variables, update the objective function first
		if (pi.isLitLabel(lit)) {
			int c = pi.litClauses[lit][0];
			if (!plog->is_clause_deleted(c)) plog->soft_clause_satisfied(c);
		} else {
			int c = pi.litClauses[litNegation(lit)][0];
			if (!plog->is_clause_deleted(c)) plog->soft_clause_falsified(c);
		}
	}

	int removed = 0;
	trace.setVar(var, litValue(lit));
	vector<int>& satClauses = pi.litClauses[lit];
	vector<int>& notSatClauses = pi.litClauses[nlit];

	if (plog && vid==-1) {
		for (int c : satClauses) {
			if (!plog->is_clause_deleted(c) && pi.clauses[c].lit.size()==1 && pi.clauses[c].isHard()) {
				vid = plog->get_vid(c);
				break;
			}
		}
	}
	for (int c : notSatClauses) {
		pi.removeLiteralFromClause(nlit, c);
		if (plog && !plog->is_clause_deleted(c)) {
			if (vid == -1) plog->clause_updated(c, pi.clauses[c].lit);
			else           plog->unit_strengthen(c, vid);
		}
	}
	int lc = -1;
	for (int c : satClauses) {
		if (plog && !plog->is_clause_deleted(c)) {
			// removeDuplicateClauses may have logged removal of some clauses to the proof even if they still exists in maxpre database
			// thus the check plog->is_clause_deleted(c) here
			if (lc==-1 && pi.clauses[c].lit.size()==1 && pi.clauses[c].isHard()) lc = c;
			else plog->delete_red_clause(c);
		}
		pi.removeClause(c);
		removed++;
	}
	if (plog && lc!=-1) plog->delete_red_clause(lc, lit);
	if (plog && plogDebugLevel>=1) plog->comment("setVariable finished, ", removed, " satisfied clauses	 removed");
	return removed;
}

// This is called only in the beginning since no tautologies are added
void Preprocessor::removeTautologies() {
	if (plog && plogDebugLevel>=1) plog->comment("removeTautologies");
	int found = 0;

	for (unsigned i = 0; i < pi.clauses.size(); i++) {
		if (isTautology(pi.clauses[i])) {
			found++;
			pi.removeClause(i);
			if (plog) {
				if (pi.clauses[i].isHard()) plog->delete_red_clause(i);
				else                        plog->delete_red_clause(i);
			}
		}
	}

	log(found, " tautologies removed");
	if (plog && plogDebugLevel>=1) plog->comment("removeTautologies finished, ", found, " tautologies removed");
}

int Preprocessor::eliminateRedundantLabels() {
	if (plog && plogDebugLevel>=1) plog->comment("eliminateRedundantLabels");
	int fnd = 0;

	for (int objective=0; objective<pi.objectives; ++objective) {
		map<int64_t, map<int, vector<int> > > labels;
		vector<int> ls;
		for (int var = 0; var < pi.vars; var++) {
			if (pi.labelIndexMask(var) == (1<<objective)) {
				if (pi.labelPolarity(var, objective) == VAR_TRUE) {
					if (pi.litClauses[posLit(var)].size() == 1 && pi.litClauses[negLit(var)].size() == 1) {
						int c = pi.litClauses[negLit(var)][0];
						for (int lit : pi.clauses[c].lit) {
							labels[pi.labelWeight(var, objective)][lit].push_back(posLit(var));
						}
						ls.push_back(posLit(var));
					}
				}
				else {
					if (pi.litClauses[negLit(var)].size() == 1 && pi.litClauses[posLit(var)].size() == 1) {
						int c = pi.litClauses[posLit(var)][0];
						for (int lit : pi.clauses[c].lit) {
							labels[pi.labelWeight(var, objective)][lit].push_back(negLit(var));
						}
						ls.push_back(negLit(var));
					}
				}
			}
		}
		vector<int> matched(pi.vars);
		//priorize matching ternary clauses
		for (int lb : ls) {
			if (matched[litVariable(lb)]) continue;
			int c = pi.litClauses[litNegation(lb)][0];
			if (pi.clauses[c].lit.size() != 3) continue;
			vector<int> lits;
			for (int lit : pi.clauses[c].lit) {
				if (!pi.isLabelVar(litVariable(lit))) lits.push_back(litNegation(lit));
			}
			if (lits.size() != 2) continue;
			int tl = lits[0];
			if (pi.litClauses[lits[1]].size() < pi.litClauses[tl].size()) tl = lits[1];
			for (int c2 : pi.litClauses[tl]) {
				if (pi.clauses[c2].lit.size() != 3) continue;
				int lb2 = -1;
				vector<int> lits2;
				for (int lit : pi.clauses[c2].lit) {
					if (!pi.isLabelVar(litVariable(lit))) lits2.push_back(lit);
					else if (pi.labelIndexMask(litVariable(lit)) != (1<<objective)) break;
					else lb2 = litNegation(lit);
				}
				if (lits2.size() != 2) continue;
				if (lb2 == -1) continue;
				if (lb2 == lb) continue;
				if (pi.labelWeight(litVariable(lb), objective) != pi.labelWeight(litVariable(lb2), objective)) continue;
				if (matched[litVariable(lb2)]) continue;
				if (pi.litClauses[litNegation(lb2)].size() > 1) continue;
				if (pi.litClauses[lb2].size() > 1) continue;
				if ((lits[0] == lits2[0] && lits[1] == lits2[1]) || (lits[1] == lits2[0] && lits[0] == lits2[1])) {
					fnd++;
					matched[litVariable(lb)] = 1;
					matched[litVariable(lb2)] = 1;
					pi.removeLiteralFromClause(litNegation(lb), c);
					pi.addLiteralToClause(litNegation(lb2), c);
					if (plog) plog->labels_matched(pi.clauses[c].lit, pi.clauses[c2].lit, c, c2, pi.litClauses[lb][0], pi.litClauses[lb2][0], litNegation(lits2[0]));
					pi.removeClause(pi.litClauses[lb][0]);
					assert(pi.isVarRemoved(litVariable(lb)));
					trace.labelEliminate(lb2, lb, litNegation(lits2[0]));
					trace.setVar(litVariable(lb), litValue(lb));
					pi.unLabel(litVariable(lb), objective);
					break;
				}
			}
		}
		//match greedily
		for (unsigned i = 0; i < ls.size(); i++) {
			if (matched[litVariable(ls[i])]) continue;
			int c1 = pi.litClauses[litNegation(ls[i])][0];
			for (int lit : pi.clauses[c1].lit) {
				if (lit == litNegation(ls[i])) continue;
				for (int l2 : labels[pi.labelWeight(litVariable(ls[i]), objective)][litNegation(lit)]) {
					if (matched[litVariable(l2)]) continue;
					int c2 = pi.litClauses[litNegation(l2)][0];
					bool taut = false;
					int tautli = 0;
					unsigned j2 = 0;
					for (unsigned j = 0; j < pi.clauses[c1].lit.size(); j++) {
						while (j2 < pi.clauses[c2].lit.size() && pi.clauses[c2].lit[j2] < pi.clauses[c1].lit[j]) {
							if (pi.clauses[c2].lit[j2] == litNegation(pi.clauses[c1].lit[j])) {
								tautli = pi.clauses[c2].lit[j2];
								taut = true;
							}
							j2++;
						}
						if (j2 < pi.clauses[c2].lit.size() && pi.clauses[c2].lit[j2] == litNegation(pi.clauses[c1].lit[j])) {
							tautli = pi.clauses[c2].lit[j2];
							taut = true;
						}
						if (taut) break;
					}
					assert(taut == true);
					fnd++;
					matched[litVariable(ls[i])] = 1;
					matched[litVariable(l2)] = 1;
					pi.removeLiteralFromClause(litNegation(l2), c2);
					pi.addLiteralToClause(litNegation(ls[i]), c2);
					if (plog) plog->labels_matched(pi.clauses[c2].lit, pi.clauses[c1].lit, c2, c1, pi.litClauses[l2][0], pi.litClauses[ls[i]][0], tautli);
					pi.removeClause(pi.litClauses[l2][0]);
					assert(pi.isVarRemoved(litVariable(l2)));
					trace.labelEliminate(ls[i], l2, tautli);
					trace.setVar(litVariable(l2), litValue(l2));
					pi.unLabel(litVariable(l2), objective);
					break;
				}
				if (matched[litVariable(ls[i])]) break;
			}
		}
	}
	if (plog && plogDebugLevel>=1) plog->comment("eliminateRedundantLabels finished ", fnd, " redundant labels removed");
	return fnd;
}

// This is called only in the beginning
void Preprocessor::identifyLabels() {
	if (plog && plogDebugLevel>=1) plog->comment("start identifyLabels");
	int found = 0;
	int eliminated = 0;

	for (int lit = 0; lit < pi.vars*2; lit++) {
		bool f = false;
		vector<int> toRemove;
		for (unsigned i=0; i<pi.litClauses[lit].size(); ++i) {
			int c=pi.litClauses[lit][i];
			if (!pi.clauses[c].isHard() && pi.clauses[c].lit.size() == 1) {
				if (!f) {
					f = true;
					swap(pi.litClauses[lit][i], pi.litClauses[lit][0]);
				} else {
					pi.pourAllWeight(c, pi.litClauses[lit][0]);
					toRemove.push_back(c);
					if (plog) plog->substitute_soft_clause(c, pi.litClauses[lit][0]);
				}
			}
		}
		if (!f) continue;
		// check unit negations...
		f = false;
		for (int c : pi.litClauses[litNegation(lit)]) {
			if (!pi.clauses[c].isHard() && pi.clauses[c].lit.size() == 1) {
				trace.removeWeight(pi.substractWeights(c, pi.litClauses[lit][0]));

				if (plog) plog->contradictory_soft_clauses(c, pi.litClauses[lit][0], lit);

				if (pi.clauses[c].isWeightless()) {
					toRemove.push_back(c);
				}

				if (pi.clauses[pi.litClauses[lit][0]].isWeightless()) {
					toRemove.push_back(pi.litClauses[lit][0]);
					f = true;
					break;
				}
			}
		}

		eliminated += toRemove.size();
		for (int c : toRemove) {
			pi.removeClause(c);
		}
		if (f) continue;

		if (litValue(lit) == true) {
			for (int objective=0; objective<pi.objectives; ++objective) {
				if (pi.clauses[pi.litClauses[lit][0]].weight(objective)) {
					pi.mkLabel(litVariable(lit), objective, VAR_TRUE);
					if (plog) plog->make_objective_variable(lit, pi.litClauses[lit][0]);
				}
			}
		} else {
			for (int objective=0; objective<pi.objectives; ++objective) {
				if (pi.clauses[pi.litClauses[lit][0]].weight(objective)) {
					pi.mkLabel(litVariable(lit), objective, VAR_FALSE);
					if (plog) plog->make_objective_variable(lit, pi.litClauses[lit][0]);
				}
			}
		}
		found++;
	}

	log(found, " labels identified");
	log(eliminated, " soft unit clauses eliminated");
	if (plog && plogDebugLevel>=1) plog->comment("identifyLabels finished ", found, " labels identified, ", eliminated, " soft unit clauses eliminated");
}

// This is called only in the beginning
void Preprocessor::createLabels() {
	if (plog && plogDebugLevel>=1) plog->comment("start createLabels");
	int added = 0;

	// Create labels for every soft clause that does not have a label yet
	for (unsigned i = 0; i < pi.clauses.size(); i++) {
		if (!pi.clauses[i].isHard() && !pi.isClauseRemoved(i) && !pi.isLabelClause(i)) {
			int nv = pi.addVar();
			if (plog) plog->set_blocking_lit(i, posLit(nv), pi.clauses.size());
			pi.addLiteralToClause(negLit(nv), i);
			pi.addClause({posLit(nv)}, pi.clauses[i].weights);
			for (int objective=0; objective<pi.objectives; ++objective) {
				if (pi.clauses[i].weight(objective))
					pi.mkLabel(nv, objective, VAR_TRUE);
			}
			pi.clauses[i].makeHard();
			added++;
		}
	}

	log(added, " labels added");
	if (plog && plogDebugLevel>=1) plog->comment("createLabels finished, ", added, " labels added");
}

int Preprocessor::removeEmptyClauses() {
	if (plog && plogDebugLevel>=1) plog->comment("start removeEmptyClauses");
	int removed = 0;
	vector<int> src;
	for (unsigned i = 0; i < pi.clauses.size(); i++) {
		if (!pi.isClauseRemoved(i)) {
			if (pi.clauses[i].lit.size() == 0) {
				if (pi.clauses[i].isHard()) {
					// UNSAT
					src.clear();
					for (unsigned j = 0; j < pi.clauses.size(); ++j) {
						if (i==j || pi.isClauseRemoved(j)) continue;
						if (pi.clauses[j].lit.size() == 0 && !pi.clauses[j].isHard()) {
							// this is done here because of prooflogging;
							// weight removal is already logged in the proof, thus keep proof and prepro instance synced
							trace.removeWeight(pi.clauses[j].weights);
						}
						if (plog) plog->delete_red_clause(j);
						pi.removeClause(j);
						removed++;
					}
					break;
				}	else {
					src.push_back(i);
				}
			}
		}
	}
	for (int c : src) {
		if (plog && !pi.isLabelClause(c)) plog->delete_unsat_clause(c);
		trace.removeWeight(pi.clauses[c].weights);
		pi.removeClause(c);
		removed++;
	}
	log(removed, " empty clauses removed");
	if (plog && plogDebugLevel>=1) plog->comment("removeEmptyClauses finished, ", removed, " empty clauses removed");
	return removed;
}

int Preprocessor::tryUP(int lit) {
	for (int c : pi.litClauses[lit]) {
		if (pi.clauses[c].lit.size() == 1 && pi.clauses[c].isHard()) {
			if (pi.isLabelVar(litVariable(lit))) {
				rLog.removeLabel(1);
			}	else {
				rLog.removeVariable(1);
			}
			int rmClauses = setVariable(lit);
			rLog.removeClause(rmClauses);
			return rmClauses;
		}
	}
	return 0;
}

int Preprocessor::tryUPAll() {
	int removed = 0;
	for (unsigned c = 0; c < pi.clauses.size(); c++) {
		if (pi.clauses[c].lit.size() == 1 && pi.clauses[c].isHard() && !pi.isClauseRemoved(c)) {
			int lit = pi.clauses[c].lit[0];
			if (pi.isLabelVar(litVariable(lit))) {
				rLog.removeLabel(1);
			}	else {
				rLog.removeVariable(1);
			}
			int rmClauses = setVariable(lit);
			rLog.removeClause(rmClauses);
			removed += rmClauses;
			if (!rLog.requestTime(Log::Technique::UP)) break;
		}
	}
	return removed;
}

int Preprocessor::doUP() {
	rLog.startTechnique(Log::Technique::UP);
	int removed = 0;
	if (!rLog.requestTime(Log::Technique::UP)) {
		rLog.stopTechnique(Log::Technique::UP);
		return 0;
	}
	if (plog && plogDebugLevel>=1) plog->comment("start UP");
	vector<int> checkLit = pi.tl.getTouchedLiterals("UP");
	if ((int)checkLit.size() > pi.vars) {
		removed = tryUPAll();
	}
	else {
		for (int lit : checkLit) {
			if (!rLog.requestTime(Log::Technique::UP)) break;
			removed += tryUP(lit);
		}
	}

	log(removed, " clauses removed by UP");
	rLog.stopTechnique(Log::Technique::UP);

	if (plog && plogDebugLevel>=1) {
		plog->comment("UP finished, ", removed, " clauses removed");
		if (plogDebugLevel>=4) plogLogState();
	}

	return removed;
}

void Preprocessor::doUP2() {
	rLog.startTechnique(Log::Technique::UP);
	for (int lit = 0; lit < 2*pi.vars; lit++) {
		assert(tryUP(lit) == 0);
	}
	rLog.stopTechnique(Log::Technique::UP);
}

int Preprocessor::removeDuplicateClauses(vector<pair<uint64_t, int> >& has) {
	int removed = 0;
	sort(has.begin(), has.end());
	bool hard = false;
	vector<int> toRemove;
	for (unsigned i = 1; i < has.size(); i++) {
		if (has[i].F != has[i - 1].F) {
			hard = false;
			continue;
		}
		if (pi.clauses[has[i].S].lit != pi.clauses[has[i - 1].S].lit) {
			hard = false;
			continue;
		}

		if (hard || pi.clauses[has[i-1].S].isHard()) {
			hard = true;
			toRemove.push_back(has[i].S);
			if (plog && !pi.isLabelClause(has[i].S)) plog->delete_red_clause(has[i].S);
		} else if (pi.clauses[has[i].S].isHard()) {
			hard = true;
			toRemove.push_back(has[i-1].S);
			if (plog) plog->delete_red_clause(has[i-1].S);
		} else {
			pi.pourAllWeight(has[i-1].S, has[i].S);
			toRemove.push_back(has[i-1].S);
			if (plog) plog->substitute_soft_clause(has[i-1].S, has[i].S);
		}
	}
	for (int c : toRemove) assert(!pi.isClauseRemoved(c));
	for (int c : toRemove) {
		if (pi.isLabelClause(c)) { // since after labelling there are no duplicate softs, this implies we have a unit hard clause and we can harden it
			removed += setVariable(pi.clauses[c].lit[0]);
		} else if (!pi.isClauseRemoved(c)) { // hardening can remove some clauses marked as to remove...
			removed++;
			pi.removeClause(c);
		}
	}
	return removed;
}

int Preprocessor::removeDuplicateClauses() {
	if (plog && plogDebugLevel>=1) plog->comment("removeDuplicateClauses");
	int removed = 0;
	vector<int> checkLit = pi.tl.getModLiterals("DPCLRM");
	vector<pair<uint64_t, int> > has;
	if ((int)checkLit.size() > pi.vars/2) { // magic constant
		for (int c = 0; c < (int)pi.clauses.size(); c++) {
			if (!pi.isClauseRemoved(c)) {
				if (pi.clauses[c].lit.size() == 0) {
					if (!pi.clauses[c].isHard()) {
						if (plog) plog->delete_unsat_clause(c);
						trace.removeWeight(pi.clauses[c].weights);
						pi.removeClause(c);
					}
				}
				else {
					uint64_t h = 0;
					for (int l : pi.clauses[c].lit) {
						h *= polyHashMul;
						h += (uint64_t)(l + 1);
					}
					has.push_back({h, c});
				}
			}
		}
		removed+=removeDuplicateClauses(has);
	}
	else {
		for (int lit : checkLit) {
			has.clear();
			for (int c : pi.litClauses[lit]) {
				uint64_t h = 0;
				for (int l : pi.clauses[c].lit) {
					h *= polyHashMul;
					h += (uint64_t)(l + 1);
				}
				has.push_back({h, c});
			}
			sort(has.begin(), has.end());
			removed+=removeDuplicateClauses(has);
		}
	}
	if (plog && plogDebugLevel>=1) plog->comment("removeDuplicateClauses finished, ", removed, " duplicate clauses removed");
	return removed;
}

#include "modelsearch.cpp"

#include "SE.cpp"
#include "BVE.cpp"
#include "SSR.cpp"
#include "BCE.cpp"
#include "SLE.cpp"
#include "BCR.cpp"
#include "SIE.cpp"
#include "BIG.cpp"
#include "BVA.cpp"
#include "GSLE.cpp"
#include "FLP.cpp"
#include "LS.cpp"
#include "AM1.cpp"
#include "TMS.cpp"
#include "RED.cpp"
#include "HARD.cpp"
#include "FLE.cpp"

PreprocessedInstance Preprocessor::getPreprocessedInstance(bool addRemovedWeight, bool sortLabelsFrequency) {
	PreprocessedInstance ret;


	for (unsigned i = 0; i < pi.clauses.size(); i++) {
		if (!pi.isClauseRemoved(i) && pi.clauses[i].isHard()) {
			ret.clauses.push_back(pi.clauses[i].lit);
			if (pi.objectives>1) ret.weightsv.push_back({});
			else                 ret.weights.push_back(HARDWEIGHT);
			ret.clause_cids.push_back(i);
		}
	}
	for (int var = 0; var < pi.vars; var++) {
		if (pi.litClauses[posLit(var)].size() > 0 || pi.litClauses[negLit(var)].size() > 0) {
			if (pi.litClauses[negLit(var)].size() == 0) {
				trace.setVar(var, true);
				if (plog && (pi.isLitLabel(posLit(var)))) plog->delete_red_clause(pi.litClauses[posLit(var)][0], posLit(var));
			} else if (pi.litClauses[posLit(var)].size() == 0) {
				trace.setVar(var, false);
				if (plog && (pi.isLitLabel(negLit(var)))) plog->delete_red_clause(pi.litClauses[negLit(var)][0], negLit(var));
			} else {
				if (pi.isLitLabel(posLit(var))) {
					assert(pi.clauses[pi.litClauses[posLit(var)][0]].lit.size() == 1);
					assert(!pi.clauses[pi.litClauses[posLit(var)][0]].isHard());
					ret.labels.push_back({posLit(var), pi.clauses[pi.litClauses[posLit(var)][0]].weights});
				}
				if (pi.isLitLabel(negLit(var))) {
					assert(pi.clauses[pi.litClauses[negLit(var)][0]].lit.size() == 1);
					assert(!pi.clauses[pi.litClauses[negLit(var)][0]].isHard());
					ret.labels.push_back({negLit(var), pi.clauses[pi.litClauses[negLit(var)][0]].weights});
				}
			}
		}
	}
	bool hasRemovedWeight = 0;
	for (auto w : trace.removedWeight) if (w) hasRemovedWeight=1;

	if (addRemovedWeight && hasRemovedWeight) {
	 	int nVar = pi.getExcessVar();
	 	ret.labels.push_back({negLit(nVar), trace.removedWeight});
	 	ret.clauses.push_back({posLit(nVar)});
	 	if (pi.objectives>1) ret.weightsv.push_back({});
	 	else                 ret.weights.push_back(HARDWEIGHT);
		if (plog) {
			ret.clause_cids.push_back(pi.clauses.size());
			plog->map_clause(pi.clauses.size(), plog->add_red_clause_({posLit(nVar)}, posLit(nVar), 1), 1);
			plog->map_unit_soft(pi.clauses.size()+1, negLit(nVar));
			plog->obju_remove_constant(pi.clauses.size()+1);
		}
	}

	if (sortLabelsFrequency) {
		auto cmp = [&](const pair<int, vector<uint64_t> >& a, const pair<int, vector<uint64_t> >&	 b) {
			if (litVariable(a.F) >= pi.vars || litVariable(b.F) >= pi.vars) return a.F > b.F;
			return pi.litClauses[a.F].size() + pi.litClauses[litNegation(a.F)].size() > pi.litClauses[b.F].size() + pi.litClauses[litNegation(b.F)].size();
		};
		sort(ret.labels.begin(), ret.labels.end(), cmp);
	}
	for (int i = 0; i < (int)ret.labels.size(); i++) {
		ret.clauses.push_back({ret.labels[i].F});
		if (pi.objectives>1) ret.weightsv.push_back(ret.labels[i].S);
		else                 ret.weights.push_back(ret.labels[i].S[0]);
	}
	return ret;
}

bool Preprocessor::validTechniques(string techniques) const {
	int sb = 0;
	string vt = "buvsrilceagphtmGSQTVdDMLHURP";
	for (int i = 0; i < (int)techniques.size(); i++) {
		if(techniques[i] == '[') {
			sb++;
		}
		else if(techniques[i] == ']') {
			sb--;
			if (sb < 0) return false;
			if (techniques[i - 1] == '[') return false;
		}
		else {
			bool f = false;
			for (char c : vt) {
				if (techniques[i] == c) {
					f = true;
					break;
				}
			}
			if (!f) return false;
		}
	}
	if (sb != 0) return false;
	return true;
}

bool Preprocessor::validPreTechniques(string techniques) const {
	int sb = 0;
	string vt = "busU";
	for (int i = 0; i < (int)techniques.size(); i++) {
		if(techniques[i] == '[') {
			sb++;
		}
		else if(techniques[i] == ']') {
			sb--;
			if (sb < 0) return false;
			if (techniques[i - 1] == '[') return false;
		}
		else {
			bool f = false;
			for (char c : vt) {
				if (techniques[i] == c) {
					f = true;
					break;
				}
			}
			if (!f) return false;
		}
	}
	if (sb != 0) return false;
	return true;
}

//b = BCE, u = UP, v = BVE, s = SE, r = SSR, l = SLE, c = BCR, i = SIE, e = EE, a = BVA, g = GSLE, p = FLP, h = UH, t = structure labeling, m = AM1, T = TMS, d=LRED, D=CRED, H=HARD

int Preprocessor::doPreprocess(const string& techniques, int l, int r, bool debug, bool topLevel) {
	int found = 0;
	if (l == r) {
		char tc = techniques[l];
		if (tc == 'b') {
			while (int f = doBCE()) {
				found += f;
			}
			if (debug) doBCE2();
		}
		else if (tc == 'u') {
			while (int f = doUP()) {
				found += f;
			}
			if (debug) doUP2();
		}
		else if (tc == 'v') {
			while (int f = doBVE()) {
				found += f;
			}
			if (debug) doBVE2();
		}
		else if (tc == 's') {
			while (int f = doSE()) {
				found += f;
			}
			if (debug) doSE2();
		}
		else if (tc == 'r') {
			while (int f = doSSR()) {
				found += f;
			}
			if (debug) doSSR2();
		}
		else if (tc == 'l') {
			while (int f = doSLE()) {
				found += f;
			}
			if (debug) doSLE2();
		}
		else if (tc == 'c') {
			while (int f = doBCR()) {
				found += f;
			}
			if (debug) doBCR2();
		}
		else if (tc == 'i') {
			while (int f = doSIE()) {
				found += f;
			}
			if (debug) doSIE2();
		}
		else if (tc == 'e') {
			while (int f = doBIG(false)) {
				found += f;
			}
			if (debug) doBIG2(false);
		}
		else if (tc == 'a') {
			while (int f = doBVA()) {
				found += f;
			}
			if (debug) doBVA2();
		}
		else if (tc == 'g') {
			while (int f = doGSLE()) {
				found += f;
			}
			if (debug) doGSLE2();
		}
		else if (tc == 'p') {
			while (int f = doFLP()) {
				found += f;
			}
			// FLP already checks every label
		}
		else if (tc == 'h') {
			while (int f = doBIG(true)) {
				found += f;
			}
			if (debug) doBIG2(true);
		}
		else if (tc == 't') {
			found += doLS();
		}
		else if (tc == 'm') {
			found += doAM1(1, 0, 0);
		}
		else if (tc == 'G') {
			found += doAM1(1, 0, 1);
		}
		else if (tc == 'S') {
			found += doAM1(1, 1, 1);
		}
		else if (tc == 'Q') {
			while (int f = doAM1(1, 1, 1)) {
				found += f;
			}
		}
		else if (tc == 'T') {
			found += doTMS();
		}
		else if (tc == 'V') {
			while (int f=doBBTMS(opt.BBTMS_maxVars)) {
				found += f;
			}
		}
		else if (tc == 'd') {
			found += doLabelRED();
		}
		else if (tc == 'D') {
			found += doClauseRED();
		}
		else if (tc == 'M') {
			found += doModelCuttingRED();
		}
		else if (tc == 'L') {
			found += doUPLitRED();
		}
		else if (tc == 'H') {
			found += doHARD();
		}
		else if (tc == 'U') {
			found += doFLE(0,1,0,1,0,0);
		}
		else if (tc == 'R') {
			found += doFLE(1,1,1,1,1,opt.FLE_redTechniques);
		}
		else {
			abort();
		}
		pi.tl.shrink(logLevel > 0);
	}
	else {
		int lp = l;
		int br = 0;
		for (int i = l; i <= r; i++) {
			if (techniques[i] == '[') {
				br++;
			}
			else if(techniques[i] == ']') {
				br--;
				if (br == 0) {
					while (int f = doPreprocess(techniques, lp + 1, i - 1, debug, false)) {
						found += f;
					}
					if (topLevel) {
						for (int j = lp + 1; j <= i - 1; j++) {
							if (techniques[j] != ']' && techniques[j] != '[' && (techniques[j] < '0' || techniques[j] > '9')) {
								bool neverAgain = true;
								for (int jj = i + 1; jj <= r; jj++) {
									if (techniques[jj] == techniques[j]) {
										neverAgain = false;
									}
								}
								if (neverAgain) {
									rLog.neverAgain(techniques[j]);
								}
							}
						}
					}
					lp = i + 1;
				}
			}
			else {
				if (br == 0) {
					assert(lp == i);
					found += doPreprocess(techniques, i, i, debug, false);
					if (topLevel) {
						bool neverAgain = true;
						for (int j = i + 1; j <= r; j++) {
							if (techniques[j] == techniques[i]) {
								neverAgain = false;
							}
						}
						if (neverAgain) {
							rLog.neverAgain(techniques[i]);
						}
					}
					lp = i + 1;
				}
			}
		}
		assert(br == 0);
	}
	return found;
}

void Preprocessor::preprocess(string techniques, double timeLimit, bool debug, bool BVEgate_, bool initialCall, bool matchLabels) {
	opt.BVEgate = BVEgate_;
	Timer preTime;
	preTime.start();
	log(originalVars, " variables, ", originalClauses, " clauses");
	
	if (plog) {
		// set up prooflogging
		plog->begin_proof();
		int nbclauses = 0;
		for (int i=0; i<(int)pi.clauses.size(); ++i) {
			if (pi.clauses[i].isHard() || pi.clauses[i].lit.size()!=1) plog->map_clause(i, ++nbclauses, pi.clauses[i].isHard());
			else                                                       plog->map_unit_soft(i, pi.clauses[i].lit[0]);
			if (!pi.clauses[i].isHard())                               plog->set_soft_clause_weight(i, pi.clauses[i].weight(0));
		}
		plog->set_nb_clauses(nbclauses);
		// check that instance matches that of the verifier
		if (plogDebugLevel>=2) plogLogState();
	}


	print("c techniques ", techniques);
	log("techniques ", techniques);


	string preTechniques;
	for (unsigned i = 0; i < techniques.size(); i++) {
		if (techniques[i] == '#') {
			preTechniques = techniques.substr(0, i);
			techniques = techniques.substr(i + 1);
			break;
		}
	}

	if (!validTechniques(techniques) || !validPreTechniques(preTechniques)) {
		log("Invalid techniques");
		print("c Invalid techniques");
		if (plog) {
			plog->comment("Could not run preprocessor: Invalid techniques");
		}
		abort();
	}

	if (plog && plogDebugLevel>=1) plog->comment("start pre-preprocessing phase, preTechniques = '", preTechniques, "'");

	if (initialCall) {
		removeTautologies();
		pi.tl.init(pi.vars);
		removeEmptyClauses();
	}

	int dpRm = removeDuplicateClauses();
	log(dpRm, " duplicate clauses removed");

	if (initialCall) {
		if (preTechniques.size() > 0) {
			preTime.stop(); // be sure that these 3 lines will be ran exactly once
			rLog.timePlan(timeLimit - preTime.getTime().count()*2, techniques);
			rLog.startTimer();
			doPreprocess(preTechniques, 0, (int)preTechniques.size() - 1, debug, false);
			if (plog && plogDebugLevel>=1) {
				plog->comment("finished pre-preprocessing phase");
				if (plogDebugLevel>=4) plogLogState();
			}
		}
		if (plog && plogDebugLevel>=1) plog->comment("start labelling");

		removeEmptyClauses();
		identifyLabels();
		createLabels();

		if (matchLabels) {
			int labelsMatched = eliminateRedundantLabels();
			rLog.labelsMatched += labelsMatched;
			log(labelsMatched, " labels matched");
		}

		dpRm = removeDuplicateClauses();
		log(dpRm, " duplicate clauses removed");

		pi.tl.init(pi.vars);

		if (plog && plogDebugLevel>=1) {
			plog->comment("labelling finished");
			if (plogDebugLevel>=4) plogLogState();
		}
	}


	if (!initialCall || preTechniques.size() == 0) {
		preTime.stop();// here
		rLog.timePlan(timeLimit - preTime.getTime().count(), techniques);
		rLog.startTimer();
	}

	if (plog && plogDebugLevel>=1) plog->comment("start main preprocessing, techniques = '", techniques, "'");

	doPreprocess(techniques, 0, (int)techniques.size() - 1, debug, true);

	if (plog && plogDebugLevel>=1) plog->comment("main preprocessing finished");


	rLog.stopTimer();

	removeEmptyClauses();

	dpRm = removeDuplicateClauses();
	log(dpRm, " duplicate clauses removed");

	rLog.weightRange = pi.getWeightSums();

	int clauses=0;
	for (unsigned i=0; i<pi.clauses.size(); ++i) {
		if (!pi.isClauseRemoved(i)) ++clauses;
	}
	int vars=0;
	for (int i=0; i< pi.vars;++i) {
		if (!pi.isVarRemoved(i)) ++vars;
	}
	for (int i=0; i<pi.objectives; ++i) {
		stats["final_weight_sum"+std::to_string(i)]=rLog.weightRange[i];
	}
	stats["final_clauses"]=clauses;
	stats["final_variables"]=vars;

	if (plog && plogDebugLevel>=2) plogLogState();
}

std::string Preprocessor::version(int l) {
	std::stringstream vs;
	if (l&1) vs << "MaxPRE ";
	vs << "2.2.2 ";
	if (l&2) vs << " (" << GIT_IDENTIFIER << ", " << __DATE__ << " " << __TIME__ << ")";
	return vs.str();
}

}
