#include <cstdint>
#include <vector>
#include <algorithm>
#include <cassert>

#include "preprocessor.hpp"
#include "preprocessedinstance.hpp"
#include "preprocessorinterface.hpp"
#include "global.hpp"
#include "utility.hpp"

#define F first
#define S second

using namespace std;
namespace maxPreprocessor {
	void PreprocessorInterface::init(const vector<vector<int> > & clauses) {
		variables = 0;
		originalVariables = 0;
		for (auto& clause : clauses) {
			for (int lit : clause) {
				assert(lit != 0);
				variables = max(variables, abs(lit));
			}
		}
		originalVariables = variables;
		preprocessed = false;
		useBVEGateExtraction = false;
		useLabelMatching = false;
		BVElocalGrow = 0;
		BVEglobalGrow = 0;


		if (inProcessMode) {
			PPVarToSolverVar.resize(variables);
			solverVarToPPVar.resize(variables);
			for (auto& clause : clauses) {
				for (int lit : clause) {
					PPVarToSolverVar[abs(lit)-1] = abs(lit);
					solverVarToPPVar[abs(lit)-1] = abs(lit);
				}
			}
		}
	}
	PreprocessorInterface::PreprocessorInterface(const vector<vector<int> >& clauses, const vector<uint64_t>& weights, uint64_t topWeight_, bool inProcessMode_)
	: preprocessor(clauses, weights, topWeight_), topWeight(topWeight_), inProcessMode(inProcessMode_) {
		init(clauses);
	}
	PreprocessorInterface::PreprocessorInterface(const vector<vector<int> >& clauses, const vector<pair<uint64_t, uint64_t> >& weights, uint64_t topWeight_, bool inProcessMode_)
	: preprocessor(clauses, weights, topWeight_), topWeight(topWeight_), inProcessMode(inProcessMode_) {
		init(clauses);
	}
	PreprocessorInterface::PreprocessorInterface(const vector<vector<int> >& clauses, const vector<vector<uint64_t> >& weights, uint64_t topWeight_, bool inProcessMode_)
	: preprocessor(clauses, weights, topWeight_), topWeight(topWeight_), inProcessMode(inProcessMode_) {
		init(clauses);
	}

	void PreprocessorInterface::logProof(std::string fname, int debugLevel, bool noOutput) {
		if (fname=="") return;
		plogfile.open(fname);
		proof_output = !noOutput;
		preprocessor.logProof(plogfile, debugLevel);
	}

	vector<uint64_t> PreprocessorInterface::getRemovedWeight() {
		return preprocessor.trace.removedWeight;
	}

	void PreprocessorInterface::preprocess(string techniques, int logLevel, double timeLimit) {
		preprocessor.logLevel = logLevel;
		preprocessor.printComments = false;
		preprocessor.opt = opt;
		preprocessor.BVElocalGrow = BVElocalGrow;
		preprocessor.BVEglobalGrow = BVEglobalGrow;

		preprocessor.preprocess(techniques, timeLimit, false, useBVEGateExtraction, !preprocessed, useLabelMatching);

		preprocessed = true;
		variables = max(variables, preprocessor.pi.vars);
	}

	void PreprocessorInterface::getInstanceClausesAndLabels(std::vector<std::vector<int> >& retClauses, std::vector<int>& retLabels) {
		retClauses = preprocessedInstance.clauses;
		for (unsigned i = 0; i < preprocessedInstance.labels.size(); i++) {
			retLabels.push_back(litToSolver(litToDimacs(preprocessedInstance.labels[i].F)));
		}
		int i=0;
		for (auto& clause : retClauses) {
			for (int& lit : clause) {
				int lit0 = lit;
				lit = litToDimacs(lit);
				variables = max(variables, abs(lit));
				lit = litToSolver(lit);
			}
		}


		if (ProofLogger* plog =  preprocessor.plog) {
			if (proof_output) {
				// TODO: this is not the most intuitive place to do prooflogging for mapping variables...
				vector<pair<int, vector<int> > > original_clauses;
				vector<pair<int, int> > mapping;
				vector<pair<uint64_t, int> > objective;
				for (int i=0; i<preprocessedInstance.clauses.size(); ++i) {
					for (int l : preprocessedInstance.clauses[i]) {
						if (litValue(l))mapping.emplace_back(l, litFromDimacs(litToSolver(litToDimacs(l))));
						else            mapping.emplace_back(litNegation(l), litFromDimacs(-litToSolver(litToDimacs(l))));
					}
					if (preprocessedInstance.weights[i]==HARDWEIGHT) {
						original_clauses.emplace_back(preprocessedInstance.clause_cids[i], preprocessedInstance.clauses[i]);
					} else {
						objective.emplace_back(preprocessedInstance.weights[i], litNegation(preprocessedInstance.clauses[i][0]));
					}
				}
				sort(mapping.begin(), mapping.end());
				mapping.erase(unique(mapping.begin(), mapping.end()), mapping.end());
				plog->remap_variables(original_clauses, mapping, objective);
				plog->end_proof(true);
			} else plog->end_proof(false);
		}
	}

	void PreprocessorInterface::_getInstance(std::vector<std::vector<int> >& retClauses, std::vector<uint64_t>& retWeights, bool addRemovedWeight, bool sortLabelsFrequency) {
		preprocessedInstance = preprocessor.getPreprocessedInstance(addRemovedWeight, sortLabelsFrequency);
		swap(retClauses, preprocessedInstance.clauses);
		swap(retWeights, preprocessedInstance.weights);
	}

	void PreprocessorInterface::getInstance(std::vector<std::vector<int> >& retClauses, std::vector<uint64_t>& retWeights, std::vector<int>& retLabels, bool addRemovedWeight, bool sortLabelsFrequency) {
		assert(preprocessor.pi.objectives == 1);

		preprocessedInstance = preprocessor.getPreprocessedInstance(addRemovedWeight, sortLabelsFrequency);
		getInstanceClausesAndLabels(retClauses, retLabels);

		retWeights.resize(preprocessedInstance.weights.size());
		for (unsigned i=0; i<preprocessedInstance.weights.size(); ++i) {
			if (preprocessedInstance.weights[i] == HARDWEIGHT) {
				retWeights[i] = topWeight;
			} else {
				retWeights[i] = preprocessedInstance.weights[i];
			}
		}
	}


	void PreprocessorInterface::getInstance(std::vector<std::vector<int> >& retClauses, std::vector<std::pair<uint64_t, uint64_t> >& retWeights, std::vector<int>& retLabels, bool addRemovedWeight, bool sortLabelsFrequency) {
		assert(preprocessor.pi.objectives == 2);

		preprocessedInstance = preprocessor.getPreprocessedInstance(addRemovedWeight, sortLabelsFrequency);
		getInstanceClausesAndLabels(retClauses, retLabels);

		retWeights.resize(preprocessedInstance.weightsv.size());
		for (unsigned i=0; i<preprocessedInstance.weightsv.size(); ++i) {
			if (preprocessedInstance.weightsv[i].size() == 0) {
				retWeights[i].F = topWeight;
				retWeights[i].S = topWeight;
			} else {
				retWeights[i].F = preprocessedInstance.weightsv[i][0];
				retWeights[i].S = (preprocessedInstance.weightsv[i].size()>1 ?  preprocessedInstance.weightsv[i][1] : 0);
				if (retWeights[i].F == HARDWEIGHT) retWeights[i].F = topWeight;
				if (retWeights[i].S == HARDWEIGHT) retWeights[i].S = topWeight;
			}
		}
	}

	void PreprocessorInterface::getInstance(std::vector<std::vector<int> >& retClauses, std::vector<std::vector<uint64_t> >& retWeights, std::vector<int>& retLabels, bool addRemovedWeight, bool sortLabelsFrequency) {
		preprocessedInstance = preprocessor.getPreprocessedInstance(addRemovedWeight, sortLabelsFrequency);
		getInstanceClausesAndLabels(retClauses, retLabels);

		if (preprocessor.pi.objectives > 1) {
			retWeights = preprocessedInstance.weightsv;
			for (auto& ws : retWeights) {
				for (uint64_t& w : ws) {
					if (w == HARDWEIGHT) {
						w = topWeight;
					}
				}
			}
		} else {
			retWeights.resize(preprocessedInstance.weights.size());
			for (unsigned i=0; i<preprocessedInstance.weights.size(); ++i) {
				uint64_t w = preprocessedInstance.weights[i];
				if (w != HARDWEIGHT) {
					retWeights[i].push_back(w);
				}
			}
		}
	}

	vector<int> PreprocessorInterface::reconstruct(const vector<int>& trueLiterals, bool convertLits) {
		vector<int> ppTrueLiterals;
		for (int lit : trueLiterals) {
			if (convertLits) lit = litToPP(lit);
			if (lit == 0) continue;
			ppTrueLiterals.push_back(lit);
		}
		return preprocessor.trace.getSolution(ppTrueLiterals, 0, variables, originalVariables).F;
	}

	vector<int> PreprocessorInterface::getFixed() {
		return preprocessor.trace.getFixed();
	}

	void PreprocessorInterface::printSolution(const vector<int>& trueLiterals, ostream& output, uint64_t ansWeight, int outputFormat) {
		vector<int> ppTrueLiterals;
		for (int lit : trueLiterals) {
			lit = litToPP(lit);
			if (lit == 0) continue;
			ppTrueLiterals.push_back(lit);
		}
		preprocessor.trace.printSolution(output, ppTrueLiterals, ansWeight, variables, originalVariables, outputFormat);
	}

	uint64_t PreprocessorInterface::getTopWeight() {
		return topWeight;
	}

	int PreprocessorInterface::addVar(int var) {
		if (!inProcessMode) return 0;
		assert(var >= 0);
		if (var == 0) {
			var = solverVarToPPVar.size() + 1;
		}
		if (var > (int)solverVarToPPVar.size()) {
			solverVarToPPVar.resize(var);
		}
		if (solverVarToPPVar[var-1] != 0) return 0;
		int nv = preprocessor.pi.addVar()+1;
		solverVarToPPVar[var-1] = nv;
		assert((int)PPVarToSolverVar.size() < nv);
		PPVarToSolverVar.resize(nv);
		PPVarToSolverVar[nv-1] = var;
		return var;
	}

	int PreprocessorInterface::addLabel(int lbl, uint64_t weight) {
		if (!inProcessMode) return 0;
		lbl = addVar(lbl);
		if (lbl == 0) return 0;
		if (weight >= topWeight) weight = HARDWEIGHT;
		int iVar = solverVarToPPVar[lbl-1]-1;
		preprocessor.pi.addClause({negLit(iVar)}, {weight});
		preprocessor.pi.mkLabel(iVar, 0, VAR_FALSE);
		return lbl;
	}

	bool PreprocessorInterface::alterWeight(int lbl, uint64_t weight) {
		if (!inProcessMode) return false;
		if (lbl < 1) return false;
		int iVar = solverVarToPPVar[lbl-1]-1;
		assert(iVar >= 0);
		int softClause = -1;
		if (preprocessor.pi.labelPolarity(iVar, 0) == VAR_TRUE) {
			//assert(preprocessor.pi.litClauses[posLit(iVar)].size() == 1);
			softClause = preprocessor.pi.litClauses[posLit(iVar)][0];
		}
		else if (preprocessor.pi.labelPolarity(iVar, 0) == VAR_FALSE) {
			//assert(preprocessor.pi.litClauses[negLit(iVar)].size() == 1);
			softClause = preprocessor.pi.litClauses[negLit(iVar)][0];
		}
		else {
			return false;
		}
		if (weight >= topWeight) {
			preprocessor.pi.unLabel(iVar, 0);
			weight = HARDWEIGHT;
		}
		assert(!preprocessor.pi.clauses[softClause].isHard());
		preprocessor.pi.clauses[softClause].weights[0] = weight;
		return true;
	}

	bool PreprocessorInterface::addClause(std::vector<int> clause) {
		if (!inProcessMode) return false;
		for (int& lit : clause) {
			assert(lit != 0);
			int tlit = litToPP(lit);
			if (tlit == 0) {
				int nvar = addVar(abs(lit));
				assert(nvar == abs(lit));
				tlit = litToPP(lit);
				assert(lit == litToSolver(tlit));
			}
			tlit = litFromDimacs(tlit);
			lit = tlit;
		}
		sort(clause.begin(), clause.end());
		clause.erase(unique(clause.begin(), clause.end()), clause.end());
		for (int i = 1; i < (int)clause.size(); i++) {
			if (clause[i] == litNegation(clause[i-1])) return true;
		}
		preprocessor.pi.addClause(clause);
		return true;
	}

	bool PreprocessorInterface::labelToVar(int lbl) {
		if (!inProcessMode) return false;
		if (lbl < 1) return false; // what
		int iVar = solverVarToPPVar[lbl-1]-1;
		assert(iVar >= 0);
		int softClause = -1;
		if (preprocessor.pi.labelPolarity(iVar, 0) == VAR_TRUE) {
			assert(preprocessor.pi.litClauses[posLit(iVar)].size() >= 1);
			softClause = preprocessor.pi.litClauses[posLit(iVar)][0];
		}
		else if (preprocessor.pi.labelPolarity(iVar, 0) == VAR_FALSE) {
			assert(preprocessor.pi.litClauses[negLit(iVar)].size() >= 1);
			softClause = preprocessor.pi.litClauses[negLit(iVar)][0];
		}
		else {
			return true;
		}
		preprocessor.pi.unLabel(iVar, 0);
		preprocessor.pi.clauses[softClause].weights[0] = 0;
		if (preprocessor.pi.clauses[softClause].isWeightless()) {
			preprocessor.pi.removeClause(softClause);
		}
		return true;
	}

	bool PreprocessorInterface::resetRemovedWeight() {
		if (!inProcessMode) return false;
		preprocessor.trace.removedWeight.clear();
		return true;
	}

	void PreprocessorInterface::setBVEGateExtraction(bool use) {
		useBVEGateExtraction = use;
	}

	void PreprocessorInterface::setLabelMatching(bool use) {
		useLabelMatching = use;
	}

	void PreprocessorInterface::setSkipTechnique(int value) {
		opt.skipTechnique = value;
	}

	void PreprocessorInterface::setBVEsortMaxFirst(bool use) {
		opt.BVEsortMaxFirst = use;
	}
	void PreprocessorInterface::setBVElocalGrowLimit(int limit) {
		BVElocalGrow = limit;
	}
	void PreprocessorInterface::setBVEglobalGrowLimit(int limit) {
		BVEglobalGrow = limit;
	}
	void PreprocessorInterface::setMaxBBTMSVars(int limit) {
		opt.BBTMS_maxVars = limit;
	}
	void PreprocessorInterface::setHardenInModelSearch(bool harden) {
		opt.hardenInModelSearch = harden;
	}
	void PreprocessorInterface::setModelSearchIterLimit(int limit) {
		opt.modelSearchIterLimit = limit;
	}
	void PreprocessorInterface::setOptionVariables(map<string, int>& intVars, map<string, bool>& boolVars, map<string, double>& doubleVars, map<string, uint64_t>& uint64Vars) {
		opt.parseValues(intVars, boolVars, doubleVars, uint64Vars);
		for (auto& v : intVars) {
			cerr << "invalid option " << v.first << " = " << v.second << endl;
			cout << "c inavlid option " << v.first << " = " << v.second << endl;
		}
		for (auto& v : boolVars) {
			cerr << "invalid option " << v.first << " = " << v.second << endl;
			cout << "c invalid option " << v.first << " = " << v.second << endl;
		}
		for (auto& v : doubleVars) {
			cerr << "invalid option " << v.first << " = " << v.second << endl;
			cout << "c invalid option " << v.first << " = " << v.second << endl;
		}
		for (auto& v : uint64Vars) {
			cerr << "invalid option " << v.first << " = " << v.second << endl;
			cout << "c invalid option " << v.first << " = " << v.second << endl;
		}
	}




	int PreprocessorInterface::litToSolver(int lit) {
		if (PPVarToSolverVar.size() < abs(lit)) PPVarToSolverVar.resize(abs(lit));
		if (PPVarToSolverVar[abs(lit)-1] == 0) {
			PPVarToSolverVar[abs(lit)-1] = solverVarToPPVar.size() + 1;
			solverVarToPPVar.push_back(abs(lit));
		}
		if (lit > 0) return PPVarToSolverVar[abs(lit)-1];
		else return -PPVarToSolverVar[abs(lit)-1];
	}

	int PreprocessorInterface::litToPP(int lit) {
		if ((int)solverVarToPPVar.size() <= abs(lit)-1) return 0;
		if (lit > 0) return solverVarToPPVar[abs(lit)-1];
		else return -solverVarToPPVar[abs(lit)-1];
	}

	void PreprocessorInterface::printInstance(ostream& output, int outputFormat) {
		std::vector<std::vector<int> > clauses;
		std::vector<std::vector<uint64_t> > weights;
		std::vector<int> labels;
		getInstance(clauses, weights, labels, true);

		assert(outputFormat == INPUT_FORMAT_WPMS || outputFormat == INPUT_FORMAT_SAT || outputFormat == INPUT_FORMAT_WPMS22 || outputFormat == INPUT_FORMAT_WMOO);

		/*
		if (clauses.size() == 0) {
			clauses.push_back({-1, 1});
			weights.push_back({topWeight});
		}
		*/

		if (outputFormat == INPUT_FORMAT_WPMS || outputFormat == INPUT_FORMAT_WPMS22) {
			if (getUpperBound() !=  HARDWEIGHT) output << "c UB " << getUpperBound() << "\n";

			output<<"c assumptions ";
			for (unsigned i = 0; i < labels.size(); i++) {
				output<<labels[i];
				if (i + 1 < labels.size()) {
					output<<" ";
				}
			}
			output<<"\n";
		}

		if (outputFormat == INPUT_FORMAT_WPMS) {
			output<<"p wcnf "<<max((int)solverVarToPPVar.size(), 1)<<" "<<clauses.size()<<" "<<topWeight<< '\n';
			for (unsigned i = 0; i < clauses.size(); i++) {
				if (weights[i].size()==0) output<<topWeight<<" ";
				else output<<weights[i][0]<<" ";
				for (int lit : clauses[i]) {
					output<<lit<<" ";
				}
				output<<"0\n";
			}
		}
		else if (outputFormat == INPUT_FORMAT_SAT) {
			output<<"p cnf "<<max((int)solverVarToPPVar.size(), 1)<<" "<<clauses.size()<<'\n';
			for (unsigned i = 0; i < clauses.size(); i++) {
				for (int lit : clauses[i]) {
					output<<lit<<" ";
				}
				output<<"0\n";
			}
		} else if (outputFormat == INPUT_FORMAT_WPMS22) {
			output<<"c p wcnf "<<max((int)solverVarToPPVar.size(), 1)<<" "<<clauses.size()<<" "<<topWeight<< '\n';
			for (unsigned i = 0; i < clauses.size(); i++) {
				if (weights[i].size()==0 || weights[i][0] == topWeight) output<<"h  ";
				else output << weights[i][0] << " ";
				for (int lit : clauses[i]) {
					output<<lit<<" ";
				}
				output<<"0\n";
			}
		} else if (outputFormat == INPUT_FORMAT_WMOO) {
			for (unsigned i = 0; i < clauses.size(); i++) {
				bool isHard  = 1;
				for (unsigned j=0; j<weights[i].size(); ++j) {
					if (weights[i][j] < topWeight) {
						isHard = 0;
						if (weights[i][j]>0) {
							output << 'o' << j+1 << " " << weights[i][j] << " ";
							for (int lit : clauses[i]) {
								output<<lit<<" ";
							}
							output<<"0\n";
						}
					}
				}
				if (isHard) {
					output << "h ";
					for (int lit : clauses[i]) {
						output<<lit<<" ";
					}
					output<<"0\n";
				}
			}
		}
		else {
			abort();
		}
		output.flush();
	}
	void PreprocessorInterface::printTechniqueLog(ostream& output) {
		preprocessor.rLog.print(output);
	}
	void PreprocessorInterface::printTimeLog(ostream& output) {
		preprocessor.rLog.printTime(output);
	}
	void PreprocessorInterface::printInfoLog(ostream& output) {
		preprocessor.rLog.printInfo(output);
	}
	void PreprocessorInterface::printPreprocessorStats(ostream& output) {
		preprocessor.printStats(output);
	}
	void PreprocessorInterface::printMap(ostream& output) {
		output<<solverVarToPPVar.size()<<" "<<variables<<" "<<originalVariables<<'\n';
		for (int t : solverVarToPPVar) {
			output<<t<<" ";
		}
		output<<'\n';
		output<<preprocessor.trace.operations.size()<<'\n';
		for (unsigned i = 0; i < preprocessor.trace.operations.size(); i++) {
			output<<preprocessor.trace.operations[i]<<" ";
			output<<preprocessor.trace.data[i].size()<<" ";
			for (int a : preprocessor.trace.data[i]) {
				output<<a<<" ";
			}
			output<<'\n';
		}
		output.flush();
	}

	std::string PreprocessorInterface::version(int l) {return Preprocessor::version(l);}

}
