// TrimMaxSAT Technique
//


int getM(int n, double z) { // assumes 0 <= z < 1
	if (n<=2) return 1;
	double p=sqrt(n);
	int l = ((int)(2*p)-1); // size of candidate list
	int i = ((int)(z*l))+1; // index (1-indexed) in the candidate list

	if (i<p) return n/i;
	else     return ((int)(2*p))-i;
}

int Preprocessor::tryTMS(vector<int>& neverSat, vector<pair<int, int> >& variablesToSet, vector<pair<int, int> >& proofClausesToDelete) {
	if (!neverSat.size()) return 0;
	for (unsigned i=0; i<neverSat.size(); ++i) {
		if (canSatLits.count(neverSat[i])) {
			neverSat[i--]=neverSat.back();
			neverSat.pop_back();
		}
	}

	vector<bool> model;
	vector<int> assumptions;
	vector<vector<int> > sets;

	//statistics...
	int SATcalls=0;
	int UNSATcalls=0;

	double lb=0, z=0.5;
	vector<int> neverSatVids;
	while (neverSat.size()) {
		if (!rLog.requestTime(rLog.activeTechnique)) {
			log("TMS stopped due to timelimit, ", SATcalls+UNSATcalls, " SAT-solver calls done by TMS, SAT: ", SATcalls, ", UNSAT: ", UNSATcalls);
			stats["TMS_interrupted"]+=1;
			return 0;
		}
		double timeLimit = rLog.allocatedTimeLeft(rLog.activeTechnique);

		// create set partition
		int m = getM(neverSat.size(), z);

		sets.resize(m);
		for (int i=0; i<m; ++i) sets[i].clear();
		for (int i=0, j=0; i<(int)neverSat.size(); ++i) {
			sets[j].push_back(neverSat[i]);
			if (++j == m) j=0;
		}

		// prepare sat solver
		assumptions.resize(m);
		for (int i=0; i<m; ++i) {
			int nv = pi.addVar();
			sets[i].push_back(posLit(nv));
			if (plog) proofClausesToDelete.emplace_back(plog->add_red_clause(sets[i], posLit(nv), 0), -1);
			satSolver->addClause(sets[i]);
			assumptions[i] = negLit(nv);
		}
		if (plog && plogDebugLevel>=1) plog->comment("invoke SAT-solver");
		int SAT = satSolver->solveLimited(assumptions, timeLimit);
		if (plog && plogDebugLevel>=1) plog->comment("SAT-solver finished with value ", SAT);

		if (SAT==-1) {
			// remove the added clauses
			vector<int> cl={0};
			for (int i=0; i<m; ++i) {
				cl[0]=sets[i].back();
				if (plog)	proofClausesToDelete.emplace_back(plog->add_red_clause(cl, cl[0], 0), -1);
				satSolver->addClause(cl);
			}
			return 0;
		}

		if (SAT) {
			++SATcalls;
			// get model, remove satisfiable clauses from neverSat
			satSolver->getModel(model);
			modelCostCheck(model); // updates UB for cost

			for (unsigned i=0; i<model.size(); ++i) {
				if (model[i]) canSatLits.insert(posLit(i));
				else          canSatLits.insert(negLit(i));
			}
			for (unsigned i=0; i<neverSat.size(); ++i) {
				if (model[litVariable(neverSat[i])] == litValue(neverSat[i])) {
					neverSat[i--]=neverSat.back();
					neverSat.pop_back();
				}
			}
			z -= (z-lb)/2;
		} else {
			++UNSATcalls;
			if (m>1) { // decrease m
				z += (1-z)/2;
			} else {   // done, all unsat softs can be hardened
					// remove added clauses...
				//satSolver->addClause(sets[0].back());
				if (plog) {
					//proofClausesToDelete.emplace_back(plog->add_red_clause_({sets[0].back()}, sets[0].back(), 0), sets[0].back());
					// make sure that all learnt units are rup
					vector<int> cl={0};
					for (int l : neverSat) {
						cl[0]=l;
						if (plog && plogDebugLevel>=1) plog->comment("invoke SAT-solver");
						satSolver->solve(cl);
						if (plog && plogDebugLevel>=1) plog->comment("call to SAT-solver finished");
						proofClausesToDelete.emplace_back(plog->add_rup_clause_({litNegation(l)}, 1), litNegation(l));
						neverSatVids.push_back(proofClausesToDelete.back().first);
					}
				}
				break;
			}
		}

		// remove added clauses...
		vector<int> cl={0};
		for (int i=0; i<m; ++i) {
			cl[0]=sets[i].back();
			if (plog) proofClausesToDelete.emplace_back(plog->add_red_clause(cl, cl[0], 0), -1);
			satSolver->addClause(cl);
		}
	}

	for (unsigned i=0; i<neverSat.size(); ++i) {
		if (pi.isLabelVar(litVariable(neverSat[i]))) {
			rLog.removeLabel(1);
		} else {
			rLog.removeVariable(1);
			stats["TMS_Vars_removed"]+=1;
		}
		int vid = (neverSatVids.size()>i) ? neverSatVids[i] : -1;
		variablesToSet.emplace_back(litNegation(neverSat[i]), vid);
	}

	log(neverSat.size(), " unsatisfiable softs detected and deleted by TMS");
	log(SATcalls+UNSATcalls, " SAT-solver calls done by TMS, SAT: ", SATcalls, ", UNSAT: ", UNSATcalls);
	return neverSat.size();
}




// Use TrimMaxSAT algorithm for general backbone computing
int Preprocessor::doBBTMS(int maxVars) {
	rLog.startTechnique(Log::Technique::BBTMS);
	if (!rLog.requestTime(Log::Technique::BBTMS)) {
		rLog.stopTechnique(Log::Technique::BBTMS);
		return 0;
	}
	if (plog && plogDebugLevel>=1) plog->comment("start BBTMS");
	prepareSatSolver(plog);
	stats["doBBTMS"]+=1;
	stats["TMS_Vars_removed"]+=0;

	vector<pair<int, int> > vars;
	for (int i=0; i<pi.vars; ++i) {
		if (pi.isVarRemoved(i)) continue;
		if (canSatLits.count(posLit(i)) && canSatLits.count(negLit(i))) continue;
		vars.push_back({-((int)pi.litClauses[posLit(i)].size()+pi.litClauses[negLit(i)].size()), i});
	}
	sort(vars.begin(), vars.end());


	vector<int> litsPos;
	vector<int> litsNeg;
	for (unsigned i=0; i<vars.size(); ++i) {
		if (maxVars>=0 && ((int)litsPos.size()>=maxVars && (int)litsNeg.size()>=maxVars)) break;
		if ((maxVars<0 || (int)litsPos.size()<maxVars) && !canSatLits.count(posLit(vars[i].S))) {
			litsPos.push_back(posLit(vars[i].S));
		}
		if ((maxVars<0 || (int)litsNeg.size()<maxVars) && !canSatLits.count(negLit(vars[i].S))) {
			litsNeg.push_back(negLit(vars[i].S));
		}
	}

	vector<pair<int, int> > proofClausesToDelete;
	vector<pair<int, int> > variablesToSet;
	int removedVars=0;
	if (rLog.requestTime(Log::Technique::BBTMS)) removedVars+=tryTMS(litsPos, variablesToSet, proofClausesToDelete);
	if (rLog.requestTime(Log::Technique::BBTMS)) removedVars+=tryTMS(litsNeg, variablesToSet, proofClausesToDelete);

	satSolver->cleanLearntClausesFromProof();
	delete satSolver;
	satSolver = nullptr;

	for (auto& t : variablesToSet) rLog.removeClause(setVariable(t.F, t.S));
	if (plog) for (auto& t : proofClausesToDelete) plog->delete_clause_vid(t.F, t.S);


	rLog.stopTechnique(Log::Technique::BBTMS);
	if (plog && plogDebugLevel>=1) plog->comment("BBTMS finished, ", removedVars, " neversat variables hardened by BBTMS");
	return removedVars;
}


int Preprocessor::doTMS() {
	rLog.startTechnique(Log::Technique::TMS);
	if (!rLog.requestTime(Log::Technique::TMS)) {
		rLog.stopTechnique(Log::Technique::TMS);
		return 0;
	}
	if (plog && plogDebugLevel>=1) plog->comment("start TMS");

	stats["doTMS"]+=1;
	stats["TMS_interrupted"]+=0;
	prepareSatSolver(plog);

	vector<int> bvars;
	for (int i=0; i<pi.vars; ++i) {
		if (!pi.isLabelVar(i) || pi.isVarRemoved(i)) continue;
		if (pi.slabelPolarity(i) == VAR_TRUE || (pi.slabelPolarity(i) != VAR_FALSE && canSatLits.count(negLit(i)))) {
			if (!canSatLits.count(posLit(i))) bvars.push_back(posLit(i));
		} else {
			if (!canSatLits.count(negLit(i))) bvars.push_back(negLit(i));
		}
	}

	vector<pair<int, int> > proofClausesToDelete;
	vector<pair<int, int> > variablesToSet;
	int removedSofts=0;
	if (rLog.requestTime(Log::Technique::TMS)) removedSofts=tryTMS(bvars, variablesToSet, proofClausesToDelete);

	satSolver->cleanLearntClausesFromProof();
	delete satSolver;
	satSolver = nullptr;

	for (auto& t : variablesToSet) rLog.removeClause(setVariable(t.F, t.S));
	if (plog) for (auto& t : proofClausesToDelete) plog->delete_clause_vid(t.F, t.S);


	if (plog && plogDebugLevel>=1) {
		plog->comment("TMS finished, ", removedSofts, " neversat labels removed by TMS");
		if (plogDebugLevel>=4) plogLogState();
	}

	rLog.stopTechnique(Log::Technique::TMS);
	return removedSofts;
}
