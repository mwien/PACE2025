
int Preprocessor::tryFLP(vector<int> fLit, int clause) {
	bool is = false;
	for (int lit : fLit) {
		for (int c : pi.litClauses[lit]) {
			if (pi.clauses[c].lit.size() < 3) {
				is = true;
				break;
			}
		}
	}
	if (!is) return 0;
	vector<int> b;
	b.resize(fLit.size());
	for (unsigned i=0; i<fLit.size(); ++i) b[i]=litNegation(fLit[i]);
	if (!satSolver->testUPConflict(b, 2)) {
		if (fLit.size() == 1) {
			int tci = -1;
			if (plog) tci = plog->add_rup_clause_({fLit[0]}, 1);
			int rmClauses = setVariable(fLit[0], tci);
			if (plog) plog->delete_clause_vid(tci, fLit[0]);
			assert(pi.isVarRemoved(litVariable(fLit[0])));
			rLog.removeClause(rmClauses);
			rLog.removeLabel(1);
		}
		else {
			vector<int> teClause = pi.clauses[clause].lit;
			for (int lit : teClause) {
				if (!pi.isLitLabel(litNegation(lit))) {
					pi.removeLiteralFromClause(lit, clause);
					rLog.removeLiteral(1);
				}
			}
			if (plog) plog->clause_updated(clause, pi.clauses[clause].lit);
		}
		return 1;
	}
	/*
	queue<int> failQ;
	for (int lit : fLit) {
		failQ.push(lit);
	}
	vector<pair<int, int> > litRemoved;
	bool conflict = false;
	unordered_set<int> satClauses;
	unordered_set<int> used;
	vector<int> binCores; // this doesn't do anything currently...?
	while (!failQ.empty()) {
		int lit = failQ.front();
		failQ.pop();
		if (used.count(lit)) continue;
		used.insert(lit);
		for (int c : pi.litClauses[litNegation(lit)]) {
			satClauses.insert(c);
		}
		vector<int> cs = pi.litClauses[lit];
		for (int c : cs) {
			if (satClauses.count(c)) continue;
			if (!pi.clauses[c].isHard()) {
				if (fLit.size() == 1) binCores.push_back(litNegation(pi.clauses[c].lit[0]));
				continue;
			}
			if (pi.clauses[c].lit.size() == 1) {
				conflict = true;
				break;
			}
			pi.removeLiteralFromClause(lit, c, false);
			litRemoved.push_back({lit, c});
			if (pi.clauses[c].lit.size() == 1) {
				failQ.push(litNegation(pi.clauses[c].lit[0]));
			}
		}
		if (conflict) break;
	}
	for (auto t : litRemoved) {
		pi.addLiteralToClause(t.F, t.S, false);
	}
	if (conflict) {
		if (fLit.size() == 1) {
			int rmClauses;
			rmClauses = setVariable(fLit[0]);
			assert(pi.isVarRemoved(litVariable(fLit[0])));
			rLog.removeClause(rmClauses);
			if (pi.isLabel[litVariable(fLit[0])]) rLog.removeLabel(1); // TODO: this should be always the case...?
			else rLog.removeVariable(1);
		}
		else {
			vector<int> teClause = pi.clauses[clause].lit;
			for (int lit : teClause) {
				if (!pi.isLitLabel(litNegation(lit))) {
					pi.removeLiteralFromClause(lit, clause);
					rLog.removeLiteral(1);
				}
			}
		}
		return 1;
	}
	*/
	return 0;
}

int Preprocessor::doFLP() {
	rLog.startTechnique(Log::Technique::FLP);
	if (!rLog.requestTime(Log::Technique::FLP)) {
		rLog.stopTechnique(Log::Technique::FLP);
		return 0;
	}
	if (plog && plogDebugLevel>=1) plog->comment("start FLP");
	prepareSatSolver();
	int removed = 0;
	for (int c = 0; c < (int)pi.clauses.size(); c++) {
		if (!rLog.requestTime(Log::Technique::FLP)) break;
		if (pi.isClauseRemoved(c)) continue;
		if (!pi.clauses[c].isHard()) continue;
		vector<int> lbs;
		bool f = false;
		for (int lit : pi.clauses[c].lit) {
			if (pi.isLitLabel(litNegation(lit))) lbs.push_back(lit);
			else f = true;
		}
		if (lbs.size() > 0 && f) removed += tryFLP(lbs, c);
	}
	log(removed, " cores found by FLP");

	if (plog && plogDebugLevel>=1) {
		plog->comment("FLP finished, ", removed, " cores found");
		if (plogDebugLevel>=4) plogLogState();
	}

	rLog.stopTechnique(Log::Technique::FLP);
	return removed;
}
