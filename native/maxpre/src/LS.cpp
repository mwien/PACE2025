void Preprocessor::tryLSBCE(int lit, unordered_set<int>& deletedClauses, unordered_set<int>& touchedList, vector<pair<int, int> >& blockedClauses) {
	for (int c1i : pi.litClauses[lit]) {
		if (deletedClauses.count(c1i)) continue;
		const vector<int>& c1 = pi.clauses[c1i].lit;
		bool f = false;
		for (int c2i : pi.litClauses[litNegation(lit)]) {
			if (deletedClauses.count(c2i)) continue;
			const vector<int>& c2 = pi.clauses[c2i].lit;
			bool ff = false;
			for (int c1l : c1) {
				for (int c2l : c2) {
					if (litNegation(c1l) == c2l && c1l != lit) {
						ff = true;
						break;
					}
				}
				if (ff) break;
			}
			if (!ff) {
				f = true;
				break;
			}
		}
		if (!f) {
			deletedClauses.insert(c1i);
			blockedClauses.push_back({c1i, lit});
			for (int l : c1) {
				touchedList.insert(litVariable(l));
			}
		}
	}
}

int Preprocessor::tryLS(int lit) {
	assert(pi.isLabelVar(litVariable(lit)));
	assert(!pi.isLitLabel(litNegation(lit)));
	vector<int>& tc = pi.litClauses[litNegation(lit)];
	if (tc.size()==0) return 0;
	vector<pair<int, int> > blockedClauses;
	unordered_set<int> touchedList;
	unordered_set<int> deletedClauses;
	for (int t : tc) {
		deletedClauses.insert(t);
		for(int l : pi.clauses[t].lit) {
			touchedList.insert(litVariable(l));
		}
	}
	while (touchedList.size() > 0) {
		int var = *touchedList.begin();
		touchedList.erase(var);
		if (pi.isLabelVar(var)) continue;
		tryLSBCE(posLit(var), deletedClauses, touchedList, blockedClauses);
		tryLSBCE(negLit(var), deletedClauses, touchedList, blockedClauses);
	}
	for (auto c : blockedClauses) {
		bool ttl = 0;
		for (int l : pi.clauses[c.F].lit) {
			if (l==lit) {
				ttl=1;
				break;
			}
		}
		if (ttl) {
			pi.removeClause(c.F);
			if (plog) plog->delete_red_clause_(c.F,  {{c.S, litNegation(lit)}});
			continue;
		}
		trace.LS(litNegation(lit), c.S, pi.clauses[c.F].lit);
		pi.addLiteralToClause(litNegation(lit), c.F);
		if (plog) {
			int tci = 0;
			tci = plog->add_rup_clause(pi.clauses[c.F].lit, 1);
			plog->delete_red_clause_(c.F, {{c.S, litNegation(lit)}});
			plog->map_clause(c.F, tci, 1);
		}
	}
	rLog.removeLiteral(-(int)blockedClauses.size());
	return blockedClauses.size();
}

int Preprocessor::doLS() {
	//while (doBCE());
	rLog.startTechnique(Log::Technique::LS);
	if (!rLog.requestTime(Log::Technique::LS)) {
		rLog.stopTechnique(Log::Technique::LS);
		return 0;
	}
	if (plog && plogDebugLevel>=1) plog->comment("start LS");
	int added = 0;
	vector<int> checkVar = pi.tl.getTouchedVariables("LS");
	for (int var : checkVar) {
		if (!pi.isLabelVar(var)) continue;
		if (pi.isVarRemoved(var)) continue;
		if (!rLog.requestTime(Log::Technique::LS)) break;
		if (pi.slabelPolarity(var) != VAR_FALSE) added+=tryLS(posLit(var));
		if (pi.slabelPolarity(var) != VAR_TRUE) added+=tryLS(negLit(var));
	}
	log(added, " clauses labeled by LS");

	if (plog && plogDebugLevel>=1) {
		plog->comment("LS finished, ", added, " clauses labeled.");
		if (plogDebugLevel>=4) plogLogState();
	}

	rLog.stopTechnique(Log::Technique::LS);
	return added;
}
