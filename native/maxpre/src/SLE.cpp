bool Preprocessor::vSubsumed(vector<int>& v1, vector<int>& v2) {
	for (int a : v1) {
		bool f = false;
		for (int b : v2) {
			if (a == b) {
				f = true;
				break;
			}
		}
		if (!f) {
			return false;
		}
	}
	return true;
}


// Even though this is not optimal implementation this is fast enough
int Preprocessor::trySLESlow(int lb1, int lb2) {
	assert(pi.isLabelVar(lb1));
	assert(pi.labelIndexMask(lb1) == pi.labelIndexMask(lb2));
	assert(pi.slabelPolarity(lb1) != 0);
	assert(pi.slabelPolarity(lb2) != 0);

	int lb1_lit = pi.slabelPolarity(lb1) == VAR_TRUE ? posLit(lb1) : negLit(lb1);
	int lb2_lit = pi.slabelPolarity(lb2) == VAR_TRUE ? posLit(lb2) : negLit(lb2);

	vector<int> cs1;
	vector<int> cs2;
	vector<uint64_t> w1, w2;


	if (pi.slabelPolarity(lb1) == VAR_TRUE) {
		if (pi.litClauses[posLit(lb1)].size()>1) return 0;
		cs1 = pi.litClauses[negLit(lb1)];
		w1 = pi.clauses[pi.litClauses[posLit(lb1)][0]].weights;
	}
	else {
		if (pi.litClauses[negLit(lb1)].size()>1) return 0;
		cs1 = pi.litClauses[posLit(lb1)];
		w1 = pi.clauses[pi.litClauses[negLit(lb1)][0]].weights;
	}
	if (pi.slabelPolarity(lb2) == VAR_FALSE) {
		if (pi.litClauses[negLit(lb2)].size()>1) return 0;
		cs2 = pi.litClauses[posLit(lb2)];
		w2 = pi.clauses[pi.litClauses[negLit(lb2)][0]].weights;
	}
	else {
		if (pi.litClauses[posLit(lb2)].size()>1) return 0;
		cs2 = pi.litClauses[negLit(lb2)];
		w2 = pi.clauses[pi.litClauses[posLit(lb2)][0]].weights;
	}

	bool s1 = vSubsumed(cs1, cs2);
	bool s2 = vSubsumed(cs2, cs1);

	int rmClauses = 0;

	if (s1 && pi.wDominates(w1, w2)) {
		int tci = -1;
		if (plog) tci = plog->add_red_clause_({lb1_lit}, {{lb1_lit, -1}, {litNegation(lb2_lit), -1}}, 1);

		rmClauses = setVariable(lb1_lit, tci);

		if (plog) plog->delete_clause_vid(tci, lb1_lit);

		assert(pi.isVarRemoved(lb1));
		rLog.removeClause(rmClauses);
		rLog.removeLabel(1);
		return 1;
	}
	else if(s2 && pi.wDominates(w2, w1)) {
		int tci = -1;
		if (plog) tci =plog->add_red_clause_({lb2_lit}, {{lb2_lit, -1}, {litNegation(lb1_lit), -1}}, 1);

		rmClauses = setVariable(lb2_lit, tci);

		if (plog) plog->delete_clause_vid(tci, lb2_lit);

		assert(pi.isVarRemoved(lb2));
		rLog.removeClause(rmClauses);
		rLog.removeLabel(1);
		return 1;
	}
	return 0;
}

int Preprocessor::doSLE() {
	rLog.startTechnique(Log::Technique::SLE);
	int removed = 0;
	if (!rLog.requestTime(Log::Technique::SLE)) {
		rLog.stopTechnique(Log::Technique::SLE);
		return 0;
	}
	if (plog && plogDebugLevel>=1) plog->comment("start SLE");
	vector<int> checkVar = pi.tl.getTouchedVariables("SLE");
	if (rLog.isTimeLimit()) {
		auto cmp = [&](int var1, int var2) {
			return pi.litClauses[negLit(var1)].size() + pi.litClauses[posLit(var1)].size() < pi.litClauses[negLit(var2)].size() + pi.litClauses[posLit(var2)].size();
		};
		sort(checkVar.begin(), checkVar.end(), cmp);
	}
	for (int var : checkVar) {
		if (!pi.isLabelVar(var)) continue;
		if (!pi.slabelPolarity(var)) continue;
		if (pi.isVarRemoved(var)) continue;
		if (!rLog.requestTime(Log::Technique::SLE)) break;

		if (pi.litClauses[negLit(var)].size() == 0) {
			int tci = -1;
			if (plog) tci = plog->add_red_clause_({posLit(var)}, posLit(var), 1);
			setVariable(posLit(var), tci);
			if (plog) plog->delete_clause_vid(tci, posLit(var));
			removed++;
			continue;
		}
		if (pi.litClauses[posLit(var)].size() == 0) {
			int tci = -1;
			if (plog) tci = plog->add_red_clause_({negLit(var)}, negLit(var), 1);
			setVariable(negLit(var), tci);
			if (plog) plog->delete_clause_vid(tci, negLit(var));
			removed++;
			continue;
		}

		bool f = true;
		while (f) {
			f = false;
			vector<int> clauses;
			if (pi.slabelPolarity(var) == VAR_TRUE) clauses = pi.litClauses[negLit(var)];
			else clauses = pi.litClauses[posLit(var)];
			for (int c : clauses) {
				for (int l : pi.clauses[c].lit) {
					if (pi.labelIndexMask(litVariable(l)) != pi.labelIndexMask(var)) continue;
					if (litVariable(l)==var) continue;
					if (pi.slabelPolarity(litVariable(l)) != litPolarity(litNegation(l))) continue;
					if (trySLESlow(var, litVariable(l))) {
						removed++;
						f = true;
						break;
					}
				}
				if (f) break;
			}
		}
	}

	log(removed, " labels removed by SLE");

	if (plog && plogDebugLevel>=1) {
		plog->comment("SLE finished, ", removed, " labels removed by SLE");
		if (plogDebugLevel>=4) plogLogState();
	}

	rLog.stopTechnique(Log::Technique::SLE);
	return removed;
}

void Preprocessor::doSLE2() {
	map<int, vector<int> > lbs;
	for (int var = 0; var < pi.vars; var++) {
		if (pi.isLabelVar(var) && pi.slabelPolarity(var) && !pi.isVarRemoved(var)) {
			lbs[pi.labelIndexMask(var)].push_back(var);
		}
	}
	for (auto& lbss : lbs) {
		for (int lb1 : lbss.S) {
			for (int lb2 : lbss.S) {
				if (lb1 != lb2 && !pi.isVarRemoved(lb1) && !pi.isVarRemoved(lb2)) {
					if (trySLESlow(lb1, lb2)) {
						print("fail SLE");
						print(lb1 + 1, " ", lb2 + 1);
						abort();
					}
				}
			}
		}
	}
}
