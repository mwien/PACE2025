bool Preprocessor::tryBCR(int c, int l11) {
	int l1 = pi.clauses[c].lit[0];
	int l2 = pi.clauses[c].lit[1];
	if (l2 == l11) swap(l1, l2);
	assert(l1 == l11);

	if (pi.litClauses[l1].size() < 2) return false;
	if (pi.litClauses[l2].size() < 2) return false;
	if (pi.litClauses[litNegation(l1)].size()>1) return false;
	if (pi.litClauses[litNegation(l2)].size()>1) return false;
	assert(pi.litClauses[litNegation(l1)].size() == 1);
	assert(pi.litClauses[litNegation(l2)].size() == 1);

	vector<vector<int> > newClauses;

	int sizeLimit = pi.litClauses[l1].size() + pi.litClauses[l2].size();

	for (int c1 : pi.litClauses[l1]) {
		if (c1 == c) continue;
		for (int l : pi.clauses[c1].lit) {
			if (l == l2) return false;
		}
		for (int c2 : pi.litClauses[l2]) {
			if (c2 == c) continue;
			vector<int> nc;
			for (int l : pi.clauses[c1].lit) {
				if (l != l1) nc.push_back(l);
			}
			for (int l : pi.clauses[c2].lit) {
				if (l != l1) nc.push_back(l);
			}
			sort(nc.begin(), nc.end());
			nc.erase(unique(nc.begin(), nc.end()), nc.end());
			bool taut = false;
			for (unsigned i = 1; i < nc.size(); i++) {
				if (litNegation(nc[i]) == nc[i - 1]) {
					taut = true;
					break;
				}
			}
			if (taut) continue;
			if ((int)newClauses.size() >= sizeLimit) return false;
			newClauses.push_back(nc);
		}
	}

	//for prooflogging
	vector<pair<int, vector<int> > > clauses1;
	vector<pair<int, vector<int> > > clauses2;
	if (plog) {
		for (int cc : pi.litClauses[l1]) {
			if (cc==c) continue;
			clauses1.emplace_back(cc, pi.clauses[cc].lit);
			for (int i=0; i<(int)clauses1.back().S.size(); ++i) {
				if (clauses1.back().S[i]==l1) {
					swap(clauses1.back().S[i], clauses1.back().S.back());
					clauses1.back().S.pop_back();
					break;
				}
			}
		}
		for (int cc : pi.litClauses[l2]) {
			if (cc==c) continue;
			clauses2.emplace_back(cc, pi.clauses[cc].lit);
			for (int i=0; i<(int)clauses2.back().S.size(); ++i) {
				if (clauses2.back().S[i]==l2) {
					swap(clauses2.back().S[i], clauses2.back().S.back());
					clauses2.back().S.pop_back();
					break;
				}
			}
		}
	}

	vector<int> toRemove;
	vector<vector<int> > nClauses;
	pi.removeClause(pi.litClauses[litNegation(l1)][0]);
	for (int cc : pi.litClauses[l1]) {
		if (!pi.isClauseRemoved(cc)) {
			pi.removeClause(cc);
			rLog.removeClause(1);
		}
		if (cc != c) {
			nClauses.push_back(vector<int>());
			for (int l : pi.clauses[cc].lit) {
				nClauses.back().push_back(l);
			}
		}
	}
	for (int cc : pi.litClauses[l2]) {
		if (!pi.isClauseRemoved(cc)) {
			pi.removeClause(cc);
			rLog.removeClause(1);
		}
	}
	vector<int> ncids;
	for (auto& nc : newClauses) {
		if (plog) ncids.push_back(pi.clauses.size());
		pi.addClause(nc);
		rLog.removeClause(-1);
	}
	if (plog) plog->binary_core_removal(pi.litClauses[litNegation(l1)][0], pi.litClauses[litNegation(l2)][0], c, clauses1, clauses2, ncids);
	rLog.removeLabel(1);
	trace.removeWeight(pi.clauses[pi.litClauses[litNegation(l2)][0]].weights);
	trace.BCR(l1, l2, nClauses);
	return true;
}

int bcrc = 0;

int Preprocessor::doBCR() {
	rLog.startTechnique(Log::Technique::BCR);
	int removed = 0;
	if (!rLog.requestTime(Log::Technique::BCR)) {
		rLog.stopTechnique(Log::Technique::BCR);
		return 0;
	}
	if (plog  && plogDebugLevel>=1) plog->comment("start BCR");
	vector<int> checkVar = pi.tl.getTouchedVariables("BCR");
	if (rLog.isTimeLimit()) {
		auto cmp = [&](int var1, int var2) {
			return pi.litClauses[negLit(var1)].size() + pi.litClauses[posLit(var1)].size() < pi.litClauses[negLit(var2)].size() + pi.litClauses[posLit(var2)].size();
		};
		sort(checkVar.begin(), checkVar.end(), cmp);
	}
	for (int var : checkVar) {
		if (!pi.isLabelVar(var)) continue;
		if (pi.slabelPolarity(var) == VAR_UNDEFINED) continue;
		if (pi.isVarRemoved(var)) continue;
		if (!rLog.requestTime(Log::Technique::BCR)) break;

		if (pi.slabelPolarity(var) == VAR_TRUE) {
			if (pi.litClauses[posLit(var)].size() > 1) continue;
			assert(pi.litClauses[posLit(var)].size() == 1);
			for (int c : pi.litClauses[negLit(var)]) {
				if (pi.clauses[c].lit.size() != 2) continue;
				const int l1 = pi.clauses[c].lit[0];
				const int l2 = pi.clauses[c].lit[1];
				const int v1 = litVariable(l1);
				const int v2 = litVariable(l2);
				if (pi.labelIndexMask(v2) != pi.labelIndexMask(v1)) continue;
				if (pi.slabelPolarity(v1) != litPolarity(litNegation(l1)) || pi.slabelPolarity(v2) != litPolarity(litNegation(l2))) continue;
				if (!pi.wEqual(pi.labelLitWeights(litNegation(l1)), pi.labelLitWeights(litNegation(l2)))) continue;
				if (tryBCR(c, negLit(var))) {
					removed++;
					break;
				}
			}
		} else if(pi.slabelPolarity(var) == VAR_FALSE) {
			if (pi.litClauses[negLit(var)].size() > 1) continue;
			assert(pi.litClauses[negLit(var)].size() == 1);
			for (int c : pi.litClauses[posLit(var)]) {
				if (pi.clauses[c].lit.size() != 2) continue;
				const int l1 = pi.clauses[c].lit[0];
				const int l2 = pi.clauses[c].lit[1];
				const int v1 = litVariable(l1);
				const int v2 = litVariable(l2);
				if (pi.labelIndexMask(v2) != pi.labelIndexMask(v1)) continue;
				if (pi.slabelPolarity(v1) != litPolarity(litNegation(l1)) || pi.slabelPolarity(v2) != litPolarity(litNegation(l2))) continue;
				if (!pi.wEqual(pi.labelLitWeights(litNegation(l1)), pi.labelLitWeights(litNegation(l2)))) continue;
				if (tryBCR(c, posLit(var))) {
					removed++;
					break;
				}
			}
		}
		else{
			assert(0);
		}
	}
	log(removed, " labels removed by BCR");

	if (plog && plogDebugLevel>=1) {
		plog->comment("BCR finished, ", removed, " labels removed");
		if (plogDebugLevel>=4) plogLogState();
	}

	rLog.stopTechnique(Log::Technique::BCR);
	return removed;
}

void Preprocessor::doBCR2() {
	for (int i = 0; i < pi.vars; i++) {
		if (!pi.isLabelVar(i) && !pi.isVarRemoved(i)) {
			if (pi.slabelPolarity(i) == VAR_TRUE) {
				if (pi.litClauses[posLit(i)].size()>1) continue;
				assert(pi.litClauses[posLit(i)].size() == 1);
				for (int c : pi.litClauses[negLit(i)]) {
					if (pi.clauses[c].lit.size() != 2) continue;
					const int l1 = pi.clauses[c].lit[0];
					const int l2 = pi.clauses[c].lit[1];
					const int v1 = litVariable(l1);
					const int v2 = litVariable(l2);
					if (pi.labelIndexMask(v2) != pi.labelIndexMask(v1)) continue;
					if (pi.slabelPolarity(v1) != litPolarity(litNegation(l1)) || pi.slabelPolarity(v2) != litPolarity(litNegation(l2))) continue;
					if (!pi.wEqual(pi.labelLitWeights(litNegation(l1)), pi.labelLitWeights(litNegation(l2)))) continue;
					if (tryBCR(c, negLit(i))) {
						print("FAIL BCR ", i);
						abort();
					}
				}
			} else if(pi.slabelPolarity(i) == VAR_FALSE) {
				if (pi.litClauses[negLit(i)].size()>1) continue;
				assert(pi.litClauses[negLit(i)].size() == 1);
				for (int c : pi.litClauses[posLit(i)]) {
					if (pi.clauses[c].lit.size() != 2) continue;
					const int l1 = pi.clauses[c].lit[0];
					const int l2 = pi.clauses[c].lit[1];
					const int v1 = litVariable(l1);
					const int v2 = litVariable(l2);
					if (pi.labelIndexMask(v2) != pi.labelIndexMask(v1)) continue;
					if (pi.slabelPolarity(v1) != litPolarity(litNegation(l1)) || pi.slabelPolarity(v2) != litPolarity(litNegation(l2))) continue;
					if (!pi.wEqual(pi.labelLitWeights(litNegation(l1)), pi.labelLitWeights(litNegation(l2)))) continue;
					if (tryBCR(c, posLit(i))) {
						print("FAIL BCR ", i);
						abort();
					}
				}
			}
			else{
				assert(0);
			}
		}
	}
}
