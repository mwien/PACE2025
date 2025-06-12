void Preprocessor::GSLEBT(int i, uint64_t w, vector<bool>& sel, vector<uint64_t>& weights, vector<vector<int> >& hs, bool& found, uint64_t& itLim) {
	if (i == (int)hs.size()) {
		found = true;
		return;
	}
	if (itLim == 0) {
		return;
	}
	itLim--;
	bool f = false;
	for (int l : hs[i]) {
		if (sel[l]) {
			f = true;
			break;
		}
	}
	if (f) {
		GSLEBT(i + 1, w, sel, weights, hs, found, itLim);
	}	else {
		for (int l : hs[i]) {
			if (weights[l] > w) continue;
			sel[l] = 1;
			GSLEBT(i + 1, w - weights[l], sel, weights, hs, found, itLim);
			if (found) return;
			sel[l] = 0;
		}
	}
}

bool Preprocessor::GSLEtryBackTrack(vector<vector<int> >& hs, vector<uint64_t>& weights, uint64_t w, uint64_t itLim, vector<bool>& sel) {
	if (hs.size() == 0) return true;
	bool found = false;
	found = false;
	int tries = opt.GSLE_tries;
	for (int l : hs[0]) {
		if (weights[l] > w) continue;
		uint64_t lm = itLim;
		sel[l] = 1;
		GSLEBT(1, w - weights[l], sel, weights, hs, found, lm);
		if (found) break;
		sel[l] = 0;
		tries--;
		if (tries < 0) break;
	}
	return found;
}

int Preprocessor::tryGSLE(int lb, int objective) {
	uint64_t lw = pi.labelWeight(litVariable(lb), objective);
	for (int c : pi.litClauses[lb]) {
		bool f = false;
		for (int l : pi.clauses[c].lit) {
			if (l != lb && pi.isLitLabel(litNegation(l), objective) && pi.labelWeight(litVariable(l), objective) <= lw && pi.labelIndexMask(litVariable(l)) == (1<<objective)) {
				f = true;
				break;
			}
		}
		if (!f) {
			return 0;
		}
	}
	vector<vector<int> > hs;
	set<int> sel;
	uint64_t selW = 0;
	for (int c : pi.litClauses[lb]) {
		vector<int> s;
		for (int l : pi.clauses[c].lit) {
			if (l != lb && pi.isLitLabel(litNegation(l), objective) && pi.labelWeight(litVariable(l), objective) <= lw && pi.labelIndexMask(litVariable(l)) == (1<<objective)) {
				bool ok = true; // if neg(l) is in a clause other than soft {neg(l)} and neg(lb) is not in that clause, don't check var(l)
				for (unsigned i=1; i<pi.litClauses[litNegation(l)].size();++i) {
					if (!binary_search(pi.clauses[pi.litClauses[litNegation(l)][i]].lit.begin(), pi.clauses[pi.litClauses[litNegation(l)][i]].lit.end(), litNegation(lb))) {
						ok = false;
						break;
					}
				}
				if (ok) s.push_back(litVariable(l));
			}
		}
		if (!s.size()) return 0;
		hs.push_back(s);
	}
	for (auto& s : hs) {
		if (s.size() == 1) {
			if (sel.count(s[0]) == 0) {
				sel.insert(s[0]);
				selW += pi.labelWeight(s[0], objective);
				if (selW > lw) return 0;
			}
		}
	}
	vector<vector<int> > hss;
	uint64_t hsl = 0;
	for (auto& s : hs) {
		if (s.size() > 1) {
			bool f = false;
			for (int l : s) {
				if (sel.count(l) > 0) {
					f = true;
					break;
				}
			}
			if (!f) {
				hss.push_back(s);
				hsl += (uint64_t)(int)s.size();
			}
		}
	}
	auto cmp = [](const vector<int>& a, const vector<int>& b) {
		return a.size() < b.size();
	};
	sort(hss.begin(), hss.end(), cmp);
	// Do coordinate compression
	vector<int> cc;
	for (auto& se : hss) {
		for (int l : se) {
			cc.push_back(l);
		}
	}
	sort(cc.begin(), cc.end());
	cc.erase(unique(cc.begin(), cc.end()), cc.end());
	vector<uint64_t> laWeights(cc.size());
	for (int i = 0; i < (int)cc.size(); i++) {
		laWeights[i] = pi.labelWeight(cc[i], objective);
	}
	for (auto& se : hss) {
		for (int& l : se) {
			l = lower_bound(cc.begin(), cc.end(), l) - cc.begin();
		}
	}
	vector<int> cnt(cc.size());
	for (int i = (int)hss.size() - 1; i >= 0; i--) {
		for (int l : hss[i]) {
			cnt[l]++;
		}
		auto cmp2 = [&](int a, int b) {// the log-approximation heuristic
			return (double)laWeights[a]/(double)cnt[a] < (double)laWeights[b]/(double)cnt[b];
		};
		sort(hss[i].begin(), hss[i].end(), cmp2);
	}
	hsl = min(hsl, (uint64_t)hss.size()*10); // magic constant

	vector<bool> selected(laWeights.size());
	if (GSLEtryBackTrack(hss, laWeights, lw - selW, hsl, selected)) {
		int tci = -1;
		if (plog) {
			vector<pair<int, int> > witness;
			for (int l : sel) witness.emplace_back(pi.labelPolarity(l, objective)==VAR_TRUE?negLit(l):posLit(l), -1);
			for (int i=0; i<(int)selected.size(); ++i) if (selected[i]) witness.emplace_back(pi.labelPolarity(cc[i], objective)==VAR_TRUE?negLit(cc[i]):posLit(cc[i]), -1);
			witness.emplace_back(litNegation(lb), -1);
			vector<int> cl = {litNegation(lb)};
			tci = plog->add_red_clause(cl, witness, 1);
		}
		int rmClauses = setVariable(litNegation(lb), tci);
		if (plog) plog->delete_clause_vid(tci, litNegation(lb));

		assert(pi.isVarRemoved(litVariable(lb)));
		rLog.removeClause(rmClauses);
		rLog.removeLabel(1);
		return 1;
	}
	return 0;
}

int Preprocessor::doGSLE() {
	rLog.startTechnique(Log::Technique::GSLE);
	int removed = 0;
	if (!rLog.requestTime(Log::Technique::GSLE)) {
		rLog.stopTechnique(Log::Technique::GSLE);
		return 0;
	}
	if (plog && plogDebugLevel>=1) plog->comment("start GSLE");
	vector<int> checkVar = pi.tl.getTouchedVariables("GSLE");
	if (rLog.isTimeLimit()) {
		auto cmp = [&](int var1, int var2) {
			return pi.litClauses[negLit(var1)].size() + pi.litClauses[posLit(var1)].size() < pi.litClauses[negLit(var2)].size() + pi.litClauses[posLit(var2)].size();
		};
		sort(checkVar.begin(), checkVar.end(), cmp);
	}
	bool skip = false;
	if (opt.skipTechnique > 0 && (int)checkVar.size() >= opt.skipTechnique * opt.skipSkipConstant) {
		for (int objective = 0; objective < pi.objectives; ++objective) {
			if (!rLog.requestTime(Log::Technique::GSLE)) break;
			for (int tc = 0; tc < opt.skipTechnique; tc++) {
				if (!rLog.requestTime(Log::Technique::GSLE)) break;
				int var = checkVar[getRand(0, (int)checkVar.size() - 1)];
				if (pi.labelIndexMask(var) != (1<<objective)) continue;
				if (pi.isVarRemoved(var)) continue;
				if (pi.labelPolarity(var, objective) == VAR_TRUE && pi.litClauses[negLit(var)].size() == 0){
					int tci = -1;
					if (plog) tci = plog->add_red_clause_({posLit(var)}, posLit(var), 1);
					setVariable(posLit(var), tci);
					if (plog) plog->delete_clause_vid(tci, posLit(var));
					removed++;
					continue;
				}
				if (pi.labelPolarity(var, objective) == VAR_FALSE && pi.litClauses[posLit(var)].size() == 0){
					int tci = -1;
					if (plog) tci = plog->add_red_clause_({negLit(var)}, negLit(var), 1);
					setVariable(negLit(var), tci);
					if (plog) plog->delete_clause_vid(tci, negLit(var));
					removed++;
					continue;
				}

				if (pi.labelPolarity(var, objective) == VAR_TRUE) {
					removed += tryGSLE(negLit(var), objective);
				} else {
					removed += tryGSLE(posLit(var), objective);
				}
			}
		}
		if (removed == 0) {
			skip = true;
			log("GSLE skipped");
		}
	}
	if (!skip) {
		for (int var : checkVar) {
			if (pi.labelObjectives(var) != 1) continue;
			if (pi.isVarRemoved(var)) continue;
			if (!rLog.requestTime(Log::Technique::GSLE)) break;

			int objective = pi.labelObjective(var);
			if (pi.labelPolarity(var, objective) == VAR_TRUE && pi.litClauses[negLit(var)].size() == 0){
				int tci = -1;
				if (plog) tci = plog->add_red_clause_({posLit(var)}, posLit(var), 1);
				setVariable(posLit(var), tci);
				if (plog) plog->delete_clause_vid(tci, posLit(var));
				removed++;
				continue;
			}
			if (pi.labelPolarity(var, objective) == VAR_FALSE && pi.litClauses[posLit(var)].size() == 0){
				int tci = -1;
				if (plog) tci = plog->add_red_clause_({negLit(var)}, negLit(var), 1);
				setVariable(negLit(var), tci);
				if (plog) plog->delete_clause_vid(tci, negLit(var));
				removed++;
				continue;
			}

			if (pi.labelPolarity(var, objective) == VAR_TRUE) {
				removed += tryGSLE(negLit(var), objective);
			} else {
				removed += tryGSLE(posLit(var), objective);
			}
		}
	}

	log(removed, " labels removed by GSLE");

	if (plog && plogDebugLevel>=1) {
		plog->comment("GSLE finished, ", removed, " labels removed");
		if (plogDebugLevel>=4) plogLogState();
	}

	rLog.stopTechnique(Log::Technique::GSLE);
	return removed;
}

void Preprocessor::doGSLE2() {
	vector<int> lbs;
	for (int var = 0; var < pi.vars; var++) {
		if (pi.labelObjectives(var) == 1  && !pi.isVarRemoved(var)) {
			lbs.push_back(var);
		}
	}
	for (int var : lbs) {
		int objective = pi.labelObjective(var);
		if (pi.labelPolarity(var, objective) == VAR_TRUE) {
			if (tryGSLE(negLit(var), objective)) {
				print("fail GSLE");
				print(var + 1);
				abort();
			}
		} else {
			if (tryGSLE(posLit(var), objective)) {
				print("fail GSLE");
				print(var + 1);
				abort();
			}
		}
	}
}
