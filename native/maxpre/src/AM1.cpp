// detect at most one constraints
// using sat solver could actually be replaced here by simple unit propagation as in FLP
// sat solver up might have some overhead

int Preprocessor::tryAM1(vector<int>& bvars, int objective, bool weight_aware, bool stratification, bool greedy_cost) {
	unordered_map<int, set<int> > conns;

	if (greedy_cost) {
		stats["AM1_litFlips"]+=0;
		stats["AM1G_extra"]+=0;
	}

	uint64_t tmaxw = 0;

	int removedClauses = 0;
	vector<int> a={0};
	vector<int> c;

	for (int b : bvars) {
		tmaxw=max(tmaxw, pi.labelWeight(litVariable(b), objective));

		a[0]=b;
		c.clear();

		bool s = satSolver->propagate(a, c, 2);
		if (s) {
			for (int j : c) {
				if (j>b) continue;

				if (!pi.isVarRemoved(litVariable(j)) && pi.isLitLabel(litNegation(j), objective)) {
					conns[litNegation(j)].insert(b);
					conns[b].insert(litNegation(j));
				}
			}
		} else {
			a[0]=litNegation(b);
			satSolver->addClause(a);
			int tci = 0;
			if (plog) tci = plog->add_rup_clause(a, 1);
			removedClauses+=setVariable(litNegation(b), tci);
			if (plog) plog->delete_clause_vid(tci, litNegation(b));

			conns[b].clear();
			rLog.removeLabel(1);
		}
	}

	uint64_t bound = 1;
	uint64_t weights_reduced = 0;
	int am1s = 0;
	if (stratification) bound = tmaxw>>1;
	for (;bound; bound>>=1) {
		for (int b : bvars) {
			if (!conns[b].size()) continue;
			uint64_t minw = pi.labelWeight(litVariable(b), objective);
			if (minw<bound) continue;
			uint64_t maxw = minw;
			vector<int> am1;
			am1.push_back(b);
			for (int b2: conns[b]) {
				if (!conns[b2].size()) continue;
				uint64_t w = pi.labelWeight(litVariable(b2), objective);
				if (w<bound) continue;
				bool fail=0;
				for (unsigned j=1; j<am1.size(); ++j) {
					if (!conns[b2].count(am1[j])) {
						fail=1;
						break;
					}
				}
				if (!fail) {
					am1.push_back(b2);
					if (w<minw) minw=w;
					if (w>maxw) maxw=w;
				}
			}
			if (am1.size()<2) continue;


			vector<pair<int, int> > soft_clauses; // for prooflogging

			uint64_t sumw=0;
			for (int bb : am1) {
				int cc = pi.litClauses[bb][0];
				sumw += pi.clauses[cc].weights[objective];

				if (plog) soft_clauses.emplace_back(cc, cc);

				if (greedy_cost) {
					pi.clauses[cc].weights[objective] -= maxw;
				} else {
					pi.clauses[cc].weights[objective] -= minw;
				}

				if (!weight_aware) conns[bb].clear();

				if (pi.clauses[cc].weights[objective] == 0) {
					conns[bb].clear();
					pi.unLabel(litVariable(bb), objective);
					if (pi.clauses[cc].isWeightless()) {
						pi.removeClause(cc);
						removedClauses++;
					}
					rLog.removeLabel(1);
				} else if ((int64_t)pi.clauses[cc].weights[objective] < 0) {
					conns[bb].clear();

					if (pi.litClauses[litNegation(bb)].size() && pi.isLabelClause(pi.litClauses[litNegation(bb)][0])) {
						int lcl = pi.litClauses[litNegation(bb)][0];
						pi.clauses[lcl].addWeight(-pi.clauses[cc].weights[objective], objective);
						if (plog) soft_clauses.back().S = lcl;
					} else {
						vector<uint64_t> weights(objective+1);
						weights[objective] = -pi.clauses[cc].weights[objective];
						pi.addClause({litNegation(bb)}, weights);
						swap(pi.litClauses[litNegation(bb)][0], pi.litClauses[litNegation(bb)].back());
						removedClauses--;
						if (plog) {
							soft_clauses.back().S = pi.litClauses[litNegation(bb)][0];
							plog->map_unit_soft(pi.litClauses[litNegation(bb)][0], litNegation(bb));
						}
					}

					pi.mkLabel(litVariable(bb), objective, litPolarity(litNegation(bb)));

					pi.clauses[cc].weights[objective] = 0;
					if (pi.clauses[cc].isWeightless()) {
						pi.removeClause(cc);
						removedClauses++;
					}
					stats["AM1_litFlips"]+=1;
				}
			}
			uint64_t removedWeight = 0;
			if (greedy_cost) {
				removedWeight = sumw - maxw;
				stats["AM1G_extra"]+=sumw-maxw-minw*(am1.size()-1);
			} else {
				removedWeight = minw*(am1.size()-1);
			}

			trace.removeWeight(removedWeight, objective);
			weights_reduced += removedWeight;

			sort(am1.begin(), am1.end());

			int nv = pi.addVar();
			am1.push_back(posLit(nv));
			pi.addClause(am1);

			vector<uint64_t> weights(objective+1);
			uint64_t w = greedy_cost ? maxw : minw;
			weights[objective] = w;

			pi.addClause({negLit(nv)}, weights);
			pi.mkLabel(nv, objective, VAR_FALSE);

			if (plog) {
				// add atmost1-clause
				plog->map_clause(pi.clauses.size()-2, plog->add_red_clause(am1, posLit(nv), 1), 1);
				// add new objective variable
				plog->map_unit_soft(pi.litClauses[negLit(nv)][0], negLit(nv));
				// change the objective
				plog->at_most_one(soft_clauses, pi.clauses.size()-2, pi.clauses.size()-1, w);
			}

			rLog.removeClause(-2);
			++am1s;
		}
	}
	rLog.removeClause(removedClauses);
	log(am1s, " at most one -constraints detected by AM1, total weight ", weights_reduced);
	log(removedClauses, " clauses removed by AM1");
	return am1s;
}




int Preprocessor::doAM1(bool weight_aware, bool stratification, bool greedy_cost) {
	rLog.startTechnique(Log::Technique::AM1);
	if (!rLog.requestTime(Log::Technique::AM1)) {
		rLog.stopTechnique(Log::Technique::AM1);
		return 0;
	}
	if (plog && plogDebugLevel>=1) plog->comment("start AM1");

	stats["doAM1"]+=1;

	prepareSatSolver();

	int applied = 0;

	for (int objective=0; objective<pi.objectives; ++objective) {
		vector<int> bvars;
		for (int i=0; i<pi.vars; ++i) {
			if (!pi.isLabelVar(i, objective) || pi.isVarRemoved(i)) continue;
			if (pi.labelPolarity(i, objective) == VAR_TRUE) {
				bvars.push_back(posLit(i));
			} else {
				bvars.push_back(negLit(i));
			}
		}

		if (rLog.requestTime(Log::Technique::AM1)) applied += tryAM1(bvars, objective, weight_aware, stratification, greedy_cost);
	}
	rLog.stopTechnique(Log::Technique::AM1);
	if (plog && plogDebugLevel>=1)

	if (plog && plogDebugLevel>=1) {
		plog->comment("AM1 finished, ", applied, " at most one constraints detected");
		if (plogDebugLevel>=4) plogLogState();
	}

	return applied;
}
