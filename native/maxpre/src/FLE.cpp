// Failed and redundant literal detection and elimination
// equivalence detection and redundant equivalence detection
//  (x->y and neg(x)->neg(y))
// implied value detection and redundant implied value detection
//  (x->y and neg(x)->y)
inline bool commonLitExists(const vector<int>& a, const vector<int>& b, int ignore1 = -1, int ignore2 = -1) {
	// assumes a and b are sorted
	if (a.size() < b.size()) {
		for (int l : a) {
			if (l==ignore1 || l==ignore2) continue;
			if (binary_search(b.begin(), b.end(), l)) return 1;
		}
	} else {
		for (int l : b) {
			if (l==ignore1 || l==ignore2) continue;
			if (binary_search(a.begin(), a.end(), l)) return 1;
		}
	}
	return 0;
}


inline void push_sorted(vector<int>& vec, int v) {
	vec.push_back(0);
	for (int i = vec.size() - 1; i>0; --i) {
		if (vec[i-1] > v) vec[i] = vec[i-1];
		else {
			vec[i] = v;
			return;
		}
	}
	vec[0] = v;
}

bool Preprocessor::testBinaryFPR(int x, int y, const vector<int>& up_neg_x, const vector<int>& up_neg_y, bool fullFilter, int& vid) {
	//test if {x, y} is redunant clause
	if (binary_search(up_neg_x.begin(), up_neg_x.end(), y) || binary_search(up_neg_y.begin(), up_neg_y.end(), x)) {
		if (plog) vid = plog->add_rup_clause_({x, y}, 1);
		return 1;
	}

	bool negX=0;
	bool negXY = 0;
	bool XnegY = 0;
	bool negXnegY = 0;
	for (int c : pi.litClauses[litNegation(x)]) {
		if (commonLitExists(up_neg_y, pi.clauses[c].lit, litNegation(x), litNegation(y))) continue;
		if (commonLitExists(up_neg_x, pi.clauses[c].lit, litNegation(x), litNegation(y))) continue;

		if (fullFilter) {
			vector<int> a(pi.clauses[c].lit);
			bool fy = 0;
			for (int& l : a) {
				if (litVariable(l) == litVariable(y)) {
					fy = 1;
					l = litNegation(y);
				} else if (l != litNegation(x)) l = litNegation(l);
			}
			if (!fy) a.push_back(litNegation(y));
			if (!satSolver->testUPConflict(a)) continue; // was unsat, untouched(c) is implied, clause can be filtered
		}
		if (binary_search(pi.clauses[c].lit.begin(), pi.clauses[c].lit.end(), y)) {
			negXY = 1;
			if (negXnegY) negX = 1;
		} else if (binary_search(pi.clauses[c].lit.begin(), pi.clauses[c].lit.end(), litNegation(y))) {
			negXnegY = 1;
			if (negXY) negX = 1;
		} else {
			negX = 1;
		}
	}
	if (!negXY && !negX) {
		if (plog) vid = plog->add_red_clause_({x, y}, x, 1);
		return 1;
	}
	for (int c : pi.litClauses[litNegation(y)]) {
		if (commonLitExists(up_neg_x, pi.clauses[c].lit, litNegation(x), litNegation(y))) continue;
		if (commonLitExists(up_neg_y, pi.clauses[c].lit, litNegation(x), litNegation(y))) continue;

		if (fullFilter) {
			vector<int> a(pi.clauses[c].lit);
			bool fx = 0;
			for (int& l : a) {
				if (litVariable(l) == litVariable(x)) {
					fx = 1;
					l = litNegation(x);
				} else if (l != litNegation(y)) l = litNegation(l);
			}
			if (!fx) a.push_back(litNegation(x));
			if (!satSolver->testUPConflict(a)) continue; // was unsat, untouched(c) is implied, clause can be filtered
		}
		if (binary_search(pi.clauses[c].lit.begin(), pi.clauses[c].lit.end(), x)) {
			if (negX) return 0;
			XnegY = 1;
		} else if (binary_search(pi.clauses[c].lit.begin(), pi.clauses[c].lit.end(), litNegation(x))) {
			if (negXY && XnegY) return 0;
			if (negXY) negX = 1;
		} else {
			if (negX || negXY) return 0; // this check is actually redundant...
		}
	}
	if (plog) {
		if (negXY && XnegY)      vid = plog->add_red_clause_({x, y}, {{x, -1}, {y, -1}}, 1); // x=1, y=1 satisfies
		else if (negX || negXY)  vid = plog->add_red_clause_({x, y}, y, 1);                 // y=1
		else                     vid = plog->add_red_clause_({x, y}, x, 1);                 // x=1
	}
	return 1;
}


bool Preprocessor::testBinaryRedundancy(int x, int y, const vector<int>& up_neg_x, const vector<int>& eqLits, int redTechniques, int& vid) {
	assert(!pi.isVarRemoved(litVariable(x)));
	assert(!pi.isVarRemoved(litVariable(y)));
	bool allsat=1;
	for (int c : pi.litClauses[litNegation(y)]) {
		if (!commonLitExists(up_neg_x, pi.clauses[c].lit, litNegation(y))) {
			allsat=0;
			break;
		}
	}
	if (allsat) {
		stats["FLE_binRED_UP"]+=1;
		if (plog) vid = plog->add_red_clause_({x, y}, y, 1);
		return 1;
	}
	if (!redTechniques) return 0;

	if (redTechniques&1) {
		vector<int> up_neg_y;
		if (redTechniques&2) {
			vector<int> a={litNegation(y)};
			if (!satSolver->propagate(a, up_neg_y)) {
				stats["FLE_success_accidental"]+=1;
				rLog.removeVariable(1);
				satSolver->addClause(y);
				int tci = -1;
				if (plog) plog->add_rup_clause_({y}, 1);
				rLog.removeClause(setVariable(y, tci));
				if (plog) plog->delete_clause_vid(tci, litNegation(x));
				return 0;
			}
			sort(up_neg_y.begin(), up_neg_y.end());
		}
		if (testBinaryFPR(x, y, up_neg_x, up_neg_y, redTechniques&4, vid)) {
			stats["FLE_binRED_FPR"]+=1;
			return 1;
		}
	}
	if (!(redTechniques&8)) return 0;
	if (!rLog.requestTime(Log::Technique::FLE)) return 0;
	vector<int> tmp;
	vector<int> cl={x, y};
	if (cl[0]>cl[1]) swap(cl[0], cl[1]);
	if (checkExtendedPositiveReduct(cl, tmp, eqLits)) {
		stats["FLE_binRED_extFPR"]+=1;
		return 1;
	}
	return 0;
}


int Preprocessor::tryFLE(int lit, vector<int>& up, bool doRLE) {
	vector<int> a={lit};
	if (!satSolver->propagate(a, up)) {
		stats["FLE_FLE_success"]+=1;
		if (pi.isLabelVar(litVariable(lit))) {
			rLog.removeLabel(1);
		} else {
			rLog.removeVariable(1);
		}
		satSolver->addClause(litNegation(lit));
		int tci = -1;
		if (plog) tci = plog->add_rup_clause_({litNegation(lit)}, 1);
		int removed = setVariable(litNegation(lit), tci);
		if (plog) plog->delete_clause_vid(tci, litNegation(lit));
		rLog.removeClause(removed);
		return 1;
	}
	bool flit=0;
	for (unsigned i=0; i<up.size(); ++i) {
		if (pi.isVarRemoved(litVariable(up[i]))) {
			up[i--]=up.back();
			up.pop_back();
			continue;
		}
		if (up[i]==lit) flit=1;
	}
	if (!flit) up.push_back(lit);

	sort(up.begin(), up.end());

	assert(binary_search(up.begin(), up.end(), lit));

	if (doRLE && !pi.isLitLabel(lit)) {
		bool allsat = 1;
		for (int c : pi.litClauses[lit]) {
			if (!commonLitExists(up, pi.clauses[c].lit, lit)) {
				allsat=0;
				break;
			}
		}
		if (allsat) {
			stats["FLE_RLE_success"]+=1;
			if (pi.isLabelVar(litVariable(lit))) rLog.removeLabel(1);
			else                                 rLog.removeVariable(1);
			satSolver->addClause(litNegation(lit));
			int tci = -1;
			if (plog) tci = plog->add_red_clause_({litNegation(lit)}, litNegation(lit), 1);
			int removed = setVariable(litNegation(lit), tci);
			if (plog) plog->delete_clause_vid(tci, litNegation(lit));
			rLog.removeClause(removed);
			return 1;
		}
	}
	return 0;
}

void Preprocessor::replaceLit(int l, int lit) {
	// replace l with lit on every clause
	// handles also labels
	vector<int> clauses = pi.litClauses[l];
	bool objective_changed = 0;
	for (int c : clauses) {
		if (!pi.clauses[c].isHard()) {
			assert(pi.clauses[c].lit.size() == 1);
			// handling labels
			if (pi.isLabelVar(litVariable(lit))) {
				bool label_clause_added = 0;
				if (pi.isLitLabel(litNegation(lit))) {
					int cl = pi.litClauses[litNegation(lit)][0];
					vector<uint64_t> wc = pi.substractWeights(cl, c);
					trace.removeWeight(wc);
					if (plog) {
						objective_changed = 1;
						plog->set_soft_clause_weight(c, pi.clauses[c].weight(0));
						plog->set_soft_clause_weight(cl, pi.clauses[cl].weight(0));
						plog->add_to_obj_constant(wc[0]);
					}
					if (pi.clauses[cl].isWeightless()) {
						if (!pi.isLitLabel(lit) && !pi.clauses[c].isWeightless()) {
							// make lit label (reuse -lit label clause)
							pi.replaceLiteralInClause(litNegation(lit), lit, cl);
							swap(pi.litClauses[lit][0], pi.litClauses[lit].back());
							pi.updateLabelMask(litVariable(lit));
							label_clause_added = 1;
							if (plog) plog->map_unit_soft(cl, lit);
						} else pi.removeClause(cl);
					}
				}
				if (!pi.clauses[c].isWeightless()) {
					if (!pi.isLitLabel(lit) && !label_clause_added) {
						pi.addClause({lit}, {0});
						swap(pi.litClauses[lit][0], pi.litClauses[lit].back());
						plog->map_unit_soft(pi.litClauses[lit][0], lit);
					}

					int cl = pi.litClauses[lit][0];
					pi.pourAllWeight(c, cl);
					if (plog) {
						objective_changed = 1;
						plog->set_soft_clause_weight(c, pi.clauses[c].weight(0));
						plog->set_soft_clause_weight(cl, pi.clauses[cl].weight(0));
					}
				}
				pi.updateLabelMask(litVariable(lit));
				pi.removeClause(c);
			} else {
				// make lit a label
				pi.replaceLiteralInClause(l, lit, c);
				swap(pi.litClauses[lit][0], pi.litClauses[lit].back());
				pi.updateLabelMask(litVariable(lit));
				if (plog) {
					objective_changed = 1;
					plog->map_unit_soft(c, lit);
				}
			}
			pi.unLabel(litVariable(l));
			continue;
		}

		// handling nonlabels

		if (binary_search(pi.clauses[c].lit.begin(), pi.clauses[c].lit.end(), litNegation(lit))) {
			if (plog) plog->delete_red_clause(c);
			pi.removeClause(c);
		} else if (binary_search(pi.clauses[c].lit.begin(), pi.clauses[c].lit.end(), lit)) {
			pi.removeLiteralFromClause(l, c);
			if (plog) plog->clause_updated(c, pi.clauses[c].lit);
		} else {
			pi.replaceLiteralInClause(l, lit, c);
			if (plog) plog->clause_updated(c, pi.clauses[c].lit);
		}
	}
	if (plog && objective_changed) plog->log_current_objective();
}

void Preprocessor::handleEqLits(int uplit, vector<int>& lits) {
	int liti=0;
	// select uplit
	for (int i=0; i<(int)lits.size(); ++i) if (lits[i]==uplit || lits[i]==litNegation(uplit)) {liti=i; break;}
	/*		// this is disabled, as it may cause the prooflogging to fail: UP implying x=y and x=z does not mean UP implies y=z...
		// select from lits the variable that has most clauses
	int nofcl=pi.litClauses[lits[0]].size()+pi.litClauses[litNegation(lits[0])].size();
	for (unsigned i=1; i<lits.size(); ++i) {
		if (pi.litClauses[lits[i]].size() + pi.litClauses[litNegation(lits[i])].size() > (unsigned)nofcl) {
			nofcl=pi.litClauses[lits[i]].size() + pi.litClauses[litNegation(lits[i])].size();
			liti=i;
		}
	}
	*/

	int lit=lits[liti];
	lits[liti]=lits.back(); lits.pop_back();

	// replace all other variables with the selected one
	vector<int> clauses;
	for (int l : lits) {
		if (pi.isLabelVar(litVariable(l))) {
			rLog.removeLabel(1);
		} else {
			rLog.removeVariable(1);
		}

		int tci1 = 0;
		int tci2 = 0;
		if (plog) {
			tci1 = plog->add_rup_clause_({{litNegation(l), lit}}, 1);
			tci2 = plog->add_rup_clause_({{l, litNegation(lit)}}, 1);
		}
		replaceLit(l, lit);
		replaceLit(litNegation(l), litNegation(lit));
		// on sat solver, only add l->lit and neg(l)->neg(lit)
		if (plog) {
			plog->delete_clause_vid(tci1, litNegation(l));
			plog->delete_clause_vid(tci2, l);
		}

		trace.setEqual(lit, l);
		assert(pi.isVarRemoved(litVariable(l)));
	}
}


int Preprocessor::tryFLE(int var, bool doRLE, bool findImplied, bool findRedImplied, bool findEqs, bool findRedEqs, int redTechniques) {
	assert(findImplied || !findRedImplied);
	assert(findEqs || !findRedEqs);
	vector<int> up1;
	vector<int> up2;
	if (tryFLE(posLit(var), up1, doRLE)) return 1;
	if (tryFLE(negLit(var), up2, doRLE)) return 1;
	vector<int> eqs;
	set<int> uvars;

	assert(binary_search(up2.begin(), up2.end(), negLit(var)));
	assert(binary_search(up1.begin(), up1.end(), posLit(var)));

	int removed=0;
	if (up1.size() < up2.size() && (findEqs || findImplied)) {
		for (int l : up1) {
			if (findEqs && binary_search(up2.begin(), up2.end(), litNegation(l))) {
				eqs.push_back(l);
				uvars.insert(litVariable(l));
				if (l!=posLit(var)) stats["FLE_Eqs"]+=1;
			} else if (findImplied && binary_search(up2.begin(), up2.end(), l)) {
				satSolver->addClause(l);
				if (pi.isLabelVar(litVariable(l))) rLog.removeLabel(1);
				else                               rLog.removeVariable(1);
				int tci = -1;
				if (plog) {
					int tci1 = plog->add_rup_clause_({posLit(var), l}, 0);
					int tci2 = plog->add_rup_clause_({negLit(var), l}, 0);
					tci = plog->resolve_clauses_vid(tci1, tci2, 1);
					plog->delete_clause_vid(tci1);
					plog->delete_clause_vid(tci2);
				}
				removed+=setVariable(l, tci);
				if (plog) plog->delete_clause_vid(tci, l);
				uvars.insert(litVariable(l));
				stats["FLE_ImpliedValues"]+=1;
			}
		}
	} else if (findEqs || findImplied) {
		for (int l : up2) {
			if (findEqs && binary_search(up1.begin(), up1.end(), litNegation(l))) {
				eqs.push_back(litNegation(l));
				uvars.insert(litVariable(l));
				if (l!=negLit(var)) stats["FLE_Eqs"]+=1;
			}
			if (findImplied && binary_search(up1.begin(), up1.end(), l)) {
				int tci = -1;
				if (plog) {
					int tci1 = plog->add_rup_clause_({posLit(var), l}, 0);
					int tci2 = plog->add_rup_clause_({negLit(var), l}, 0);
					tci = plog->resolve_clauses_vid(tci1, tci2, 1);
					plog->delete_clause_vid(tci1);
					plog->delete_clause_vid(tci2);
				}
				satSolver->addClause(l);
				if (pi.isLabelVar(litVariable(l))) rLog.removeLabel(1);
				else                               rLog.removeVariable(1);
				removed+=setVariable(l, tci);
				if (plog) plog->delete_clause_vid(tci, l);
				uvars.insert(litVariable(l));
				stats["FLE_ImpliedValues"]+=1;
			}
		}
	}

	if ((findRedEqs || findRedImplied) && !pi.isLabelVar(var)) {
		int vid;
		for (int l : up1) {
			if (l==posLit(var)) continue;
			if (uvars.count(litVariable(l))) continue;
			if (pi.isLabelVar(litVariable(l))) continue;
			if (pi.isVarRemoved(litVariable(l))) continue;
			if (findRedImplied) {
				// lit -> l   is known
				// check if neg(lit) -> l is redundant
				if (testBinaryRedundancy(posLit(var), l, up2, eqs, redTechniques, vid)) {
					int tci = -1;
					if (plog) {
						int tci1 = plog->add_rup_clause_({negLit(var), l}, 0);
						tci = plog->resolve_clauses_vid(tci1, vid, 1);
						plog->delete_clause_vid(tci1);
					}
					satSolver->addClause(l);
					uvars.insert(litVariable(l));
					rLog.removeVariable(1);
					removed+=setVariable(l, tci);
					if (plog) {
						plog->delete_clause_vid(vid, l);
						plog->delete_clause_vid(tci, l);
					}
					continue;
				}
			}
			if (pi.isVarRemoved(litVariable(l))) continue;
			if (findRedEqs) {
				// lit -> l is known
				// check if neg(lit) -> neg(l) is redundant
				if (testBinaryRedundancy(posLit(var), litNegation(l), up2, eqs, redTechniques, vid)) {
					satSolver->addClause(posLit(var), litNegation(l));
					if (posLit(var)<litNegation(l))	pi.addClause({posLit(var), litNegation(l)});
					else                            pi.addClause({litNegation(l), posLit(var)});
					if (plog) plog->map_clause(pi.clauses.size()-1, vid, 1);
					push_sorted(up2, litNegation(l));
					uvars.insert(litVariable(l));
					eqs.push_back(l);
					stats["FLE_RedEqs"]+=1;
				}
			}
		}
		for (int l : up2) {
			if (l==negLit(var)) continue;
			if (uvars.count(litVariable(l))) continue;
			if (pi.isLabelVar(litVariable(l))) continue;
			if (pi.isVarRemoved(litVariable(l))) continue;
			if (findRedImplied) {
				// neg(lit) -> l is known
				// check if lit -> l is redundant
				if (testBinaryRedundancy(negLit(var), l, up1, eqs, redTechniques, vid)) {
					int tci = -1;
					if (plog) {
						int tci1 = plog->add_rup_clause_({posLit(var), l}, 0);
						tci = plog->resolve_clauses_vid(tci1, vid, 1);
						plog->delete_clause_vid(tci1);
					}
					satSolver->addClause(l);
					uvars.insert(litVariable(l));
					rLog.removeVariable(1);
					removed+=setVariable(l, tci);
					if (plog) {
						plog->delete_clause_vid(vid, l);
						plog->delete_clause_vid(tci, l);
					}
					continue;
				}
			}
			if (pi.isVarRemoved(litVariable(l))) continue;
			if (findRedEqs) {
				// neg(lit) -> l is known
				// check if lit -> neg(l) is redundant
				if (testBinaryRedundancy(negLit(var), litNegation(l), up1, eqs, redTechniques, vid)) {
					satSolver->addClause(negLit(var), litNegation(l));
					if (negLit(var)<litNegation(l))	pi.addClause({negLit(var), litNegation(l)});
					else                            pi.addClause({litNegation(l), negLit(var)});
					if (plog) plog->map_clause(pi.clauses.size()-1, vid, 1);
					push_sorted(up1, litNegation(l));
					eqs.push_back(litNegation(l));
					uvars.insert(litVariable(l));
				}
			}
		}
	}

	rLog.removeClause(removed);
	bool returnValue = removed;
	if (eqs.size()>1) {
		handleEqLits(posLit(var), eqs); // Similar technique proposed in Probing-Based Preprocessing Techniquesfor Propositional Satisfiability, Inˆes Lynce and Jo ̃ao Marques-Silva, 2003
		eqs.clear();
		returnValue = 1;
	}

	// neighbourhood PR clause technique
	if (redTechniques>>4 && !pi.isVarRemoved(var)) {
		set<int> neighbourhood;
		for (int l : up1) {
			if (pi.isVarRemoved(litVariable(l))) continue;
			for (int c : pi.litClauses[l]) {
				for (int lit : pi.clauses[c].lit) {
					if (pi.isLabelVar(litVariable(lit))) continue;
					neighbourhood.insert(litVariable(lit));
				}
			}
		}
		for (int l : up1) neighbourhood.erase(litVariable(l));
		neighbourhood.erase(var);

		for (int v : neighbourhood) {
			if (!rLog.requestTime(Log::Technique::FLE)) break;
			int vid;
			if (testBinaryRedundancy(negLit(var), negLit(v), up1, eqs, redTechniques>>4, vid)) {
				satSolver->addClause(negLit(var), negLit(v));
				if (var<v) pi.addClause({negLit(var), negLit(v)});
				else		   pi.addClause({negLit(v), negLit(var)});

				push_sorted(up1, negLit(v));

				stats["FLE_RED"]+=1;
				returnValue = 1;
			}
			if (pi.isVarRemoved(v)) continue;
			if (testBinaryRedundancy(negLit(var), posLit(v), up1, eqs, redTechniques>>4, vid)) {
				satSolver->addClause(negLit(var), posLit(v));
				if (var<v) pi.addClause({negLit(var), posLit(v)});
				else		   pi.addClause({posLit(v), negLit(var)});

				push_sorted(up1, posLit(v));
				stats["FLE_RED"]+=1;
				returnValue = 1;
			}
		}

		neighbourhood.clear();
		for (int l : up2) {
			if (pi.isVarRemoved(litVariable(l))) continue;
			for (int c : pi.litClauses[l]) {
				if (!pi.clauses[c].isHard()) continue;
				for (int lit : pi.clauses[c].lit) {
					if (pi.isLabelVar(litVariable(l))) continue;
					neighbourhood.insert(litVariable(lit));
				}
			}
		}
		for (int l : up2) neighbourhood.erase(litVariable(l));
		neighbourhood.erase(var);

		for (int v : neighbourhood) {
			if (!rLog.requestTime(Log::Technique::FLE)) break;
			int vid;
			if (testBinaryRedundancy(posLit(var), negLit(v), up2, eqs, redTechniques>>4, vid)) {
				satSolver->addClause(posLit(var), negLit(v));
				if (var<v) pi.addClause({posLit(var), negLit(v)});
				else       pi.addClause({negLit(v), posLit(var)});

				push_sorted(up2, negLit(v));

				stats["FLE_RED"]+=1;
				returnValue = 1;
			}
			if (pi.isVarRemoved(v)) continue;
			if (testBinaryRedundancy(posLit(var), posLit(v), up2, eqs, redTechniques>>4, vid)) {
				satSolver->addClause(posLit(var), posLit(v));
				if (var<v)	pi.addClause({posLit(var), posLit(v)});
				else 				pi.addClause({posLit(v), posLit(var)});

				push_sorted(up2, posLit(v));

				stats["FLE_RED"]+=1;
				returnValue = 1;
			}
		}
	}

	return returnValue;
}





int Preprocessor::doFLE(bool doRLE, bool findImplied, bool findRedImplied, bool findEqs, bool findRedEqs, int redTechniques) {
	rLog.startTechnique(Log::Technique::FLE);
	if (!rLog.requestTime(Log::Technique::FLE)) {
		rLog.stopTechnique(Log::Technique::FLE);
		return 0;
	}
	if (plog && plogDebugLevel>=1) plog->comment("start FLE");
	if (redTechniques) {
	    while (fleActiveTechniques != redTechniques && (stats["FLE_stop_position"]+1)*opt.FLE_redTechniquesActivate > __builtin_popcount(fleActiveTechniques)) {
		    fleActiveTechniques |= (((redTechniques^fleActiveTechniques)-1) & redTechniques) ^ redTechniques;
	    }
	    redTechniques = fleActiveTechniques;
	}

	prepareSatSolver();

	stats["FLE_FLE_success"]+=0;
	stats["FLE_success_accidental"]+=0;
	stats["FLE_RLE_success"]+=0;
	stats["FLE_Eqs"]+=0;
	stats["FLE_RedEqs"]+=0;
	stats["FLE_ImpliedValues"]+=0;
	stats["FLE_RedImpliedValues"]+=0;
	stats["FLE_binRED_UP"]+=0;
	stats["FLE_binRED_FPR"]+=0;
	stats["FLE_binRED_extFPR"]+=0;
	stats["FLE_RED"]+=0;



	int removed=0;
	stats["doFLE"]+=1;
	vector<int> tvars =  pi.tl.getTouchedVariables("FLE");
	sort(tvars.begin(), tvars.end());
	vector<int> svars;
	for (int vvar=0; vvar<pi.vars; ++vvar) {
		int var=vvar+flePos;
		if (var>=pi.vars) var-=pi.vars;
		if (pi.isVarRemoved(var)) continue;
		if (!binary_search(tvars.begin(), tvars.end(), var)) {
			svars.push_back(var);
			continue;
		}

		if (!rLog.requestTime(Log::Technique::FLE)) {
			flePos=var;
			stats["FLE_stop_position"]+=float(vvar-svars.size())/pi.vars;
			rLog.stopTechnique(Log::Technique::FLE);
			return removed;
		}
		removed += tryFLE(var, doRLE, findImplied, findRedImplied, findEqs, findRedEqs, redTechniques);
	}

	for (unsigned i=0; i<svars.size(); ++i) {
		int var=svars[i];
		if (pi.isVarRemoved(var)) continue;
		if (!rLog.requestTime(Log::Technique::FLE)) {
			flePos=var;
			stats["FLE_stop_position"]+=float(pi.vars-svars.size()-i)/pi.vars;
			rLog.stopTechnique(Log::Technique::FLE);
			return removed;
		}
		removed += tryFLE(var, doRLE, findImplied, findRedImplied, findEqs, findRedEqs, redTechniques);
	}

	stats["FLE_stop_position"]+=1;

	if (plog && plogDebugLevel>=1) {
		 plog->comment("FLE finished");
		if (plogDebugLevel>=4) plogLogState();
	}

	rLog.stopTechnique(Log::Technique::FLE);
	return removed;
}
