// Label hardening, uses SAT-solver-calls to find models...



int Preprocessor::tryHARD() {
	assert(pi.objectives == 1);
	vector<pair<uint64_t, int> > labels;
	for (int lit=0; lit<2*pi.vars; ++lit) {
		if (pi.isVarRemoved(litVariable(lit))) continue;
		if (pi.isLitLabel(lit)) {
			labels.push_back({pi.labelWeight(litVariable(lit), 0), lit});
		}
	}
	sort(labels.begin(), labels.end());

	vector<bool> best_model;

	uint64_t best_cost = findGoodModel(best_model, opt.HARD_asearchIterLimit, opt.HARD_improveTimeLimit, opt.HARD_satLikeTries, opt.HARD_satLikeTimeLimit);

	vector<pair<int, int> > unit_vids;
	if (plog && labels.size() && labels.back().F>best_cost) {
		vector<pair<int, int> > model_witness;
		int tci = 0;
		for (int i=0; i<pi.vars; ++i) {
			if (pi.isVarRemoved(i)) continue;
			if (best_model[i]) model_witness.emplace_back(posLit(i), -1);
			else               model_witness.emplace_back(negLit(i), -1);
		}
		tci = plog->add_ub_constraint_on_weight(best_cost, model_witness, 0);
		for (int i=(int)labels.size()-1;i>=0 && labels[i].F>best_cost;--i) 	unit_vids.emplace_back(plog->add_rup_clause_({labels[i].S}, 1), labels[i].S);
		if (plog && tci) plog->delete_clause_vid(tci);
	}

	int removed=0;
	int removedLabels=0;
	for (int i=(int)labels.size()-1;i>=0 && labels[i].F>best_cost;--i) {
		int vid = -1;
		if (plog) vid = unit_vids[labels.size()-1-i].F;
		removed+=setVariable(labels[i].S, vid);
		++removedLabels;
	}
	for (auto& uc : unit_vids) plog->delete_clause_vid(uc.F, uc.S);

	rLog.removeLabel(removedLabels);
	log("Hardening done, removed ", removedLabels, " labels, ", removed, " clauses.");
	return removedLabels;
}




int Preprocessor::doHARD() {
	assert(pi.objectives == 1);
	rLog.startTechnique(Log::Technique::HARD);
	if (!rLog.requestTime(Log::Technique::HARD)) {
		rLog.stopTechnique(Log::Technique::HARD);
		return 0;
	}
	if (plog && plogDebugLevel>=1) plog->comment("start HARD");

	stats["doHARD"]+=1;


	int hardened = 0;
	if (rLog.requestTime(Log::Technique::HARD)) hardened = tryHARD();

	if (plog && plogDebugLevel>=1) {
		plog->comment("HARD finished, ", hardened, " objective variables hardened.");
		if (plogDebugLevel>=4) plogLogState();
	}

	rLog.stopTechnique(Log::Technique::HARD);
	return hardened;
}
