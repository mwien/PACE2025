map<string, string> getFlags(int argc, char* argv[]) {
	map<string, string> ret;
	int i0=3;
	if (argc>2 && argv[2][0]=='-') i0=2;
	for (int i = i0; i < argc; i++) {
		string s(argv[i]);
		if (s.size() == 0 || s[0] != '-') {
			cout<<"c Invalid arg "<<s<<endl;
			cerr<<"Invalid arg "<<s<<endl;
		}
		else {
			int p = -1;
			int prd = 0;
			for (int j = 0; j < (int)s.size(); j++) {
				if (s[j] == '=') {
					p = j;
					break;
				}
				if (j == prd && s[j] == '-') prd++;
			}
			if (p == -1) {
				ret[s.substr(prd)] = "";
			}
			else {
				ret[s.substr(prd, p-prd)] = s.substr(p+1);
			}
		}
	}
	return ret;
}

int parseInt(string& s) {
	if (s=="inf") return ~(1<<31);
	if (s=="-inf") return (1<<31);
	stringstream ss;
	ss<<s;
	int r;
	ss>>r;
	return r;
}
unsigned parseUnsigned(string& s) {
	if (s=="inf") return ~(0u);
	stringstream ss;
	ss<<s;
	unsigned r;
	ss>>r;
	return r;
}
bool parseBool(string& s) {
	if (s=="1") return 1;
	if (s=="0" || s=="false" || s=="False" || s=="FALSE") return 0;
	return 1;
}
double parseDouble(string& s) {
	if (s=="inf") return 1e9;
	if (s=="-inf") return -(1e9);
	stringstream ss;
	ss<<s;
	int r;
	ss>>r;
	return r;
}
double parseUint64(string& s) {
	if (s=="inf") return ~(0ull);
	stringstream ss;
	ss<<s;
	uint64_t r;
	ss>>r;
	return r;
}

string parseTechniques(map<string, string>& flags, int verb, int iverb) {
	string techniques = "[bu]#[buvsrgc]";
	if (flags.count("techniques")) {
		techniques = flags["techniques"];
		if (iverb>0) cout<<"c Techniques "<<techniques<<endl;
		if (verb>0)  cerr<<"Techniques "<<techniques<<endl;
	}
	else {
		if (iverb>0) cout<<"c No -techniques= given, defaulting to "<<techniques<<endl;
		if (verb>0)  cerr<<"No -techniques= given, defaulting to "<<techniques<<endl;
	}
	return techniques;
}

double parseTimeLimit(map<string, string>& flags, int verb, int iverb) {
	double timeLimit = 1e9;
	if (flags.count("timelimit")) {
		stringstream ss;
		ss<<flags["timelimit"];
		ss>>timeLimit;
		if (iverb>0) cout<<"c Preprocess time limit "<<timeLimit<<endl;
		if (verb>0)  cerr<<"Preprocess time limit "<<timeLimit<<endl;
	}
	else {
		if (iverb>0) cout<<"c No -timelimit= given, defaulting to inf"<<endl;
		if (verb>0)  cerr<<"No -timelimit= given, defaulting to inf"<<endl;
	}
	return timeLimit;
}

bool parseBVEgate(map<string, string>& flags, int verb, int iverb) {
	bool BVEgate = false;
	if (flags.count("bvegate")) {
		if (flags["bvegate"] == "1") {
			BVEgate = true;
			if (iverb>0) cout<<"c BVE gate extraction enabled"<<endl;
			if (verb>0)  cerr<<"BVE gate extraction enabled"<<endl;
		}
		else if (flags["bvegate"] == "0") {
			BVEgate = false;
			if (iverb>0) cout<<"c BVE gate extraction disabled"<<endl;
			if (verb>0)  cerr<<"BVE gate extraction disabled"<<endl;
		}
		else {
			if (iverb>0) cout<<"c Invalid bvegate flag"<<endl;
			cerr<<"Invalid bvegate flag"<<endl;
			exit(0);
		}
	}
	else {
		if (iverb>0) cout<<"c No -bvegate= given, defaulting to disabled"<<endl;
		if (verb>0)  cerr<<"No -bvegate= given, defaulting to disabled"<<endl;
	}
	return BVEgate;
}

bool parseLabelMatching(map<string, string>& flags, int verb, int iverb) {
	bool labelMatching = false;
	if (flags.count("matchlabels")) {
		if (flags["matchlabels"] == "1") {
			labelMatching = true;
			if (iverb>0) cout<<"c Label matching enabled"<<endl;
			if (verb>0)  cerr<<"Label matching enabled"<<endl;
		}
		else if (flags["matchlabels"] == "0") {
			labelMatching = false;
			if (iverb>0) cout<<"c Label matching disabled"<<endl;
			if (verb>0)  cerr<<"Label matching disabled"<<endl;
		}
		else {
			if (iverb>0) cout<<"c Invalid matchlabels flag"<<endl;
			cerr<<"Invalid matchlabels flag"<<endl;
			exit(0);
		}
	}
	else {
		if (iverb>0) cout<<"c No -matchlabels given, defaulting to disabled"<<endl;
		if (verb>0)  cerr<<"No -matchlabels given, defaulting to disabled"<<endl;
	}
	return labelMatching;
}

int parseProblemType(map<string, string>& flags, int verb, int iverb) {
	int problemType = 1;
	if (flags.count("problemtype")) {
		for (char& c : flags["problemtype"]) {
			c = tolower(c);
		}
		if (flags["problemtype"] == "sat") {
			problemType = 0;
			if (iverb>0) cout<<"c Problem type is SAT"<<endl;
			if (verb>0)  cerr<<"Problem type is SAT"<<endl;
		}
		else if (flags["problemtype"] == "maxsat" || flags["problemtype"] == "max-sat") {
			problemType = 1;
			if (iverb>0) cout<<"c Problem type is Max-SAT"<<endl;
			if (verb>0)  cerr<<"Problem type is Max-SAT"<<endl;
		}
		else if (flags["problemtype"] == "biobj" || flags["problemtype"] == "multiobj" || flags["problemtype"] == "moo" || flags["problemtype"] == "mcnf") {
			problemType = 2;
			if (iverb>0) cout<<"c Problem type is multiobjective optimization"<<endl;
			if (verb>0)  cerr<<"Problem type is multiobjective optimization"<<endl;
		}
		else {
			if (iverb>0) cout<<"c Invalid problemtype flag"<<endl;
			cerr<<"Invalid problemtype flag"<<endl;
			exit(0);
		}
	}
	else {
		if (iverb>0) cout<<"c No -problemtype given, defaulting to Max-SAT"<<endl;
		if (verb>0)  cerr<<"No -problemtype given, defaulting to Max-SAT"<<endl;
	}
	return problemType;
}

int parseSkipTechnique(map<string, string>& flags, int verb, int iverb) {
	int skipTechnique = 0;
	if (flags.count("skiptechnique")) {
		stringstream ss;
		ss<<flags["skiptechnique"];
		ss>>skipTechnique;
		if (iverb>0) cout<<"c Skiptechnique "<<skipTechnique<<endl;
		if (verb>0)  cerr<<"Skiptechnique "<<skipTechnique<<endl;

		if (skipTechnique <= 0 || skipTechnique > 1000000000) {
			if (iverb>0) cout<<"c Invalid skiptechnique flag"<<endl;
			cerr<<"Invalid skiptechinque flag"<<endl;
			exit(0);
		}
	}
	else {
		if (iverb>0) cout<<"c No -skiptechnique given, defaulting to disabled"<<endl;
		if (verb>0)  cerr<<"No -skiptechnique given, defaulting to disabled"<<endl;
	}
	return skipTechnique;
}

bool parseBVEsortMaxFirst(map<string, string>& flags, int verb, int iverb) {
  bool BVEsortMaxFirst = false;
  if (flags.count("bvesortmaxfirst")) {
    if (flags["bvesortmaxfirst"] == "1") {
      BVEsortMaxFirst = true;
      if (iverb>0) cout<<"c BVEsortMaxFirst enabled"<<endl;
      if (verb>0)  cerr<<"BVEsortMaxFirst enabled"<<endl;
    }
    else if (flags["bvesortmaxfirst"] == "0") {
      BVEsortMaxFirst = false;
      if (iverb>0) cout<<"c BVEsortMaxFirst disabled"<<endl;
      if (verb>0)  cerr<<"BVEsortMaxFirst disabled"<<endl;
    }
    else {
      if (iverb>0) cout<<"c Invalid bvesortmaxfirst flag"<<endl;
      cerr<<"Invalid bvesortmaxfirst flag"<<endl;
      exit(0);
    }
  }
  else {
    if (iverb>0) cout<<"c No -bvesortmaxfirst given, defaulting to disabled"<<endl;
    if (verb>0)  cerr<<"No -bvesortmaxfirst given, defaulting to disabled"<<endl;
  }
  return BVEsortMaxFirst;
}

int parseBVElocalGrow(map<string, string>& flags, int verb, int iverb) {
  int BVElocalGrow = 0;
  if (flags.count("bvelocalgrow")) {
    stringstream ss;
    ss<<flags["bvelocalgrow"];
    ss>>BVElocalGrow;
    if (iverb>0) cout<<"c BVElocalgrow "<<BVElocalGrow<<endl;
    if (verb>0)  cerr<<"BVElocalgrow "<<BVElocalGrow<<endl;

    if (BVElocalGrow <= 0 || BVElocalGrow > 1000000000) {
      if (iverb>0) cout<<"c Invalid bvelocalgrow flag"<<endl;
      cerr<<"Invalid bvelocalgrow flag"<<endl;
      exit(0);
    }
  }
  else {
    if (iverb>0) cout<<"c No -bvelocalgrow given, defaulting to disabled"<<endl;
    if (verb>0)  cerr<<"No -bvelocalgrow given, defaulting to disabled"<<endl;
  }
  return BVElocalGrow;
}

int parseBVEglobalGrow(map<string, string>& flags, int verb, int iverb) {
  int BVEglobalGrow = 0;
  if (flags.count("bveglobalgrow")) {
    stringstream ss;
    ss<<flags["bveglobalgrow"];
    ss>>BVEglobalGrow;
    if (iverb>0) cout<<"c BVEglobalgrow "<<BVEglobalGrow<<endl;
    if (verb>0)  cerr<<"BVEglobalgrow "<<BVEglobalGrow<<endl;

    if (BVEglobalGrow <= 0 || BVEglobalGrow > 1000000000) {
      if (iverb>0) cout<<"c Invalid bveglobalgrow flag"<<endl;
      cerr<<"Invalid bveglobalgrow flag"<<endl;
      exit(0);
    }
  }
  else {
    if (iverb>0) cout<<"c No -bveglobalgrow given, defaulting to disabled"<<endl;
    if (verb>0)  cerr<<"No -bveglobalgrow given, defaulting to disabled"<<endl;
  }
  return BVEglobalGrow;
}

int parseProofNoOutput(map<string, string>& flags, int verb, int iverb) {
	if (flags.count("proof-no-output")) {
		if (iverb>0) cout<<"c -proof-no-output option activate:."<<endl;
		if (verb>0)  cerr<<"Activated -proof-no-output option activate."<<endl;
		return 1;
	}
	return 0;
}




// common variable parsing
void parseIntVars(map<string, string>& flags, map<string, int>& intVars, int verb, int iverb) {
	for (auto& v : intVars) {
		const string& key=v.first;
		if (flags.count(key)) {
			intVars[key]=parseInt(flags[key]);
			if (iverb>0) cout << "c " << key << " " << intVars[key] << endl;
			if (verb>0)  cerr << key << " " << intVars[key] << endl;
		}
	}
}
void parseBoolVars(map<string, string>& flags, map<string, bool>& boolVars, int verb, int iverb) {
	for (auto& v : boolVars) {
		const string& key=v.first;
		if (flags.count(key)) {
			boolVars[key]=parseBool(flags[key]);
			if (iverb>0) cout << "c " << key << " " << boolVars[key] << endl;
			if (verb>0)  cerr << key << " " << boolVars[key] << endl;
		}
	}
}
void parseDoubleVars(map<string, string>& flags, map<string, double>& doubleVars, int verb, int iverb) {
	for (auto& v : doubleVars) {
		const string& key=v.first;
		if (flags.count(key)) {
			doubleVars[key]=parseDouble(flags[key]);
			if (iverb>0) cout << "c " << key << " " << doubleVars[key] << endl;
			if (verb>0)  cerr << key << " " << doubleVars[key] << endl;
		}
	}
}
void parseUint64Vars(map<string, string>& flags, map<string, uint64_t>& uint64Vars, int verb, int iverb) {
	for (auto& v : uint64Vars) {
		const string& key=v.first;
		if (flags.count(key)) {
			uint64Vars[key]=parseUint64(flags[key]);
			if (iverb>0) cout << "c " << key << " " << uint64Vars[key] << endl;
			if (verb>0)  cerr << key << " " << uint64Vars[key] << endl;
		}
	}
}



pair<unsigned, unsigned> parseSizeLimit(map<string, string>& flags, int verb, int iverb) {
	pair<unsigned, unsigned> sizeLimit={0,~0u};
	if (flags.count("sizelimit")) {
		stringstream ss;
		ss<<flags["sizelimit"];
		string t1;
		string t2;
		getline(ss, t1, '-');
		getline(ss, t2, '-');
		sizeLimit.first=parseUnsigned(t1);
		sizeLimit.second=parseUnsigned(t2);
		if (iverb>0) cout<<"c sizeLimit: "<< (sizeLimit.first==(~0u)?"inf":to_string(sizeLimit.first)) << "-" << (sizeLimit.second==(~0u)?"inf":to_string(sizeLimit.second)) <<endl;
		if (verb>0)  cerr<<"sizeLimit: "<< (sizeLimit.first==(~0u)?"inf":to_string(sizeLimit.first)) << "-" << (sizeLimit.second==(~0u)?"inf":to_string(sizeLimit.second)) <<endl;
	}
	return sizeLimit;
}

string parsePrepFilename(map<string, string>& flags, int verb, int iverb) {
	if (flags.count("prepfile")) {
		if (iverb>0) cout << "c prepfile " << flags["prepfile"] << endl;
		if (verb>0)  cerr << "prepfile " << flags["prepfile"] << endl;
		return flags["prepfile"];
	}
	return "preprocessed.wcnf";
}

string parseSolFilename(map<string, string>& flags, int verb, int iverb) {
	if (flags.count("solfile")) {
		if (iverb>0) cout << "c solfile " << flags["solfile"] << endl;
		if (verb>0)  cerr << "solfile " << flags["solfile"] << endl;
		return flags["solfile"];
	}
	return "sol0.sol";
}

string parseProofFilename(map<string, string>& flags, int verb, int iverb) {
	if (flags.count("proof")) {
		if (flags["proof"]=="") flags["proof"]="proof.pbp";
		if (iverb>0) cout << "c proof " << flags["proof"] << endl;
		if (verb>0)  cerr << "proof " << flags["proof"] << endl;
		return flags["proof"];
	}
	return "";
}

int parseProofDebugLevel(map<string, string>& flags, int verb, int iverb) {
	if (flags.count("proof-debug")) {
		if (flags["proof-debug"]=="") return 0;
		stringstream ss;
		ss<<flags["proof-debug"];
		int rv;
		ss>>rv;
		return rv;
	}
	return 0;
}


int parseVerb(map<string, string>& flags) {
	int verb = 0;
	if (flags.count("verb")) {
		if (flags["verb"] == "0") {
			verb = 0;
		}
		else if (flags["verb"] == "1") {
			verb = 1;
		}
		else if (flags["verb"] == "2") {
			verb = 2;
		}
		else {
			cout<<"c Invalid verb flag"<<endl;
			cerr<<"Invalid verb flag"<<endl;
			exit(0);
		}
		if (verb>0) {
			cout<<"c Verb "<<verb<<endl;
			cerr<<"Verb "<<verb<<endl;
		}
	}
	else {
		cout<<"c No -verb given, defaulting to "<<verb<<endl;
		cerr<<"No -verb given, defaulting to "<<verb<<endl;
	}
	return verb;
}

int parseVerbInstance(map<string, string>& flags) {
  return !flags.count("nc");
}


int parseIOFormat(string option, string v, int defaultValue, int autoValue, int verb, int iverb) {
	int ioformat = defaultValue;

	if (v == "auto")	{
		if (autoValue==-1) {
			cout << "c " << option << " option 'auto' not available with the selected mode" << endl;
			cout << option << " option 'auto' not available with the selected mode" << endl;
		} else {
			ioformat = autoValue;
		}
	}

	else if (v == "wpms")   ioformat = maxPreprocessor::INPUT_FORMAT_WPMS;
	else if (v == "wpms22") ioformat = maxPreprocessor::INPUT_FORMAT_WPMS22;
	else if (v == "sat")    ioformat = maxPreprocessor::INPUT_FORMAT_SAT;
	else if (v == "moo" || v == "mcnf" || v == "biobj" || v == "multiobj") ioformat = maxPreprocessor::INPUT_FORMAT_WMOO;
	else {
		cout << "c invalid " << option << " value " << v << endl;
		cerr << "Invalid  " << option << "value " << v << endl;
	}


	if (ioformat == maxPreprocessor::INPUT_FORMAT_MS) {
		// preprocessor works in labeled cnf so it cannot output pure maxsat
		ioformat = maxPreprocessor::INPUT_FORMAT_WPMS;
	}
	string outf;
	if (ioformat == maxPreprocessor::INPUT_FORMAT_WPMS) {
		outf = "weighted partial Max-SAT (pre 2022)";
	}
	else if (ioformat == maxPreprocessor::INPUT_FORMAT_SAT) {
		outf = "SAT";
	}
	else if (ioformat == maxPreprocessor::INPUT_FORMAT_WPMS22) {
		outf = "weighted partial Max-SAT (2022 ->)";
	}
	else if (ioformat == maxPreprocessor::INPUT_FORMAT_WMOO) {
		outf = "multiobjective optimization";
	}
	else {
		return 0;
	}
	if (iverb>0) cout<<"c " << option << " " << outf <<endl;
	if (verb>0)  cerr<< option << outf << endl;
	return ioformat;
}

int parseOutputFormat(map<string, string>& flags, int defaultValue, int autoValue, int verb, int iverb) {
	if (flags.count("outputformat")) return parseIOFormat("outputformat", flags["outputformat"], defaultValue, autoValue, verb, iverb);
	return defaultValue;
}

int parseSolutionFormat(map<string, string>& flags, int defaultValue, int autoValue, int verb, int iverb) {
	if (flags.count("solutionformat")) return parseIOFormat("solutionformat", flags["solutionformat"], defaultValue, autoValue, verb, iverb);
	return defaultValue;
}

int parseSolverSolutionFormat(map<string, string>& flags, int defaultValue, int autoValue, int verb, int iverb) {
	if (flags.count("solversolutionformat")) return parseIOFormat("solversolutionformat", flags["solversolutionformat"], defaultValue, autoValue, verb, iverb);
	return defaultValue;
}

void printHelp(ostream& out, map<string, int>& intVars, map<string, bool>& boolVars, map<string, double>& doubleVars, map<string, uint64_t> uint64Vars, bool shrt, bool veryshort) {
	out<<"The first argument is the instance file, the second is preprocess, reconstruct or solve."<<endl;
	out<<endl;

	out<<"An example of using the preprocessor:"<<endl;
	out<<"\t./preprocessor test.wcnf preprocess -techniques=[bu]#[buvsrg] -mapfile=test.map > preprocessed.wcnf"<<endl;
	out<<"\t./solver < preprocessed.wcnf > sol0.sol"<<endl;
	out<<"\t./preprocessor sol0.sol reconstruct -mapfile=test.map > solution.sol"<<endl;
	out<<endl;
	if (!shrt) {
		out<<"Another way to do the same thing:"<<endl;
		out<<"\t./preprocessor test.wcnf solve -solver=./solver -techniques=[bu]#[buvsrg] > solution.sol"<<endl;
		out<<endl;
	}
	if (veryshort) return;
	out<<"Parameters:"<<endl;
	out<<endl;

	out<<"-techniques (default: [bu]#[buvsrgc])"<<endl;
	if (!shrt) {
		out<<"\tstring:"<<endl;
		out<<"\tThis string defines the preprocessing techniques to use and the order of them."<<endl;
		out<<"\tEach letter corresponds to a preprocessing technique. Each preprocessing technique is applied until its fixpoint."<<endl;
		out<<"\tTechniques inside brackets are applied until all of them are in fixpoint. The brackets work recursively. "<<endl;
		out<<"\tIf # character is given, all techniques before it are applied before group detection and adding labels (techniques available before labeling are BCE, UP and SE)."<<endl;
		out<<"\tTechniques:"<<endl;
	}
	if (veryshort) return;
	out<<"\tb = blocked clause elimintation"<<endl;
	out<<"\tu = unit propagation"<<endl;
	out<<"\tv = bounded variable elimination"<<endl;
	out<<"\ts = subsumption elimination"<<endl;
	out<<"\tr = self subsuming resolution"<<endl;
	out<<"\tl = subsumed label elimintion"<<endl;
	out<<"\tc = binary core removal"<<endl;
	out<<"\ta = bounded variable addition"<<endl;
	out<<"\tg = generalized subsumed label elimination"<<endl;
	out<<"\te = equivalence elimination"<<endl;
	out<<"\th = unhiding techniques on binary implication graph (failed literals, hidden tautology elimination, hidden literal elimination)"<<endl;
	out<<"\tt = structure labeling"<<endl;
	out<<"\tG = intrinsic atmost1 constraints"<<endl;
	out<<"\tT = TrimMaxSat"<<endl;
	out<<"\tV = TrimMaxsat based backbone detection"<<endl;
	out<<"\tH = hardening"<<endl;
	out<<"\tR = failed literal elimination + unhiding (extended with redundancy detection)"<<endl;
	if (!shrt) out<<endl;

	out<<"-proof (default: disabled)"<<endl;
	if (!shrt) {
		out<<"\tstring:"<<endl;
		out<<"\tLog proof to file"<<endl;
		out<<endl;
	}

	out<<"-proof-no-output (default: disabled)"<<endl;
	if (!shrt) {
		out<<"\tIf option -proof-no-output is used, the proof ends with ``output EQUIOPTIMAL IMPLICIT``, and the proof will not rename the variables."<<endl;
		out<<endl;
	}

	out<<"-solver (default: disabled)"<<endl;
	if (!shrt) {
		out<<"\tstring:"<<endl;
		out<<"\tThe solver to use to solve the preprocessed instance"<<endl;
		out<<endl;
	}
	out<<"-solverflags (default: disabled)"<<endl;
	if (!shrt) {
		out<<"\tstring:"<<endl;
		out<<"\tThe flags to use with the solver"<<endl;
		out<<"\tFor example -solver=./LMHS -solverflags=\"--infile-assumps --no-preprocess\" results in using the command ./LMHS preprocessed.wcnf --infile-assumps --no-preprocess > sol0.sol"<<endl;
		out<<endl;
	}
	out<<"-mapfile (default: disabled)"<<endl;
	if (!shrt) {
		out<<"\tstring:"<<endl;
		out<<"\tThe file to write the solution reconstruction map"<<endl;
		out<<endl;
	}
	out<<"-problemtype (default: maxsat)"<<endl;
	if (!shrt) {
		out<<"\tstring: {maxsat, sat, mcnf}"<<endl;
		out<<"\tShould the problem be preprocessed as a MaxSAT or SAT instance"<<endl;
		out<<endl;
	}
	out<<"-outputformat (default: auto)"<<endl;
	if (!shrt) {
		out<<"\tstring: {auto, wpms, wpms22, sat, mcnf}"<<endl;
		out<<"\tBy default the preprocessor always gives the output in weighted partial MaxSAT format"<<endl;
		out<<"\tOption 'auto' sets the format according to input file format."<<endl;
		out<<endl;
	}
	out<<"-solutionformat (default: wpms22 on reconstruct mode, auto on solve mode)"<<endl;
	if (!shrt) {
		out<<"\tstring: {auto, wpms, wpms22}"<<endl;
		out<<"\tThe format in which the solution is printed when 'solve' or 'reconstruct' mode is used."<<endl;
		out<<"\tOption 'auto' sets the format according to the outputformat value."<<endl;
		out<<endl;
	}
	out<<"-solversolutionformat (default: wpms22 on reconstruct mode, auto on solve mode)"<<endl;
	if (!shrt) {
		out<<"\tstring: {auto, wpms, wpms22}"<<endl;
		out<<"\tThe format in which the solver outputs its solution (when 'solve' or 'reconstruct' mode is used). "<<endl;
		out<<"\tOption 'auto' sets the format according to the outputformat value."<<endl;
		out<<endl;
	}
	out<<"-timelimit (default: inf)"<<endl;
	if (!shrt) {
		out<<"\tdouble: [0, 500000000]"<<endl;
		out<<"\tLimit for preprocessing time in seconds"<<endl;
		out<<endl;
	}
	out<<"-skiptechnique (default: disabled)"<<endl;
	if (!shrt) {
		out<<"\tint: [1, 1000000000]"<<endl;
		out<<"\tSkip a preprocessing technique if it seems to be not effective in x tries (x is given in this flag)"<<endl;
		out<<"\tRecommended values for this could be something between 10 and 1000"<<endl;
		out<<endl;
	}
	out<<"-matchlabels (default: 0)"<<endl;
	if (!shrt) {
		out<<"\tbool: {0, 1}"<<endl;
		out<<"\tUse label matching technique to reduce the number of labels"<<endl;
		out<<endl;
	}
	out<<"-bvegate (default: 0)"<<endl;
	if (!shrt) {
		out<<"\tbool: {0, 1}"<<endl;
		out<<"\tUse BVE gate extraction to extend BVE"<<endl;
		out<<"\tNote: applying BCE will destroy all recognizable gate structures"<<endl;
		out<<endl;
	}
	out<<"-sizelimit (default: 0-inf)"<<endl;
	if (!shrt) {
		out<<"\tstring: int-int, range for ints [0, 2^32-1], constant inf=2^32-1"<<endl;
		out<<"\tUse preprocessing only if the number of clauses in the instance is on the given range"<<endl;
		out<<"\tFor example -sizelimit=1000000-inf skips preprocessing when there are less than a million clauses on the instance"<<endl;
		out<<endl;
	}
	out<<"-ignore-exit-code (default: not set)"<<endl;
	if (!shrt) {
		out<<"\tBy default if MaxSAT solver exits with a nonzero exit code, maxpre will halt and any solution of the solver is ignored."<<endl;
		out<<"\tUse flag -ignore-exit-code to ignore the exit value of the MaxSAT solver and try to parse and analyze the result anyways."<<endl;
		out<<endl;
	}
	out<<"-prepfile (default: preprocessed.wcnf)"<<endl;
	if (!shrt) {
		out<<"\tstring"<<endl;
		out<<"\tSet the auxiliary file into which the preprocessed instance is saved when type solve is used."<<endl;
		out<<endl;
	}
	out<<"-solfile (default: sol0.sol)"<<endl;
	if (!shrt) {
		out<<"\tstring"<<endl;
		out<<"\tSet the auxiliary file into which the output of the MaxSAT solver is piped when type solve is used."<<endl;
		out<<endl;
	}


	out<<"-verb (default: 0)"<<endl;
	if (!shrt) {
		out<<"\tint: [0, 1, 2]"<<endl;
		out<<"\tControls the amount of information printed to standard error."<<endl;
	}
	out<<endl;

	out<<"-nc (default: disabled)"<<endl;
	if (!shrt) {
		out<<"\tIf -nc flag is used, the output instance will not contain comments about the preprocessor statistics"<<endl;
	}
	out<<endl;

	if (intVars.size()) {
		if (!shrt) out<<"Following integer values"<<endl;
		for (auto& s : intVars) out<<(shrt?"":"\t")<<"-"<<s.first<<" (default: "<<s.second<<")"<<endl;
		if (!shrt) out << endl;
	}
	if (boolVars.size()) {
		if (!shrt) out<<"Following boolean values"<<endl;
		for (auto& s : boolVars) out<<(shrt?"":"\t")<<"-"<<s.first<<" (default: "<<(s.second?"true":"false")<<")"<<endl;
		if (!shrt) out << endl;
	}
	if (doubleVars.size()) {
		if (!shrt) out<<"Following double values"<<endl;
		out << std::fixed << setprecision(1);
		for (auto& s : doubleVars) out<<(shrt?"":"\t")<<"-"<<s.first<<" (default: "<<s.second<<")"<<endl;
		if (!shrt) out << endl;
	}
	if (uint64Vars.size()) {
		if (!shrt) out<<"Following uint64 values"<<endl;
		for (auto& s : uint64Vars) out<<(shrt?"":"\t")<<"-"<<s.first<<" (default: "<<s.second<<")"<<endl;
		if (!shrt) out << endl;
	}
}

int isHelp(char* arg) {
	return string(arg) == "-help" || string(arg) == "--help" || string(arg) == "-h" || string(arg) == "--h";
}
