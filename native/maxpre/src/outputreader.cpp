#include <iostream>
#include <sstream>
#include <vector>
#include <cstdint>

#include "outputreader.hpp"
#include "global.hpp"

using namespace std;
namespace maxPreprocessor {

int OutputReader::readSolution(istream& input, int outputFormat) {
	status = 0;
	string line;
	while (getline(input, line)) {
		if (line[0] == 'o') {
			stringstream ss;
			ss<<line;
			string temp;
			ss>>temp;
			ss>>ansW;
		}
		if (line[0] == 's' || line[0] == 'S') { // actually upper case is not valid format, but....
			stringstream ss;
			ss<<line;
			string s;
			while (ss>>s) {
				if (s == "UNSATISFIABLE") {
					status = 2;
				}
				if (s == "OPTIMUM") {
					status = 1;
				}
			}
		}
		if (line[0] == 'v') {
		    if (outputFormat==INPUT_FORMAT_WPMS22) {
			    stringstream ss;
			    ss<<line;
			    string lits;
			    ss>>lits; ss>>lits;
			    trueLits.clear();
			    for (int i=0; i<(int)lits.size(); ++i) {
		            if (lits[i]=='0')      trueLits.push_back(-i-1);
		            else if (lits[i]=='1') trueLits.push_back(i+1);
			    }
	        } else {
			    stringstream ss;
			    ss<<line;
			    string temp;
			    ss>>temp;
			    int lit;
			    trueLits.clear();
			    while (ss>>lit) {
				    trueLits.push_back(lit);
			    }
			}
		}
	}
	if (status == 0) return 1;
	return 0;
}

}
