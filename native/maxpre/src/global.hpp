#ifndef MAXPP_GLOBAL_HPP
#define MAXPP_GLOBAL_HPP

#include <cstdint>

namespace maxPreprocessor {
const uint64_t HARDWEIGHT = (uint64_t)1 << (uint64_t)63;

const int VAR_UNDEFINED = 0;
const int VAR_TRUE = 1;
const int VAR_FALSE = 2;

const int INPUT_FORMAT_WPMS = 1;	// pre-22 wcnf file format
const int INPUT_FORMAT_MS = 2;	  // cnf maximum satisfiability
const int INPUT_FORMAT_SAT = 3;	  // cnf sat
const int INPUT_FORMAT_WPMS22 = 4;// 22 wcnf file format
const int INPUT_FORMAT_WMOO = 5;  // multiobjective optimization file format


inline int litValue(int x) {
	return !(x&1);
}
inline int litPolarity(int x) { // VAR_TRUE if TRUE, VAR_FALSE if FALSE
	return 2-litValue(x);
}

inline int litVariable(int x) {
	return (x>>1);
}
inline int litNegation(int x) {
	return x^1;
}

inline int posLit(int x) {
	return x<<1;
}
inline int negLit(int x) {
	return (x<<1)^1;
}
}
#endif
