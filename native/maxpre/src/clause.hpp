#ifndef MAXPP_CLAUSE_HPP
#define MAXPP_CLAUSE_HPP

#include <vector>
#include <cstdint>

namespace maxPreprocessor {
class ClauseIter;
class ConstClauseIter;

class Clause {
public:
	std::vector<int> lit;
	std::vector<uint64_t> weights;
	// note: if weight vector is empty, clause is HARD
	// if weight vector has a value (other than HARDWEIGHT) for some objective, values for all other objectives are assumed to be 0
	// weight vector should never have some value set to HARDWEIGHT and some other value to something else:
	// a clause is either HARD (it must be satisfied) or SOFT (not satisfying incurs a cost) even if there are more than one objective
	uint64_t hash;

	void updateHash();
	bool isHard() const;
	bool isWeightless() const;
	uint64_t weight(int objective) const;
	void addWeight(uint64_t w, int objective);
	void setWeight(uint64_t w, int objective);

	void makeHard();
	void addLiteral(int lit);
	void removeLiteral(int lit);
	void replaceLiteral(int lit1, int lit2);
	Clause (std::vector<int> literals_, std::vector<uint64_t> weight_);
};
}
#endif
