#ifndef MAXPP_PREPROCESSEDINSTANCE_HPP
#define MAXPP_PREPROCESSEDINSTANCE_HPP

#include <vector>
#include <iostream>
#include <cstdint>

namespace maxPreprocessor {
class PreprocessedInstance {
public:
	std::vector<std::vector<int> > clauses;
	std::vector<int> clause_cids;
	std::vector<std::vector<uint64_t> > weightsv;
	std::vector<uint64_t> weights;
	std::vector<std::pair<int, std::vector<uint64_t> > > labels;
};
}
#endif
