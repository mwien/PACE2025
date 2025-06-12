#include "preprocessorinterface.hpp"

namespace maxPreprocessor {

struct Wrapper {
  PreprocessorInterface *preprocessor{};

  uint64_t top_weight;
  bool inprocess_mode;

  // Input clauses and weights while initializing and preprocessed clauses and
  // weights after preprocessing
  std::vector<std::vector<int>> clauses = {{}};
  std::vector<std::vector<uint64_t>> weights = {{}};

  // Preprocessed labels after preprocessing
  std::vector<int> labels{};
  // Literals fixed after preprocessing
  std::vector<int> fixed{};
  // Weight removed in preprocessing
  std::vector<uint64_t> removed_weight{};

  // Preprocessed assignment to reconstruct. Set of true literals.
  std::vector<int> prepro_assignment{};
  // Reconstructed assignment. This is _not_ a set of true literals but a map
  // indexed by variable indices.
  std::vector<int> reconstr_assignment{};

  // Clause being added via addClause
  std::vector<int> clause{};

  Wrapper(uint64_t top_weight, bool inprocess_mode)
      : top_weight(top_weight), inprocess_mode(inprocess_mode) {}

  ~Wrapper() { delete preprocessor; }
};

static const char *signature =
    "MaxPRE 2.0.3 beta (" GIT_IDENTIFIER ", " __DATE__ " " __TIME__ ")";

} // namespace maxPreprocessor

using namespace maxPreprocessor;

extern "C" {

#include "cpreprocessorinterface.h"

const char *cmaxpre_signature() { return signature; }

CMaxPre *cmaxpre_init_start(uint64_t top_weight, char inprocess_mode) {
  return (CMaxPre *)new Wrapper(top_weight, inprocess_mode != CMAXPRE_FALSE);
}

void cmaxpre_release(CMaxPre *handle) { delete (Wrapper *)handle; }

void cmaxpre_init_add_weight(CMaxPre *handle, uint64_t weight) {
  ((Wrapper *)handle)->weights.back().push_back(weight);
}

void cmaxpre_init_add_lit(CMaxPre *handle, int lit) {
  Wrapper *wrapper = (Wrapper *)handle;
  if (lit) {
    wrapper->clauses.back().push_back(lit);
    return;
  }
  // Finalize current clause
  wrapper->clauses.push_back({});
  wrapper->weights.push_back({});
}

void cmaxpre_init_finalize(CMaxPre *handle) {
  Wrapper *wrapper = (Wrapper *)handle;
  wrapper->clauses.pop_back();
  wrapper->weights.pop_back();
  wrapper->preprocessor =
      new PreprocessorInterface(wrapper->clauses, wrapper->weights,
                                wrapper->top_weight, wrapper->inprocess_mode);
  wrapper->clauses.clear();
  wrapper->weights.clear();
}

void cmaxpre_preprocess(CMaxPre *handle, const char *techniques, int log_level,
                        double time_limit, char add_removed_weight,
                        char sort_labels_frequency) {
  std::string techniques_str = techniques;
  Wrapper *wrapper = (Wrapper *)handle;
  wrapper->preprocessor->preprocess(techniques_str, log_level, time_limit);
  wrapper->preprocessor->getInstance(wrapper->clauses, wrapper->weights,
                                     wrapper->labels,
                                     add_removed_weight != CMAXPRE_FALSE,
                                     sort_labels_frequency != CMAXPRE_FALSE);
  wrapper->fixed = wrapper->preprocessor->getFixed();
  wrapper->removed_weight = wrapper->preprocessor->getRemovedWeight();
}

uint64_t cmaxpre_get_top_weight(CMaxPre *handle) {
  return ((Wrapper *)handle)->preprocessor->getTopWeight();
}

unsigned cmaxpre_get_n_prepro_clauses(CMaxPre *handle) {
  return ((Wrapper *)handle)->clauses.size();
}

uint64_t cmaxpre_get_prepro_weight(CMaxPre *handle, unsigned cl_idx,
                                   unsigned obj_idx) {
  Wrapper *wrapper = (Wrapper *)handle;
  if (cl_idx >= wrapper->weights.size() ||
      obj_idx >= wrapper->weights[cl_idx].size())
    return wrapper->top_weight;
  return ((Wrapper *)handle)->weights[cl_idx][obj_idx];
}

int cmaxpre_get_prepro_lit(CMaxPre *handle, unsigned cl_idx, unsigned lit_idx) {
  Wrapper *wrapper = (Wrapper *)handle;
  if (cl_idx >= wrapper->clauses.size() ||
      lit_idx >= wrapper->clauses[cl_idx].size())
    return 0;
  return ((Wrapper *)handle)->clauses[cl_idx][lit_idx];
}

unsigned cmaxpre_get_n_prepro_labels(CMaxPre *handle) {
  return ((Wrapper *)handle)->labels.size();
}

int cmaxpre_get_prepro_label(CMaxPre *handle, unsigned lbl_idx) {
  Wrapper *wrapper = (Wrapper *)handle;
  if (lbl_idx >= wrapper->labels.size())
    return 0;
  return ((Wrapper *)handle)->labels[lbl_idx];
}

unsigned cmaxpre_get_n_prepro_fixed(CMaxPre *handle) {
  return ((Wrapper *)handle)->fixed.size();
}

int cmaxpre_get_prepro_fixed_lit(CMaxPre *handle, unsigned lit_idx) {
  Wrapper *wrapper = (Wrapper *)handle;
  if (lit_idx >= wrapper->fixed.size())
    return 0;
  return ((Wrapper *)handle)->fixed[lit_idx];
}

void cmaxpre_assignment_reset(CMaxPre *handle) {
  ((Wrapper *)handle)->prepro_assignment.clear();
  ((Wrapper *)handle)->reconstr_assignment.clear();
}

void cmaxpre_assignment_add(CMaxPre *handle, int lit) {
  ((Wrapper *)handle)->prepro_assignment.push_back(lit);
}

void cmaxpre_reconstruct(CMaxPre *handle) {
  Wrapper *wrapper = (Wrapper *)handle;
  std::vector<int> litSet =
      wrapper->preprocessor->reconstruct(wrapper->prepro_assignment);
  wrapper->prepro_assignment.clear();
  // Build reconstructed assignment map
  wrapper->reconstr_assignment.resize(litSet.size() + 1, 0);
  for (int lit : litSet) {
    if (abs(lit) >= wrapper->reconstr_assignment.size())
      wrapper->reconstr_assignment.resize(abs(lit) + 1, 0);
    wrapper->reconstr_assignment[abs(lit)] = lit;
  }
}

int cmaxpre_reconstructed_val(CMaxPre *handle, int lit) {
  Wrapper *wrapper = (Wrapper *)handle;
  if (abs(lit) >= wrapper->reconstr_assignment.size())
    return 0;
  return lit >= 0 ? wrapper->reconstr_assignment[lit]
                  : -wrapper->reconstr_assignment[-lit];
}

int cmaxpre_add_var(CMaxPre *handle, int var) {
  return ((Wrapper *)handle)->preprocessor->addVar(var);
}

char cmaxpre_add_lit(CMaxPre *handle, int lit) {
  Wrapper *wrapper = (Wrapper *)handle;
  if (!lit) {
    bool ret = wrapper->preprocessor->addClause(wrapper->clause);
    wrapper->clause.clear();
    return ret ? CMAXPRE_TRUE : CMAXPRE_FALSE;
  }
  wrapper->clause.push_back(lit);
  return CMAXPRE_TRUE;
}

int cmaxpre_add_label(CMaxPre *handle, int lbl, uint64_t weight) {
  return ((Wrapper *)handle)->preprocessor->addLabel(lbl, weight);
}

char cmaxpre_alter_weight(CMaxPre *handle, int lbl, uint64_t weight) {
  return ((Wrapper *)handle)->preprocessor->alterWeight(lbl, weight);
}

char cmaxpre_label_to_var(CMaxPre *handle, int lbl) {
  return ((Wrapper *)handle)->preprocessor->labelToVar(lbl);
}

char cmaxpre_reset_removed_weight(CMaxPre *handle) {
  return ((Wrapper *)handle)->preprocessor->resetRemovedWeight();
}

uint64_t cmaxpre_get_removed_weight(CMaxPre *handle, unsigned obj_idx) {
  Wrapper *wrapper = (Wrapper *)handle;
  if (obj_idx >= wrapper->removed_weight.size())
    return 0;
  return ((Wrapper *)handle)->removed_weight[obj_idx];
}

void cmaxpre_set_bve_gate_extraction(CMaxPre *handle, char use) {
  ((Wrapper *)handle)->preprocessor->setBVEGateExtraction(use);
}

void cmaxpre_set_label_matching(CMaxPre *handle, char use) {
  ((Wrapper *)handle)->preprocessor->setLabelMatching(use);
}

void cmaxpre_set_skip_technique(CMaxPre *handle, int value) {
  ((Wrapper *)handle)->preprocessor->setSkipTechnique(value);
}

void cmaxpre_set_bve_sort_max_first(CMaxPre *handle, char use) {
  ((Wrapper *)handle)->preprocessor->setBVEsortMaxFirst(use);
}

void cmaxpre_set_bve_local_grow_limit(CMaxPre *handle, int limit) {
  ((Wrapper *)handle)->preprocessor->setBVElocalGrowLimit(limit);
}

void cmaxpre_set_bve_global_grow_limit(CMaxPre *handle, int limit) {
  ((Wrapper *)handle)->preprocessor->setBVEglobalGrowLimit(limit);
}

void cmaxpre_set_max_bbtms_vars(CMaxPre *handle, int limit) {
  ((Wrapper *)handle)->preprocessor->setMaxBBTMSVars(limit);
}

void cmaxpre_set_harden_in_model_search(CMaxPre *handle, char harden) {
  ((Wrapper *)handle)->preprocessor->setHardenInModelSearch(harden);
}

void cmaxpre_set_model_search_iter_limit(CMaxPre *handle, int limit) {
  ((Wrapper *)handle)->preprocessor->setModelSearchIterLimit(limit);
}

int cmaxpre_get_original_variables(CMaxPre *handle) {
  return ((Wrapper *)handle)->preprocessor->getOriginalVariables();
}

uint64_t cmaxpre_get_upper_bound(CMaxPre *handle) {
  return ((Wrapper *)handle)->preprocessor->getUpperBound();
}

// void cmaxpre_print_instance_stdout(CMaxPre *handle, int instanceFormat) {
//   ((Wrapper *)handle)->preprocessor->printInstance(cout, instanceFormat);
// }

// void cmaxpre_print_solution_stdout(CMaxPre *handle, uint64_t weight, int solFormat) {
//   Wrapper *wrapper = (Wrapper *)handle;
//   wrapper->preprocessor->printSolution(wrapper->prepro_assignment, cout,
//                                        weight, solFormat);
//   wrapper->prepro_assignment.clear();
// }

void cmaxpre_print_map_stdout(CMaxPre *handle) {
  ((Wrapper *)handle)->preprocessor->printMap(cout);
}

void cmaxpre_print_technique_log_stdout(CMaxPre *handle) {
  ((Wrapper *)handle)->preprocessor->printTechniqueLog(cout);
}

void cmaxpre_print_info_log_stdout(CMaxPre *handle) {
  ((Wrapper *)handle)->preprocessor->printInfoLog(cout);
}

void cmaxpre_print_preprocessor_stats_stdout(CMaxPre *handle) {
  ((Wrapper *)handle)->preprocessor->printPreprocessorStats(cout);
}
}
