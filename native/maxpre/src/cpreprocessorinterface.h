#ifndef MAXPP_CPREPROCESSORINSTANCE_HPP
#define MAXPP_CPREPROCESSORINSTANCE_HPP

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>

// C wrapper for the MaxPre API
// Generally, C++ bools are represented as chars with 1 = true and 0 = false

#define CMAXPRE_TRUE 1
#define CMAXPRE_FALSE 0

// A preprocessor handle
typedef struct CMaxPre CMaxPre;

const char *cmaxpre_signature();

// ---------------------------------------------------------------------------
// Initialization

// Instatiates a new preprocessor. Begins the initialization phase.
CMaxPre *cmaxpre_init_start(uint64_t top_weight, char inprocess_mode);

// The next functions pass an instance the the constructor of
// PreprocessorInterface. If they are called after cmaxpre_init_finalize, they
// do not have an effect.
// For adding a new clause, first call cmaxpre_init_add_weight for each
// objective, then call cmaxpre_init_add_lit in the same style as ipasir_add.

// Adds a weight for the current clause. For n objectives, call n times.
void cmaxpre_init_add_weight(CMaxPre *, uint64_t weight);
// Add a clause during initialization. The clause is finalized by calling this
// with argument 0.
void cmaxpre_init_add_lit(CMaxPre *, int lit);

// Finalizes the preprocessor initialization. After calling this, all init
// functions do not have an effect anymore and all other functions become
// available.
void cmaxpre_init_finalize(CMaxPre *);
// ---------------------------------------------------------------------------

// Destroys the preprocessor
void cmaxpre_release(CMaxPre *);

// PreprocessorInterface::preprocess
void cmaxpre_preprocess(CMaxPre *, const char *techniques, int log_level,
                        double time_limit, char add_removed_weight,
                        char sort_labels_frequency);

// PreprocessorInterface::getTopWeight
uint64_t cmaxpre_get_top_weight(CMaxPre *);

// ---------------------------------------------------------------------------
// Get preprocessed instance

// Gets the number of clauses after preprocessing
unsigned cmaxpre_get_n_prepro_clauses(CMaxPre *);
// Gets the weight of the clause with index cl_idx for the objective with
// index obj_idx. Returns top_weight if the clause or the objective do not
// exist.
uint64_t cmaxpre_get_prepro_weight(CMaxPre *, unsigned cl_idx,
                                   unsigned obj_idx);
// Gets the literal at position lit_idx in the clause with index cl_idx.
// Returns 0 if the clause does not exist or is shorter than lit_idx.
int cmaxpre_get_prepro_lit(CMaxPre *, unsigned cl_idx, unsigned lit_idx);
// Gets the number of labels after preprocessing
unsigned cmaxpre_get_n_prepro_labels(CMaxPre *);
// Gets the preprocessed label with index lbl_idx. Returns 0 if the index is too
// high.
int cmaxpre_get_prepro_label(CMaxPre *, unsigned lbl_idx);
// Gets the number of fixed literals
unsigned cmaxpre_get_n_prepro_fixed(CMaxPre *);
// Gets the fixed literal with index lit_idx. Returns 0 if the index is too
// high.
int cmaxpre_get_prepro_fixed_lit(CMaxPre *, unsigned lit_idx);
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Reconstruct a solution

// Resets the assignment to reconstruct as well as the reconstructed one. This
// is also done when calling cmaxpre_reconstruct.
void cmaxpre_assignment_reset(CMaxPre *);
// Add a true literal to the assignment to reconstruct.
void cmaxpre_assignment_add(CMaxPre *, int lit);
// Reconstructs and resets the assignment from cmaxpre_assignment_add. Returns
// the number of literals in the reconstructed assignment.
void cmaxpre_reconstruct(CMaxPre *);
// Gets the value for an original literal after reconstruction. The return
// value follows ipasir_val.
int cmaxpre_reconstructed_val(CMaxPre *, int lit);
// ---------------------------------------------------------------------------

// PreprocessorInterface::addVar
int cmaxpre_add_var(CMaxPre *, int var);
// Like ipasir_add for PreprocessorInterface::addClause.
char cmaxpre_add_lit(CMaxPre *, int lit);
// PreprocessorInterface::addLabel
int cmaxpre_add_label(CMaxPre *, int lbl, uint64_t weight);
// PreprocessorInterface::alterWeight
char cmaxpre_alter_weight(CMaxPre *, int lbl, uint64_t weight);
// PreprocessorInterface::labelToVar
char cmaxpre_label_to_var(CMaxPre *, int lbl);
// PreprocessorInterface::resetRemovedWeight
char cmaxpre_reset_removed_weight(CMaxPre *);

// Gets the removed weight for an objective index
uint64_t cmaxpre_get_removed_weight(CMaxPre *, unsigned obj_idx);

// PreprocessorInterface::setBVEGateExtraction
void cmaxpre_set_bve_gate_extraction(CMaxPre *, char use);
// PreprocessorInterface::setLabelMatching
void cmaxpre_set_label_matching(CMaxPre *, char use);
// PreprocessorInterface::setSkipTechnique
void cmaxpre_set_skip_technique(CMaxPre *, int value);

// PreprocessorInterface::setBVEsortMaxFirst
void cmaxpre_set_bve_sort_max_first(CMaxPre *, char use);
// PreprocessorInterface::setBVElocalGrowLimit
void cmaxpre_set_bve_local_grow_limit(CMaxPre *, int limit);
// PreprocessorInterface::setBVEglobalGrowLimit
void cmaxpre_set_bve_global_grow_limit(CMaxPre *, int limit);

// PreprocessorInterface::setMaxBBTMSVars
void cmaxpre_set_max_bbtms_vars(CMaxPre *, int limit);

// PreprocessorInterface::setHardenInModelSearch
void cmaxpre_set_harden_in_model_search(CMaxPre *, char harden);
// PreprocessorInterface::setModelSearchIterLimit
void cmaxpre_set_model_search_iter_limit(CMaxPre *, int limit);

// PreprocessorInterface::getOriginalVariables
int cmaxpre_get_original_variables(CMaxPre *);
// PreprocessorInterface::getUpperBound
uint64_t cmaxpre_get_upper_bound(CMaxPre *);

// PreprocessorInterface::printInstance for stdout
//void cmaxpre_print_instance_stdout(CMaxPre *, int instanceFormat = maxPreprocessor::INPUT_FORMAT_WPMS22);
// PreprocessorInterface::printSolution for stdout with an assignment added
// with cmaxpre_assignment_add
//void cmaxpre_print_solution_stdout(CMaxPre *, uint64_t weight, int solFormat = maxPreprocessor::INPUT_FORMAT_WPMS22);
// PreprocessorInterface::printMap for stdout
void cmaxpre_print_map_stdout(CMaxPre *);
// PreprocessorInterface::printTechniqueLog for stdout
void cmaxpre_print_technique_log_stdout(CMaxPre *);
// PreprocessorInterface::printInfoLog for stdout
void cmaxpre_print_info_log_stdout(CMaxPre *);
// PreprocessorInterface::printPreprocessorStats for stdout
void cmaxpre_print_preprocessor_stats_stdout(CMaxPre *);

#ifdef __cplusplus
}
#endif

#endif
