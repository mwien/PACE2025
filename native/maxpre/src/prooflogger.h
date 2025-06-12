#ifndef PROOFLOGGER_H
#define PROOFLOGGER_H

#include <iostream>
#include <ostream>
#include <unordered_map>
#include <map>
#include <vector>
#include "global.hpp"

namespace maxPreprocessor {

class ProofLogger {
private:
  std::ostream& out;
  std::string s; // to faster output, we first construct output in string s, then do out << s;

  int add_comments;


  int nb_original_vars;

  int nb_ver_clauses;

  /*
  Mapping of variables of MaxPRE to the variables of the proof:
  (1) Original non-unit soft clauses will each have a _b variable in the proof
      MaxPRE does not know about these variables. Instead ProofLogger saves for
      each MaxPRE clause id (cid) if it was originally soft non-unit. If that is
      the case, _b variable is taken into account when something is done with
      clause cid
  (2) When MaxPRE identifies lables, it calls make_objective_variable. Then,
      if a clause was originally non-unit soft but has become a unit soft,
      ProofLogger replaces its _b variable with the unit literal in the
      objective and removes now-redundant (l, ~_b) clause
  (3) When MaxPRE adds labels, it calls set_blocking_lit function. ProofLogger
      saves to blitmap that MaxPRE variable x corresponds to _b variable of the
      clause If literal l is not mapped to _b variable, blitmap[l]=-1
  (4) The proof may use some auxiliary variables that are not known by MaxPRE
      (in functions labels_matched and binary_core_removal). Sometimes a MaxPRE
      variable is mapped into one of these auxiliary variables. This information
      is saved to pflitmap.

      Variable naming in the proof:
      x-variables: original problem
      _b-variables: objective variables of non-unit soft-clauses
      y-variables: extra variables introduced by MaxPRE. If original variables
                   of the instance were x1 x2, x3, the first y-variable will be
                   y4
      z-variables: variables introduced by ProofLogger, indexing starts from z1

      The implementation of mapping MaxSAT literal l to its corresponding
      variable in the proof:
        (1) Check if l is in pflitmap. If it is return the corresponding z-var
        (2) Check if l is in blitmap. If it is, return the corresponding b-var
        (3) Check if l was original variable (by comparing it to the number of
            original variables, nb_original_vars), select prefix x or y accordingly
  */
  std::vector<int> lit_to_zlit;  // map literals to the auxiliary z-variables of the prooflogger
  std::vector<int> lit_to_blit;  // map literals to the _b variables

  int nb_zvars; // number of z-variables introduced by ProofLogger

  std::string subst_separ; // either ' ' or " -> "

  bool isxlit(int l); // returns true if literal l is mapped to x-lit
public:
  std::string gl(int l); // map MaxSAT literal to proof literal
  std::string get_substitution(int l); // get string for substitution l -> 1
  std::string get_substitution(int l1, int l2); // get string for substitution l1 -> l2, if l2=-1, get string substitution for l1 -> 1
private:
  // helper functions for outputting constraints
  void out_l(int l); // similar to gl
  inline void out_raw_l(int l, char c) {if (!litValue(l)) s+='~'; s+=c; s+=std::to_string(litVariable(l)+1);}
  void out_nl(int l) {out_l(litNegation(l)); }
  void out_substitution(int l); //similar to get_substitution
  void out_substitution(int l1, int l2);
  void out_raw_substitution(int l, char c);
  void out_bvar_substitution(int cid);
  void out_nbvar_substitution(int cid);
  void out_bvar_substitution(int cid, int lit);
  void out_nbvar_substitution(int cid, int lit);
  void out_zsubstitution1(int z){s+=" z"; s+=std::to_string(z); s+=subst_separ; s+='1';}
  void out_zsubstitution0(int z){s+=" z"; s+=std::to_string(z); s+=subst_separ; s+='0';}

  inline void out_w(int64_t w) {s+=' ';if (w>0)s+="+";s+=std::to_string(w);s+=' ';}
  inline void out_ge(int rhs) {s+=" >= ";s+=std::to_string(rhs);}
  inline void out_term(int l) {s+=" +1 "; out_l(l);}
  inline void out_nterm(int l) {s+=" +1 "; out_l(litNegation(l));}
  inline void out_term(int64_t w, int l) { out_w(w); out_l(l);}
  inline void out_term(int64_t w, std::string l) { out_w(w); s+=' '; s+=l; }
  inline void out_nterm(int64_t w, int l) { out_w(w); out_l(litNegation(l));}
  inline void out_raw_term(int l, char c) { s+=" +1 "; out_raw_l(l, c);}
  inline void out_raw_term(int64_t w, int l, char c) { out_w(w); out_raw_l(l, c);}
  inline void out_zterm(int z) {s+=" +1 z";s+=std::to_string(z);}
  inline void out_zterm(int64_t w, int z) {out_w(w); s+="z"; s+=std::to_string(z);}
  inline void out_nzterm(int z)  {s+=" +1 ~z"; s+=std::to_string(z);}
  inline void out_nzterm(int64_t w, int z)  {out_w(w); s+="~z"; s+=std::to_string(z);}
  inline void out_bvar_term(int cid) {s+=" +1 "; s+=get_bvar(cid); }
  inline void out_nbvar_term(int cid) {s+=" +1 "; s+=get_nbvar(cid); }
  inline void out_bvar_term(int64_t w, int cid) {out_w(w); s+=get_bvar(cid); }
  inline void out_nbvar_term(int64_t w, int cid) {out_w(w); s+=get_nbvar(cid); }

  inline void out_add_to_core(int vid) {s+="core id "; s+=std::to_string(vid); s+='\n';}
  inline void out_del_id(int vid){s+="del id "; s+=std::to_string(vid); s+='\n';}
  inline void out_del_id_pp(int vid){s+="del id "; s+=std::to_string(vid); s+=" ;";}

  inline void outnl() {s+='\n'; }
  inline void outflush() {out << s; s.clear(); }
private:
  struct Clause {
    bool is_hard = 0;       // true if clause is a hard clause
    bool unit_soft = 0;     // true if the clause is unit soft (and thus does
                            // not actually exist in the verifier)
    int ulit = 0;           // if clause is a unit soft, the soft lit of the clause
    int vid = 0;            // clause id in the verifier
    bool deleted = 0;

    // for soft clauses, get blocking variable string formats without constructing
    // them every time:
    std::string bvar, nbvar, bvar_substitution, nbvar_substitution;
  };
  std::vector<Clause> clauses; // maps MaxPRE clause cid to information about
                               // the clause in the verifier/proof

  // auxiliary functions to get string formats of objective variables of clause
  std::string compute_bvar(int cid);
  std::string compute_nbvar(int cid);
  std::string compute_bvar_substitution(int cid);
  std::string compute_nbvar_substitution(int cid);
  const std::string& get_bvar(int cid);
  const std::string& get_nbvar(int cid);
  const std::string& get_bvar_substitution(int cid);
  const std::string& get_nbvar_substitution(int cid);
  std::string get_bvar_substitution(int cid, int lit);
  std::string get_nbvar_substitution(int cid, int lit);
  void reset_clause_computed_strs(int cid);

  std::unordered_map<int, uint64_t> soft_clause_weights;
  uint64_t objective_constant;

public:
  // only used in debug-comments
  std::string strclause(std::vector<int>& clause); // convert clause to string used in comments...
  std::string strsubsts(std::vector<std::pair<int, int> >& substs); // convert substitutions to string used in comments...
private:
  //
  void log_objective(bool include_constant = 1, bool negated = 0);
public:
  void begin_proof();
  void set_nb_clauses(int nbclauses);
  void end_proof(bool output_file);
  void flush(){ out.flush();}


  /*
    Setting up stuff to map correctly between MaxPRE and proof/verifier
  */
  void     set_soft_clause_weight(int cid, uint64_t w);
  uint64_t get_soft_clause_weight(int cid);
  void     add_to_obj_constant(int64_t w);

  void log_current_objective(); // for debugging purposes

  // Called when MaxPRE adds a label lit to a clause lit, with new unit soft
  // clause label_cid. lit_to_blit is updated so that MaxPre litearl lit is
  // mapped to the correct _b variable in the proof
  void set_blocking_lit(int cid, int lit, int label_cid);
  // Tell ProofLogger that clause cid of MaxPRE is same as clause vid in the proof
  // Called in the beginning for each clause and may be called when new clauses
  // are introduced
  void map_clause(int cid, int vid, bool is_hard);
  // Called in the beginning for unit softs, similar function to map_clause except
  // that the unit soft clauses do not correspond to constraints in the proof
  void map_unit_soft(int cid, int lit);
  // Called when MaxPRE identifies labels. If cid was not originally unit soft,
  // handle the added _b-var
  void make_objective_variable(int lit, int cid);



  /*

  */

  // check if clause is already deleted in proof
  bool is_clause_deleted(int cid1);

  // move constraint vid to core
  void move_to_core(int vid);

  int get_vid(int cid);




  /*
    Adding constraints
    Each function returns the proof/verifier id of the new clause
  */

  // add clause using polish notation
  // operations must refer to constraints by their index in proof/verifier!
  // (not by MaxPRE clause ids)
  int add_pol_clause(std::vector<std::pair<int, char> >& operations, bool add_to_core);
  int add_pol_clause_(std::vector<std::pair<int, char> > operations, bool add_to_core) {return add_pol_clause(operations, add_to_core); }
  // add rup clause
  int add_rup_clause(std::vector<int>& clause, bool add_to_core);
  int add_rup_clause_(std::vector<int> clause, bool add_to_core) {return add_rup_clause(clause, add_to_core);}
  // add clauses and cardinality constraint or clause with redundancy based strengthening
  int add_red_cc(std::vector<int>& lits, int rhs, int witness_lit, bool add_to_cpre);
  int add_red_cc_(std::vector<int> lits, int rhs, int witness_lit, bool add_to_core) {return add_red_cc(lits, rhs, witness_lit, add_to_core);}
  int add_red_clause(std::vector<int>& clause, int witness_lit, bool add_to_core) {return add_red_cc(clause, 1, witness_lit, add_to_core);}
  int add_red_clause_(std::vector<int> clause, int witness_lit, bool add_to_core) {return add_red_clause(clause, witness_lit, add_to_core);}
  // more complicated witness than single literal. Each pair (l1, l2) in witness:
  // substitute l1 -> l2, if l2==-1, substitute l1 -> 1
  int add_red_cc(std::vector<int>& clause, int rhs, std::vector<std::pair<int, int> > witness, bool add_to_core);
  int add_red_cc_(std::vector<int> clause, int rhs, std::vector<std::pair<int, int> > witness, bool add_to_core) {return add_red_cc(clause, rhs, witness, add_to_core);}
  int add_red_clause(std::vector<int>& clause, std::vector<std::pair<int, int> > witness, bool add_to_core) {return add_red_cc(clause, 1, witness, add_to_core);}
  int add_red_clause_(std::vector<int> clause, std::vector<std::pair<int, int> > witness, bool add_to_core) {return add_red_clause(clause, witness, add_to_core);}
  // create new clause resolving two existing clauses (sum and divide by 2)
  int resolve_clauses_vid(int vid1, int vid2, bool add_to_core);
  int resolve_clauses(int cid1, int cid2, bool add_to_core);
  // used in hardening, when a model is found, adds constraint cost <= ub to prove
  // hardening for each l for which w(l) >= ub
  int add_ub_constraint_on_weight(uint64_t ub, std::vector<std::pair<int, int> >& witness, bool add_to_core);




  /*
   Deleting clauses
  */

  // delete clause, use verifier id of the clause!
  void delete_clause_vid(int vid, int witness_lit = -1);
  void delete_clause_vid(int vid, std::vector<std::pair<int, int> >& witness);
  void delete_clause_vid_(int vid, std::vector<std::pair<int, int> > witness) { delete_clause_vid(vid, witness); }
  // use pol_proof to derive the redundancy of the given clause
  void delete_clause_vid_pol(int vid, std::vector<std::pair<int, char> >& pol_proof);
  void delete_clause_vid_pol_(int vid, std::vector<std::pair<int, char> > pol_proof) { delete_clause_vid_pol(vid, pol_proof); }

  // update the objective function when a soft clause is satisfied/falsified
  void soft_clause_satisfied(int cid);
  void soft_clause_falsified(int cid);
  // delete a clause that is redundant, handles soft clauses also
  void delete_red_clause(int cid, int witness_lit=-1);
  void delete_red_clause(int cid, std::vector<std::pair<int, int> >& witness);
  void delete_red_clause_(int cid, std::vector<std::pair<int, int> > witness) {delete_red_clause(cid, witness);}
  // delete soft clause that cannot be satisfied
  void delete_unsat_clause(int cid);



  /*
   Other modifications and technique-specific functions
  */

  // clause changed in maxpre, creates new clause and updates the mappings
  // assumes the change is provable by RUP
  void clause_updated(int cid, std::vector<int>& clause);
  // clause cid is replaced with clause cid + vid, vid is assumed to be a unit clause with literal that has negation in cid.
  void unit_strengthen(int cid, int vid);
  // soft clauses cid1 and cid2 are equivalent
  // remove cid1 (replace by cid2)
  void substitute_soft_clause(int cid1, int cid2);
  // cid1 and cid2 are unit soft clauses, one is a negation of the other.
  // update their weights and objective so that one of them gets weight 0.
  // That soft clause is then removed.
  // parameter witness_lit is the unit soft lit of cid1 (needed because the
  // clauses are not necessarily unit softs in verifier)
  void contradictory_soft_clauses(int cid1, int cid2, int witness_lit);

  // label matching technique, MaxPRE replaced label lb1 with lb2
  void labels_matched(std::vector<int>& clause1, std::vector<int>& clause2, int cid1, int cid2, int lb1, int lb2, int witness_lit);

  // at most one applied, the weight of each soft clause is reduced by w
  // constant (soft_clauses.size()-1)*w is added to the objective, new_var
  // gets weight w
  // Soft clauses in the atmost1-constraints are given as pairs: {F, S}.
  // In this pair, F is the soft clause cid, S is the cid of the negation of
  // soft clauses (only needed when w>w(F)).
  void at_most_one(std::vector<std::pair<int, int> >& soft_clauses, int am1_cid, int label_cid, uint64_t w);

  // BCR applied, label cid1 is removed
  void binary_core_removal1(int cid1, int cid2, int core_cid, std::vector<std::pair<int, std::vector<int> > >& clauses1, std::vector<std::pair<int, std::vector<int> > >& clauses2, std::vector<int>& new_clauses);
  void binary_core_removal2(int cid1, int cid2, int core_cid, std::vector<std::pair<int, std::vector<int> > >& clauses1, std::vector<std::pair<int, std::vector<int> > >& clauses2, std::vector<int>& new_clauses);
  void binary_core_removal(int cid1, int cid2, int core_cid, std::vector<std::pair<int, std::vector<int> > >& clauses1, std::vector<std::pair<int, std::vector<int> > >& clauses2, std::vector<int>& new_clauses) {
    binary_core_removal2(cid1, cid2, core_cid, clauses1, clauses2, new_clauses);
  }





  // checking that maxpre clause matches with that of prooflogger
  void clause_check(int cid, std::vector<int>& clause);
  // checking that a clause is in the proof
  void clause_check(std::vector<int>& clause);

  // remove constant from objective, cid is a soft clause that is always falsified
  void obju_remove_constant(int cid);

  void remap_variables(std::vector<std::pair<int, std::vector<int> > >& original_clauses, std::vector<std::pair<int, int> >& mapping, std::vector<std::pair<uint64_t, int> >& objective);




  // functions for logging comments and error messages
private:
  template<typename T>  void error_(T t) {
    if (add_comments==0) return;
    out << t;
    std::cerr << t;
  }
  template<typename T, typename... Args>  void error_(T t, Args... args) {
    if (add_comments==0) return;
    out << t;
    std::cerr << t;
    error_(args...);
  }
public:
  template<typename T>  void raw_print(T t) {
    out << t;
  }
  template<typename T, typename... Args>  void raw_print(T t, Args... args) {
    out << t;
    raw_print(args...);
  }
  template<typename T>  void comment(T t) {
    if (add_comments==0) return;
    out << "c " << "* " << t << '\n';
  }
  template<typename T, typename... Args>  void comment(T t, Args... args) {
    if (add_comments==0) return;
    out << "c " << "* " << t;
    raw_print(args...);
    out << '\n';
  }
  template<typename T>  void error(T t) {
    if (add_comments) out << "* ProofLogger Error in " << t << '\n';
    std::cerr << "ProofLogger Error in " << t << std::endl;
  }
  template<typename T, typename... Args> void error(T t, Args... args) {
  if (add_comments) out << "* ProofLogger Error in " << t;
    std::cerr << "ProofLogger Error in " << t;
    error_(args...);
    out << '\n';
    std::cerr << std::endl;
  }


  ProofLogger(std::ostream& o, int nbvars, int comments_level);
};

}
#endif
