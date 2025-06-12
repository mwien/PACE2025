#include "prooflogger.h"
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <algorithm>

using namespace maxPreprocessor;
using namespace std;


/*
=============================================
           AUXILIARY FUNCTIONS
=============================================
*/

bool ProofLogger::isxlit(int lit) {
  if (lit<0) return 0;
  if (litVariable(lit)>=nb_original_vars) return 0;
  if (lit<(int)lit_to_zlit.size() && lit_to_zlit[lit]!=-1) return 0;
  if (lit<(int)lit_to_blit.size() && lit_to_blit[lit]!=-1) return 0;
  return 1;
}

string ProofLogger::gl(int lit) {
  if (lit<0) return "[none]";
  string nm = litVariable(lit)>=nb_original_vars ? "y" : "x";
  if (lit<(int)lit_to_zlit.size() && lit_to_zlit[lit]!=-1)lit = lit_to_zlit[lit], nm="z";
  else if (lit<(int)lit_to_blit.size() && lit_to_blit[lit]!=-1)  lit = lit_to_blit[lit], nm = "_b";
  return litValue(lit)?nm+to_string(litVariable(lit)+1) : "~"+nm+to_string(litVariable(lit)+1);
}

string ProofLogger::get_substitution(int lit) {
  string nm = litVariable(lit)>=nb_original_vars ? "y" : "x";
  if (lit<(int)lit_to_zlit.size() && lit_to_zlit[lit]!=-1)lit = lit_to_zlit[lit], nm="z";
  else if (lit<(int)lit_to_blit.size() && lit_to_blit[lit]!=-1)  lit = lit_to_blit[lit], nm = "_b";
  return litValue(lit)?nm+to_string(litVariable(lit)+1)+subst_separ+"1" : nm+to_string(litVariable(lit)+1)+subst_separ+"0";
}

string ProofLogger::get_substitution(int lit1, int lit2) {
  if (lit2==-1) return get_substitution(lit1);
  string nm = litVariable(lit1)>=nb_original_vars ? "y" : "x";
  if (lit1<(int)lit_to_zlit.size() && lit_to_zlit[lit1]!=-1) lit1 = lit_to_zlit[lit1], nm="z";
  else if (lit1<(int)lit_to_blit.size() && lit_to_blit[lit1]!=-1)   lit1 = lit_to_blit[lit1], nm = "_b";
  return litValue(lit1)?nm+to_string(litVariable(lit1)+1)+subst_separ+gl(lit2) : nm+to_string(litVariable(lit1)+1)+subst_separ+gl(litNegation(lit2));
}

void ProofLogger::out_l(int lit) {
  if (lit<0) return;
  if (lit<(int)lit_to_zlit.size() && lit_to_zlit[lit]!=-1) {
    lit = lit_to_zlit[lit];
    if (!litValue(lit)) s+="~";
    s+="z";
  } else if (lit<(int)lit_to_blit.size() && lit_to_blit[lit]!=-1) {
    lit = lit_to_blit[lit];
    if (!litValue(lit)) s+="~";
    s+="_b";
  } else {
    if (!litValue(lit))  s+="~";
    if (litVariable(lit)>=nb_original_vars) s+="y";
    else s+="x";
  }
  s+=to_string(litVariable(lit)+1);
}

void ProofLogger::out_substitution(int lit) {
  if (lit<0) return;
  s+=' ';
  if (lit<(int)lit_to_zlit.size() && lit_to_zlit[lit]!=-1) {
    lit = lit_to_zlit[lit];
    s+="z";
  } else if (lit<(int)lit_to_blit.size() && lit_to_blit[lit]!=-1) {
    lit = lit_to_blit[lit];
    s+="_b";
  } else {
    if (litVariable(lit)>=nb_original_vars) s+="y";
    else s+="x";
  }
  s+=to_string(litVariable(lit)+1);
  s+=subst_separ;
  s+=litValue(lit)?"1":"0";
}

void ProofLogger::out_raw_substitution(int lit, char c) {
  if (lit<0) return;
  s+=' ';
  s+=c;
  s+=to_string(litVariable(lit)+1);
  s+=subst_separ;
  s+=litValue(lit)?"1":"0";
}

void ProofLogger::out_substitution(int lit1, int lit2) {
  if (lit2==-1) {out_substitution(lit1);return;}
  if (lit1<0) return;
  s+=' ';
  if (lit1<(int)lit_to_zlit.size() && lit_to_zlit[lit1]!=-1) {
    lit1 = lit_to_zlit[lit1];
    s+="z";
  } else if (lit1<(int)lit_to_blit.size() && lit_to_blit[lit1]!=-1) {
    lit1 = lit_to_blit[lit1];
    s+="_b";
  } else {
    if (litVariable(lit1)>=nb_original_vars) s+="y";
    else s+="x";
  }
  s+=to_string(litVariable(lit1)+1);
  s+=subst_separ;
  out_l(litValue(lit1)?lit2:litNegation(lit2));
}

void ProofLogger::out_bvar_substitution(int cid) {
  s+=' ';
  s+=get_bvar_substitution(cid);
}
void ProofLogger::out_nbvar_substitution(int cid) {
  s+=' ';
  s+=get_nbvar_substitution(cid);
}
void ProofLogger::out_bvar_substitution(int cid, int lit) {
  s+=' ';
  if (get_bvar(cid)[0]=='~') { s+=get_nbvar(cid); s+=subst_separ; out_nl(lit);}
  else {s+=get_bvar(cid); s+=subst_separ; out_l(lit); }
}
void ProofLogger::out_nbvar_substitution(int cid, int lit) {
  s+=' ';
  if (get_nbvar(cid)[0]=='~') { s+=get_bvar(cid); s+=subst_separ; out_nl(lit);}
  else { s+=get_nbvar(cid); s+=subst_separ; out_l(lit); }
}



/*
=============================================
BLOCING VARIABLE STRINGS FOR SOFT CLAUSES
=============================================
*/



string ProofLogger::compute_bvar(int cid) {
  if (clauses[cid].unit_soft) return gl(clauses[cid].ulit);
  return "_b"+to_string(cid+1);
}
string ProofLogger::compute_nbvar(int cid) {
  if (clauses[cid].unit_soft) return gl(litNegation(clauses[cid].ulit));
  return "~_b"+to_string(cid+1);
}
string ProofLogger::compute_bvar_substitution(int cid) {
  if (clauses[cid].unit_soft) return get_substitution(clauses[cid].ulit);
  return "_b"+to_string(cid+1) + subst_separ + "1";

}
string ProofLogger::compute_nbvar_substitution(int cid) {
  if (clauses[cid].unit_soft) return get_substitution(litNegation(clauses[cid].ulit));
  return "_b"+to_string(cid+1) + subst_separ + "0";
}


const string& ProofLogger::get_bvar(int cid) {
  if (clauses[cid].bvar=="") clauses[cid].bvar = compute_bvar(cid);
  return clauses[cid].bvar;
}
const string& ProofLogger::get_nbvar(int cid) {
  if (clauses[cid].nbvar=="") clauses[cid].nbvar = compute_nbvar(cid);
  return clauses[cid].nbvar;
}
const string& ProofLogger::get_bvar_substitution(int cid) {
  if (clauses[cid].bvar_substitution=="") clauses[cid].bvar_substitution = compute_bvar_substitution(cid);
  return clauses[cid].bvar_substitution;

}
const string& ProofLogger::get_nbvar_substitution(int cid) {
  if (clauses[cid].nbvar_substitution=="") clauses[cid].nbvar_substitution = compute_nbvar_substitution(cid);
  return clauses[cid].nbvar_substitution;
}

string ProofLogger::get_bvar_substitution(int cid, int lit) {
  if (get_bvar(cid)[0]=='~') return get_nbvar(cid)+subst_separ+gl(litNegation(lit));
  return clauses[cid].bvar+subst_separ+gl(lit);
}

string ProofLogger::get_nbvar_substitution(int cid, int lit) {
  if (get_nbvar(cid)[0]=='~') return get_bvar(cid)+subst_separ+gl(litNegation(lit));
  return clauses[cid].nbvar+subst_separ+gl(lit);
}

void ProofLogger::reset_clause_computed_strs(int cid) {
  clauses[cid].bvar="";
  clauses[cid].nbvar="";
  clauses[cid].bvar_substitution="";
  clauses[cid].nbvar_substitution="";
}





/*
=============================================
     AUXILIARY FUNCTIONS FOR COMMENTING
=============================================
*/


string ProofLogger::strclause(vector<int>& clause) {
  string so;
  for (int i=0; i<(int)clause.size(); ++i ) {
    if (i) so+=' ';
    so+=gl(clause[i]);
  }
  return so;
}
string ProofLogger::strsubsts(vector<pair<int, int> >& substs) {
  string so;
  for (int i=0; i<(int)substs.size(); ++i ) {
    if (i) so+=' ';
    so+=get_substitution(substs[i].first, substs[i].second);
  }
  return so;
}



/*
=============================================
        PROOF SYNTAX THINGS
=============================================
*/





void ProofLogger::begin_proof() {
  out << "pseudo-Boolean proof version 2.0\n";

}

void ProofLogger::set_nb_clauses(int nbclauses) {
  out << "f " << nbclauses << '\n';
  nb_ver_clauses = nbclauses;
}

void ProofLogger::end_proof(bool output_file) {
  if (output_file) {
    out << "output EQUIOPTIMAL FILE\n";
  } else {
    out << "output EQUIOPTIMAL IMPLICIT\n";
  }
  out << "conclusion NONE\n";
  out << "end pseudo-Boolean proof\n";
  out.flush();
}


/*
=============================================
  MAXPRE-VERIFIER INTERACTION RELATED STUFF
=============================================
*/



void ProofLogger::log_objective(bool include_constant, bool negated) {
  map<string, int64_t> bvar_weights;
  int64_t c = 0;
  for (auto& t : soft_clause_weights) {
    if (t.second==0) continue;
    string bvar = get_nbvar(t.first);
    string nbvar = get_bvar(t.first);
    // do not inculde lit and its negation
    if (bvar_weights[nbvar]) {
      if (bvar_weights[nbvar]>(int64_t)t.second) {
        bvar_weights[nbvar]-=t.second;
        c+=t.second;
      } else {
        bvar_weights[bvar]+=t.second-bvar_weights[nbvar];
        c+=bvar_weights[nbvar];
        bvar_weights[nbvar]=0;
      }
    } else {
      bvar_weights[bvar]+=t.second;
    }
  }

  for (auto& t : bvar_weights) if (t.second)  out_term(negated?-t.second:t.second, t.first);
  if (include_constant) out_w(objective_constant+c);
}





void ProofLogger::set_soft_clause_weight(int cid, uint64_t w) {
  if (add_comments>2) comment("set_soft_clause_weight(", cid, ", ", w, ")");
  soft_clause_weights[cid] = w;
}

uint64_t ProofLogger::get_soft_clause_weight(int cid) {
  if (soft_clause_weights.count(cid)) return soft_clause_weights[cid];
  return 0;
}

void ProofLogger::add_to_obj_constant(int64_t w) {
  if (add_comments>2) comment("add_to_obj_constant(", w, ")");
  objective_constant += w;
}


void ProofLogger::log_current_objective() {
  if (add_comments>1) comment("log_current_objective()");
  s+="obju new "; log_objective(); s+=" ; \n";
  outflush();
}


void ProofLogger::set_blocking_lit(int cid, int lit, int label_cid) {
  if (add_comments>2) comment("set_blocking_lit(", cid, ", ", gl(lit), "[=_b", cid+1, "])");
  if (cid>=(int)clauses.size()) {error("set_blocking_lit: clause id ", cid, " out of bounds"); return;}

  clauses[cid].is_hard = 1;
  if (lit+1>=(int)lit_to_blit.size()) lit_to_blit.resize(lit+2, -1);
  lit_to_blit[lit] = posLit(cid);
  lit_to_blit[litNegation(lit)] = negLit(cid);
  if (label_cid>=(int)clauses.size()) clauses.resize(label_cid+1);
  clauses[label_cid].unit_soft = 1;
  clauses[label_cid].ulit = lit;
  set_soft_clause_weight(label_cid, get_soft_clause_weight(cid));
  set_soft_clause_weight(cid, 0);
  reset_clause_computed_strs(cid);
}

void ProofLogger::map_clause(int cid, int vid, bool is_hard) {
  if (add_comments>2) comment("map_clause(", cid, ", ", vid, ", ", is_hard, ")");

  if (cid>=(int)clauses.size()) clauses.resize(cid+1);
  clauses[cid].is_hard = is_hard;
  clauses[cid].vid = vid;
  clauses[cid].deleted = 0;
}

void ProofLogger::map_unit_soft(int cid, int lit) {
  if (add_comments>2) comment("map_unit_soft(", cid, ", ", gl(lit), ")");

  if (cid>=(int)clauses.size()) clauses.resize(cid+1);
  clauses[cid].unit_soft = 1;
  clauses[cid].ulit = lit;
  reset_clause_computed_strs(cid);
}

void ProofLogger::make_objective_variable(int lit, int cid) {
  if (add_comments>2) comment("make_objective_variable(", gl(lit), ", ", cid, ")");
  if (cid>=(int)clauses.size()) error("make_objective_variable: clause ", cid, " not found.");
  if (clauses[cid].deleted) error("make_objective_variable: clause ", cid, " is deleted.");
  if (clauses[cid].is_hard) error("make_objective_variable: clause ", cid, " is hard.");
  if (clauses[cid].unit_soft) return;

  // make ~lit = ~b
  // there is clause (lit, ~_b), introduce (~lit, _b), witness _b -> 1
  s+="red"; out_nterm(lit); out_bvar_term(cid); s+=" >= 1 ; "; out_bvar_substitution(cid); outnl();
  int vid = ++nb_ver_clauses;
  out_add_to_core(vid);

  // update objective function, replace w ~_b with w ~lit
  uint64_t w = get_soft_clause_weight(cid);
  s+="obju diff"; out_nbvar_term(-w, cid); out_term(w, litNegation(lit)); s+=" ;\n";

  // delete (~lit, _b), witness _b ->1 and (lit, ~_b), witness _b->0
  out_del_id_pp(vid); out_bvar_substitution(cid); outnl();
  out_del_id_pp(clauses[cid].vid); out_nbvar_substitution(cid); outnl();

  // update internal data structures
  clauses[cid].unit_soft = 1;
  clauses[cid].ulit = lit;
  reset_clause_computed_strs(cid);

  outflush();
}



/*
=============================================
     ...
=============================================
*/



bool ProofLogger::is_clause_deleted(int cid) {
  if (add_comments>2) comment("is_clause_deleted(", cid, ")");
  if (cid>=(int)clauses.size()){ error("is_clause_deleted: could not find clause ", cid, " (index out of bounds)"); return 0;}
  return clauses[cid].deleted;
}


void ProofLogger::move_to_core(int vid) {
  if (add_comments>2) comment("move_to_core(", vid, ")");
  out_add_to_core(vid);
  outflush();
}

int ProofLogger::get_vid(int cid) {
  if (add_comments>2) comment("get_vid(", cid, ")");
  if (cid>=(int)clauses.size()){ error("get_vid: could not find clause ", cid, " (index out of bounds)"); return -1;}
  return clauses[cid].vid;
}


int ProofLogger::add_pol_clause(vector<pair<int, char> >& operations, bool add_to_core) {
  if (add_comments>1) comment("add_pol_clause(...)");
  s+="pol";
  for (auto& op : operations) {s+=' ';s+=to_string(op.first);s+=' ';s+=op.second;}
  outnl();
  int vid = ++nb_ver_clauses;
  if (add_to_core) out_add_to_core(vid);
  outflush();
  return vid;
}





/*
=============================================
             ADDING CONSTRAINTS
=============================================
*/

int ProofLogger::add_rup_clause(vector<int>& clause, bool add_to_core) {
  if (add_comments>1) comment("add_rup_clause([", strclause(clause), "])");
  s+="rup"; for (int l : clause) out_term(l); s+=" >= 1 ;\n";
  int vid = ++nb_ver_clauses;
  if (add_to_core) out_add_to_core(vid);
  outflush();
  return vid;
}


int ProofLogger::add_red_cc(vector<int>& clause, int rhs, int witness_lit, bool add_to_core) {
  if (add_comments>1) comment("add_red_cc([", strclause(clause), "], ", rhs, ", ", gl(witness_lit), ")");
  s+="red"; for (int l : clause) out_term(l); out_ge(rhs); s+=" ;";
  if (witness_lit!=-1) out_substitution(witness_lit);
  outnl();
  int vid = ++nb_ver_clauses;
  if (add_to_core) out_add_to_core(vid);
  outflush();
  return vid;
}

int ProofLogger::add_red_cc(vector<int>& clause, int rhs, vector<pair<int, int> > witness, bool add_to_core) {
  if (add_comments>1) comment("add_red_clause([", strclause(clause), "], ", rhs, ", ", strsubsts(witness), ")");
  s+="red"; for (int l : clause) out_term(l); out_ge(rhs); s+=" ;";
  for (auto& w : witness)  out_substitution(w.first, w.second);
  outnl();
  int vid = ++nb_ver_clauses;
  if (add_to_core) out_add_to_core(vid);
  outflush();
  return vid;
}

int ProofLogger::resolve_clauses_vid(int vid1, int vid2, bool add_to_core) {
  if (add_comments>1) comment("resolve_clauses_vid(", vid1, ", ", vid2, ")");
  s+="pol ";s+=to_string(vid1);s+=' ';s+=to_string(vid2);s+=" + 2 d\n";
  int vid = ++nb_ver_clauses;
  if (add_to_core) out_add_to_core(vid);
  outflush();
  return vid;
}
int ProofLogger::resolve_clauses(int cid1, int cid2, bool add_to_core) {
  if (add_comments>1) comment("resolve_clauses(", cid1, ", ", cid2, ")");
  if (cid1>=(int)clauses.size()){ error("resolve_clauses: could not find clause ", cid1, " (index out of bounds)"); return 0; }
  if (cid2>=(int)clauses.size()){ error("resolve_clauses: could not find clause ", cid2, " (index out of bounds)"); return 0; }
  if (clauses[cid1].deleted) { error("resolve_clauses: clause ", cid1, " (=", clauses[cid1].vid, ") is deleted"); return 0; }
  if (clauses[cid2].deleted) { error("resolve_clauses: clause ", cid2, " (=", clauses[cid2].vid, ") is deleted"); return 0; }
  s+="pol "; s+=to_string(clauses[cid1].vid); s+=' '; s+=to_string(clauses[cid2].vid); s+=" + 2 d\n";
  int vid = ++nb_ver_clauses;
  if (add_to_core) out_add_to_core(vid);
  outflush();
  return vid;
}


int ProofLogger::add_ub_constraint_on_weight(uint64_t ub, vector<pair<int, int> >& witness, bool add_to_core) {
  if (add_comments>1) comment("add_ub_constraint_on_weigh(", ub, ", ", strsubsts(witness), ")");
  // TODO
  s+="red";
  log_objective(0, 1);
  s+=" >= -"; s+=to_string(ub); s+=" ;";
  for (auto& w : witness) out_substitution(w.first, w.second);
  s+='\n';
  ++nb_ver_clauses;
  if (add_to_core) out_add_to_core(nb_ver_clauses);
  outflush();
  return nb_ver_clauses;
}



/*
=============================================
          DELETING CONSTRAINTS
=============================================
*/

void ProofLogger::delete_clause_vid(int vid, int witness_lit) {
  if (add_comments>1) comment("delete_clause_vid(", vid, ", ", gl(witness_lit), ")");

  if (witness_lit!=-1) { out_del_id_pp(vid); out_substitution(witness_lit); outnl();}
  else out_del_id(vid);
  outflush();
}

void ProofLogger::delete_clause_vid(int vid, vector<pair<int, int> >& witness) {
  if (add_comments>1) comment("delete_clause_vid(", vid, ", [witness])");

  out_del_id_pp(vid);
  for (auto& w : witness) {out_substitution(w.first, w.second);}
  outnl();
}


void ProofLogger::delete_clause_vid_pol(int vid, std::vector<std::pair<int, char> >& pol_proof) {
  if (add_comments>1) comment("delete_clause_vid_pol(", vid, ", [pol_proof])");

  out_del_id_pp(vid);
  s+=" ; begin\n";
  s+="  pol";
  for (auto& op : pol_proof) { s+=' '; s+=to_string(op.first); if (op.second) {s+=' ';s+=op.second; } }
  s+=' '; s+=to_string(++nb_ver_clauses); s+=" +\nend\n";
  nb_ver_clauses++;
  outflush();
}

void ProofLogger::soft_clause_satisfied(int cid) {
  if (add_comments>1) comment("soft_clause_satisfied(", cid, ")");
  if (cid>=(int)clauses.size()) { error("soft_clause_satisfied: clause ", cid, " does not exist."); return; }
  if (clauses[cid].is_hard) { error("soft_clause_satisfied: clause ", cid, " is hard."); return; }

  uint64_t w = get_soft_clause_weight(cid);
  set_soft_clause_weight(cid, 0);
  s+="obju diff"; out_nbvar_term(-(int64_t)w, cid); outnl();
  outflush();
}

void ProofLogger::soft_clause_falsified(int cid) {
  if (add_comments>1) comment("soft_clause_falsified(", cid, ")");
  if (cid>=(int)clauses.size()) { error("soft_clause_falsified: clause ", cid, " does not exist."); return; }
  if (clauses[cid].is_hard) { error("soft_clause_falsified: clause ", cid, " is hard."); return; }

  uint64_t w = get_soft_clause_weight(cid);
  set_soft_clause_weight(cid, 0);
  add_to_obj_constant(w);
  s+="obju diff"; out_nbvar_term(-(int64_t)w, cid); out_w(w); s+=" ;\n";
  outflush();
}



void ProofLogger::delete_red_clause(int cid, int witness_lit) {
  if (add_comments>1) comment("delete_red_clause(", cid, ", ", gl(witness_lit), ")");
  if (cid>=(int)clauses.size()) {error("delete_red_clause: clause ", cid, " did not point to any VeriPB clause");return; }
  if (clauses[cid].deleted) {error("delete_red_clause: clause ", cid, " (=", clauses[cid].vid, ") already deleted"); return; }

  // delete clause cid
  // if clause was originally unit soft, nothing to be deleted
  if (!clauses[cid].unit_soft) {
    if (witness_lit!=-1) { out_del_id_pp(clauses[cid].vid); out_substitution(witness_lit); outnl();}
    else out_del_id(clauses[cid].vid);
  }

  // to update the objective...
  uint64_t w = get_soft_clause_weight(cid);
  if (!clauses[cid].is_hard && w>0) {
    set_soft_clause_weight(cid, 0);

    if (!clauses[cid].unit_soft || witness_lit != -1)  {
      // introduce unit bvar to the core
      s+="red"; out_bvar_term(cid); s+=" >= 1 ;"; out_bvar_substitution(cid); outnl();
      out_add_to_core(++nb_ver_clauses);
    }
    s+="obju diff"; out_nbvar_term(-(int64_t)w, cid); s+=" ;\n";
    if (!clauses[cid].unit_soft || witness_lit != -1) {
      out_del_id_pp(nb_ver_clauses); out_bvar_substitution(cid); outnl();
    }
  }

  clauses[cid].deleted = 1;
  outflush();
}

void ProofLogger::delete_red_clause(int cid, vector<pair<int, int> >& witness) {
  if (add_comments>1) comment("delete_red_clause(", cid, ", ", strsubsts(witness), ")");

  if (cid>=(int)clauses.size()) {
    error("delete_red_clause: clause ", cid, " did not point to any VeriPB clause");
    return;
  } else if (clauses[cid].deleted) {
    error("delete_red_clause: clause ", cid, " (=", clauses[cid].vid, ") already deleted");
    return;
  }
  // delete clause cid
  // if clause was originally unit soft, nothing to be deleted
  if (!clauses[cid].unit_soft) {
    if (witness.size()) {
      out_del_id_pp(clauses[cid].vid);
      for (auto& w : witness)  out_substitution(w.first, w.second);
      outnl();
    } else out_del_id(clauses[cid].vid);
  }

  // to update the objective...
  uint64_t w = get_soft_clause_weight(cid);
  if (!clauses[cid].is_hard && w>0) {
    set_soft_clause_weight(cid, 0);

    if (!clauses[cid].unit_soft || witness.size())  {
      // introduce unit bvar to the core
      s+="red"; out_bvar_term(cid); s+=" >= 1 ;"; out_bvar_substitution(cid); outnl();
      out_add_to_core(++nb_ver_clauses);
    }

    s+="obju diff"; out_nbvar_term(-(int64_t)w, cid); s+=" ;\n";
    if (!clauses[cid].unit_soft || witness.size()) {
      out_del_id_pp(nb_ver_clauses); out_bvar_substitution(cid); outnl();
    }
  }

  clauses[cid].deleted = 1;

  outflush();
}


void ProofLogger::delete_unsat_clause(int cid) {
  if (add_comments>1) comment("delete_unsat_clause(", cid, ")");

  if (cid>=(int)clauses.size()) {
    error("delete_unsat_clause: clause " , cid, " did not point to any VeriPB clause");
    return;
  } else if (clauses[cid].deleted) {
    if (!clauses[cid].unit_soft) error("delete_unsat_clause: clause ", cid, " already deleted");
    return;
  } else if (clauses[cid].is_hard) {
    error("delete_red_clause: can not delete hard unsat clause ", cid);
    return;
  }

  uint64_t w = get_soft_clause_weight(cid);
  if (w>0) {
    add_to_obj_constant(w);
    set_soft_clause_weight(cid, 0);

    s+="obju diff"; out_nbvar_term(-(int64_t)w, cid); out_w(w); s+=";\n";

    if (!clauses[cid].unit_soft)  {
      out_del_id_pp(clauses[cid].vid); out_nbvar_substitution(cid); outnl();
    }
  }

  clauses[cid].deleted = 1;
  outflush();
}



/*
=============================================
          OTHER MODIFICATIONS
=============================================
*/



void ProofLogger::clause_updated(int cid, vector<int>& clause) {
  if (add_comments>1) comment("clause_updated(", cid, ", [", strclause(clause), "])");
  if (cid>=(int)clauses.size()){ error("clause_updated: could not find clause ",cid, " (index out of bounds)");return;}
  if (clauses[cid].deleted) { error("clause_updated: clause ",cid, " (=", clauses[cid].vid, ") is deleted");return;}

  if (clauses[cid].unit_soft)  {
    uint64_t w = get_soft_clause_weight(cid);
    add_to_obj_constant(w);
    set_soft_clause_weight(cid, 0);
    s+="obju diff"; out_nbvar_term(-(int64_t)w, cid); out_w(w); s+=" ;\n";
    outflush();
    return;
  }

  s+="rup";
  for (int l : clause) out_term(l);
  if (!clauses[cid].is_hard) out_nbvar_term(cid);
  s+=" >= 1 ;\n";
  out_add_to_core(++nb_ver_clauses);
  out_del_id(clauses[cid].vid);
  clauses[cid].vid = nb_ver_clauses;

  outflush();
}

void ProofLogger::unit_strengthen(int cid, int vid) {
  if (add_comments>1) comment("unit_strengthen(", cid, ", ", vid, ")");
  if (cid>=(int)clauses.size()){ error("unit_strengthen: could not find clause ",cid, " (index out of bounds)");return;}
  if (clauses[cid].deleted) { error("unit_strengthen: clause ",cid, " (=", clauses[cid].vid, ") is deleted");return;}

  if (clauses[cid].unit_soft)  {
    uint64_t w = get_soft_clause_weight(cid);
    add_to_obj_constant(w);
    set_soft_clause_weight(cid, 0);
    s+="obju diff"; out_nbvar_term(-(int64_t)w, cid); out_w(w); s+=" ;\n";
    outflush();
    return;
  }

  s+="pol "; s+=to_string(clauses[cid].vid); s+=' '; s+=to_string(vid); s+=" +\n";
  out_add_to_core(++nb_ver_clauses);
  out_del_id(clauses[cid].vid);
  clauses[cid].vid = nb_ver_clauses;

  outflush();
}


void ProofLogger::substitute_soft_clause(int cid1, int cid2) {
  if (add_comments>1) comment("substitute_soft_clause(", cid1, ",", cid2, ")");
  if (cid1>=(int)clauses.size()) {error("substitute_soft_clause: could not find clause ", cid1, " (index out of bounds)"); return; }
  if (cid2>=(int)clauses.size()) {error("substitute_soft_clause: could not find clause ", cid2, " (index out of bounds)"); return; }
  if (clauses[cid1].deleted) {error("substitute_soft_clause: clause ", cid1, " is deleted"); return; }
  if (clauses[cid2].deleted) {error("substitute_soft_clause: clause ", cid2, " is deleted"); return; }
  if (clauses[cid1].is_hard)  {error("substitute_soft_clause: clause ", cid1, " is a hard clause"); return; }
  if (clauses[cid2].is_hard)  {error("substitute_soft_clause: clause ", cid2, " is a hard clause"); return; }

  uint64_t w1 = get_soft_clause_weight(cid1);
  uint64_t w2 = get_soft_clause_weight(cid2);
  set_soft_clause_weight(cid2, w1+w2);
  set_soft_clause_weight(cid1, 0);

  // special case: two equivalent original unit soft clauses, nothing needs to be done her:
  if (clauses[cid1].unit_soft && clauses[cid2].unit_soft && clauses[cid1].ulit==clauses[cid2].ulit) return;

  s+="red "; out_nbvar_term(cid1); out_bvar_term(cid2); s+=" >= 1 ;"; out_bvar_substitution(cid2); outnl();
  int vid1=++nb_ver_clauses;
  s+="red "; out_bvar_term(cid1); out_nbvar_term(cid2); s+=" >= 1 ;"; out_bvar_substitution(cid1); outnl();
  int vid2=++nb_ver_clauses;
  out_add_to_core(vid1);
  out_add_to_core(vid2);
  s+="obju diff "; out_nbvar_term(-(int64_t)w1, cid1); out_nbvar_term(w1, cid2); s+=" ;\n";
  out_del_id_pp(vid1); out_bvar_substitution(cid2); outnl();
  out_del_id_pp(vid2); out_bvar_substitution(cid1); outnl();
  if (!clauses[cid1].unit_soft) {
    out_del_id_pp(clauses[cid1].vid); out_nbvar_substitution(cid1); outnl();
  }
  outflush();
}

// cid1 and cid2 are unit soft clauses, one is a negation of the other.
// update their weights and objective so that one of them gets weight 0. That soft clause is then removed.
void ProofLogger::contradictory_soft_clauses(int cid1, int cid2, int witness_lit) {
  if (add_comments>1) comment("contradictory_soft_clauses(", cid1, ", ", cid2, ", ", gl(witness_lit), ")");
  if (cid1>=(int)clauses.size()) {error("contradictory_soft_clauses: could not find clause ", cid1); return; }
  if (cid2>=(int)clauses.size()) {error("contradictory_soft_clauses: could not find clause ", cid2); return; }
  if (clauses[cid1].deleted) {error("contradictory_soft_clauses: clause ", cid1, " is deleted"); return; }
  if (clauses[cid2].deleted) {error("contradictory_soft_clauses: clause ", cid2, " is deleted"); return; }
  if (clauses[cid1].is_hard)  {error("contradictory_soft_clauses: clause ", cid1, " is a hard clause"); return; }
  if (clauses[cid2].is_hard)  {error("contradictory_soft_clauses: clause ", cid2, " is a hard clause"); return; }

  uint64_t w1 = get_soft_clause_weight(cid1);
  uint64_t w2 = get_soft_clause_weight(cid2);
  uint64_t mw = min(w1, w2);
  add_to_obj_constant(mw);
  set_soft_clause_weight(cid1, w1-mw);
  set_soft_clause_weight(cid2, w2-mw);

  // special case: two contradicting original unit soft clauses, nothing needs to be done her:
  if (clauses[cid1].unit_soft && clauses[cid2].unit_soft) return;

  // TODO: in case original units, there is redundancy here :)
  s+="rup"; out_nbvar_term(cid1); out_nbvar_term(cid2); s+=" >= 1 ;\n";

  s+="red"; out_bvar_term(cid1); out_bvar_term(cid2); s+=" >= 1 ;";
  if (!clauses[cid1].unit_soft) out_bvar_substitution(cid1, litNegation(witness_lit));
  if (!clauses[cid2].unit_soft) out_bvar_substitution(cid2, witness_lit);
  outnl();

  int vid1=++nb_ver_clauses;
  int vid2=++nb_ver_clauses;
  out_add_to_core(vid1);
  out_add_to_core(vid2);
  s+="obju diff"; out_nbvar_term(-(int64_t)mw, cid1); out_nbvar_term(-(int64_t)mw, cid2); out_w(mw); s+=";\n";
  out_del_id(vid1);
  out_del_id_pp(vid2);
  if (!clauses[cid1].unit_soft) out_bvar_substitution(cid1, litNegation(witness_lit));
  if (!clauses[cid2].unit_soft) out_bvar_substitution(cid2, witness_lit);
  outnl();
  if (!clauses[cid1].unit_soft && get_soft_clause_weight(cid1)==0) {
    out_del_id_pp(clauses[cid1].vid); out_nbvar_substitution(cid1); outnl();
  }
  if (!clauses[cid2].unit_soft && get_soft_clause_weight(cid2)==0) {
    out_del_id_pp(clauses[cid2].vid); out_nbvar_substitution(cid2); outnl();
  }
  outflush();
}

void ProofLogger::labels_matched(vector<int>& cl1, vector<int>& cl2, int cid1, int cid2, int lcid1, int lcid2, int witness_lit) {
  if (add_comments>1) comment("labels_matched([", strclause(cl1), "], [", strclause(cl2), "], ", cid1, ", ", cid2, ", ", lcid1, " -> ", get_bvar(lcid1), ", ", lcid2, " -> ", get_bvar(lcid2), ", ", gl(witness_lit), ")");
  if (cid1>=(int)clauses.size()) {error("labels_matched: clause cid1 ", cid1, " does not exist."); return;}
  if (cid2>=(int)clauses.size()) {error("labels_matched: clause cid2 ", cid2, " does not exist."); return;}
  if (lcid1>=(int)clauses.size()) {error("labels_matched: clause lcid1 ", lcid1, " does not exist."); return;}
  if (lcid2>=(int)clauses.size()) {error("labels_matched: clause lcid2 ", lcid2, " does not exist."); return;}
  if (!clauses[lcid1].unit_soft) {error("labels_matched: clause lcid1 ", lcid1, " not a unit soft."); return;}
  if (!clauses[lcid2].unit_soft) {error("labels_matched: clause lcid2 ", lcid2, " not a unit soft."); return;}

  s+="red"; out_bvar_term(lcid1); out_bvar_term(lcid2); s+=" >= 1 ;"; out_bvar_substitution(lcid1, witness_lit); out_bvar_substitution(lcid2, litNegation(witness_lit)); outnl();
  int vid_lim = ++nb_ver_clauses;
  out_add_to_core(vid_lim);

  // introduce new variable z=b_1+b_2
  int z = ++nb_zvars;
  int64_t w = get_soft_clause_weight(lcid1);
  s+="red"; out_bvar_term(lcid1); out_bvar_term(lcid2); out_nzterm(z); s+=" >= 2 ; z"; s+=to_string(z); s+=subst_separ; s+='0'; out_bvar_substitution(lcid1, witness_lit); out_bvar_substitution(lcid2, litNegation(witness_lit)); outnl();
  s+="red"; out_nbvar_term(lcid1);out_nbvar_term(lcid2);out_zterm(z);  s+=" >= 1 ; z"; s+=to_string(z); s+=subst_separ; s+="1 \n";
  int vid_def = nb_ver_clauses+1;
  out_add_to_core(++nb_ver_clauses);
  out_add_to_core(++nb_ver_clauses);
  if (w>1) {
    s+="pol "; s+=to_string(vid_def); s+=' '; s+=to_string(w); s+=" *\n";
    out_add_to_core(++nb_ver_clauses);
  }


  // update the objective function
  set_soft_clause_weight(lcid1, 0);
  set_soft_clause_weight(lcid2, 0);
  set_soft_clause_weight(lcid2, w);
  s+="obju diff"; out_nbvar_term(-(int64_t)w, lcid1); out_nbvar_term(-(int64_t)w, lcid2); out_nzterm(w, z); s+=" ;\n";

  // introduce C\lor z, D\lor z
  int nlb1 = litNegation(clauses[lcid1].ulit);
  int nlb2 = litNegation(clauses[lcid2].ulit);
  int vid_subst = nb_ver_clauses+1;
  s+="rup";
  for (int l : cl1) {
    if  (l!=nlb1 && l!=nlb2) out_term(l);
    else                     out_nzterm(z);
  }
  s+=" >= 1 ;\n";
  out_add_to_core(++nb_ver_clauses);

  s+="rup";
  for (int l : cl2) {
    if  (l!=nlb1 && l!=nlb2) out_term(l);
    else                     out_nzterm(z);
  }
  s+=" >= 1 ;\n";
  out_add_to_core(++nb_ver_clauses);

  // Delete constraints C\lor b_1, D\lor b_2
  out_del_id_pp(clauses[cid1].vid); out_bvar_substitution(lcid1, witness_lit); out_bvar_substitution(lcid2, litNegation(witness_lit)); outnl();
  out_del_id_pp(clauses[cid2].vid); out_bvar_substitution(lcid1, witness_lit); out_bvar_substitution(lcid2, litNegation(witness_lit)); outnl();
  // Delete constraints z=b_1+b_2
  out_del_id_pp(vid_def);  out_bvar_substitution(lcid1); out_bvar_substitution(lcid2); outnl();
  if (w>1) {out_del_id_pp(vid_def+2);  out_bvar_substitution(lcid1); out_bvar_substitution(lcid2); outnl(); }
  out_del_id_pp(vid_def+1);  out_nbvar_substitution(lcid1); out_bvar_substitution(lcid2); outnl();
  // Delete b_1+b_2\le 1
  out_del_id_pp(vid_lim); out_bvar_substitution(lcid1); outnl();

  // update database of mappings
  int l = clauses[lcid2].ulit;
  if (l+1>=(int)lit_to_zlit.size()) lit_to_zlit.resize(l+2, -1);
  lit_to_zlit[l] = posLit(z-1);
  lit_to_zlit[litNegation(l)] = negLit(z-1);
  reset_clause_computed_strs(lcid2);

  clauses[cid1].vid = vid_subst;
  clauses[cid2].vid = vid_subst+1;
  outflush();
}


void ProofLogger::at_most_one(vector<pair<int, int> >& soft_clauses, int am1_cid, int label_cid, uint64_t w) {
  if (add_comments>1) comment("at_most_one([soft_clauses], ", am1_cid, ", ", label_cid, ", ", w, ")");
  if (label_cid>=(int)clauses.size()) {error("at_most_one: clause label_cid ", label_cid, " does not exist."); return;}
  if (!clauses[label_cid].unit_soft) {error("at_most_one: clause label_cid ", label_cid, " is not a unit soft."); return;}
  if (am1_cid>=(int)clauses.size()) {error("at_most_one: clause am1_cid ", am1_cid, " does not exist."); return;}
  vector<int> am1;
  for (int i=0; i<(int)soft_clauses.size(); ++i) {
    auto& c = soft_clauses[i];
    if (c.first>=(int)clauses.size()) {error("at_most_one: clause soft_clauses[", i, "].first ", c.first, ", does not exist."); return;}
    if (!clauses[c.first].unit_soft) {error("at_most_one: clause soft_clauses[", i, "].first ", c.first, ", is not a unit soft."); return;}
    if (c.second>=(int)clauses.size()) {error("at_most_one: clause soft_clauses[", i, "].second ", c.second, ", does not exist."); return;}
    if (!clauses[c.second].unit_soft) {error("at_most_one: clause soft_clauses[", i, "].second ", c.second, ", is not a unit soft."); return;}
    am1.push_back(clauses[c.first].ulit);
  }

  // add the binary clauses
  int nc0 = nb_ver_clauses+1;
  for (int i=1; i<(int)am1.size();++i) {
    for (int j=0; j<i; ++j) {
      s+="rup"; out_nterm(am1[i]); out_nterm(am1[j]); s+=" >= 1 ;\n";
      out_add_to_core(++nb_ver_clauses);
    }
  }

  // derive the lb constraint
  int amvid = nc0;
  if (am1.size()>2) {
    s+="pol ";
    int bin_vid = nc0;
    for (int i=1; i<(int)am1.size();++i) {
      if (i>2) { s+=to_string(i-1); s+=" * "; }
      for (int j=0; j<i; ++j) {
        s+=to_string(bin_vid++);
        if (i>1) s+=" + ";
        else s+=' ';
      }
      if (i>1) { s+=to_string(i); s+=" d ";}
    }
    outnl();
    amvid=++nb_ver_clauses;
    out_add_to_core(amvid);
  }

  // add the lb constraint
  s+="red"; for (int l : am1) out_nterm(l); out_term(clauses[label_cid].ulit); s+=" >= "; s+=to_string(am1.size()); s+=" ;"; out_substitution(clauses[label_cid].ulit); outnl();
  int am1_lb_vid = ++nb_ver_clauses;
  out_add_to_core(am1_lb_vid);
  if (w>1) {
    s+="pol "; s+=to_string(am1_lb_vid); s+=" "; s+=to_string(w); s+=" *\n";
    out_add_to_core(++nb_ver_clauses);
  }

  // update the objective
  s+="obju diff";
  for (int l : am1) out_nterm(-(int64_t)w, l);
  out_nterm(w, clauses[label_cid].ulit);
  out_w(w*(am1.size()-1));
  outnl();

  // update the information about soft clause weights
  set_soft_clause_weight(label_cid, w);
  add_to_obj_constant(w*(am1.size()-1));
  for (auto& c : soft_clauses) {
    int64_t wl = get_soft_clause_weight(c.first);
    if (wl>=(int64_t)w) set_soft_clause_weight(c.first, wl-w);
    else {
      add_to_obj_constant(wl-w);
      set_soft_clause_weight(c.first, 0);
      set_soft_clause_weight(c.second, w-wl);
    }
  }


  // udelete unnecessary clauses
  // delete lb constraint with w coefficient
  if (w>1) {
    out_del_id_pp(am1_lb_vid+1);
    s+=" ; begin\n  pol ";
    s+=to_string(am1_lb_vid); s+=" "; s+=to_string(w); s+=" * ";
    s+=to_string(++nb_ver_clauses);
    s+=" +\nend\n";
    nb_ver_clauses++;
  }
  // delete lb constraint
  out_del_id_pp(am1_lb_vid); out_substitution(clauses[label_cid].ulit); outnl();

  if (am1.size()>2) {
    // delete amvid constraint
    out_del_id_pp(amvid);
    s+=" ; begin\n  pol ";
    int bin_vid = nc0;
    for (int i=1; i<(int)am1.size();++i) {
      if (i>2) {s+=to_string(i-1); s+=" * "; }
      for (int j=0; j<i; ++j) {
        s+=to_string(bin_vid++);
        if (i>1) s+=" + ";
        else s+=' ';
      }
      if (i>1) { s+=to_string(i); s+=" d ";}
    }
    s+=to_string(++nb_ver_clauses);
    s+=" +\nend\n";
    ++nb_ver_clauses;
  } else out_del_id(amvid);

  // delete binary constraints
  int bin_vid = nc0;
  for (int i=1; i<(int)am1.size();++i)
    for (int j=0; j<i; ++j)
      if (bin_vid!=amvid) out_del_id(bin_vid++);
  outflush();
}


void ProofLogger::binary_core_removal1(int cid1, int cid2, int core_cid, vector<pair<int, vector<int> > >& clauses1, vector<pair<int, vector<int> > >& clauses2, vector<int>& new_clauses) {
  if (add_comments>1) comment("binary_core_removal(", cid1, ", ", cid2, ", ", core_cid, "[clauses1], [clauses2])");
  if (cid1>=(int)clauses.size()) {error("binary_core_removal: no clause for cid1 ", cid1); return;}
  if (cid2>=(int)clauses.size()) {error("binary_core_removal: no clause for cid2 ", cid2); return;}
  if (core_cid>=(int)clauses.size()) {error("binary_core_removal: no clause for core_cid ", core_cid); return;}
  if (clauses[cid1].deleted) {error("binary_core_removal: clause cid1 ", cid1, "(vid ", clauses[cid1].vid, ") is deleted"); return; }
  if (clauses[cid2].deleted) {error("binary_core_removal: clause cid2 ", cid2, "(vid ", clauses[cid2].vid, ") is deleted"); return; }
  if (clauses[core_cid].deleted) {error("binary_core_removal: clause core_cid ", core_cid, "(vid ", clauses[core_cid].vid, ") is deleted"); return; }
  if (!clauses[core_cid].is_hard) {error("binary_core_removal: clause core_cid ", core_cid, "(vid ", clauses[core_cid].vid, ") is not hard"); return; }
  if (clauses[cid1].is_hard) {error("binary_core_removal: clause cid1 ", cid1, "(vid ", clauses[cid1].vid, ") is hard"); return; }
  if (clauses[cid2].is_hard) {error("binary_core_removal: clause cid1 ", cid2, "(vid ", clauses[cid2].vid, ") is hard"); return; }
  if (!clauses[cid1].unit_soft) {error("binary_core_removal: clause cid1 ", cid1, "(vid ", clauses[cid1].vid, ") is not a unit soft"); return; }
  if (!clauses[cid2].unit_soft) {error("binary_core_removal: clause cid1 ", cid2, "(vid ", clauses[cid2].vid, ") is not a unit soft"); return; }
  //
  for (int i=0; i<(int)clauses1.size(); ++i) {
    int& cid = clauses1[i].first;
    if (cid>=(int)clauses.size()) {error("binary_core_removal: no clause for cid ", cid, " (clauses1[", i, "])"); return;}
    if (clauses[cid].deleted) {error("binary_core_removal: clause cid ", cid, " (clauses1[", i, "], vid ", clauses[cid].vid, ") is deleted."); return;}
    if (!clauses[cid].is_hard) {error("binary_core_removal: clause cid ", cid, " (clauses1[", i, "], vid ", clauses[cid].vid, ") is not hard."); return;}
    cid=clauses[cid].vid;
  }
  for (int i=0; i<(int)clauses2.size(); ++i) {
    int& cid = clauses2[i].first;
    if (cid>=(int)clauses.size()) {error("binary_core_removal: no clause for cid ", cid, " (clauses2[", i, "])"); return;}
    if (clauses[cid].deleted) {error("binary_core_removal: clause cid ", cid, " (clauses2[", i, "], vid ", clauses[cid].vid, ") is deleted."); return;}
    if (!clauses[cid].is_hard) {error("binary_core_removal: clause cid ", cid, " (clauses2[", i, "], vid ", clauses[cid].vid, ") is not hard."); return;}
    cid=clauses[cid].vid;
  }
  uint64_t w = get_soft_clause_weight(cid1);

  // introduce auxiliary variables
  int yVar0 = nb_zvars+1;
  int yCls0 = nb_ver_clauses+1;
  for (auto& c : clauses1) {
    int y = ++nb_zvars;
    s+="red";
    out_zterm(c.second.size()>0?c.second.size():1, y);
    for (int l : c.second) out_nterm(l);
    out_ge(c.second.size());
    s+=" ; z"; s+=to_string(y); s+=subst_separ; s+="1\n";
    out_add_to_core(++nb_ver_clauses);
  }
  for (int i=0; i<(int)clauses1.size(); ++i) {
    int y = yVar0+i;
    s+="red";
    out_nzterm(y);
    for (int l : clauses1[i].second) out_term(l);
    s+=" >= 1 ; z"; s+=to_string(y); s+=subst_separ; s+="0\n";
    out_add_to_core(++nb_ver_clauses);
  }
  int zVar0 = nb_zvars+1;
  int zCls0 = nb_ver_clauses+1;
  for (auto& c : clauses2) {
    int z = ++nb_zvars;
    s+="red";
    out_zterm(c.second.size()>0?c.second.size():1, z);
    for (int l : c.second) out_nterm(l);
    out_ge(c.second.size());
    s+=" ; z"; s+=to_string(z); s+=subst_separ; s+="1\n";
    out_add_to_core(++nb_ver_clauses);
  }
  for (int i=0; i<(int)clauses2.size(); ++i) {
    int z = zVar0+i;
    s+="red";;
    out_nzterm(z);
    for (int l : clauses2[i].second) out_term(l);
    s+=" >= 1 ; z"; s+=to_string(z); s+=subst_separ; s+="0\n";
    out_add_to_core(++nb_ver_clauses);
  }

  // introduce upper bounds b_1, b_2
  s+="red"; out_bvar_term(cid1); out_bvar_term(cid2);
  for (int y = yVar0; y<yVar0+(int)clauses1.size(); ++y) out_nzterm(y);
  s+=" >= 1 ;"; out_bvar_substitution(cid1); outnl();
  int ub1_vid = ++nb_ver_clauses;
  out_add_to_core(ub1_vid);

  s+="red"; out_bvar_term(cid1); out_bvar_term(cid2);
  for (int z = zVar0; z<zVar0+(int)clauses2.size(); ++z) out_nzterm(z);
  s+=" >= 1 ;"; out_bvar_substitution(cid2); outnl();
  int ub2_vid = ++nb_ver_clauses;
  out_add_to_core(ub2_vid);

  // introduce new variable b_3
  int b3 = ++nb_zvars;
  // encode ~b_3 -> ~b_1 \land ~b_2
  s+="red"; out_zterm(w, b3); out_nbvar_term(w, cid1); out_nbvar_term(w, cid2); out_ge(2*w); s+=" ; z"; s+=to_string(b3);s+=subst_separ;s+="1\n";
  int def1_b3 = ++nb_ver_clauses;
  out_add_to_core(def1_b3);
  // encode ~b_1 \land ~b_2 -> ~b_3
  s+="red"; out_nzterm(b3); out_bvar_term(cid1); out_bvar_term(cid2); s+=" >= 1 ; z"; s+=to_string(b3); s+=subst_separ; s+="0\n";
  int def2_b3 = ++nb_ver_clauses;
  out_add_to_core(def2_b3);

  // Introduce the new constraints...
  map<pair<int, int>, int > ncmap;
  vector<vector<int> > weaken;
  int nc0 = nb_ver_clauses+1;
  for (auto& c1 : clauses1) {
    for (auto& c2 : clauses2) {
      vector<int> nc;
      for (int l1 : c1.second) nc.push_back(l1);
      for (int l2 : c2.second) nc.push_back(l2);
      sort(nc.begin(), nc.end());
      bool ttl = 0;
      for (int i=1; i<(int)nc.size() && !ttl; ++i) if (nc[i]==litNegation(nc[i-1])) ttl=1;
      if (ttl) continue;
      weaken.emplace_back();
      for (int i=1; i<(int)nc.size(); ++i) if (nc[i]==nc[i-1]) weaken.back().push_back(nc[i]);
			nc.erase(unique(nc.begin(), nc.end()), nc.end());

      /*
      s+="rup";
      for (int l : nc) out_term(l);
      out_nzterm(b3); s+=" >= 1 ;\n";
      */
      s+="pol "; s+=to_string(c1.first); s+=' '; s+=to_string(c2.first); s+=" + "; s+=to_string(def2_b3); s+=" + s\n";
      //s+="pol "; s+=to_string(c1.first); s+=' '; s+=to_string(c2.first); s+=" + "; s+=to_string(def2_b3); s+=" + s\n";
      ncmap[{c1.first, c2.first}]=++nb_ver_clauses;
      map_clause(new_clauses[ncmap.size()-1], nb_ver_clauses, 1);
      out_add_to_core(nb_ver_clauses);
    }
  }



  // update the objective function
  int core_vid = clauses[core_cid].vid;
  s+="obju diff"; out_nbvar_term(-(int64_t)w, cid1); out_nbvar_term(-(int64_t)w, cid2); out_nzterm(w, b3); out_w(w); s+=";\n";
  set_soft_clause_weight(cid1, 0);
  add_to_obj_constant(w);


  //delete constraints
  out_del_id_pp(def2_b3);
  s+=" ; begin\n  ";
  int cvid = ++nb_ver_clauses;
  vector<int> ncs;
  for (int i=0; i<(int)clauses1.size(); ++i) {
    int newc0 = nb_ver_clauses+1;
    for (int j=0; j<(int)clauses2.size(); ++j) {
      if (!ncmap.count({clauses1[i].first, clauses2[j].first})) {
        s+="  rup"; out_zterm(yVar0+i); out_zterm(zVar0+j); out_nzterm(b3); s+=" >= 1 ;\n";
        ++nb_ver_clauses;
        continue;
      }
      int ncvid = ncmap[{clauses1[i].first, clauses2[j].first}];
      s+="  pol "; s+=to_string(ncvid); s+=' '; s+=to_string(yCls0+i); s+=" + "; s+=to_string(zCls0+j); s+=" +";
      for (int l : weaken[ncvid-nc0]) {s+=' '; out_l(l); s+=" w";}
      s+=" s\n";
      ++nb_ver_clauses;
    }
    s+="  pol "; s+=to_string(newc0);
    for (int c = newc0+1; c<=nb_ver_clauses; ++c) {s+=' '; s+=to_string(c); s+=" +";}
    s+=' '; s+=to_string(ub2_vid); s+=" +";
    //if (clauses2.size()>1) { s+=' '; s+=to_string(clauses2.size()); s+=" d";}
    s+=" s\n";
    ncs.push_back(++nb_ver_clauses);
  }
  s+="  pol "; s+=to_string(ncs[0]);
  for (int i=1; i<(int)ncs.size(); ++i) { s+=' '; s+=to_string(ncs[i]); s+=" +"; }
  s+=' '; s+=to_string(ub1_vid); s+=" +";
  //if (clauses1.size()>1) { s+=' '; s+=to_string(clauses1.size()); s+=" d"; }
  s+=" s "; s+=to_string(cvid); s+=" +\nend\n";
  ++nb_ver_clauses;

  out_del_id_pp(def1_b3); s+=" z"; s+=to_string(b3); s+=subst_separ; s+="1\n";
  out_del_id_pp(ub1_vid); out_bvar_substitution(cid1); outnl();
  out_del_id_pp(ub2_vid); out_bvar_substitution(cid2); outnl();
  for (int i=0; i<(int)clauses1.size(); ++i) {out_del_id_pp(yCls0+clauses1.size()+i); out_zsubstitution0(yVar0+i); outnl(); }
  for (int i=0; i<(int)clauses2.size(); ++i) {out_del_id_pp(zCls0+clauses2.size()+i); out_zsubstitution0(zVar0+i); outnl(); }
  for (int i=0; i<(int)clauses1.size(); ++i) {out_del_id_pp(yCls0+i); out_zsubstitution1(yVar0+i); outnl();}
  for (int i=0; i<(int)clauses2.size(); ++i) {out_del_id_pp(zCls0+i); out_zsubstitution1(zVar0+i); outnl();}
  out_del_id_pp(core_vid); out_nbvar_substitution(cid1); outnl();
  for (auto& c : clauses1) {out_del_id_pp(c.first); out_nbvar_substitution(cid1); outnl();}
  for (auto& c : clauses2) {out_del_id_pp(c.first); out_nbvar_substitution(cid2); outnl();}

  // map label1 to new variable
  int lb = clauses[cid2].ulit;
  if (lb+1>=(int)lit_to_zlit.size()) lit_to_zlit.resize(lb+2, -1);
  lit_to_zlit[lb] = posLit(b3-1);
  lit_to_zlit[litNegation(lb)] = negLit(b3-1);
  reset_clause_computed_strs(cid2);
  outflush();
}



void ProofLogger::binary_core_removal2(int cid1, int cid2, int core_cid, vector<pair<int, vector<int> > >& clauses1, vector<pair<int, vector<int> > >& clauses2, vector<int>& new_clauses) {
  if (add_comments>1) comment("binary_core_removal(", cid1, ", ", cid2, ", ", core_cid, "[clauses1], [clauses2])");
  if (cid1>=(int)clauses.size()) {error("binary_core_removal: no clause for cid1 ", cid1); return;}
  if (cid2>=(int)clauses.size()) {error("binary_core_removal: no clause for cid2 ", cid2); return;}
  if (core_cid>=(int)clauses.size()) {error("binary_core_removal: no clause for core_cid ", core_cid); return;}
  if (clauses[cid1].deleted) {error("binary_core_removal: clause cid1 ", cid1, "(vid ", clauses[cid1].vid, ") is deleted"); return; }
  if (clauses[cid2].deleted) {error("binary_core_removal: clause cid2 ", cid2, "(vid ", clauses[cid2].vid, ") is deleted"); return; }
  if (clauses[core_cid].deleted) {error("binary_core_removal: clause core_cid ", core_cid, "(vid ", clauses[core_cid].vid, ") is deleted"); return; }
  if (!clauses[core_cid].is_hard) {error("binary_core_removal: clause core_cid ", core_cid, "(vid ", clauses[core_cid].vid, ") is not hard"); return; }
  if (clauses[cid1].is_hard) {error("binary_core_removal: clause cid1 ", cid1, "(vid ", clauses[cid1].vid, ") is hard"); return; }
  if (clauses[cid2].is_hard) {error("binary_core_removal: clause cid1 ", cid2, "(vid ", clauses[cid2].vid, ") is hard"); return; }
  if (!clauses[cid1].unit_soft) {error("binary_core_removal: clause cid1 ", cid1, "(vid ", clauses[cid1].vid, ") is not a unit soft"); return; }
  if (!clauses[cid2].unit_soft) {error("binary_core_removal: clause cid1 ", cid2, "(vid ", clauses[cid2].vid, ") is not a unit soft"); return; }
  //
  for (int i=0; i<(int)clauses1.size(); ++i) {
    int& cid = clauses1[i].first;
    if (cid>=(int)clauses.size()) {error("binary_core_removal: no clause for cid ", cid, " (clauses1[", i, "])"); return;}
    if (clauses[cid].deleted) {error("binary_core_removal: clause cid ", cid, " (clauses1[", i, "], vid ", clauses[cid].vid, ") is deleted."); return;}
    if (!clauses[cid].is_hard) {error("binary_core_removal: clause cid ", cid, " (clauses1[", i, "], vid ", clauses[cid].vid, ") is not hard."); return;}
    cid=clauses[cid].vid;
  }
  for (int i=0; i<(int)clauses2.size(); ++i) {
    int& cid = clauses2[i].first;
    if (cid>=(int)clauses.size()) {error("binary_core_removal: no clause for cid ", cid, " (clauses2[", i, "])"); return;}
    if (clauses[cid].deleted) {error("binary_core_removal: clause cid ", cid, " (clauses2[", i, "], vid ", clauses[cid].vid, ") is deleted."); return;}
    if (!clauses[cid].is_hard) {error("binary_core_removal: clause cid ", cid, " (clauses2[", i, "], vid ", clauses[cid].vid, ") is not hard."); return;}
    cid=clauses[cid].vid;
  }
  uint64_t w = get_soft_clause_weight(cid1);

  // new variable
  int b3 = ++nb_zvars;

  // do at-most-ones
  // am1-clause (b1, b2, ~b3)
  s+="red"; out_bvar_term(cid1), out_bvar_term(cid2), out_nzterm(b3); s+=" >= 1 ;"; out_zsubstitution0(b3); outnl();
  int am1c = ++nb_ver_clauses;
  out_add_to_core(am1c);

  // lb constraint
  int core_vid = clauses[core_cid].vid;
  // add the lb constraint ~b1 + ~b2 + b3 >= 2
  s+="red"; out_nbvar_term(cid1), out_nbvar_term(cid2), out_zterm(b3); s+=" >= 2 ;"; out_zsubstitution1(b3); outnl();
  int am1_lb_vid = ++nb_ver_clauses;
  out_add_to_core(am1_lb_vid);
  if (w>1) {
    s+="pol "; s+=to_string(am1_lb_vid); s+=" "; s+=to_string(w); s+=" *\n";
    out_add_to_core(++nb_ver_clauses);
  }

  // update the objective function
  s+="obju diff"; out_nbvar_term(-(int64_t)w, cid1); out_nbvar_term(-(int64_t)w, cid2); out_nzterm(w, b3); out_w(w); s+=";\n";
  set_soft_clause_weight(cid1, 0);
  add_to_obj_constant(w);

  // udelete unnecessary clauses
  // delete lb constraint with w coefficient
  if (w>1) {
    out_del_id_pp(am1_lb_vid+1);
    s+=" ; begin\n  pol ";
    s+=to_string(am1_lb_vid); s+=" "; s+=to_string(w); s+=" * ";
    s+=to_string(++nb_ver_clauses);
    s+=" +\nend\n";
    ++nb_ver_clauses;
  }
  // delete lb constraint
  out_del_id_pp(am1_lb_vid); out_zsubstitution1(b3); outnl();

  vector<int> tmpclauses;
  // BVE on b1
  for (auto& c1 : clauses1) {
    s+="pol "; s+=to_string(c1.first); s+=' '; s+=to_string(am1c); s+=" + 2 d\n";
    tmpclauses.push_back(++nb_ver_clauses);
    out_add_to_core(tmpclauses.back());
  }
  for (auto& c1 : clauses1) {
    s+="del id "; s+=to_string(c1.first); s+=" ; "; out_nbvar_substitution(cid1); outnl();
  }
  s+="del id "; s+=to_string(core_vid); s+=" ;"; out_nbvar_substitution(cid1); outnl();
  s+="del id "; s+=to_string(am1c); s+=" ;"; out_bvar_substitution(cid1); outnl();

  // BVE on b2
  int nci = 0;
  for (int i=0; i<(int)clauses1.size(); ++i) {
    auto& c1 = clauses1[i];
    int tmpvid = tmpclauses[i];
    for (auto& c2 : clauses2) {
      // skip tautological clauses
      vector<int> nc;
      for (int l1 : c1.second) nc.push_back(l1);
      for (int l2 : c2.second) nc.push_back(l2);
      sort(nc.begin(), nc.end());
      bool ttl = 0;
      for (int j=1; j<(int)nc.size() && !ttl; ++j) if (nc[j]==litNegation(nc[j-1])) ttl=1;
      if (ttl) continue;
      s+="pol "; s+=to_string(tmpvid); s+=' '; s+=to_string(c2.first); s+=" + 2 d\n";
      out_add_to_core(++nb_ver_clauses);
      map_clause(new_clauses[nci++], nb_ver_clauses, 1);
    }
  }
  for (auto& c2 : clauses2) {
    s+="del id "; s+=to_string(c2.first); s+=" ; "; out_nbvar_substitution(cid2); outnl();
  }
  for (auto& v : tmpclauses) {
    s+="del id "; s+=to_string(v); s+=" ; "; out_bvar_substitution(cid2); outnl();
  }


  // map label1 to new variable
  int lb = clauses[cid2].ulit;
  if (lb+1>=(int)lit_to_zlit.size()) lit_to_zlit.resize(lb+2, -1);
  lit_to_zlit[lb] = posLit(b3-1);
  lit_to_zlit[litNegation(lb)] = negLit(b3-1);
  reset_clause_computed_strs(cid2);
  outflush();
}

void ProofLogger::clause_check(int cid, vector<int>& clause) {
  if (add_comments>2) comment("clause_check(", cid, ", [", strclause(clause), "])");
  if (cid>=(int)clauses.size()) {error("clause_check: could not find clause ", cid);return;}
  if (clauses[cid].deleted) error("clause_check: could not find clause ", cid);
  if (clauses[cid].unit_soft) return;
  s+="e "; s+=to_string(clauses[cid].vid); s+=" :";
  for (int l : clause) out_term(l);
  if (!clauses[cid].is_hard) out_nbvar_term(cid);;
  s+=" >= 1 ;\n";
  outflush();
}


void ProofLogger::clause_check(vector<int>& clause) {
  if (add_comments>2) comment("clause_check([", strclause(clause), "])");
  s+="e";
  for (int l : clause) out_term(l);
  s+=" >= 1 ;\n";
  outflush();
  return;
}


void ProofLogger::obju_remove_constant(int cid) {
  if (add_comments>1) comment("obju_remove_constant(", cid, ")");
  set_soft_clause_weight(cid, objective_constant);
  s+="obju diff"; out_nbvar_term(objective_constant, cid);
  s+=" -"; s+=to_string(objective_constant);
  s+="\n";
  objective_constant=0;
  outflush();
}


inline int map_lit(int l, vector<pair<int, int> >& mapping) {
  auto m = lower_bound(mapping.begin(), mapping.end(), make_pair(min(l, litNegation(l)), 0));
  if (m==mapping.end()) return -1;
  return (m->first==l)?m->second:litNegation(m->second);
}



void ProofLogger::remap_variables(vector<pair<int, vector<int> > >& original_clauses, vector<pair<int, int> >& mapping, vector<pair<uint64_t, int> >& objective) {
  if (add_comments>1) comment("remap_variables(original_clauses [size=", original_clauses.size(), "], mapping [size=",mapping.size(),"], objective [size=", objective.size(), "])");
  sort(mapping.begin(), mapping.end());
  // using rup vs deriving everything
  bool explicit_new = 1;
  bool explicit_remove = 1;
  bool explicit_obju = 0; // VeriPB performance seemed slightly better when explicit_obju=0


  // (1) Add temporary variables equivalent to the variables in the current variable space
  set<int> keep;
  bool something_mapped = 0;
  int first_clause = nb_ver_clauses+1;
  map<int, int> nlit_to_vid;
  for (auto& m : mapping) {
    if (m.first != m.second || !isxlit(m.first)) {
      s+="red";out_term(m.first); out_raw_term(litNegation(m.first), 't'); s+=" >= 1 ; "; out_raw_substitution(litNegation(m.first), 't'); outnl();
      out_add_to_core(++nb_ver_clauses);
      s+="red";out_term(litNegation(m.first)); out_raw_term(m.first, 't'); s+=" >= 1 ; "; out_raw_substitution(m.first, 't'); outnl();
      out_add_to_core(++nb_ver_clauses);

      nlit_to_vid[litNegation(m.first)] = nb_ver_clauses-1;
      nlit_to_vid[m.first] = nb_ver_clauses;

      something_mapped = 1;
    } else keep.insert(litVariable(m.first));
  }
  outflush();
  if (!something_mapped) {
    s+="obju new";
    for (auto& t : objective) {
      int l = map_lit(t.second, mapping);
      out_raw_term(t.first, l, 'x');
    }
    out_w(0);
    outnl();
    return;
  }

  // (2) Update the objective to have variables in the temporary namespace
  for (auto& t : objective) {
    if (!keep.count(litVariable(t.second))) {
      s+="obju diff";
      out_term(-(int64_t)t.first, t.second);
      out_raw_term(t.first, t.second, keep.count(litVariable(t.second))?'x':'t');
      if (explicit_obju) {
        s+=" ; begin\n  proofgoal #1\n    pol ";
        s+=to_string(nlit_to_vid[t.second]); s+=' '; s+=to_string(t.first); s+=" * "; s+=to_string(++nb_ver_clauses); s+=" +\n"; ++nb_ver_clauses;
        s+="  end -1\n  proofgoal #2\n    pol ";
        s+=to_string(nlit_to_vid[litNegation(t.second)]); s+=' '; s+=to_string(t.first); s+=" * "; s+=to_string(++nb_ver_clauses); s+=" +\n"; ++nb_ver_clauses;
        s+="  end -1\nend";
      }
      outnl();
    }
  }
  outflush();


  // (3) Replace original constraints with constraints in the temporary name space
  for (auto& c : original_clauses) {
    bool needed = 0;
    for (int l : c.second) if (!keep.count(litVariable(l))) {needed = 1; break;}
    if (!needed) continue;

    if (explicit_new) {
      s+="pol ";
      s+=to_string(clauses[c.first].vid);
      s+=' ';
      for (int l : c.second) {
        if (!nlit_to_vid.count(l)) continue;
        s+=to_string(nlit_to_vid[l]);
        s+=" + ";
      }
      outnl();
    } else {
      s+="rup";
      for (int l : c.second) out_raw_term(l, keep.count(litVariable(l))?'x':'t');
      s+=" >= 1 ;\n";
    }
    out_add_to_core(++nb_ver_clauses);

    if (explicit_remove) {
      out_del_id_pp(clauses[c.first].vid);
      s+=" ; begin\n  pol ";s+=to_string(nb_ver_clauses);s+=' ';
      for (int l : c.second) {
        if (!nlit_to_vid.count(litNegation(l))) continue;
        s+=to_string(nlit_to_vid[litNegation(l)]);
        s+=" + ";
      }
      s+=to_string(++nb_ver_clauses); s+=" +\nend\n";
      nb_ver_clauses++;
      clauses[c.first].vid = nb_ver_clauses-2;
    } else {
      out_del_id(clauses[c.first].vid);
      clauses[c.first].vid = nb_ver_clauses;
    }
  }
  outflush();

  // (4) Delete the equivalence clauses introduced in step (1)
  for (auto& m : mapping) {
    if (!keep.count(litVariable(m.first))) {
      out_del_id_pp(first_clause++); out_substitution(m.first); outnl();
      out_del_id_pp(first_clause++); out_substitution(litNegation(m.first)); outnl();
    }
  }
  outflush();

  // (5) introduce mapping of temporary variables to the desired namespace
  nlit_to_vid.clear();
  first_clause = nb_ver_clauses+1;
  for (auto& m : mapping) {
    if (!keep.count(litVariable(m.first))) {
      s+="red";out_raw_term(m.second, 'x'); out_raw_term(litNegation(m.first), 't'); s+=" >= 1 ; "; out_raw_substitution(m.second, 'x'); outnl();
      out_add_to_core(++nb_ver_clauses);
      s+="red";out_raw_term(litNegation(m.second), 'x'); out_raw_term(m.first, 't'); s+=" >= 1 ; "; out_raw_substitution(litNegation(m.second), 'x'); outnl();
      out_add_to_core(++nb_ver_clauses);

      nlit_to_vid[m.first] = nb_ver_clauses-1;
      nlit_to_vid[litNegation(m.first)] = nb_ver_clauses;
    }
  }
  outflush();


  // (6) Update the objective to have the variables in the final namespace
  for (auto& t : objective) {
    if (!keep.count(litVariable(t.second))) {
      s+="obju diff";
      out_raw_term(-(int64_t)t.first, t.second, keep.count(litVariable(t.second))?'x':'t');
      int l = map_lit(t.second, mapping);
      out_raw_term(t.first, l, 'x');
      if (explicit_obju) {
        s+=" ; begin\n  proofgoal #1\n    pol ";
        s+=to_string(nlit_to_vid[t.second]); s+=' '; s+=to_string(t.first); s+=" * "; s+=to_string(++nb_ver_clauses); s+=" +\n"; ++nb_ver_clauses;
        s+="  end -1\n  proofgoal #2\n    pol ";
        s+=to_string(nlit_to_vid[litNegation(t.second)]); s+=' '; s+=to_string(t.first); s+=" * "; s+=to_string(++nb_ver_clauses); s+=" +\n"; ++nb_ver_clauses;
        s+="  end -1\nend";
      }
      outnl();
    }
  }
  outflush();


  // (7) Replace the temporary constraints with the constraints in the desired namespace
  for (auto& c : original_clauses) {
    bool needed = 0;
    for (int l : c.second) if (!keep.count(litVariable(l))) {needed = 1; break;}
    if (!needed) continue;
    if (explicit_new) {
      s+="pol ";
      s+=to_string(clauses[c.first].vid);
      s+=' ';
      for (int l : c.second) {
        if (!nlit_to_vid.count(l)) continue;
        s+=to_string(nlit_to_vid[l]);
        s+=" + ";
      }
      outnl();
    } else {
      s+="rup";
      for (int l : c.second) out_raw_term(map_lit(l, mapping), 'x');
      s+=" >= 1 ;\n";
    }
    out_add_to_core(++nb_ver_clauses);

    if (explicit_remove) {
      out_del_id_pp(clauses[c.first].vid);
      s+=" ; begin\n  pol ";s+=to_string(nb_ver_clauses);s+=' ';
      for (int l : c.second) {
        if (!nlit_to_vid.count(litNegation(l))) continue;
        s+=to_string(nlit_to_vid[litNegation(l)]);
        s+=" + ";
      }
      s+=to_string(++nb_ver_clauses); s+=" +\nend\n";
      nb_ver_clauses++;
      clauses[c.first].vid = nb_ver_clauses-2;
    } else {
      out_del_id(clauses[c.first].vid);
      clauses[c.first].vid = nb_ver_clauses;
    }
  }
  outflush();

  // (8) delete the equivalence clauses introduced in the second mapping step, step (5)
  for (auto& m : mapping) {
    if (!keep.count(litVariable(m.first))) {
      out_del_id_pp(first_clause++); out_raw_substitution(litNegation(m.first), 't'); outnl();
      out_del_id_pp(first_clause++); out_raw_substitution(m.first, 't'); outnl();
    }
  }

  // reset mappings to be able to still use prooflogger
  // every variable is x
  lit_to_blit.clear();
  lit_to_zlit.clear();
  // map unit soft literals
  for (int i=0; i<(int)clauses.size(); ++i) {
    if (clauses[i].unit_soft) clauses[i].ulit = map_lit(clauses[i].ulit, mapping);
    reset_clause_computed_strs(i);
  }

  // log_current_objective();
  // Currently proofchecker complains about 0-coefficients, this fixes it for now:
  s+="obju new";
  for (auto& t : objective) {
    int l = map_lit(t.second, mapping);
    out_raw_term(t.first, l, 'x');
  }
  out_w(0);
  outnl();

  outflush();
}




ProofLogger::ProofLogger(ostream& o, int nbv, int comments_level) :
  out(o), add_comments(comments_level), nb_original_vars(nbv), nb_ver_clauses(0), nb_zvars(0), subst_separ(" -> "), objective_constant(0) {
}
