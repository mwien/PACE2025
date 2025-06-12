#include "Formula.hpp"
#include "cadicalinterface.h"
#include "EvalMaxSAT.h"
namespace Eval
{
  
  Formula::Formula() {
    monMaxSat = new EvalMaxSAT<Solver_cadical>();
  }
  
  Formula::~Formula() {
    EvalMaxSAT<Solver_cadical> *monMaxSat = (EvalMaxSAT<Solver_cadical> *)this->monMaxSat;
    delete monMaxSat;
    this->monMaxSat = nullptr;
  }

  int Formula::addClause(const int ps[], size_t length, long w) {
    EvalMaxSAT<Solver_cadical> *monMaxSat = (EvalMaxSAT<Solver_cadical> *)this->monMaxSat;
    std::vector<int> clause;
    for (size_t i = 0; i < length; i++) {
      int lit = ps[i];
      while (abs(lit) > monMaxSat->nVars()) monMaxSat->newVar();
      clause.push_back(lit);
    }
    
    std::optional<long long> ww = {};
    if (w > 0) { ww = w; }
    return monMaxSat->addClause(clause, ww);
  }

  bool Formula::getValue(int lit) {
    EvalMaxSAT<Solver_cadical> *monMaxSat = (EvalMaxSAT<Solver_cadical> *)this->monMaxSat;
    return monMaxSat->getValue(lit);
  }

  bool Formula::solve() {
    EvalMaxSAT<Solver_cadical> *monMaxSat = (EvalMaxSAT<Solver_cadical> *)this->monMaxSat;
    return monMaxSat->solve();
  }

  
};
