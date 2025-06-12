#ifndef Formula_H_
#define Formula_H_
#include <cstdint>
#include <cstdio>
#include <optional>
#include <vector>

namespace Eval
{
  class Formula
  {
  private:
    void *monMaxSat;

  public:
    Formula();
    ~Formula();

    
    int addClause(const int ps[], size_t length, long w = 0);
    bool getValue(int lit);
    bool solve();
  };
};
#endif
