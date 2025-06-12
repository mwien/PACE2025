#ifndef EVALMAXSAT_UTILE_H__
#define EVALMAXSAT_UTILE_H__

#include <vector>
#include <cmath>
#include <cassert>
#include <tuple>

#include "ParseUtils.h"


std::string savePourTest_file;

typedef unsigned long long int t_weight;

class WeightVector {
    std::vector<long long int> _weight;
public:
    long long int operator[](int lit) {
        assert(abs(lit) < _weight.size());
        return (_weight[abs(lit)] ^ (lit >> 31)) - (lit >> 31);
    }

    unsigned int size() const {
        return _weight.size();
    }

    void resize(unsigned int newSize) {
        _weight.resize(newSize);
    }

    void push_back(long long int v) {
        _weight.push_back(v);
    }

    void set(int lit, long long int weight) {
        assert(abs(lit) < _weight.size());
        if(lit < 0 ) {
            _weight[-lit] = -weight;
        } else {
            _weight[lit] = weight;
        }
    }

    void add(int lit, long long int weight) {
        assert(abs(lit) < _weight.size());
        if(lit < 0 ) {
            _weight[-lit] += -weight;
        } else {
            _weight[lit] += weight;
        }
    }
};

template<class T>
class doublevector {

    std::vector<T> posIndexVector;
    std::vector<T> negIndexVector;

public:

    void push_back(const T& v) {
        posIndexVector.push_back(v);
    }

    T& back() {
        if(posIndexVector.size()) {
            return posIndexVector.back();
        } else {
            return negIndexVector[0];
        }
    }

    void pop_back() {
        if(posIndexVector.size()) {
            posIndexVector.pop_back();
        } else {
            negIndexVector.erase(negIndexVector.begin());
        }
    }

    void add(int index, const T& val) {
        if(index >= 0) {
            if(index >= posIndexVector.size()) {
                posIndexVector.resize(index+1);
            }
            posIndexVector[index] = val;
        } else {
            if(-index >= negIndexVector.size()) {
                negIndexVector.resize((-index)+1);
            }
            negIndexVector[-index] = val;
        }
    }

    T& operator [](int index) {
        if(index >= 0) {
            assert( index < posIndexVector.size() );
            return posIndexVector[index];
        } else {
            assert( -index < negIndexVector.size() );
            return negIndexVector[-index];
        }
        assert(false);
    }

    T& get(int index) {
        if(index >= 0) {
            if(index >= posIndexVector.size()) {
                posIndexVector.resize(index+1);
            }
            return posIndexVector[index];
        } else {
            if(-index >= negIndexVector.size()) {
                negIndexVector.resize((-index)+1);
            }
            return negIndexVector[-index];
        }
    }


};


/// POUR DEBUG ////
template<class B>
static void readClause(B& in, std::vector<int>& lits) {
    int parsed_lit;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        lits.push_back( parsed_lit );
    }
}

/// POUR DEBUG ////
t_weight calculateCost(const std::string & file, std::vector<bool> &result) {
    t_weight cost = 0;
   
    return cost;
}


template<class MAXSAT_SOLVER>
std::vector<int> readClause(StreamBuffer &in, MAXSAT_SOLVER* solveur) {
    std::vector<int> clause;

    for (;;) {
        int lit = parseInt(in);

        if (lit == 0)
            break;
        clause.push_back(lit);
        while( abs(lit) > solveur->nVars()) {
            solveur->newVar();
        }
    }

    return clause;
}

template<class MAXSAT_SOLVER>
bool parse(const std::string& filePath, MAXSAT_SOLVER* solveur) {
    return true;
 }


std::vector<int> readClause(StreamBuffer &in) {
    std::vector<int> clause;

    for (;;) {
        int lit = parseInt(in);
        if (lit == 0)
            break;
        clause.push_back(lit);
    }

    return clause;
}




#endif
