/*
    Copyright 2007-2012 Janez Konc

    If you use this program, please cite:
    Janez Konc and Dusanka Janezic. An improved branch and bound algorithm for
   the maximum clique problem. MATCH Commun. Math. Comput. Chem., 2007, 58,
   569-590.

    More information at: http://www.sicmm.org/~konc

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include "mcqd.h"
#include <assert.h>
#include <map>
#include <set>
#include <string.h>

using namespace std;

void read_graph(int numEdges, int *fromNode, int *toNode, bool **&conn,
                int &size) {
  set<int> v;
  multimap<int, int> e;
  for (int i = 0; i < numEdges; ++i) {
    int vi = fromNode[i];
    int vj = toNode[i];
    v.insert(vi);
    v.insert(vj);
    e.insert(make_pair(vi, vj));
  }
  //  size = v.size() + 1;
  size = *v.rbegin() + 1;
  conn = new bool *[size];
  for (int i = 0; i < size; i++) {
    conn[i] = new bool[size];
    memset(conn[i], 0, size * sizeof(bool));
  }
  for (multimap<int, int>::iterator it = e.begin(); it != e.end(); it++) {
    conn[it->first][it->second] = true;
    conn[it->second][it->first] = true;
  }
}

extern "C" void mcqd_solve(int numEdges, int *fromNode, int *toNode,
                           int *solution) {
  bool **conn;
  int size;
  read_graph(numEdges, fromNode, toNode, conn, size);

  mycliquesolver::Maxclique m(conn, size, 0.1);
  int *qmax;
  int qsize;
  m.mcqdyn(qmax, qsize);

  for (int i = 0; i < qsize; i++)
    solution[qmax[i]] = 1;

  delete[] qmax;

  for (int i = 0; i < size; i++)
    delete[] conn[i];
  delete[] conn;
}
