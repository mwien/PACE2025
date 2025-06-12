#!/usr/bin/python3
import sys

class Solution:
    # This class is used to store the solution of a graph
    # k denotes the solution size and vertices is a list containing the solution
    def __init__(self, k, vertices):
        self.k = k
        self.vertices = vertices

class HyperGraph:
    # Create a hypergraph from a list of hyperedges
    # Edges are tuples of the form (v1, v2, ..., vk)
    def __init__(self, num_vertices, edges):
        self.vertices = list(range(1, num_vertices + 1))
        self.num_edges = len(edges)
        self.edges = {} # adjacency list: maps a vertex to a list of hyperedges

        if edges:
            for e in edges:
                sorted(e) # sort all edges to make them comparable
                for u in e:
                    self.edges.setdefault(u, []).append(e)

    # Return a list of hyperedges incident to the given vertex
    def incident_hyperedges(self, u):
        return self.edges[u] if u in self.edges else []
    
    
# Returns a graph from the given .hgr file
# The file should be in the format of the DIMACS graph format
def read_hypergraph(filename):
    with open(filename, "r", encoding='utf-8') as gr:
        n = 0
        edges = []
        for line in gr:
            line = line.strip()
            if line == "" or line[0] == "c":
                continue

            if line[0] == "p":
                n = int(line.split(" ")[2])
            else:
                edges.append(tuple(map(int, line.split(" "))))

        return HyperGraph(n, edges)

# Read the solution from a file
def read_solution(filename):
    vertices = []
    k = -1
    with open(filename, "r", encoding='utf-8') as f:
        # Read the first non-comment line to get the size of the solution
        # Then collect the vertices of the solution
        foundFirstLine = False
        for line in f.readlines():
            if line.strip() == "" or line[0] == "c":
                continue

            if not foundFirstLine:
                foundFirstLine = True
                k = int(line.strip())
            else:
                vertices.append(int(line.strip()))   
            
    return Solution(k, vertices)

def verify_solution(graph, solution):
    # Check if the solution size matches the number of vertices in the solution
    if solution.k != len(solution.vertices):
        return False
    
    # Check if all vertices are unique
    if len(set(solution.vertices)) != len(solution.vertices):
        return False

    # Check if all vertices are in the range [1, n]
    for v in solution.vertices:
        if v < 1 or v > len(graph.vertices):
            return False


    # Check if the solution is a hitting set
    dom = set()
    for v in solution.vertices:
        for u in graph.incident_hyperedges(v):
            dom.add(u)

    return len(dom) == graph.num_edges

# Read graph and user solution
def main():
    try:
        try: 
            graph = read_hypergraph(sys.argv[1])
        except Exception as e:
            print("could not read input graph correctly")
            return -1
        
        if(len(sys.argv) < 3):
            print("no user solution provided")
            return -1

        try:    
            their_solution = read_solution(sys.argv[2])
        except Exception as e:
            print("could not read user solution correctly")
            return -1
        
        if not verify_solution(graph, their_solution):
            print("user solution is not valid")
            return -1        

        print(f"{their_solution.k}")
        return 0

    except Exception as e:
        print("something went very wrong")
        return -1

if __name__ == '__main__':
    sys.exit(main())