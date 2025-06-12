use crate::Graph;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::mem::swap;

#[derive(Debug, Clone)]
pub struct Hypergraph {
    pub n: usize,
    pub sets: Vec<Vec<usize>>,
}

impl Hypergraph {
    pub fn new(n: usize) -> Hypergraph {
        Hypergraph {
            n,
            sets: Vec::new(),
        }
    }

    pub fn new_from_file(file_name: &str) -> Hypergraph {
        let file = File::open(file_name).unwrap();
        let reader = BufReader::new(file);
        let mut n = 0;
        let mut sets = Vec::new();
        for line in reader.lines() {
            let line = line.unwrap();
            let line = line.trim();
            let tokens: Vec<&str> = line.split(' ').collect();
            match tokens[0] {
                "c" => {}
                "p" => {
                    n = tokens[2].parse::<usize>().unwrap();
                }
                _ => {
                    let mut set: Vec<_> =
                        tokens.iter().map(|x| x.parse::<usize>().unwrap()).collect();
                    set.sort();
                    set.dedup();
                    sets.push(set);
                }
            }
        }
        Hypergraph { n, sets }
    }

    pub fn new_from_graph(g: Graph) -> Hypergraph {
        let mut h = Hypergraph::new(g.n);
        for u in 0..g.n {
            let mut neighborhood = g.neighbors[u].to_vec();
            neighborhood.push(u);
            h.add_set(neighborhood);
        }
        h
    }

    fn add_set(&mut self, set: Vec<usize>) {
        let mut sorted_set = set.clone();
        sorted_set.sort();
        sorted_set.dedup();
        self.sets
            .push(sorted_set.into_iter().map(|x| x + 1).collect::<Vec<_>>());
    }

    pub fn prune(&self) -> (Self, Vec<usize>) {
        // remove irrelevant vertices
        let mut cnt_links = vec![0; self.n + 1];
        for set in self.sets.iter() {
            set.iter().for_each(|&x| cnt_links[x] += 1);
        }

        let mut inv_mapping = vec![None; self.n + 1];
        let mut mapping = vec![0]; // could init with final size
        let mut cnt = 1;
        for v in 1..self.n + 1 {
            if cnt_links[v] > 0 {
                inv_mapping[v] = Some(cnt);
                mapping.push(v);
                cnt += 1;
            }
        }

        let new_n = mapping.len() - 1;
        let mut new_sets = Vec::new();
        for set in self.sets.iter() {
            let new_set: Vec<_> = set
                .iter()
                .filter(|&x| inv_mapping[*x].is_some())
                .map(|&x| inv_mapping[x].unwrap())
                .collect();
            if !new_set.is_empty() {
                new_sets.push(new_set);
            }
        }

        (
            Hypergraph {
                n: new_n,
                sets: new_sets,
            },
            mapping,
        )
    }

    pub fn is_sat_instance(&self) -> bool {
        if self.n % 2 != 0 {
            return false;
        }
        let mut matched = vec![false; self.n];
        for set in self.sets.iter() {
            if set.len() == 2 {
                let mut a = set[0];
                let mut b = set[1];
                if a > b {
                    swap(&mut a, &mut b);
                }
                if b == a + 1 && a % 2 == 1 {
                    matched[a - 1] = true;
                    matched[b - 1] = true;
                }
            }
        }
        matched.iter().all(|&x| x)
    }

    pub fn is_vc_instance(&self) -> bool {
        self.sets.iter().all(|set| set.len() == 2)
    }
}
