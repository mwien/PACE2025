//! This module provides the `Presolve` structure and its associated methods.
//!
//! # Overview
//! `Presolve` encapsulates preprocessing and reduction rules for the *hitting set* problem.
//!
//! # Interaction
//! The module is used by initializing the `Presolve` structure using the `new` function, which
//! expects as input an iterator over strings encoding a PACE 2025 file.
//!
//! ```
//! // If a PACE 2025 file is piped to the program:
//! let mut presolve = Presolve::new( io::stdin().lock().lines().flatten() );
//! ```
//!
//! Alternatively, you can construct presolve using the ```from_edge_list``` function, which
//! expects ```n```, the number of elements, and a &Vec<Vec<usize>> containing the edges (with
//! elements given 1-indexed).
//!
//! ## Applying Reduction Rules
//!
//! To start the presolve, the `apply` function needs to be called.
//! An optional time limit in seconds can be given.
//!
//! ```
//! presolve.apply(None); // applies the reduction rules exhaustively
//! presolve.apply(Some(60)); // applies the reduction rules for 60 seconds
//! ```
//!
//! Note that the time limits only the fact that after the given time, no new reduction rule is applied.
//! If a reduction rule was started before the time limit is hit, it is always finished (wish may take more time).
//!
//! ## Getting the Reduced Instance
//!
//! There are two methods to obtain the reduced instance:
//!
//! - `get_instance` returns a vector of strings, representing the new instance in PACE 2025 format
//! - `get_remaining_edges` return a vector of vectors of usize, representing the remaining edges
//!
//! Presolve may also detect vertices that need to be added to any solution. These can be retrieved using:
//!
//! - `get_picks` which returns a vector of usize
//!
//! ## Obtaining Statistics
//!
//! Once presolve is completed, statistics can be retrieved using `get_stats`, which returns a vector containing in order:
//! - number of picked vertices
//! - number of discarded vertices
//! - number of discarded edges
//! - how often was the unit edge rule was applied
//! - how often was the unit node rule was applied
//! - how often was the edge domination rule was applied
//! - how often was the node domination rule was applied
//!

use std::collections::HashSet;
use std::time::Instant;

pub struct Presolve {
    // encoding of the hypergraph
    n: usize,
    link: Vec<Vec<(usize, usize)>>,
    edges: Vec<Vec<(usize, usize)>>,
    link_lookup: Vec<HashSet<usize>>,
    edges_lookup: Vec<HashSet<usize>>,
    // data structures to manage reduction rules
    picks: Vec<usize>,
    unit_edges: Vec<usize>,
    unit_nodes: Vec<usize>,
    // Bookkeeping
    n_unit_edge_rule: usize,
    n_unit_node_rule: usize,
    n_node_domination_rule: usize,
    n_edge_domination_rule: usize,
}

/*
 * ========= Public Interface =========
*/

impl Presolve {
    pub fn new<T>(input: T) -> Presolve
    where
        T: IntoIterator<Item = String>,
    {
        let mut n = 0;
        let mut link = Vec::new();
        let mut edges = Vec::new();
        let mut edges_lookup = Vec::new();
        for line in input {
            let ll = line.split(" ").collect::<Vec<_>>();
            if ll[0] == "c" {
                continue;
            }
            if ll[0] == "p" {
                n = ll[2].parse::<usize>().unwrap();
                link = vec![Vec::new(); n];
                continue;
            }
            let e = ll
                .into_iter()
                .map(|v| v.parse::<usize>().unwrap())
                .collect::<Vec<_>>();
	    edges_lookup.push(HashSet::from_iter(e.iter().map(|&x| x - 1)));
            edges.push(Vec::new());
            let e_idx = edges.len() - 1;
            for (i, &v_one_indexed) in e.iter().enumerate() {
                let v = v_one_indexed - 1;
                edges[e_idx].push((v, link[v].len()));
                link[v].push((e_idx, i));
            }
        }
        let link_lookup: Vec<_> = link
            .iter()
            .map(|l| HashSet::from_iter(l.iter().map(|(x, _)| x).copied()))
            .collect();
        Presolve {
            n,
            link,
            edges,
            link_lookup,
            edges_lookup,
            picks: Vec::new(),
            unit_edges: Vec::new(),
            unit_nodes: Vec::new(),
            n_unit_edge_rule: 0,
            n_unit_node_rule: 0,
            n_node_domination_rule: 0,
            n_edge_domination_rule: 0,
        }
    }

    pub fn from_edge_list(n: usize, edge_list: &[Vec<usize>]) -> Presolve {
        let mut link = vec![Vec::new(); n];
        let mut edges = Vec::new();
        let mut edges_lookup = Vec::new();
        for e in edge_list.iter() {
            edges_lookup.push(HashSet::from_iter(e.iter().map(|&x| x - 1)));
            edges.push(Vec::new());
            let e_idx = edges.len() - 1;
            for (i, &v_one_indexed) in e.iter().enumerate() {
                let v = v_one_indexed - 1;
                edges[e_idx].push((v, link[v].len()));
                link[v].push((e_idx, i));
            }
        }
        let link_lookup: Vec<_> = link
            .iter()
            .map(|l| HashSet::from_iter(l.iter().map(|(x, _)| x).copied()))
            .collect();
        Presolve {
            n,
            link,
            edges,
            link_lookup,
            edges_lookup,
            picks: Vec::new(),
            unit_edges: Vec::new(),
            unit_nodes: Vec::new(),
            n_unit_edge_rule: 0,
            n_unit_node_rule: 0,
            n_node_domination_rule: 0,
            n_edge_domination_rule: 0,
        }
    }

    pub fn apply(&mut self, time_s: Option<u64>) {
        // scan for unit edges
        self.edges
            .iter()
            .enumerate()
            .filter(|(_, e)| e.len() == 1)
            .for_each(|(i, _)| self.unit_edges.push(i));

        // scan for unit nodes
        self.link
            .iter()
            .enumerate()
            .filter(|(_, link)| link.len() == 1)
            .for_each(|(v, _)| self.unit_nodes.push(v));

        let tstart = Instant::now();
        let duration = time_s.unwrap_or(u64::MAX);
        let mut flag = true;
        while flag {
            flag = self.unit_edge_rule();
            flag |= self.unit_node_rule();
            flag |= self.node_domination_rule();
            flag |= self.edge_domination_rule();
            if tstart.elapsed().as_secs() >= duration {
                flag = false;
            }
        }
    }

    pub fn get_picks(&self) -> Vec<usize> {
        self.picks.iter().map(|x| x + 1).collect()
    }

    pub fn get_remaining_edges(&self) -> Vec<Vec<usize>> {
        self.edges
            .iter()
            .filter(|e| !e.is_empty())
            .map(|e| e.iter().map(|&(x, _)| x + 1).collect::<Vec<_>>())
            .collect()
    }

    pub fn get_instance(&self) -> Vec<String> {
        let mut buffer = Vec::new();
        buffer.push(format!(
            "p hs {} {}",
            self.n,
            self.edges.iter().filter(|e| !e.is_empty()).count()
        ));
        self.edges.iter().filter(|e| !e.is_empty()).for_each(|e| {
            buffer.push(
                e.iter()
                    .map(|&(v, _)| (v + 1).to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
                    .to_string(),
            )
        });
        buffer
    }

    pub fn get_stats(&self) -> Vec<usize> {
        vec![
            self.picks.len(),
            (0..self.n).filter(|&v| self.link[v].is_empty()).count(),
            self.edges.iter().filter(|e| e.is_empty()).count(),
            self.n_unit_edge_rule,
            self.n_unit_node_rule,
            self.n_edge_domination_rule,
            self.n_node_domination_rule,
        ]
    }
}

/*
 * ========= Helpers (Private) =========
*/

fn update_index(
    primal: &mut [Vec<(usize, usize)>],
    dual: &mut [Vec<(usize, usize)>],
    primal_val: usize,
    primal_idx: usize,
) {
    if primal_idx < primal[primal_val].len() {
        let (swapped_dual_val, swapped_dual_idx) = primal[primal_val][primal_idx];
        dual[swapped_dual_val][swapped_dual_idx] = (primal_val, primal_idx);
    }
}

fn rem_and_update(
    primal: &mut [Vec<(usize, usize)>],
    dual: &mut [Vec<(usize, usize)>],
    primal_val: usize,
    primal_idx: usize,
) {
    // swap remove element at index idx in primal
    let (dual_val, dual_idx) = primal[primal_val][primal_idx];
    primal[primal_val].swap_remove(primal_idx);

    // take care of dual
    dual[dual_val].swap_remove(dual_idx);

    // update idxs of swapped els
    update_index(primal, dual, primal_val, primal_idx);
    update_index(dual, primal, dual_val, dual_idx);
}

fn is_subset(x: &[(usize, usize)], y: &HashSet<usize>) -> bool {
    if x.len() > y.len() {
        return false;
    }
    for (el, _) in x.iter() {
        if !y.contains(el) {
            return false;
        }
    }
    true
}

/*
 * ========= Reduction Rules (Private) =========
*/

impl Presolve {
    fn delete_edge(&mut self, e_idx: usize) {
        let edge = self.edges[e_idx].clone();
        for &(v, i) in edge.iter() {
            // this removes element from self.edges as well
            rem_and_update(&mut self.link, &mut self.edges, v, i);
            if self.link[v].len() == 1 {
                self.unit_nodes.push(v);
            }
        }
    }

    fn select_node(&mut self, v: usize) {
        self.picks.push(v);
        let link = self.link[v].clone();
        for (e, _) in link {
            self.delete_edge(e);
        }
    }

    fn discard_node(&mut self, v: usize) {
        let link = self.link[v].clone();
        for &(e, i) in link.iter() {
            // this removes element from self.link as well
            rem_and_update(&mut self.edges, &mut self.link, e, i);
            if self.edges[e].len() == 1 {
                self.unit_edges.push(e);
            }
        }
    }

    fn unit_edge_rule(&mut self) -> bool {
        let mut flag = false;
        while let Some(e) = self.unit_edges.pop() {
            if self.edges[e].len() != 1 {
                continue;
            } // e is not unit any more
            let (v, _) = *self.edges[e].first().unwrap();
            self.select_node(v);
            flag = true;
            self.n_unit_edge_rule += 1;
        }
        flag
    }

    fn unit_node_rule(&mut self) -> bool {
        let mut flag = false;
        while let Some(v) = self.unit_nodes.pop() {
            if self.link[v].len() != 1 {
                continue;
            } // v is not unit any more
            let (e, _) = *self.link[v].first().unwrap();
            if self.edges[e].len() != 1 {
                self.discard_node(v);
            }
            flag = true;
            self.n_unit_node_rule += 1;
        }
        flag
    }

    fn node_domination_rule(&mut self) -> bool {
        let mut flag = false;
        for v in 0..self.n {
            if self.link[v].is_empty() {
                continue;
            }

            let smallest_edge = self.link[v]
                .iter()
                .min_by_key(|&(x, _)| self.edges[*x].len())
                .unwrap()
                .0;

            let sparse_candidates: Vec<usize> =
                self.edges[smallest_edge].iter().map(|(w, _)| *w).collect();

            for &w in sparse_candidates.iter() {
                if v != w && is_subset(&self.link[v], &self.link_lookup[w]) {
                    self.discard_node(v);
                    flag = true;
                    self.n_node_domination_rule += 1;
                    break;
                }
            }
        }
        flag
    }

    fn edge_domination_rule(&mut self) -> bool {
        let mut flag = false;
        for e in 0..self.edges.len() {
            if self.edges[e].is_empty() {
                continue;
            }

            let smallest_link = self.edges[e]
                .iter()
                .min_by_key(|&(x, _)| self.link[*x].len())
                .unwrap()
                .0;

            let sparse_candidates: Vec<usize> =
                self.link[smallest_link].iter().map(|(f, _)| *f).collect();

            for &f in sparse_candidates.iter() {
                if e != f && is_subset(&self.edges[e], &self.edges_lookup[f]) {
                    self.delete_edge(f);
                    flag = true;
                    self.n_edge_domination_rule += 1;
                    break;
                }
            }
        }
        flag
    }
}
