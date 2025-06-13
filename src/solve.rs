use crate::{vcsolve, Formula, Graph, Hypergraph, MaxPre, Presolve};

use gag::Gag;

pub enum Task {
    DominatingSet,
    HittingSet,
}

struct Settings {
    maxpre: bool,
    maxpre_techniques: String,
    maxpre_time: f64,
    prune: bool,
}

pub fn solve(task: Task) {
    let mut h = match task {
        Task::DominatingSet => Hypergraph::new_from_graph(Graph::new_from_stdin()),
        Task::HittingSet => Hypergraph::new_from_stdin(),
    };

    let settings = match task {
        Task::DominatingSet => Settings {
            maxpre: true,
            maxpre_techniques: "[bu]#[buvsrglehtG]".to_owned(),
            maxpre_time: 1e20,
            prune: true,
        },
        Task::HittingSet => Settings {
            maxpre: false,
            maxpre_techniques: "[bu]#[buvsrglehtG]".to_owned(),
            maxpre_time: 1e20,
            prune: true,
        },
    };

    // Apply Hitting Set Presolve.
    let mut presolve = Presolve::from_edge_list(h.n, &h.sets);
    presolve.apply(None);
    h.sets = presolve.get_remaining_edges();
    let mut picked: Vec<_> = presolve.get_picks();

    let (g, mapping) = if settings.prune {
        h.prune()
    } else {
        (h.clone(), (0..h.n + 1).collect::<Vec<usize>>())
    };

    // Solve SAT instances with Kissat
    if g.is_sat_instance() {
        let mut solver = kissat::Solver::new();
        let mut vars = Vec::new();
        for _ in 0..g.n / 2 {
            vars.push(solver.var());
        }
        for set in g.sets.iter() {
            let clause: Vec<_> = set
                .iter()
                .map(|x| {
                    if x % 2 == 1 {
                        vars[x / 2]
                    } else {
                        !vars[(x - 1) / 2]
                    }
                })
                .collect();
            solver.add(&clause);
        }
        if let Some(solution) = solver.sat() {
            let mut result = picked.clone();
            for x in 0..g.n / 2 {
                match solution.get(vars[x]) {
                    Some(true) => result.push(mapping[x * 2 + 1]),
                    Some(false) => result.push(mapping[x * 2 + 2]),
                    None => (),
                };
            }
            println!("{}", result.len());
            for v in result.iter() {
                println!("{}", v);
            }
            return;
        }
    }

    // Solve VC Instances via a Clique solver
    if g.is_vc_instance() && g.n <= 350 {
        let mut result = picked.clone();
        let solution = vcsolve::vc_solve(&g);
        for &u in solution.iter() {
            result.push(mapping[u]);
        }
        println!("{}", result.len());
        for v in result.iter() {
            println!("{}", v);
        }
        return;
    }

    // Remaining instances use MaxSAT solver
    // Build the MaxSAT formula
    let mut hard = Vec::new();
    let mut soft = Vec::new();
    for set in g.sets.iter() {
        hard.push(set.iter().map(|x| *x as i32).collect());
    }
    for v in 1..=g.n {
        soft.push((vec![-(v as i32)], 1));
    }

    // Apply MaxSAT preprocessing
    let mut maxpre = MaxPre::new(hard.clone(), soft.clone());
    let (hard, soft) = match settings.maxpre {
        true => maxpre.run(
            settings.maxpre_techniques.as_str(),
            false,
            settings.maxpre_time,
        ),
        false => (hard, soft),
    };

    // Run solver
    let mut phi = Formula::new();
    for c in hard.iter() {
        phi.add_clause(c, None);
    }
    for (c, w) in soft.iter() {
        phi.add_clause(c, Some(*w as i64));
    }
    let result = {
        let _gag = Gag::stdout().unwrap();
        phi.solve()
    };

    // Reconstruct and output
    if result {
        let sol = (1..=g.n)
            .map(|v| v as i32)
            .map(|v| match phi.value(v) {
                true => v,
                false => -v,
            })
            .collect::<Vec<i32>>();
        let sol = match settings.maxpre {
            true => maxpre.reconstruct(g.n, sol),
            false => sol,
        };

        for v in sol {
            if v > 0 {
                picked.push(mapping[v as usize]);
            }
        }
        println!("{}", picked.len());
        for v in picked.iter() {
            println!("{}", v);
        }
    }
}
