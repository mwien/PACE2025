use crate::Hypergraph;
use gag::Gag;

extern "C" {
    pub fn mcqd_solve(
        num_edges: ::std::os::raw::c_int,
        from_node: *const ::std::os::raw::c_int,
        to_node: *const ::std::os::raw::c_int,
        solution: *mut ::std::os::raw::c_int,
    ) -> ::std::os::raw::c_int;

}

pub fn vc_solve(g: &Hypergraph) -> Vec<usize> {
    let mut am = vec![vec![false; g.n + 1]; g.n + 1];
    for set in g.sets.iter() {
        // assume set has length 2
        am[set[0]][set[1]] = true;
        am[set[1]][set[0]] = true;
    }
    let mut num_edges: i32 = 0;
    let mut from_node = Vec::new();
    let mut to_node = Vec::new();
    #[allow(clippy::needless_range_loop)]
    for i in 1..g.n + 1 {
        for j in 1..g.n + 1 {
            if i == j {
                continue;
            }
            if !am[i][j] {
                from_node.push(i as i32);
                to_node.push(j as i32);
                num_edges += 1;
            }
        }
    }

    if num_edges == 0 {
        // add all but last node
        return (1..g.n).collect();
    }

    let mut solution = vec![0_i32; g.n + 1];

    {
        let _gag = Gag::stdout().unwrap();
        unsafe {
            mcqd_solve(
                num_edges,
                from_node.as_ptr(),
                to_node.as_ptr(),
                solution.as_mut_ptr(),
            );
        }
    }

    let mut result = Vec::new();
    #[allow(clippy::needless_range_loop)]
    for i in 1..g.n + 1 {
        if solution[i] == 0 {
            result.push(i);
        }
    }
    result
}
