//! Bindings to the maxpre2 MaxSAT preprocessor.

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(dead_code)]

pub mod bindings {
    include!(concat!(env!("OUT_DIR"), "/maxpre_bindings.rs"));
}

pub struct MaxPre {
    inner: *mut bindings::CMaxPre,
}

impl MaxPre {
    pub fn new(hard: Vec<Vec<i32>>, soft: Vec<(Vec<i32>, u64)>) -> Self {
        unsafe {
            let top = soft.iter().map(|(_, w)| *w).sum::<u64>() + 1;
            let inner = bindings::cmaxpre_init_start(top, 0);

            for c in hard {
                for l in c {
                    bindings::cmaxpre_init_add_lit(inner, l)
                }
                bindings::cmaxpre_init_add_lit(inner, 0);
            }

            for (c, w) in soft {
                bindings::cmaxpre_init_add_weight(inner, w);
                for l in c {
                    bindings::cmaxpre_init_add_lit(inner, l);
                }
                bindings::cmaxpre_init_add_lit(inner, 0);
            }

            bindings::cmaxpre_init_finalize(inner);
            MaxPre { inner }
        }
    }

    pub fn run(
        &mut self,
        techniques: &str,
        log: bool,
        time_limit: f64,
    ) -> (Vec<Vec<i32>>, Vec<(Vec<i32>, u64)>) {
        unsafe {
            bindings::cmaxpre_preprocess(
                self.inner,
                std::ffi::CString::new(techniques).unwrap().as_ptr(),
                match log {
                    true => 2,
                    _ => 0,
                },
                time_limit,
                0,
                0,
            );

            let (mut hard, mut soft) = (Vec::new(), Vec::new());
            for i in 0..self.get_n_clauses() {
                let c = self.get_clause(i);
                let w = self.get_weight(i);
                match w == self.top() {
                    true => hard.push(c),
                    false => soft.push((c, w)),
                }
            }
            (hard, soft)
        }
    }

    fn top(&mut self) -> u64 {
        unsafe { bindings::cmaxpre_get_top_weight(self.inner) }
    }

    fn get_n_clauses(&mut self) -> u32 {
        unsafe { bindings::cmaxpre_get_n_prepro_clauses(self.inner) }
    }

    fn get_weight(&mut self, i: u32) -> u64 {
        unsafe { bindings::cmaxpre_get_prepro_weight(self.inner, i, 0) }
    }

    fn get_clause(&mut self, i: u32) -> Vec<i32> {
        unsafe {
            let mut c = Vec::new();
            for j in 0.. {
                let l = bindings::cmaxpre_get_prepro_lit(self.inner, i, j);
                if l == 0 {
                    break;
                }
                c.push(l);
            }
            c
        }
    }

    pub fn get_fixed(&mut self) -> Vec<i32> {
        unsafe {
            let mut fixed = Vec::new();
            for i in 0..bindings::cmaxpre_get_n_prepro_fixed(self.inner) {
                fixed.push(bindings::cmaxpre_get_prepro_fixed_lit(self.inner, i));
            }
            fixed
        }
    }

    pub fn reconstruct(&mut self, n: usize, assignment: Vec<i32>) -> Vec<i32> {
        unsafe {
            for l in assignment {
                bindings::cmaxpre_assignment_add(self.inner, l);
            }
            bindings::cmaxpre_reconstruct(self.inner);
            (1..=n)
                .map(|v| bindings::cmaxpre_reconstructed_val(self.inner, v as i32))
                .collect()
        }
    }
}
