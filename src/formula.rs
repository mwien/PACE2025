#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(dead_code)]

pub mod bindings {
    include!(concat!(env!("OUT_DIR"), "/evalmaxsat_bindings.rs"));
}

pub struct Formula {
    inner: bindings::Eval_Formula,
}

impl Default for Formula {
    fn default() -> Self {
        Self::new()
    }
}

impl Formula {
    pub fn new() -> Self {
        unsafe {
            Formula {
                inner: bindings::Eval_Formula::new(),
            }
        }
    }

    pub fn add_clause(&mut self, clause: &[i32], w: Option<i64>) {
        unsafe {
            self.inner
                .addClause(clause.as_ptr(), clause.len(), w.unwrap_or(0));
        }
    }

    pub fn solve(&mut self) -> bool {
        unsafe { self.inner.solve() }
    }

    pub fn value(&mut self, lit: i32) -> bool {
        unsafe { self.inner.getValue(lit) }
    }
}
