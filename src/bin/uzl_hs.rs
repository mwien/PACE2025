use solve::Task;
use solver::solve;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    solve::solve(Task::HittingSet, &args[1]);
}
