# UzL Solver for Dominating Set and Hitting Set

This repository contains the submission of Max Bannach, Florian Chudigiewitsch, Marcel Wienöbst to the exact tracks of PACE 2025.

## Installation

We rely on the following system dependencies:

- gcc
- clang
- cmake
- cargo

To install our solvers, execute the following in the project root:
```bash
cargo build --release
```

The solvers can be run as `./target/release/uzl_ds` for the dominating set solver and `./target/release/uzl_hs` for the hitting set solver.

As an example installation, we provide the Dockerfiles `docker-eval/pace-eval-ds-exact/Dockerfile` and `docker-eval/pace-eval-hs-exact/Dockerfile`. The docker compose file in the project root can be used to evaluate the solvers. For this, place the instances under ```docker-eval/instances/ds/``` and ```docker-eval/instances/hs/```. The output is written to ```docker-eval/output/```.
