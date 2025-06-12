FROM ubuntu:22.04

# Basic Setup
RUN apt-get update && apt-get install -y \
    build-essential \
    python3 \
    python3-pip \
    time \
    util-linux \
    && rm -rf /var/lib/apt/lists/*

RUN apt update && apt install openjdk-21-jdk -y

# INSTALL YOUR SOLVER AND DEPENDENCIES HERE
RUN apt-get install -y \
    curl \
    cmake \
    clang
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"
COPY ../../build.rs /solver/build.rs
COPY ../../Cargo.toml /solver/Cargo.toml
COPY ../../Cargo.lock /solver/Cargo.lock
COPY ../../native/ /solver/native/
COPY ../../src/ /solver/src/
WORKDIR /solver
RUN cargo build --release
# END OF YOUR CODE HERE.

# working directory
# NOTE: changed lines below
WORKDIR /docker-eval
COPY docker-eval/src/eval.py eval.py
COPY docker-eval/src/ds_verifier.py verifier.py

RUN mkdir -p /output && chmod 777 /output
CMD ["python3", "eval.py"]
