use std::fs::File;
use std::io::{BufRead, BufReader};

pub struct Graph {
    pub n: usize,
    pub neighbors: Vec<Vec<usize>>,
}

impl Graph {
    pub fn new_from_file(file_name: &str) -> Graph {
        let file = File::open(file_name).unwrap();
        let reader = BufReader::new(file);
        let mut adj_list = Vec::new();
        for line in reader.lines() {
            let line = line.unwrap();
            let line = line.trim();
            let tokens: Vec<&str> = line.split(' ').collect();
            match tokens[0] {
                "c" => {}
                "p" => {
                    let n = tokens[2].parse::<usize>().unwrap();
                    adj_list = vec![Vec::new(); n];
                }
                _ => {
                    let a = tokens[0].parse::<usize>().unwrap();
                    let b = tokens[1].parse::<usize>().unwrap();
                    adj_list[a - 1].push(b - 1);
                    adj_list[b - 1].push(a - 1);
                }
            }
        }
        Graph {
            n: adj_list.len(),
            neighbors: adj_list,
        }
    }
}
