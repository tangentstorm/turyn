use std::env;
use std::fs;
use std::process;
use std::time::Instant;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 || args[1] == "--help" || args[1] == "-h" {
        eprintln!("Usage: radical <file.cnf>");
        eprintln!("  Reads a DIMACS CNF file and solves it with the radical CDCL solver.");
        process::exit(if args.len() < 2 { 1 } else { 0 });
    }

    let path = &args[1];
    let contents = fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", path, e);
        process::exit(1);
    });

    let start = Instant::now();
    let mut solver = radical::parse_dimacs(&contents);
    let parse_elapsed = start.elapsed();
    eprintln!("Parsed: {} vars, {} clauses in {:.3?}", solver.num_vars(), solver.num_clauses(), parse_elapsed);

    let solve_start = Instant::now();
    let result = solver.solve();
    let solve_elapsed = solve_start.elapsed();

    match result {
        Some(true) => {
            println!("s SATISFIABLE");
            let mut vals = String::from("v");
            for v in 1..=solver.num_vars() as i32 {
                let lit = if solver.value(v) == Some(true) { v } else { -v };
                vals.push_str(&format!(" {}", lit));
            }
            vals.push_str(" 0");
            println!("{}", vals);
        }
        Some(false) => {
            println!("s UNSATISFIABLE");
        }
        None => {
            println!("s UNKNOWN");
        }
    }
    eprintln!("Solved in {:.3?}, {} conflicts", solve_elapsed, solver.num_conflicts());
    process::exit(match result {
        Some(true) => 10,
        Some(false) => 20,
        None => 0,
    });
}
