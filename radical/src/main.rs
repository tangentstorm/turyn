use std::env;
use std::fs;
use std::process;
use std::time::Instant;

fn main() {
    let args: Vec<String> = env::args().collect();

    let mut path: Option<String> = None;
    let mut config = radical::SolverConfig::default();
    let mut conflict_limit: u64 = 0;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--help" | "-h" => {
                print_help();
                process::exit(0);
            }
            "--ema-restarts" => config.ema_restarts = true,
            "--no-ema-restarts" => config.ema_restarts = false,
            "--probing" => config.probing = true,
            "--no-probing" => config.probing = false,
            "--rephasing" => config.rephasing = true,
            "--no-rephasing" => config.rephasing = false,
            "--xor-propagation" => config.xor_propagation = true,
            "--no-xor" => config.xor_propagation = false,
            s if s.starts_with("--conflict-limit=") => {
                conflict_limit = s
                    .strip_prefix("--conflict-limit=")
                    .unwrap()
                    .parse()
                    .unwrap_or(0);
            }
            s if !s.starts_with('-') => {
                path = Some(s.to_string());
            }
            _ => {
                eprintln!("Unknown option: {}", args[i]);
                process::exit(1);
            }
        }
        i += 1;
    }

    let Some(path) = path else {
        print_help();
        process::exit(1);
    };

    let contents = fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", path, e);
        process::exit(1);
    });

    let start = Instant::now();
    let mut solver = radical::parse_dimacs(&contents);
    solver.config = config;
    if conflict_limit > 0 {
        solver.set_conflict_limit(conflict_limit);
    }
    let parse_elapsed = start.elapsed();
    eprintln!(
        "Parsed: {} vars, {} clauses in {:.3?}",
        solver.num_vars(),
        solver.num_clauses(),
        parse_elapsed
    );
    eprintln!(
        "Config: xor={}, ema={}, probing={}, rephasing={}",
        solver.config.xor_propagation,
        solver.config.ema_restarts,
        solver.config.probing,
        solver.config.rephasing
    );

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
    eprintln!(
        "Solved in {:.3?}, {} conflicts",
        solve_elapsed,
        solver.num_conflicts()
    );
    process::exit(match result {
        Some(true) => 10,
        Some(false) => 20,
        None => 0,
    });
}

fn print_help() {
    eprintln!("radical - Minimal CDCL SAT solver");
    eprintln!();
    eprintln!("USAGE: radical [OPTIONS] <file.cnf>");
    eprintln!();
    eprintln!("  Reads a DIMACS CNF file and solves it.");
    eprintln!();
    eprintln!("OPTIONS:");
    eprintln!("  --conflict-limit=<N>  Max conflicts before returning UNKNOWN (0 = unlimited)");
    eprintln!();
    eprintln!("SOLVER FEATURES (toggle on/off):");
    eprintln!("  --xor-propagation     Enable GF(2) XOR constraint propagation (default: on)");
    eprintln!("  --no-xor              Disable XOR propagation");
    eprintln!("  --ema-restarts        Use glucose-style EMA restarts instead of Luby");
    eprintln!("  --no-ema-restarts     Use Luby restart schedule (default)");
    eprintln!("  --probing             Run failed literal probing before solving");
    eprintln!("  --no-probing          Disable probing (default)");
    eprintln!("  --rephasing           Periodically reset phase saving heuristic");
    eprintln!("  --no-rephasing        Disable rephasing (default)");
    eprintln!();
    eprintln!("Note: XOR propagation only applies when XOR constraints are present");
    eprintln!("(not in plain DIMACS CNF). It is used internally by the turyn binary.");
}
