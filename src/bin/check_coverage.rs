//! Falsify a search run's coverage claim against the published catalogue.
//!
//! A mode that reports `covered=1.000` is asserting it searched the whole
//! space. That assertion is checkable at any `n` the catalogue covers:
//! canonicalize every solution the run printed, canonicalize every
//! catalogued solution, and compare the two sets. Anything in the
//! catalogue that the run did not find is a completeness hole, and a
//! `covered=1.0` alongside it means the mass model is reporting
//! coverage the search never achieved.
//!
//! Usage:
//!   target/release/turyn search --n=14 --wz=apart --mdd-k=5 --all ... > run.log
//!   target/release/check_coverage 14 run.log
//!
//! Reads the `X =: '...'` / `Y =: ...` / `Z =: ...` / `W =: ...` blocks the
//! search prints (ANSI colouring is stripped), so the raw log works as-is.

use std::collections::BTreeMap;
use std::path::Path;

use turyn::corpus::*;

fn strip_ansi(s: &str) -> String {
    let b = s.as_bytes();
    let mut out = String::with_capacity(s.len());
    let mut i = 0;
    while i < b.len() {
        if b[i] == 0x1b {
            while i < b.len() && b[i] != b'm' {
                i += 1;
            }
            i += 1;
        } else {
            out.push(b[i] as char);
            i += 1;
        }
    }
    out
}

fn parse_pm(s: &str) -> Option<Vec<i8>> {
    s.chars()
        .map(|c| match c {
            '+' => Some(1i8),
            '-' => Some(-1i8),
            _ => None,
        })
        .collect()
}

/// Pull every (X, Y, Z, W) quadruple out of a search log.
fn parse_run_log(n: usize, path: &str) -> Result<Vec<Solution>, String> {
    let raw = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let text = strip_ansi(&raw);
    let mut pending: BTreeMap<char, Vec<i8>> = BTreeMap::new();
    let mut out = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        let Some(tag) = line.chars().next() else {
            continue;
        };
        if !matches!(tag, 'X' | 'Y' | 'Z' | 'W') || !line[1..].trim_start().starts_with("=:") {
            continue;
        }
        let Some(open) = line.find('\'') else {
            continue;
        };
        let Some(close) = line[open + 1..].find('\'') else {
            continue;
        };
        let Some(seq) = parse_pm(&line[open + 1..open + 1 + close]) else {
            continue;
        };
        pending.insert(tag, seq);
        if pending.len() == 4 {
            let x = pending.remove(&'X').unwrap();
            let y = pending.remove(&'Y').unwrap();
            let z = pending.remove(&'Z').unwrap();
            let w = pending.remove(&'W').unwrap();
            if x.len() == n && y.len() == n && z.len() == n && w.len() + 1 == n {
                out.push(Solution { n, x, y, z, w });
            }
            pending.clear();
        }
    }
    Ok(out)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: check_coverage <n> <run.log> [more.log ...]");
        std::process::exit(2);
    }
    let n: usize = args[1].parse().expect("n must be an integer");

    let catalogue = load_solutions(Path::new("data")).expect("failed to load data/");
    let Some(expected) = catalogue.get(&n) else {
        eprintln!("no catalogue entry for n={n}");
        std::process::exit(2);
    };
    let expected_sigs: BTreeMap<String, &Solution> =
        expected.iter().map(|s| (signature(s), s)).collect();

    let mut any_hole = false;
    for path in &args[2..] {
        let found = match parse_run_log(n, path) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(2);
            }
        };
        let mut found_sigs: BTreeMap<String, usize> = BTreeMap::new();
        let mut invalid = 0usize;
        let mut noncanon = 0usize;
        for sol in &found {
            if sol.verify().is_err() {
                invalid += 1;
                continue;
            }
            if !sol.canonical_rule_ok() {
                noncanon += 1;
            }
            match canonicalize(sol) {
                Ok(c) => *found_sigs.entry(signature(&c)).or_insert(0) += 1,
                Err(e) => eprintln!("  canonicalization failed: {e}"),
            }
        }

        // Airtight cross-check, independent of `canonicalize` being
        // correct: a catalogued class is genuinely absent only if NO
        // member of its 1024-element symmetry orbit appears verbatim
        // among the quadruples the run printed.
        let raw_printed: std::collections::HashSet<String> = found.iter().map(signature).collect();
        let orbit_absent = |s: &Solution| -> bool {
            !s.orbit()
                .iter()
                .any(|img| raw_printed.contains(&signature(img)))
        };

        let missed: Vec<&String> = expected_sigs
            .keys()
            .filter(|k| !found_sigs.contains_key(*k))
            .collect();
        let spurious: Vec<&String> = found_sigs
            .keys()
            .filter(|k| !expected_sigs.contains_key(*k))
            .collect();
        let dupes: usize = found_sigs.values().filter(|&&c| c > 1).count();

        println!("== {path}  (n={n})");
        println!("  quadruples printed by the run : {}", found.len());
        println!("  ... failing Turyn verification: {invalid}");
        println!("  ... not in BDKR canonical form: {noncanon}");
        println!("  distinct canonical classes    : {}", found_sigs.len());
        println!("  classes emitted more than once: {dupes}");
        println!("  catalogue classes for n={n}    : {}", expected.len());
        println!("  MISSED (in catalogue, not found): {}", missed.len());
        println!("  spurious (found, not catalogued): {}", spurious.len());
        let orbit_confirmed = missed
            .iter()
            .filter(|sig| orbit_absent(expected_sigs[**sig]))
            .count();
        println!(
            "  ... confirmed absent by full-orbit check: {orbit_confirmed} of {}",
            missed.len()
        );
        for sig in missed.iter().take(10) {
            let s = expected_sigs[*sig];
            let (sx, sy, sz, sw) = s.tuple();
            let mark = if orbit_absent(s) {
                ""
            } else {
                "  (orbit member WAS printed)"
            };
            println!("    missed: {sig}   sum-tuple ({sx}, {sy}, {sz}, {sw}){mark}");
        }
        if missed.len() > 10 {
            println!("    ... and {} more", missed.len() - 10);
        }
        if !missed.is_empty() {
            // Which sum-tuple shells are affected, and is the whole
            // shell gone or only part of it? A whole missing shell
            // points at tuple enumeration; a partial one points
            // downstream of it.
            let key = |s: &Solution| {
                let (x, y, z, w) = s.tuple();
                (x.abs(), y.abs(), z.abs(), w.abs())
            };
            let mut per_shell: BTreeMap<(i32, i32, i32, i32), (usize, usize)> = BTreeMap::new();
            for s in expected.iter() {
                per_shell.entry(key(s)).or_default().0 += 1;
            }
            for sig in found_sigs.keys() {
                if let Some(s) = expected_sigs.get(sig) {
                    per_shell.entry(key(s)).or_default().1 += 1;
                }
            }
            println!("  per |sum-tuple| shell (found / catalogued):");
            for (k, (exp, got)) in &per_shell {
                let flag = if got < exp { "   <-- HOLE" } else { "" };
                println!(
                    "    (|x|,|y|,|z|,|w|) = ({}, {}, {}, {})  {:>5} / {:<5}{}",
                    k.0, k.1, k.2, k.3, got, exp, flag
                );
            }
        }
        if missed.is_empty() && spurious.is_empty() {
            println!("  => COMPLETE: the run found every catalogued class, and nothing else");
        } else {
            any_hole = true;
            println!("  => INCOMPLETE: a covered=1.0 claim on this run is not justified");
        }
        println!();
    }
    if any_hole {
        std::process::exit(1);
    }
}
