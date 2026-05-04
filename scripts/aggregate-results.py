#!/usr/bin/env python3
"""Aggregate paired-bench TSV files into a markdown summary table.

Usage: aggregate-results.py <name1=file1.tsv> <name2=file2.tsv> ...
"""
import sys, math, csv

def t_critical(df):
    table = {1:12.706, 2:4.303, 3:3.182, 4:2.776, 5:2.571, 6:2.447,
             7:2.365, 8:2.306, 9:2.262, 10:2.228, 11:2.201, 12:2.179}
    return table.get(df, 2.0)

def stats(path):
    rows = list(csv.DictReader(open(path), delimiter='\t'))
    A = [float(r['A_mean']) for r in rows]
    B = [float(r['B_mean']) for r in rows]
    deltas = [(b-a)/a*100 for a,b in zip(A,B)]
    n = len(deltas)
    mean = sum(deltas)/n
    var = sum((d-mean)**2 for d in deltas)/(n-1) if n>1 else 0
    sd = math.sqrt(var)
    se = sd/math.sqrt(n) if n>1 else 0
    tc = t_critical(n-1)
    ci_lo = mean - tc*se
    ci_hi = mean + tc*se
    sig = 'YES' if abs(mean)>tc*se and se>0 else 'noise'
    direction = 'B faster' if mean<0 else 'B slower' if mean>0 else 'tie'
    minA, minB = min(A), min(B)
    dmin = (minB-minA)/minA*100
    sign_pos = sum(1 for d in deltas if d>0)
    sign_neg = sum(1 for d in deltas if d<0)
    return dict(n=n, mean=mean, sd=sd, ci_lo=ci_lo, ci_hi=ci_hi,
                sig=sig, dir=direction, dmin=dmin,
                sign=f"{sign_neg}/{sign_pos}")

def main():
    print(f"| {'Candidate':<10} | {'n':>3} | {'mean Δ%':>9} | {'sd%':>5} | {'95% CI':<22} | {'Δmin%':>7} | {'sign B</>A':>10} | {'verdict':<10} |")
    print(f"|------------|-----:|----------:|------:|----------------------|--------:|-----------:|------------|")
    for arg in sys.argv[1:]:
        name, path = arg.split('=', 1)
        try:
            s = stats(path)
        except Exception as e:
            print(f"| {name:<10} | err  |     err   |  err  | err                  |    err  |    err     | err        |")
            continue
        ci = f"[{s['ci_lo']:+.2f}%, {s['ci_hi']:+.2f}%]"
        verdict = s['sig']
        if s['sig'] != 'YES' and abs(s['mean']) < 0.5:
            verdict = 'noise/null'
        elif s['sig'] != 'YES':
            verdict = f"hint {s['dir'][:1]}"
        else:
            verdict = f"SIG {s['dir']}"
        print(f"| {name:<10} | {s['n']:>3} | {s['mean']:>+8.2f}% | {s['sd']:>4.2f}% | {ci:<22} | {s['dmin']:>+6.2f}% | {s['sign']:>10} | {verdict:<10} |")

if __name__ == '__main__':
    main()
