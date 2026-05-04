#!/usr/bin/env python3
"""Paired-t analysis for ABBA-block bench output.

Reads TSV with at least columns: A_mean, B_mean.
Reports mean delta, paired-t 95% CI, sign test, and min/median.
"""
import sys, math, csv

def t_critical(df):
    table = {1:12.706, 2:4.303, 3:3.182, 4:2.776, 5:2.571, 6:2.447,
             7:2.365, 8:2.306, 9:2.262, 10:2.228, 11:2.201, 12:2.179,
             15:2.131, 20:2.086, 25:2.060, 30:2.042, 40:2.021,
             60:2.000, 120:1.980, 99999:1.960}
    for k in sorted(table.keys()):
        if df <= k:
            return table[k]
    return 1.96

def main():
    rows = list(csv.DictReader(sys.stdin, delimiter='\t'))
    if not rows:
        print("no data"); return
    A = [float(r['A_mean']) for r in rows]
    B = [float(r['B_mean']) for r in rows]
    deltas = [(b-a)/a for a,b in zip(A,B)]
    n = len(deltas)
    mean = sum(deltas)/n
    var = sum((d-mean)**2 for d in deltas)/(n-1) if n>1 else 0
    sd = math.sqrt(var)
    se = sd / math.sqrt(n) if n>1 else 0
    tc = t_critical(n-1)
    ci_lo = mean - tc*se
    ci_hi = mean + tc*se
    t_stat = mean/se if se>0 else 0
    pos = sum(1 for d in deltas if d>0)
    neg = sum(1 for d in deltas if d<0)
    minA, minB = min(A), min(B)
    medA = sorted(A)[n//2]; medB = sorted(B)[n//2]
    print(f"n_blocks  = {n}  (each block: A B B A, 4 runs)")
    print(f"mean ΔB-A = {mean*100:+.3f}%   (negative = B faster)")
    print(f"sd        = {sd*100:.3f}%      (per-block)")
    print(f"95% CI    = [{ci_lo*100:+.3f}%, {ci_hi*100:+.3f}%]")
    print(f"t_stat    = {t_stat:+.2f}   (|t| > {tc:.2f} ⇒ p<0.05)")
    sig = "SIGNIFICANT" if abs(t_stat) > tc else "noise"
    direction = "B faster" if mean<0 else "B slower"
    print(f"verdict   = {sig} ({direction})")
    print(f"sign test = {pos} B>A, {neg} B<A  (n={n})")
    print(f"min A     = {minA:.4f}s    min B = {minB:.4f}s    Δmin = {(minB-minA)/minA*100:+.3f}%")
    print(f"med A     = {medA:.4f}s    med B = {medB:.4f}s    Δmed = {(medB-medA)/medA*100:+.3f}%")

if __name__ == '__main__':
    main()
