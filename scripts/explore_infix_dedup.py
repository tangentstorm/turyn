"""Enumerate valid j-column Turyn infix settings and bucket by inside-sum signature.

An "infix" of width j (even, >= 2) sits at 0-based positions (k - j/2, ..., k + j/2 - 1)
of a length-n=2k Turyn sequence. It carries j * 4 = 4j bits: one +/-1 per (column,
sequence) for sequences X, Y, Z, W.

LOCAL XY product rules (one per reflection pair (i, n+1-i), 1-based, both inside
the infix) apply at column pairs (r, j-1-r) for r = 0 .. j/2 - 1:
    col[r][0] * col[r][1] * col[j-1-r][0] * col[j-1-r][1] == -1
Each rule acts on a disjoint 4-bit group, so valid count = 2^(4j) * (1/2)^(j/2)
                                                        = 2^(7j/2).

INSIDE-ONLY ACF pairs at lag ell (1 <= ell <= j-1) are the column pairs (c, c+ell)
with 0 <= c <= j-1-ell. We compute the Turyn-weighted sum
    I_ell = N_X(ell) + N_Y(ell) + 2*N_Z(ell) + 2*N_W(ell)
restricted to these inside-only pairs. The maximal-lag pair (0, j-1) is always an
XY product rule pair, so I_{j-1}'s XY contribution is forced to 0.

Usage:
    python explore_infix_dedup.py [--j J]

Default j=4. Practical limit is j=6 (2^21 infixes, ~10s). j=8 would be 2^28 ~268M
and take a few minutes.
"""

import argparse
import sys
import time
from collections import defaultdict, Counter
from itertools import product

WEIGHTS = (1, 1, 2, 2)  # X, Y, Z, W


def valid_xy_quads():
    """All 8 tuples (xa, ya, xb, yb) with xa*ya*xb*yb == -1."""
    return [(xa, ya, xb, yb)
            for xa, ya, xb, yb in product([-1, 1], repeat=4)
            if xa * ya * xb * yb == -1]


def inside_pairs(j):
    """Return a dict {lag -> list of (col_i, col_j) inside pairs}."""
    pairs = {}
    for lag in range(1, j):
        pairs[lag] = [(c, c + lag) for c in range(j - lag)]
    return pairs


def enumerate_infixes(j):
    """Yield every valid infix as a tuple of j columns, each a 4-tuple (X,Y,Z,W)."""
    assert j >= 2 and j % 2 == 0, "j must be even and >= 2"
    xy_quads = valid_xy_quads()
    num_rules = j // 2
    num_zw = 2 * j

    for xy_choices in product(xy_quads, repeat=num_rules):
        # xy_choices[r] = (x_left, y_left, x_right, y_right) for rule pair (r, j-1-r)
        xy_bits = [[None, None] for _ in range(j)]  # xy_bits[col] = [X, Y]
        for r, (xl, yl, xr, yr) in enumerate(xy_choices):
            xy_bits[r][0] = xl
            xy_bits[r][1] = yl
            xy_bits[j - 1 - r][0] = xr
            xy_bits[j - 1 - r][1] = yr

        for zw in product([-1, 1], repeat=num_zw):
            cols = tuple(
                (xy_bits[c][0], xy_bits[c][1], zw[2 * c], zw[2 * c + 1])
                for c in range(j)
            )
            yield cols


def turyn_inside(cols, pairs):
    lags = len(pairs)
    I = [0] * lags
    for lag, plist in pairs.items():
        acc = 0
        for pi, pj in plist:
            ci, cj = cols[pi], cols[pj]
            acc += (ci[0] * cj[0]          # X
                    + ci[1] * cj[1]        # Y
                    + 2 * ci[2] * cj[2]    # 2*Z
                    + 2 * ci[3] * cj[3])   # 2*W
        I[lag - 1] = acc
    return tuple(I)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--j", type=int, default=4, help="infix width (even, >= 2)")
    args = ap.parse_args()
    j = args.j
    if j < 2 or j % 2 != 0:
        print("j must be even and >= 2", file=sys.stderr)
        sys.exit(1)

    pairs = inside_pairs(j)
    expected_valid = 2 ** (7 * j // 2)

    print(f"j = {j} columns ({4 * j} bits)")
    print(f"XY rules: {j // 2}  (one per reflection pair)")
    print(f"Expected valid infixes: 2^{7*j//2} = {expected_valid:,}")
    print(f"Inside-only pairs per lag: "
          f"{ {ell: len(pl) for ell, pl in pairs.items()} }")
    if j >= 8:
        print(f"Warning: j={j} means ~{expected_valid/1e6:.0f}M iterations, "
              f"this will take a while.", file=sys.stderr)
    print()

    t0 = time.time()
    by_sig = Counter()
    valid = 0
    for cols in enumerate_infixes(j):
        valid += 1
        sig = turyn_inside(cols, pairs)
        by_sig[sig] += 1
    elapsed = time.time() - t0

    print(f"Enumeration time: {elapsed:.1f}s")
    print(f"Valid infixes:                 {valid:,}")
    print(f"Distinct inside-sum signatures: {len(by_sig):,}")
    print(f"Average bucket size:           {valid/len(by_sig):.1f}")
    print(f"Compression ratio:             {valid/len(by_sig):.0f}:1")
    print()

    counts = sorted(by_sig.values(), reverse=True)
    print(f"Largest bucket:  {counts[0]:>10,}  ({100*counts[0]/valid:.3f}%)")
    print(f"Median bucket:   {counts[len(counts)//2]:>10,}")
    print(f"Smallest bucket: {counts[-1]:>10,}")
    print()

    # Per-lag marginals
    for ell in range(1, j):
        marginal = Counter()
        for sig, ct in by_sig.items():
            marginal[sig[ell - 1]] += ct
        values = sorted(marginal)
        print(f"I_{ell}: {len(values)} distinct values in [{values[0]}, {values[-1]}]")
    print()

    # XY-forced-zero check at maximal lag
    max_lag = j - 1
    zero_frac = sum(ct for sig, ct in by_sig.items() if sig[max_lag - 1] == 0) / valid
    print(f"Fraction with I_{max_lag} = 0: {100*zero_frac:.2f}%  "
          f"(XY-forced plus 0-ZW contributions)")


if __name__ == "__main__":
    main()
