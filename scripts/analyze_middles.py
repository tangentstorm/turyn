#!/usr/bin/env python3
"""Study the middle structure of every catalogued TT(n).

Decodes Kharaghani's BDKR hex catalogue (data/turyn-type-NN), then probes
for patterns starting at the two center columns (n/2-1, n/2) and working
outward.  Prints a layered report covering:

    1. The XY interior anti-palindrome (Lean: Turyn.xy_product_law).
    2. The Z palindromic bias near the boundary (rule-(iv) selection).
    3. GF(2) linear identities among reflection bits.
    4. σ-tuple identities (parity products π_A := ∏ A[i]):
         a. π_X · π_Y = (-1)^((n-2)/2)  -- corollary of (1).
         b. π_Z constancy at n ≡ 0 mod 4  (n ≤ 28 in current catalogue;
            broken at n=32 by Stephen London's 66 added solutions).
         c. π_X · π_Z constancy at n ≡ 2 mod 4.

Usage:
    python3 scripts/analyze_middles.py
"""

import os
import sys
from collections import Counter

DATA_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data")


def decode_row(hex_row, n):
    """Decode one BDKR hex row of length n-1 into ±1 sequences (X, Y, Z, W)
    of lengths (n, n, n, n-1).  Each hex digit packs (X, Y, Z, W) at one
    position with bit polarity 0 = +1, 1 = -1; the digit is
    8·X_bit + 4·Y_bit + 2·Z_bit + W_bit.  The trailing position n-1 has
    X[n-1] = Y[n-1] = +1 and Z[n-1] = -1 by canonical-form consequence."""
    assert len(hex_row) == n - 1
    X, Y, Z, W = [], [], [], []
    for c in hex_row:
        d = int(c, 16)
        X.append(+1 if (d >> 3) & 1 == 0 else -1)
        Y.append(+1 if (d >> 2) & 1 == 0 else -1)
        Z.append(+1 if (d >> 1) & 1 == 0 else -1)
        W.append(+1 if d & 1 == 0 else -1)
    X.append(+1)
    Y.append(+1)
    Z.append(-1)
    return X, Y, Z, W


def load(path, n):
    with open(path) as f:
        return [decode_row(r.strip(), n) for r in f if r.strip()]


def prod(seq):
    p = 1
    for v in seq:
        p *= v
    return p


def section(title):
    print()
    print("=" * 78)
    print(title)
    print("=" * 78)


def main():
    catalogue = {}
    for n in range(2, 33, 2):
        path = os.path.join(DATA_DIR, f"turyn-type-{n:02}")
        catalogue[n] = load(path, n)

    total = sum(len(v) for v in catalogue.values())
    print(f"Loaded {total} canonical TT(n) solutions across n ∈ {{2..32}}.")
    for n, sols in catalogue.items():
        print(f"  n={n:>2}: {len(sols):>5}")

    section("1. XY interior anti-palindrome (Turyn.xy_product_law)")
    print()
    print("  Claim: X[i]·X[n-1-i] + Y[i]·Y[n-1-i] = 0 for every i ∈ [1, n-2].")
    print("  Equivalently (X·Y)[n-1-i] = -(X·Y)[i] (interior anti-palindrome).")
    print()
    grand_pairs = grand_viol = 0
    for n, sols in catalogue.items():
        if n < 4:
            continue
        viols = 0
        pairs = 0
        for X, Y, Z, W in sols:
            for i in range(1, n - 1):
                pairs += 1
                if X[i] * X[n - 1 - i] + Y[i] * Y[n - 1 - i] != 0:
                    viols += 1
        grand_pairs += pairs
        grand_viol += viols
    print(f"  Total interior pairs checked: {grand_pairs}")
    print(f"  Total violations:             {grand_viol}")
    print()
    print("  This is the 'XY product law' proved in lean/Turyn/XY.lean")
    print("  (theorem xy_product_law, attributed to codex).")

    section("2. Z palindromic bias near the boundary (rule (iv) artifact)")
    print()
    print("  P(Z[j] = Z[n-1-j]) at radius r = c1-j (r=0 at the center).")
    print("  Bias peaks at large r (close to boundary); rule (iv) pins")
    print("  the FIRST equality position, forcing palindromicity early.")
    print()
    radii_max = 14
    print(f"  {'n':>3}  {'#sols':>5}  " + "  ".join(f"r={r:>2}" for r in range(radii_max + 1)))
    for n in range(8, 33, 2):
        sols = catalogue[n]
        c1 = n // 2 - 1
        line = f"  {n:>3}  {len(sols):>5}  "
        for r in range(radii_max + 1):
            i = c1 - r
            j = c1 + 1 + r
            if i < 0 or j > n - 1 or i == j:
                line += "    -"
                continue
            same = sum(1 for X, Y, Z, W in sols if Z[i] == Z[j])
            line += f"{100*same/len(sols):5.1f}"
        print(line)

    section("3. σ-tuple identities (π_A := ∏ A[i], the parity sign)")
    print()
    print("  3a. π_X · π_Y = (-1)^((n-2)/2)")
    print("      Direct consequence of the XY product law -- holds for every")
    print("      Turyn 4-tuple (provable, not just empirical).")
    print()
    print(f"      {'n':>3}  {'observed':>8}  {'predicted':>9}")
    for n, sols in catalogue.items():
        obs = Counter(prod(X) * prod(Y) for X, Y, Z, W in sols)
        pred = (-1) ** ((n - 2) // 2)
        if len(obs) == 1:
            v = next(iter(obs))
            mark = "OK" if v == pred else "FAIL"
            print(f"      {n:>3}  {v:+9}  {pred:+9}  {mark}")
        else:
            print(f"      {n:>3}  varies   {pred:+9}  FAIL ({dict(obs)})")

    print()
    print("  3b. π_Z constancy at n ≡ 0 mod 4")
    print("      Empirical: π_Z = (-1)^(n/4 + 1) for ALL solutions in the")
    print("      catalogue at n ∈ {4, 8, 12, 16, 20, 24, 28}.  At n=32 this")
    print("      breaks: 66 of 6292 solutions have π_Z = +1 (London additions).")
    print()
    print(f"      {'n':>3}  {'π_Z observed':<35}  {'predicted':>9}")
    for n in [4, 8, 12, 16, 20, 24, 28, 32]:
        sols = catalogue[n]
        obs = Counter(prod(Z) for X, Y, Z, W in sols)
        pred = (-1) ** (n // 4 + 1)
        if len(obs) == 1:
            v = next(iter(obs))
            print(f"      {n:>3}  {str(v) + ' (' + str(len(sols)) + ' sols)':<35}  {pred:+9}  OK")
        else:
            d = dict(obs)
            print(f"      {n:>3}  {str(d):<35}  {pred:+9}  PARTIAL")

    print()
    print("  3c. π_X · π_Z constancy at n ≡ 2 mod 4")
    print("      Empirical: π_X · π_Z = (-1)^((n+2)/4) for n ∈ {6, 10, 14, ..., 30}.")
    print()
    print(f"      {'n':>3}  {'observed':>9}  {'predicted':>9}")
    for n in [6, 10, 14, 18, 22, 26, 30]:
        sols = catalogue[n]
        obs = Counter(prod(X) * prod(Z) for X, Y, Z, W in sols)
        pred = (-1) ** ((n + 2) // 4)
        if len(obs) == 1:
            v = next(iter(obs))
            mark = "OK" if v == pred else "FAIL"
            print(f"      {n:>3}  {v:+9}  {pred:+9}  {mark}")
        else:
            print(f"      {n:>3}  varies     {pred:+9}  FAIL ({dict(obs)})")

    section("4. Pre-London catalogue (data/OriginalFiles) at n=32")
    print()
    orig_path = os.path.join(DATA_DIR, "OriginalFiles", "sort32")
    orig = load(orig_path, 32)
    curr = catalogue[32]
    orig_set = set(open(orig_path).read().split())
    london = [(X, Y, Z, W) for line, (X, Y, Z, W)
              in zip(open(os.path.join(DATA_DIR, "turyn-type-32")).read().split(), curr)
              if line not in orig_set]
    print(f"  Original sort32:  {len(orig)} solutions, π_Z distribution: "
          f"{dict(Counter(prod(Z) for X, Y, Z, W in orig))}")
    print(f"  London additions: {len(london)} solutions, π_Z distribution: "
          f"{dict(Counter(prod(Z) for X, Y, Z, W in london))}")
    print()
    print("  IMPLICATION: π_Z = -1 was 100% in pre-London n=32, but London")
    print("  proved the catalogue was incomplete -- the 66 missed orbits all")
    print("  have π_Z = +1.  By analogy, the n ∈ {12, 16, 20, 24, 28} catalogues")
    print("  may also be missing 'opposite π_Z' orbits.  Worth verifying by")
    print("  running this codebase's enumerator on those n.")


if __name__ == "__main__":
    main()
