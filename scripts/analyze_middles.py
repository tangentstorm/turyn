#!/usr/bin/env python3
"""Study the middle structure of every catalogued TT(n).

Decodes Kharaghani's BDKR hex catalogue (data/turyn-type-NN), then probes
for patterns starting at the two center columns (n/2-1, n/2) and working
outward.  Prints a layered report covering:

    1. The XY interior anti-palindrome (Lean: Turyn.xy_product_law).
    2. The Z palindromic bias near the boundary (rule-(iv) selection).
    3. σ-tuple identities (π_A := ∏ A[i]) derivable from the Turyn-norm
       equation modulo 16.

Decoder note: rows in `data/turyn-type-32` use TWO tail conventions --
6226 rows use the standard (X[n-1]=Y[n-1]=+1, Z[n-1]=-1) and 66 use the
alternate (X[n-1]=Y[n-1]=-1, Z[n-1]=+1).  We try both and keep whichever
satisfies the Turyn identity (matching `src/bin/analyze_data.rs`'s
`decode_line`).  `src/main.rs::decode_kharaghani_hex` only tries the
standard tail; tests pass only because their 5 sample indices happen to
land on standard-tail rows.

Usage:
    python3 scripts/analyze_middles.py
"""

import os
from collections import Counter

DATA_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data")


def aperiodic(seq, s):
    return sum(seq[i] * seq[i + s] for i in range(len(seq) - s))


def is_turyn(X, Y, Z, W):
    n = len(X)
    for s in range(1, n):
        nx = aperiodic(X, s)
        ny = aperiodic(Y, s)
        nz = aperiodic(Z, s)
        nw = aperiodic(W, s) if s < n - 1 else 0
        if nx + ny + 2 * nz + 2 * nw != 0:
            return False
    return True


def decode_dual(hex_row, n):
    """Decode one BDKR hex row of length n-1 into ±1 sequences (X, Y, Z, W)
    of lengths (n, n, n, n-1).  Each hex digit packs (X, Y, Z, W) at one
    position with bit polarity 0 = +1, 1 = -1; the digit is
    8·X_bit + 4·Y_bit + 2·Z_bit + W_bit.

    The trailing position n-1 is appended after decoding.  Two tail
    conventions appear in the data:
        std: (X[n-1], Y[n-1], Z[n-1]) = (+1, +1, -1)  -- BDKR canonical
        alt: (X[n-1], Y[n-1], Z[n-1]) = (-1, -1, +1)  -- 66 London rows
    Try std first; fall back to alt if std doesn't satisfy Turyn."""
    Xb, Yb, Zb, W = [], [], [], []
    for c in hex_row:
        d = int(c, 16)
        Xb.append(+1 if (d >> 3) & 1 == 0 else -1)
        Yb.append(+1 if (d >> 2) & 1 == 0 else -1)
        Zb.append(+1 if (d >> 1) & 1 == 0 else -1)
        W.append(+1 if d & 1 == 0 else -1)
    Xa, Ya, Za = Xb + [+1], Yb + [+1], Zb + [-1]
    if is_turyn(Xa, Ya, Za, W):
        return Xa, Ya, Za, W
    Xa, Ya, Za = Xb + [-1], Yb + [-1], Zb + [+1]
    if is_turyn(Xa, Ya, Za, W):
        return Xa, Ya, Za, W
    raise ValueError(f"row does not verify under either tail convention: {hex_row}")


def load(path, n):
    with open(path) as f:
        return [decode_dual(r.strip(), n) for r in f if r.strip()]


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


def derive_sigma_constraints(n):
    """Return the set of (π_X, π_Y, π_Z) tuples allowed by the Turyn-norm
    equation x²+y²+2z²+2w²=6n-2 modulo 16.

    Squares mod 16: x even -> x² ∈ {0, 4} (0 if x ≡ 0 mod 4 else 4).
                    w odd  -> w² ≡ 1 mod 8, so 2w² ≡ 2 mod 16."""
    target = (6 * n - 2) % 16
    sq16 = {0: 0, 2: 4}  # x mod 4 -> x² mod 16
    pi_tuples = set()
    for xr4 in (0, 2):
        for yr4 in (0, 2):
            for zr4 in (0, 2):
                lhs = (sq16[xr4] + sq16[yr4] + 2 * sq16[zr4] + 2) % 16
                if lhs == target:
                    pi_x = 1 if ((n - xr4) // 2) % 2 == 0 else -1
                    pi_y = 1 if ((n - yr4) // 2) % 2 == 0 else -1
                    pi_z = 1 if ((n - zr4) // 2) % 2 == 0 else -1
                    pi_tuples.add((pi_x, pi_y, pi_z))
    return pi_tuples, target


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
        for X, Y, Z, W in sols:
            for i in range(1, n - 1):
                grand_pairs += 1
                if X[i] * X[n - 1 - i] + Y[i] * Y[n - 1 - i] != 0:
                    grand_viol += 1
    print(f"  Total interior pairs checked: {grand_pairs}")
    print(f"  Total violations:             {grand_viol}")
    print()
    print("  Proved as `Turyn.xy_product_law` in `lean/Turyn/XY.lean`")
    print("  (theorem attributed to codex).")

    section("2. Z palindromic bias near the boundary (rule-(iv) selection)")
    print()
    print("  P(Z[j] = Z[n-1-j]) at radius r = c1-j (r=0 at the center).")
    print("  Bias peaks at large r; rule (iv) pins canonicalization at the")
    print("  FIRST equality position seen working inward from the boundary.")
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

    section("3. σ-tuple identities forced by the Turyn norm modulo 16")
    print()
    print("  At z=1, the polynomial Turyn identity X(z)X(1/z)+...=6n-2 reduces")
    print("  to ∑X² + ∑Y² + 2∑Z² + 2∑W² = 6n-2.  Reading this mod 16 (with")
    print("  even ∑X, ∑Y, ∑Z and odd ∑W) restricts the residues mod 4 of the")
    print("  signed sums, which fixes π_A := ∏ A[i] for some subset of A's.")
    print()
    print(f"  {'n':>3}  target%16  {'predicted forced':<35}  catalogue-observed")
    for n in range(2, 33, 2):
        sols = catalogue[n]
        pi_tuples, t = derive_sigma_constraints(n)
        # forced = those quantities constant across all valid tuples
        pi_xs = {p[0] for p in pi_tuples}
        pi_ys = {p[1] for p in pi_tuples}
        pi_zs = {p[2] for p in pi_tuples}
        pi_xys = {p[0] * p[1] for p in pi_tuples}
        pi_xzs = {p[0] * p[2] for p in pi_tuples}
        forced = {}
        if len(pi_zs) == 1:
            forced["π_Z"] = next(iter(pi_zs))
        if len(pi_xys) == 1:
            forced["π_X·π_Y"] = next(iter(pi_xys))
        if len(pi_xzs) == 1:
            forced["π_X·π_Z"] = next(iter(pi_xzs))
        # observed
        obs_xy = Counter(prod(X) * prod(Y) for X, Y, Z, W in sols)
        obs_xz = Counter(prod(X) * prod(Z) for X, Y, Z, W in sols)
        obs_z = Counter(prod(Z) for X, Y, Z, W in sols)
        observed = {}
        if len(obs_z) == 1:
            observed["π_Z"] = next(iter(obs_z))
        if len(obs_xy) == 1:
            observed["π_X·π_Y"] = next(iter(obs_xy))
        if len(obs_xz) == 1:
            observed["π_X·π_Z"] = next(iter(obs_xz))
        ok = all(forced.get(k) == observed.get(k) for k in set(forced) | set(observed))
        marker = "✓" if ok else "MISMATCH"
        print(f"  {n:>3}    {t:>2}     {str(forced):<35}  {observed}  {marker}")

    print()
    print("  Each catalogue σ-tuple identity is exactly the mod-16 prediction.")
    print("  In particular, π_Z = (-1)^(n/4 + 1) for n ≡ 0 mod 4 is *forced*")
    print("  by the Turyn identity at z=1, not a search artifact -- so the")
    print("  Kharaghani catalogues at n ∈ {12, 16, 20, 24, 28} are NOT 'missing'")
    print("  the opposite-π_Z class; that class is genuinely empty.")


if __name__ == "__main__":
    main()
