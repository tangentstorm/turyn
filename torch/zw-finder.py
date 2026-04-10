import argparse
import numpy as np
import sqlite3
import time
import sys

def npaf(s):
    """Nonperiodic autocorrelation of ±1 sequence"""
    n = len(s)
    return np.array([np.sum(s[:n-k] * s[k:]) for k in range(n)])

def score_zw(z, w):
    nz = npaf(z)
    nw = npaf(w)
    combined = nz[:len(nw)] + nw
    comb_score = np.sum(combined[1:]**2)          # off-zero only
    max_ind = max(np.max(np.abs(nz[1:])), np.max(np.abs(nw[1:])))
    sum_z = int(np.sum(z))
    sum_w = int(np.sum(w))
    return comb_score, max_ind, sum_z, sum_w

def pack(seq):
    bits = ((seq + 1) // 2).astype(np.uint64)
    return np.bitwise_or.reduce(bits << np.arange(len(bits), dtype=np.uint64))

def make_seed(m):
    # Trimmed m-sequence of period 63
    n = 6
    state = (1 << n) - 1
    seq = []
    for _ in range(63):
        seq.append(1 if state & 1 else -1)
        fb = (state & 1) ^ ((state >> 1) & 1)
        state = (state >> 1) | (fb << (n-1))
    seq = np.array(seq, dtype=np.int8)
    z = seq[:m].copy()
    w = seq[:m-1].copy()
    if z[0] == -1:
        z = -z
        w = -w
    return z, w

def get_positive_tuples(n):
    """Return only positive plausible tuples (sumZ > 0, sumW > 0)"""
    candidates = []
    for sz in [2, 4]:
        for sw in [1, 3]:
            if (sz % 2 == n % 2) and (sw % 2 == (n-1) % 2):
                candidates.append((sz, sw))
    return candidates

def main():
    parser = argparse.ArgumentParser(description="Simulated annealing for (Z, W) Turyn-type pairs - positive tuples only")
    parser.add_argument("--n", type=int, help="Length of Z (even, >= 4)")
    parser.add_argument("--tuple", type=str, help="Specific sum tuple 'sumz,sumw' e.g. '2,1'. If omitted, tries all positive tuples.")
    args = parser.parse_args()

    if not args.n:
        parser.print_help()
        print("\nExample: python turyn_search.py --n 56")
        print("         python turyn_search.py --n 56 --tuple 2,1")
        sys.exit(1)

    if args.n % 2 != 0 or args.n < 4:
        print("Error: n must be even and >= 4")
        sys.exit(1)

    m = args.n
    db_file = f"turyn_zw_n{m}.db"

    # Determine tuples
    if args.tuple:
        try:
            sumz, sumw = map(int, args.tuple.split(','))
            if sumz <= 0 or sumw <= 0:
                print("Error: --tuple must be positive (e.g. 2,1)")
                sys.exit(1)
            tuples_to_try = [(sumz, sumw)]
        except:
            print("Error: --tuple must be in format 'sumz,sumw' e.g. '2,1'")
            sys.exit(1)
    else:
        tuples_to_try = get_positive_tuples(m)
        print(f"No --tuple given. Searching positive tuples for n={m}: {tuples_to_try}")

    # Database (one file per n)
    conn = sqlite3.connect(db_file)
    conn.execute("""CREATE TABLE IF NOT EXISTS pairs 
                    (score REAL, max_indiv REAL, sumz INTEGER, sumw INTEGER, 
                     z_int INTEGER, w_int INTEGER, UNIQUE(z_int, w_int))""")
    conn.commit()

    print(f"Starting search for n={m} → {db_file}")

    for target_sumz, target_sumw in tuples_to_try:
        print(f"\n=== Searching for (+{target_sumz}, +{target_sumw}) ===")
        
        z, w = make_seed(m)
        best_score = float('inf')
        T = 12.0
        step = 0
        start_time = time.time()

        while True:
            flip_z = np.random.rand(m-1) < 1.1 / m
            flip_w = np.random.rand(m-2) < 1.1 / m
            
            z_c = z.copy()
            w_c = w.copy()
            z_c[1:][flip_z] *= -1
            w_c[1:][flip_w] *= -1

            # Enforce positive target sums with tolerance
            if abs(z_c.sum() - target_sumz) > 4 or abs(w_c.sum() - target_sumw) > 3:
                step += 1
                continue

            comb_score, max_ind, sz, sw = score_zw(z_c, w_c)

            # Simulated annealing
            if comb_score < best_score or np.random.rand() < np.exp((best_score - comb_score) / T):
                z, w = z_c, w_c
                if comb_score < best_score:
                    best_score = comb_score
                    if step % 200 == 0:
                        print(f"New best: {best_score:.0f}   max_indiv={max_ind:.0f}   T={T:.4f}")

            # Log promising candidates
            if comb_score < 30000 and max_ind < 12:
                z_int = pack(z)
                w_int = pack(w)
                conn.execute("INSERT OR IGNORE INTO pairs VALUES (?,?,?,?,?,?)",
                             (float(comb_score), float(max_ind), int(sz), int(sw), int(z_int), int(w_int)))

            if step % 5000 == 0:
                conn.commit()

            if step % 20000 == 0 and step > 0:
                elapsed = (time.time() - start_time) / 60
                print(f"Step {step:7d} | Best {best_score:.0f} | T {T:.5f} | elapsed {elapsed:.1f} min")

            # Cooling
            if step % 150 == 0:
                T = max(T * 0.9990, 1e-5)

            step += 1

if __name__ == "__main__":
    main()

