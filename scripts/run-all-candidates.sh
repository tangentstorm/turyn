#!/usr/bin/env bash
# Sequentially run paired ABBA bench for each candidate against baseline.
# Outputs to /tmp/{name}.tsv.
set -euo pipefail
BASE="$1"; shift
BLOCKS="${1:-4}"; shift || true

for cand in "$@"; do
  name=$(basename "$cand")
  out="/tmp/${name}.tsv"
  echo "=== $cand ($BLOCKS blocks ABBA) → $out ==="
  scripts/bench-pair.sh "$BASE" "$cand" "$BLOCKS" > "$out" 2>&1
  echo "--- stats for $name ---"
  scripts/paired-stats.py < "$out" || true
  echo
done
