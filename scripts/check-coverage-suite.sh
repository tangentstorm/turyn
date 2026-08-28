#!/bin/bash
# Coverage regression guard: run each mode to its own completion at a
# small n and diff what it found against the published catalogue.
#
# This is the check that would have caught the defects in
# docs/TTC-AUDIT.md. It is cheap enough for CI: the two fast cases below
# take ~2 s and ~30 s respectively.
#
#   scripts/check-coverage-suite.sh          # fast cases only
#   scripts/check-coverage-suite.sh --full   # adds the slower ones
set -u
cd "$(dirname "$0")/.."
fail=0

run_case() {
  local label="$1" n="$2" expect="$3"; shift 3
  local log
  log=$(mktemp)
  if ! timeout 1800 target/release/turyn search --n="$n" --all --threads=1 --seed=0 "$@" \
       > "$log" 2>&1; then
    echo "FAIL $label: run did not complete"
    fail=1
    rm -f "$log"
    return
  fi
  local found
  found=$(target/release/check_coverage "$n" "$log" 2>/dev/null \
          | grep 'distinct canonical' | grep -o '[0-9]*$')
  if [ "$found" = "$expect" ]; then
    echo "ok   $label: $found/$expect classes"
  else
    echo "FAIL $label: found ${found:-0} classes, expected $expect"
    fail=1
  fi
  rm -f "$log"
}

for kk in 2 3 4 5; do
  [ -f "mdd-$kk.bin" ] || target/release/gen_mdd "$kk" >/dev/null 2>&1
done

# cross has no MDD and reproduces the catalogue exactly.
run_case "cross n=10" 10 43 --wz=cross
# Small k / large middle is the regime that used to lose solutions
# (TTC-AUDIT §12.2, §12.2d). Keep the smallest k in the fast set.
run_case "apart n=12 k=2" 12 127 --wz=apart --mdd-k=2
run_case "apart n=14 k=5" 14 186 --wz=apart --mdd-k=5

if [ "${1:-}" = "--full" ]; then
  run_case "cross n=12" 12 127 --wz=cross
  run_case "apart n=14 k=3" 14 186 --wz=apart --mdd-k=3
  run_case "apart n=16 k=4" 16 739 --wz=apart --mdd-k=4
  run_case "together n=14 k=5" 14 186 --wz=together --mdd-k=5
fi

exit $fail
