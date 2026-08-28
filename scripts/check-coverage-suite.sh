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

[ -f mdd-5.bin ] || target/release/gen_mdd 5 >/dev/null 2>&1
[ -f mdd-6.bin ] || target/release/gen_mdd 6 >/dev/null 2>&1

# cross has no MDD and reproduces the catalogue exactly.
run_case "cross n=10" 10 43 --wz=cross
# apart at a k large enough to be complete at this n (see TTC-AUDIT §12.2:
# completeness is k-dependent; k=5 loses 2 classes here).
run_case "apart n=14 k=6" 14 186 --wz=apart --mdd-k=6

if [ "${1:-}" = "--full" ]; then
  run_case "cross n=12" 12 127 --wz=cross
  run_case "apart n=16 k=6" 16 739 --wz=apart --mdd-k=6
fi

exit $fail
