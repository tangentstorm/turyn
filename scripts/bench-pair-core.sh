#!/usr/bin/env bash
# Like bench-pair.sh but accepts a core argument as 4th positional.
set -euo pipefail
A="$1"; B="$2"; N="${3:-12}"; CORE="${4:-2}"
ARGS=(--n=18 --wz=apart --mdd-k=5 --conj-tuple --continue-after-sat --sat-secs=300)
PIN=(taskset -c "$CORE" setarch "$(uname -m)" -R)
ENV=(env TURYN_THREADS=1)

now() { date +%s.%N; }

run_one() {
  local bin="$1" s e
  s=$(now)
  "${ENV[@]}" "${PIN[@]}" "$bin" "${ARGS[@]}" >/dev/null 2>&1
  e=$(now)
  awk "BEGIN{printf \"%.6f\", $e - $s}"
}

run_one "$A" >/dev/null
run_one "$B" >/dev/null

printf 'block\tA1\tB1\tB2\tA2\tA_mean\tB_mean\tdelta_pct\n'
for i in $(seq 1 "$N"); do
  a1=$(run_one "$A")
  b1=$(run_one "$B")
  b2=$(run_one "$B")
  a2=$(run_one "$A")
  am=$(awk "BEGIN{printf \"%.6f\", ($a1+$a2)/2}")
  bm=$(awk "BEGIN{printf \"%.6f\", ($b1+$b2)/2}")
  d=$(awk "BEGIN{printf \"%.4f\", 100*($bm-$am)/$am}")
  printf '%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$i" "$a1" "$b1" "$b2" "$a2" "$am" "$bm" "$d"
done
