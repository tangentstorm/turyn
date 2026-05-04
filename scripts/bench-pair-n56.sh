#!/usr/bin/env bash
# Paired ABBA bench for n=56 (--wz=apart --mdd-k=7).
# Metric: W solves and Z solves completed in --sat-secs window (throughput).
# Lower wall-clock per W-solve = faster.
# Usage: bench-pair-n56.sh <turyn.A> <turyn.B> <blocks> [core] [sat-secs]
set -euo pipefail
A="$1"; B="$2"; N="${3:-4}"; CORE="${4:-2}"; SECS="${5:-20}"
ARGS=(--n=56 --wz=apart --mdd-k=7 --sat-secs="$SECS")
PIN=(taskset -c "$CORE" setarch "$(uname -m)" -R)
ENV=(env TURYN_THREADS=1)

now() { date +%s.%N; }

# Returns: "wall_s\tw_solves\tz_solves"
run_one() {
  local bin="$1" out s e wall_s w_solves z_solves
  s=$(now)
  out=$("${ENV[@]}" "${PIN[@]}" "$bin" "${ARGS[@]}" 2>&1)
  e=$(now)
  wall_s=$(awk "BEGIN{printf \"%.4f\", $e - $s}")
  w_solves=$(echo "$out" | awk '/flow W:/ {for(i=1;i<=NF;i++) if($i~/^solves=/){sub("solves=","",$i); print $i; exit}}')
  z_solves=$(echo "$out" | awk '/flow Z:/ {for(i=1;i<=NF;i++) if($i~/^solves=/){sub("solves=","",$i); print $i; exit}}')
  printf '%s\t%s\t%s' "$wall_s" "${w_solves:-0}" "${z_solves:-0}"
}

# 2 warmups (one of each)
run_one "$A" >/dev/null
run_one "$B" >/dev/null

printf 'block\tA_wall\tA_w\tA_z\tB_wall\tB_w\tB_z\tA_w_avg\tB_w_avg\tdelta_w_pct\n'
for i in $(seq 1 "$N"); do
  read -r a1_wall a1_w a1_z <<<"$(run_one "$A")"
  read -r b1_wall b1_w b1_z <<<"$(run_one "$B")"
  read -r b2_wall b2_w b2_z <<<"$(run_one "$B")"
  read -r a2_wall a2_w a2_z <<<"$(run_one "$A")"
  am_wall=$(awk "BEGIN{printf \"%.4f\", ($a1_wall+$a2_wall)/2}")
  bm_wall=$(awk "BEGIN{printf \"%.4f\", ($b1_wall+$b2_wall)/2}")
  am_w=$(awk "BEGIN{printf \"%.2f\", ($a1_w+$a2_w)/2}")
  bm_w=$(awk "BEGIN{printf \"%.2f\", ($b1_w+$b2_w)/2}")
  am_z=$(awk "BEGIN{printf \"%.2f\", ($a1_z+$a2_z)/2}")
  bm_z=$(awk "BEGIN{printf \"%.2f\", ($b1_z+$b2_z)/2}")
  # Delta on W solves: positive = B did more work in same time = B faster
  d_w=$(awk "BEGIN{printf \"%.4f\", 100*($bm_w-$am_w)/$am_w}")
  printf '%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$i" \
    "$am_wall" "$am_w" "$am_z" \
    "$bm_wall" "$bm_w" "$bm_z" \
    "$am_w" "$bm_w" "$d_w"
done
