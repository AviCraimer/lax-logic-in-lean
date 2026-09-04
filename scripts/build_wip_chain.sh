#!/bin/zsh
# Timed rebuild of the wip olean chain on v4.31.0.
# Topological order (spaceindiff depends on packaging): absorb_base, adequacy, packaging, indiff, spaceindiff, final.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DEP="${WIPDEPS:-$ROOT/.lake/wipdeps}"
LOG="${WIPLOG:-$DEP/build_chain.log}"
rm -rf "$DEP"; mkdir -p "$DEP"
cd "$ROOT"
: > "$LOG"

build () {
  local name="$1"; local emit="$2"   # emit=1 -> write olean, 0 -> just check (final)
  local t0=$(date +%s)
  echo "=== START $name $(date '+%H:%M:%S') ===" | tee -a "$LOG"
  if [ "$emit" = "1" ]; then
    lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$DEP\" lean wip/$name.lean -o $DEP/$name.olean" >>"$LOG" 2>&1
  else
    lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$DEP\" lean wip/$name.lean" >>"$LOG" 2>&1
  fi
  local rc=$?
  local t1=$(date +%s)
  echo "=== END   $name rc=$rc elapsed=$((t1-t0))s ===" | tee -a "$LOG"
  if [ "$rc" != "0" ]; then
    echo "!!! ABORT: $name failed rc=$rc" | tee -a "$LOG"
    exit "$rc"
  fi
}

GT0=$(date +%s)
build absorb_base 1
build adequacy 1
build packaging 1
build indiff 1
build spaceindiff 1
build final 0
GT1=$(date +%s)
echo "=== CHAIN COMPLETE total=$((GT1-GT0))s ===" | tee -a "$LOG"
