#!/bin/zsh
# Run one wip/*.lean runner file (a `#eval` harness) under a HARD wall-clock
# cap, the way `scripts/probe` does for compiled executables.
#
#   zsh wip/_probe_elab.sh <seconds> <file-stem>
#
# `scripts/probe` only drives `.lake/build/bin/<exe>`, and declaring a new
# executable means editing `lakefile.toml`.  Runner files in `wip/` are
# elaboration-driven instead (the round-5 refute stages are the precedent),
# so they need the same cap applied to `lean` itself.
#
# Partial output is the norm and is fine: the frontier harness appends and
# FLUSHES every corpus line as it is produced, so whatever reached the file
# before the cap is intact and usable.
set -u
if [[ $# -lt 2 ]]; then
  print -u2 "usage: zsh wip/_probe_elab.sh <seconds> <file-stem>"
  exit 2
fi
cap=$1; shift
f=$1; shift
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DEP=$ROOT/.dep
cd $ROOT
lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$DEP\" lean wip/$f.lean -o $DEP/$f.olean" &
pid=$!
( sleep "$cap"; kill -TERM $pid 2>/dev/null ) &
watcher=$!
wait $pid
rc=$?
kill $watcher 2>/dev/null
if [[ $rc -ne 0 ]]; then
  printf "%s\n" "-- '$f' stopped at the ${cap}s cap (rc=$rc); durable output is partial but valid."
fi
exit 0
