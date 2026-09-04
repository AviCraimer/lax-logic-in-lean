#!/bin/sh
# Finalize the enlarged round after the cells2 sweep completes.
# Usage: sh wip/gen2logs/finalize.sh   (from the worktree root)
set -e
BIN=.lake/build/bin/rnDictGen

# 1. Rerun OPEN cells that are NOT hand-overridden, with the
#    extras-enabled binary (their .cell files get overwritten).
OVR=$(grep -o '"c[A-Za-z]*_[0-9_]*"' wip/rnDictGen.lean | tr -d '"' | sort -u)
OPEN=$(cat wip/gen2logs/slice*.log | grep "?? " | sed 's/.*?? \(c[A-Za-z_0-9]*\):.*/\1/' | sort -u)
RERUN=""
for c in $OPEN; do
  if ! echo "$OVR" | grep -qx "$c"; then RERUN="$RERUN $c"; fi
done
echo "post-pass rerun cells:$RERUN"
[ -n "$RERUN" ] && $BIN cells2 400000 $RERUN 2> wip/gen2logs/postpass.log

echo "=== post-pass done; NEW-class cells now: ==="
grep -l "REFUTED CELL" wip/gen2/*.cell | sed 's|wip/gen2/||;s|\.cell||' | sort | tee wip/gen2logs/newcells.txt
echo "=== still-OPEN cells (sorried, shortlists): ==="
grep -l "OPEN CELL" wip/gen2/*.cell | sed 's|wip/gen2/||;s|\.cell||' | sort | tee wip/gen2logs/opencells.txt
