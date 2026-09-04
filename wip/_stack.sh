#!/bin/zsh
# Standalone build of the tower stack (root-level imports, not Lake targets).
# Usage: wip/_stack.sh absorb_base adequacy packaging indiff spaceindiff final
set -e
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DEP=$ROOT/.dep
mkdir -p $DEP
cd $ROOT
for f in "$@"; do
  echo "=== $f ==="
  lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$DEP\" lean wip/$f.lean -o $DEP/$f.olean"
  echo "--- ok $f ---"
done
