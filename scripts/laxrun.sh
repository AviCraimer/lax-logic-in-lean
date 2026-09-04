#!/bin/sh
# laxrun — run the LaxLogic CLI (Main.lean → LaxLogic.PLLExec drivers).
#
# Native path: the v4.22.0-rc3-era code-generator bug (NULL fields in
# `Set.instBoundedOrder`'s constant closure; history in Main.lean) is fixed
# on the current toolchain (≥ v4.31.0), so this runs the compiled binary.
# Build it once with `lake build laxrun`.  Interpreter fallback if ever
# needed again:  exec lake env lean --run Main.lean "$@"
#
# Usage: scripts/laxrun.sh <subcommand> [args...]   (see `scripts/laxrun.sh help`)
cd "$(dirname "$0")/.." || exit 1
exec lake exe laxrun "$@"
