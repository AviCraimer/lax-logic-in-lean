import LaxLogic.PLLExec

/-!
# `laxrun` — the CLI entry point

Subcommand dispatch onto the pure drivers of `LaxLogic.PLLExec`.  All the
actual computation lives there; this file is just the argv → driver map.

## How to run it

    scripts/laxrun.sh help
    scripts/laxrun.sh timing
    scripts/laxrun.sh search gap 10000
    scripts/laxrun.sh quant g3
    scripts/laxrun.sh zoo g3-e

which is `lake env lean --run Main.lean <args>` — the interpreter path.

## Known toolchain issue: the native `lake exe laxrun` binary crashes

A `lean_exe` target (`laxrun`, kept in the lakefile) builds this file into a
native binary, and that is the intended long-term path.  On the current
toolchain, however, the built binary segfaults at startup, and the fault is
in the toolchain, not in this code:

* **Repro** (macOS arm64, `leanprover/lean4:v4.22.0-rc3`, current Mathlib
  cache): a `lean_exe` whose root is just
  `import Mathlib.Tactic.Ring; def main : IO Unit := IO.println "hi"`
  crashes identically — `EXC_BAD_ACCESS (address=0x0)` inside
  `lean_mark_persistent`, called from `initialize_Mathlib_Data_Set_Basic`,
  before `main` runs.  A zero-import `main` runs fine.
* **Root cause**: the cache-shipped C IR
  (`.lake/packages/mathlib/.lake/build/ir/Mathlib/Data/Set/Basic.c`)
  contains `_init_l_Set_instBoundedOrder___closed__0`, which does
  `x_1 = lean_alloc_ctor(0, 2, 0); return x_1;` — a two-object-field
  constructor returned with both fields uninitialised (NULL on fresh pages).
  Both fields of `BoundedOrder (Set α)` are erased `Set`-values that should
  have been materialised as `lean_box(0)`.  `lean_mark_persistent` then
  walks the object graph during module initialisation and dereferences the
  NULL field.  The interpreter (`#eval`, `lean --run`) never executes this
  C code — it works from `.olean`s — which is why the library builds green
  and every `#eval` in the repo is unaffected.
* **Not the linker**: reproduced identically under the bundled `ld64.lld`
  (chained fixups and `-no_fixup_chains`) and Apple's system `ld`
  (`--ld-path=/usr/bin/ld`).
* **Way out**: a toolchain bump past the fix (the v4.22 cycle churned
  exactly this area — erased-constructor handling in the new code
  generator, e.g. lean4#8634).  When bumping, retest with
  `lake build laxrun && .lake/build/bin/laxrun help`; once it prints the
  usage text, `scripts/laxrun.sh` can be switched to `lake exe laxrun`.
-/

open PLLND

def main (args : List String) : IO Unit :=
  match args with
  | [] => runHelp
  | "help" :: _ => runHelp
  | "timing" :: _ => runTiming
  | "search" :: rest => runSearch rest
  | "quant" :: rest => runQuant rest
  | "zoo" :: rest => runZoo rest
  | cmd :: _ => do
      IO.eprintln s!"unknown subcommand '{cmd}'"
      runHelp
