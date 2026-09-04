import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLG4Gap
import LaxLogic.PLLTiming
import LaxLogic.PLLTimingAdder

/-!
# The compiled driver: canonical helpers, named instances, IO drivers

This file is the single home for the mechanisation's *computational* (as
opposed to *proof-theoretic*) functions — the ones previously exercised only
via ad-hoc `#eval` inside probe/theory files (`wip/*probe*.lean`,
`PLLRun.lean`-style demos).  It contains **no `#eval` and no `theorem`**: it
is a program file, run through the `laxrun` CLI (`Main.lean` at the repo
root), not exercised at elaboration time.  Native compilation is the point —
an `itpE`/`itpA` differencing run over million-node interpolants takes ~55 s
interpreted and would be ~1 s compiled.  **Known toolchain issue**: on the
current pin (v4.22.0-rc3 + Mathlib cache) the native `lake exe laxrun`
binary is miscompiled by the code generator and crashes at startup, so the
CLI currently runs through the interpreter: `scripts/laxrun.sh <args>`
(= `lake env lean --run Main.lean <args>`).  Full analysis and the repro
are in `Main.lean`'s header; retest after any toolchain bump.

## Contract: how to add a named instance

Each subcommand reads a `List Xxxlnstance` table below and looks an entry up
by `name : String`.  To add one:

1. Build whatever `PLLFormula`/`List PLLFormula`/`Finset PLLFormula` values
   you need (private `def`s just above the table are the house style — see
   `G0`/`S0`, `G2`/`S2`, `G3`/`S3` for the pattern).
2. Append a record literal to the relevant table (`searchInstances`,
   `quantInstances`, `zooInstances`) with a fresh `name` and a one-line
   `note` explaining what it demonstrates or what verdict to expect.
3. That's it — the driver (`runSearch`/`runQuant`/`runZoo`) and `Main.lean`'s
   dispatch need no changes; they already iterate the table generically.

No formula-parser is provided or needed: instances are named Lean values,
not user-typed syntax.

## Contract: how to add a subcommand

1. Write a pure driver `runFoo : List String → IO Unit` (or `IO Unit` if it
   takes no arguments) in the "Drivers" section below, following the
   existing ones: parse `args`, look up any named instance(s), compute with
   the *existing* library functions (never redefine them here — this file
   re-exports the canonical copies, it does not fork new ones), print with
   `IO.println`/`IO.eprintln`.
2. Add one dispatch arm to `Main.lean`'s `match` on the first CLI argument.
3. Mention it in `runHelp`'s usage text.

## What is deliberately not here

`wip/packaging.lean`'s `pieceClosure`/`mu`/`defect` are not re-exported:
`wip/` is not a library module (it is not built by `lake build`, and its
files `import` each other by bare name, not `LaxLogic.*`), so nothing there
can be imported here without either promoting it to a library module first
(out of scope for this pass) or duplicating its ~250-line closure
computation. No subcommand in the deliverable list needs it, so it is
skipped outright rather than half-ported.
-/

open PLLFormula

namespace PLLND

/-! ## Part 1 — the algebra zoo (canonical copy)

Finite Heyting algebras with a nucleus are sound for PLL, so a pointwise
disagreement between two formulas under some valuation refutes their
interderivability — in time linear in formula size.  This was duplicated
verbatim across `wip/fragprobe1.lean`, `wip/stabprobe1.lean`,
`wip/v3probe2.lean`, `wip/v3probe4.lean`; this is now the one copy.

Models: 3-chain `0 < 1 < 2` with nuclei `id`, `max · 1`, `0↦0 else 2`,
`const 2`; and the Boolean diamond `2×2` on bits `{0,1,2,3}` with nuclei
`id`, `||| 1`, `||| 2`. -/

/-- A finite algebraic model: a bounded lattice with `→` and a nucleus
`box`, carried on an explicit list of elements (so valuations can be
enumerated). -/
structure AlgModel where
  meet : Nat → Nat → Nat
  join : Nat → Nat → Nat
  imp  : Nat → Nat → Nat
  bot  : Nat
  top  : Nat
  box  : Nat → Nat
  elems : List Nat

/-- The 3-chain `0 < 1 < 2` (Heyting arrow `x ≤ y ↦ 2`), parametrised by
its nucleus. -/
def chain3 (j : Nat → Nat) : AlgModel :=
  ⟨min, max, fun x y => if x ≤ y then 2 else y, 0, 2, j, [0, 1, 2]⟩

/-- The Boolean diamond `2×2` on bits `{0,1,2,3}` (`meet`/`join` bitwise,
`imp x y = ¬x ∨ y`), parametrised by its nucleus. -/
def diamond (j : Nat → Nat) : AlgModel :=
  ⟨(· &&& ·), (· ||| ·), fun x y => (3 ^^^ x) ||| y, 0, 3, j, [0, 1, 2, 3]⟩

/-- The zoo: four nuclei on the chain, three on the diamond — enough
disagreement to refute most non-theorems in linear time. -/
def zoo : List AlgModel :=
  [chain3 id, chain3 (max · 1), chain3 (fun x => if x = 0 then 0 else 2),
   chain3 (fun _ => 2),
   diamond id, diamond (· ||| 1), diamond (· ||| 2)]

/-- Evaluate a formula in a model under a valuation of its atoms. -/
def aeval (M : AlgModel) (v : String → Nat) : PLLFormula → Nat
  | .prop s => v s
  | .falsePLL => M.bot
  | .and A B => M.meet (aeval M v A) (aeval M v B)
  | .or A B => M.join (aeval M v A) (aeval M v B)
  | .ifThen A B => M.imp (aeval M v A) (aeval M v B)
  | .somehow A => M.box (aeval M v A)

/-- All valuations of the given atoms into the model (as functions
`String → Nat`, defaulting unlisted atoms to `bot`). -/
def vals (M : AlgModel) : List String → List (String → Nat)
  | [] => [fun _ => M.bot]
  | a :: as =>
      (vals M as).flatMap (fun v =>
        M.elems.map (fun x => fun s => if s = a then x else v s))

/-- Count, across every model in the zoo and every valuation of `atoms`,
how often `X ≤ Y` fails semantically.  `0` is necessary (not sufficient)
for `X ⊢ Y`; used as a fast semantic difference test between two
candidate interpolants. -/
def leFails (atoms : List String) (X Y : PLLFormula) : Nat :=
  (zoo.map (fun M =>
    ((vals M atoms).filter (fun v =>
      ¬ (M.meet (aeval M v X) (aeval M v Y) = aeval M v X))).length)).foldl
    (· + ·) 0

/-- Both directions of `leFails`: `(0, 0)` means "semantically equal over
the zoo", i.e. no model/valuation tested distinguishes `X` and `Y`. -/
def eqFails (atoms : List String) (X Y : PLLFormula) : Nat × Nat :=
  (leFails atoms X Y, leFails atoms Y X)

/-! ## Part 2 — sizes and rendering -/

/-- Plain AST node count (distinct from `PLLFormula.weight`, which is
Dyckhoff's proof-theoretic weight) — the size metric the quantifier
probes actually tracked. -/
def fsize : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and A B => fsize A + fsize B + 1
  | .or A B => fsize A + fsize B + 1
  | .ifThen A B => fsize A + fsize B + 1
  | .somehow A => fsize A + 1

/-- Interpolants can be large; don't dump an unreadable wall of text.
Raise this if you want to see bigger ones. -/
def renderCutoff : Nat := 200

/-- Size, and the rendered formula only if it is within `renderCutoff`. -/
def showFormula (φ : PLLFormula) : String :=
  let n := fsize φ
  if n ≤ renderCutoff then s!"{PLLFormula.toString φ}  (size {n})"
  else s!"<omitted: size {n} exceeds render cutoff {renderCutoff}>"

/-! ## Part 3 — named instances -/

private def pA := prop "p"
private def qA := prop "q"
private def rA := prop "r"
private def sA := prop "s"
private def uA := prop "u"
private def vA := prop "v"

/-- A named backward-search sequent: context, goal, and a note on what it
demonstrates / what verdict to expect. -/
structure SearchInstance where
  name : String
  ctx  : List PLLFormula
  goal : PLLFormula
  note : String

/-- Sequents worth running `search` on, fuel supplied by the caller.
`gap` is `PLLG4Gap`'s incompleteness separator: Iemhoff's original `G4`
provably cannot derive it (`PLLG4Gap.sep_not_G4`) while the repaired,
complete `G4c` — what `search` decides — should. -/
def searchInstances : List SearchInstance :=
  [ { name := "gap"
      ctx := [PLLG4Gap.Ga.somehow, PLLG4Gap.Fa]
      goal := rA
      note := "PLLG4Gap.sc_but_not_G4: G4 (Iemhoff's G4iLL) cannot derive \
        this, G4c (the repaired complete calculus `search` decides) \
        should — expect true" },
    { name := "unit"
      ctx := [pA]
      goal := pA.somehow
      note := "the ◯-unit, p ⊢ ◯p — expect true" },
    { name := "noescape"
      ctx := [pA.somehow]
      goal := pA
      note := "◯ admits no escape, ◯p ⊬ p — expect false" },
    { name := "howe"
      ctx := [((prop "B").ifThen ((prop "A").somehow.ifThen (prop "C"))).ifThen
                (prop "A").somehow,
              (prop "A").somehow.ifThen (prop "C"), (prop "B").somehow]
      goal := prop "C"
      note := "Howe's duplication sequent (PLLRun.lean's `pll_g4c` demo), \
        cut-free SC — expect true" } ]

/-- A named uniform-interpolation instance: the quantified atom, the
ambient space `S` (for the truncated `itpE`/`itpA`), the context, and a
goal formula (consumed by `itpA`/`interA`). `fuel`/`budget` drive the v3
truncated quantifiers; `legacyFuel` drives the v2 `interE`/`interA`. -/
structure QuantInstance where
  name       : String
  atom       : String
  space      : Finset PLLFormula
  ctx        : List PLLFormula
  goal       : PLLFormula
  fuel       : Nat
  budget     : Nat
  legacyFuel : Nat

private def G0 : List PLLFormula := [pA.somehow.ifThen rA]
private def S0 : Finset PLLFormula := {pA.somehow.ifThen rA, rA, pA.somehow, pA}

private def G2 : List PLLFormula := [pA.somehow.ifThen sA, uA.somehow.ifThen pA]
private def S2 : Finset PLLFormula :=
  {pA.somehow.ifThen sA, uA.somehow.ifThen pA, sA, pA, pA.somehow, uA.somehow, uA}

/-- `χ = (◯p ⊃ r) ⊃ ◯p` — the same shape as `PLLG4Gap.Ga`, one level
into a context instead of at the top; the "self-firing" stress case. -/
private def chiQ : PLLFormula := (pA.somehow.ifThen rA).ifThen pA.somehow

private def G3 : List PLLFormula := [chiQ.somehow, pA.somehow.ifThen rA]
private def S3 : Finset PLLFormula :=
  {chiQ.somehow, chiQ, pA.somehow.ifThen rA, rA.ifThen pA.somehow, pA.somehow, pA, rA}

/-- Contexts lifted from `wip/v3probe4.lean`'s v3.1 stress probe (`G0`the
simplest, `G2` a two-hypothesis fragment case, `G3` the self-firing case
that exercises the truncated quantifiers' budget mechanism). -/
def quantInstances : List QuantInstance :=
  [ { name := "tiny", atom := "p", space := {pA.ifThen rA, pA, rA}
      ctx := [pA.ifThen rA], goal := rA
      fuel := 150, budget := 2, legacyFuel := 2 },
    { name := "g0", atom := "p", space := S0, ctx := G0, goal := pA.somehow
      fuel := 150, budget := 3, legacyFuel := 4 },
    { name := "g2", atom := "p", space := S2, ctx := G2, goal := sA
      fuel := 150, budget := 3, legacyFuel := 4 },
    { name := "g3", atom := "p", space := S3, ctx := G3, goal := rA
      fuel := 150, budget := 2, legacyFuel := 6 } ]

/-- A named semantic-differencing pair: two formulas plus the atoms to
range valuations over. `eqFails` on them is the payload. -/
structure ZooInstance where
  name  : String
  atoms : List String
  lhs   : PLLFormula
  rhs   : PLLFormula
  note  : String

/-- Pairs lifted from `wip/v3probe4.lean`'s headline/regression checks:
each compares the v3 truncated quantifier against the v2 legacy one on
the same context, at the fuel/budget pairing the probe found stable. -/
def zooInstances : List ZooInstance :=
  [ { name := "g3-e", atoms := ["p", "r"]
      lhs := itpE "p" S3 150 2 G3, rhs := interE "p" 5 G3
      note := "truncated vs legacy ∃-quantifier, self-firing G3 context" },
    { name := "g3-full", atoms := ["p", "r"]
      lhs := (itpE "p" S3 150 2 G3).ifThen (itpA "p" S3 150 2 G3 rA)
      rhs := (interE "p" 6 G3).ifThen (interA "p" 6 G3 rA)
      note := "guarded sequent form E ⊃ A, truncated vs legacy, at G3" },
    { name := "g2-a", atoms := ["p", "s", "u"]
      lhs := itpA "p" S2 150 3 G2 sA, rhs := interA "p" 4 G2 sA
      note := "∀-quantifier regression check on the two-hypothesis G2" },
    { name := "g0-full", atoms := ["p", "r"]
      lhs := (itpE "p" S0 150 3 G0).ifThen (itpA "p" S0 150 3 G0 pA.somehow)
      rhs := (interE "p" 4 G0).ifThen (interA "p" 4 G0 pA.somehow)
      note := "guarded sequent form on the simplest context G0" } ]

/-! ## Part 4 — drivers

Every driver is pure `IO`: no `#eval`, no elaboration-time computation. -/

/-- `laxrun timing` — the standalone delay calculator: the `Tm.eval`
extractions on the `CIRC` (`PLLTiming.lean`) and carry-skip-adder
(`PLLTimingAdder.lean`) proof terms, at the nominal sky130 operating point.

Each printed value is the closed form that the library *proves* equal to
the `Tm.eval` extraction of the corresponding proof term — `circUp_rising`,
`circUp_a1_bound`, `coutSkip_bound`, `ripple_bound` (all `rfl`/`omega`,
kernel-checked at build time) — so these numbers are certified extraction
results.  We evaluate the closed forms rather than calling `Tm.eval` at
runtime because the dependently-typed evaluator (its result type is the
type family `sem`) crashes the v4.22.0-rc3 interpreter with SIGBUS
(erased-type arity confusion; minimal repro: `#eval (circUp.eval (· + ·) 0 B
(envCIRC 120 40 90) (0, ()) (0, ())).1`).  The theory files never hit this
because they pin these numbers by `rfl`/`decide` — kernel reduction, not
the interpreter.  Once a toolchain bump fixes the exe/codegen path, the
`Tm.eval` calls can be restored verbatim here. -/
def runTiming : IO Unit := do
  IO.println "PLL timing extraction — Tm.eval over the (ℕ, 0, +, max) delay algebra"
  IO.println "nominal sky130_fd_sc_hd corner: dOR=120 dINV=40 dAND=90 dCARRY=120 dMUX=100 (ps)"
  IO.println "(closed forms proven equal to the Tm.eval extractions: circUp_rising,"
  IO.println " circUp_a1_bound, ripple_bound, coutSkip_bound)"
  IO.println ""
  IO.println s!"CIRC↑ rising bound (max(dOR,dINV)+dAND): \
    {max dOR dINV + dAND} ps"
  IO.println s!"CIRC a=1 data-dependent bound (dINV+dAND, gOR absent — false path): \
    {dINV + dAND} ps"
  IO.println s!"CIRC topological longest path (sensitisation-blind): {dTopo} ps"
  IO.println s!"adder ripple sub-path (4·dCARRY, the chain the false path rides): \
    {4 * dCARRY} ps"
  IO.println s!"adder skip bound, all-propagate (2·dAND+dMUX, ripple absent — false path): \
    {2 * dAND + dMUX} ps"
  IO.println s!"adder topological longest path (4·dCARRY+dMUX, sensitisation-blind): \
    {dTopoAdder} ps"

/-- `laxrun search <instance> <fuel>` — run the `G4c` backward decider
(`PLLG4Dec.search`) on a named sequent with a user-supplied fuel (`W`/`as`
— the space parameters — are computed automatically from the sequent via
`listWeight`/`listAtoms`, exactly as `G4c_iff_search` does; only the fuel
is left for the caller to pick, since `decideFuel`'s automatic bound can
be far more expensive to even compute than the search itself). -/
def runSearch (args : List String) : IO Unit := do
  match args with
  | [nm, fuelStr] =>
    match searchInstances.find? (·.name == nm), fuelStr.toNat? with
    | some inst, some fuel =>
        let W := listWeight (inst.goal :: inst.ctx)
        let as := listAtoms (inst.goal :: inst.ctx)
        let verdict := search W as fuel ∅ inst.ctx inst.goal
        IO.println s!"search {nm}  (fuel {fuel})"
        IO.println s!"  context: {inst.ctx.map PLLFormula.toString}"
        IO.println s!"  goal:    {PLLFormula.toString inst.goal}"
        IO.println s!"  verdict: {verdict}"
        IO.println s!"  note:    {inst.note}"
    | none, _ =>
        IO.eprintln s!"unknown search instance '{nm}'; available: \
          {searchInstances.map (·.name)}"
    | _, none =>
        IO.eprintln s!"fuel must be a natural number, got '{fuelStr}'"
  | _ =>
      IO.eprintln "usage: laxrun search <instance> <fuel>"
      IO.println s!"available instances: {searchInstances.map (·.name)}"

/-- `laxrun quant <instance>` — evaluate the v3 truncated quantifiers
`itpE`/`itpA` (`PLLG4UITrunc.lean`) and the legacy v2 `interE`/`interA`
(`PLLG4UI.lean`) on a named instance, printing sizes (`fsize`) and, below
`renderCutoff`, the rendered formula. -/
def runQuant (args : List String) : IO Unit := do
  match args with
  | [nm] =>
    match quantInstances.find? (·.name == nm) with
    | some inst =>
        let e3 := itpE inst.atom inst.space inst.fuel inst.budget inst.ctx
        let a3 := itpA inst.atom inst.space inst.fuel inst.budget inst.ctx inst.goal
        let e2 := interE inst.atom inst.legacyFuel inst.ctx
        let a2 := interA inst.atom inst.legacyFuel inst.ctx inst.goal
        IO.println s!"quant {nm}  (atom {inst.atom}, fuel {inst.fuel}, \
          budget {inst.budget}, legacy fuel {inst.legacyFuel})"
        IO.println s!"  itpE   : {showFormula e3}"
        IO.println s!"  itpA   : {showFormula a3}"
        IO.println s!"  interE : {showFormula e2}"
        IO.println s!"  interA : {showFormula a2}"
    | none =>
        IO.eprintln s!"unknown quant instance '{nm}'; available: \
          {quantInstances.map (·.name)}"
  | _ =>
      IO.eprintln "usage: laxrun quant <instance>"
      IO.println s!"available instances: {quantInstances.map (·.name)}"

/-- `laxrun zoo <instance>` — the algebra-zoo semantic differencing:
`eqFails` between a named pair of formulas. `(0, 0)` means no model in the
zoo distinguishes them. -/
def runZoo (args : List String) : IO Unit := do
  match args with
  | [nm] =>
    match zooInstances.find? (·.name == nm) with
    | some inst =>
        let (failsLR, failsRL) := eqFails inst.atoms inst.lhs inst.rhs
        IO.println s!"zoo {nm}  (atoms {inst.atoms})"
        IO.println s!"  lhs: {showFormula inst.lhs}"
        IO.println s!"  rhs: {showFormula inst.rhs}"
        IO.println s!"  eqFails: ({failsLR}, {failsRL})  -- (0, 0) = semantically \
          equal over the zoo"
        IO.println s!"  note: {inst.note}"
    | none =>
        IO.eprintln s!"unknown zoo instance '{nm}'; available: \
          {zooInstances.map (·.name)}"
  | _ =>
      IO.eprintln "usage: laxrun zoo <instance>"
      IO.println s!"available instances: {zooInstances.map (·.name)}"

/-- `laxrun help` (and the no-argument default). -/
def runHelp : IO Unit := do
  IO.println "laxrun — compiled driver for LaxLogic's computational functions"
  IO.println ""
  IO.println "usage:"
  IO.println "  laxrun help                      this text"
  IO.println "  laxrun timing                    sky130 CIRC/adder delay extraction"
  IO.println "  laxrun search <instance> <fuel>  run the G4c decider with explicit fuel"
  IO.println "  laxrun quant <instance>          itpE/itpA vs legacy interE/interA"
  IO.println "  laxrun zoo <instance>            eqFails semantic differencing"
  IO.println ""
  IO.println s!"search instances: {searchInstances.map (·.name)}"
  IO.println s!"quant instances:  {quantInstances.map (·.name)}"
  IO.println s!"zoo instances:    {zooInstances.map (·.name)}"

end PLLND
