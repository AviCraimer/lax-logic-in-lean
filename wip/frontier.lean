import frontierCore
import round5refute
import Plausible

/-!
# THE FRONTIER SAMPLER — PLL instantiation

`wip/frontierCore.lean` is the generic layer (strata, admissibility gate,
corpus, replay); this file instantiates it at the tower's live obligation.

## What it screens

Two statements, one sequent.  Both are the `◯`-goal descent

    E@(ft, b+1)(Γ)  ,  A@(fs, b+1)(Γ, ◯D)   ⟹   A@(ft, b)(Γ, ◯D)

and they differ only in their **side conditions**:

* `cascade_boxgoal_pos` (`wip/absorb_base.lean`:2269, the tower's one `sorry`)
  carries the ROOM `defect S Γ · (|jumpGoals S| + 2) ≤ b`.  A refutation at a
  room-carrying cell re-opens the STATEMENT.
* `Round4.BoxDesc` (`wip/round4Comp.lean`:101) is room-free: only `1 ≤ b` and
  `fs ≤ ft`.  It is what PROGRESS §61(c) alternative 1 and the round-6/7
  prove route need.  A refutation at any admissible cell, including a
  SUB-ROOM one, kills that route.

So a single screen of `[src, amb] ⊢ tgt` settles both, and the cell's
recorded `stmt` column says which statement it is admissible for:
`both` when the room holds, `boxdesc` when `1 ≤ b < room`.

## Why a sampler and not another sweep

PROGRESS §§59–63 screened by exhaustive sweeps over small bounded regions,
re-scoped per formula of interest as each arose.  The shape that mattered in
round 6 — a space containing a doubly-boxed γ-clause `◯◯E ⊃ B`, witness
`S3` = piece-closure of `◯◯(a⊃b) ⊃ c` — sits one `◯`-nesting level beyond
the swept region and was found proof-side, two rounds after a
depth-stratified sample would have flagged the family.  This harness samples
sparsely and BROADLY along the axes the tables branch on, one structural
level beyond current use.

## The rules of the screen

* **Countermodel-only.**  `PLLND.Search.refute?` with `emitClosureCap := 0`
  runs the certified frame battery and nothing else: no proof search, no
  exponential closure emitter.  Every verdict is a kernel-checkable
  `FinCM.checkB` certificate or silence.  Countermodel CHECKING is cheap;
  proof SEARCH is not, and it is not this harness's job.
* **A quiet cell is quiet.**  `quiet` is recorded, never escalated and never
  reported as a positive result.  Escalation is a separate, statement-driven
  decision.
* **Never count an inadmissible cell.**  The six gates below are machine
  checks on the generated instance; a cell failing any of them is written to
  the corpus as `gate=FAIL:…` and excluded from every count.
-/

open PLLFormula PLLND PLLND.Search Plausible

namespace PLLND
namespace Frontier

open FrontierSampler

/-! ## §1  Seeded generation

`Plausible.Gen` supplies the generator combinators; `runSeeded` is the pure,
explicitly seeded runner.  `Plausible.Gen.run` is NOT used anywhere: it draws
from the global `stdGenRef` and is therefore not reproducible. -/

/-- **Seed diffusion.**  `Plausible.runRandWith` feeds the seed to
`mkStdGen`, whose first draws on nearby seeds are strongly correlated: the
pilot run drew the same γ-clause `(◯c) ⊃ a` from seeds `1000, 1009, 1017`.
One splitmix64 step before the seed reaches `mkStdGen` decorrelates it, and
the campaign stays exactly as reproducible (the mixing is a pure function of
the recorded seed). -/
def scramble (seed : Nat) : Nat := (Splitmix.step (Splitmix.mk (seed + 1))).1.toNat

/-- Pure, seeded, reproducible run of a `Plausible` generator: the adapter
from `Plausible.Gen` to `FrontierSampler.SeedGen`. -/
def runSeeded {α : Type} (seed size : Nat) (g : Gen α) : Option α :=
  ((runRandWith (scramble seed) g :
      ReaderT (ULift Nat) (Except GenError) α).run ⟨size⟩).toOption

/-- Pick an index in `[0, n)`; `0` when `n = 0`. -/
def pick (n : Nat) : Gen Nat := do
  let i ← Gen.choose Nat 0 (n - 1) (by omega)
  pure i.val

/-- Three DISTINCT atoms from a pool, chosen by a rotation so that generated
implications and jump shapes are never degenerate. -/
def genTriple (pool : List String) : Gen (String × String × String) := do
  let n := pool.length
  let i ← pick n
  pure (pool.getD (i % n) "a", pool.getD ((i + 1) % n) "b",
        pool.getD ((i + 2) % n) "c")

def genAtom (pool : List String) : Gen PLLFormula := do
  let i ← pick pool.length
  pure (prop (pool.getD i "a"))

/-- The four body shapes the tables branch on. -/
inductive BodyShape where
  | atom      -- `a`
  | jump      -- `(a ⊃ b) ⊃ c`   (a jump-shaped member: contributes to `jumpGoals`)
  | nestedBox -- `◯(a ⊃ b)`      (the `S3` frontier shape)
  | disj      -- `a ∨ b`
  deriving DecidableEq, Repr, Inhabited

def BodyShape.tag : BodyShape → String
  | .atom => "atom" | .jump => "jump" | .nestedBox => "nbox" | .disj => "or"

def genBodyOf (pool : List String) : BodyShape → Gen PLLFormula
  | .atom => genAtom pool
  | .jump => do
      let (x, y, z) ← genTriple pool
      pure (((prop x).ifThen (prop y)).ifThen (prop z))
  | .nestedBox => do
      let (x, y, _) ← genTriple pool
      pure (((prop x).ifThen (prop y)).somehow)
  | .disj => do
      let (x, y, _) ← genTriple pool
      pure ((prop x).or (prop y))

/-- `boxK k A` = `A` under `k` boxes.  `k` is the `◯`-nesting depth of a
γ-clause body: `k = 1` is `◯E ⊃ B`, `k = 2` the round-6 frontier
`◯◯E ⊃ B`, `k = 3` one level beyond it. -/
def boxK : Nat → PLLFormula → PLLFormula
  | 0, A => A
  | (n + 1), A => (boxK n A).somehow

/-! ## §2  The space, by piece-closure of a generated seed -/

/-- The pieces of a formula: exactly what `Round5Refute.pieceClosedB`
demands be present.  Closing a seed formula under `pieces` therefore
produces a piece-closed space by construction; the gate checks it anyway. -/
def pieces : PLLFormula → List PLLFormula
  | .prop a => [prop a]
  | .falsePLL => [falsePLL]
  | .and A B => (A.and B) :: (pieces A ++ pieces B)
  | .or A B => (A.or B) :: (pieces A ++ pieces B)
  | .ifThen A B => (A.ifThen B) :: (pieces A ++ pieces B)
  | .somehow A => A.somehow :: pieces A

def closureOfSeeds (fs : List PLLFormula) : List PLLFormula :=
  (fs.flatMap pieces).eraseDups

/-- Shape test used to pick a goal body of the requested kind. -/
def hasShape : BodyShape → PLLFormula → Bool
  | .atom, .prop _ => true
  | .jump, .ifThen (.ifThen _ _) _ => true
  | .nestedBox, .somehow _ => true
  | .disj, .or _ _ => true
  | _, _ => false

/-- Elements of the space whose absence from the context makes some clause
LIVE: the consequent of an implication of `S`, or the body of a box of `S`.
Dropping these is what round 5's `miss-c` / `miss-e` families do by hand. -/
def hotOf (Sl : List PLLFormula) : List PLLFormula :=
  (Sl.filterMap (fun F => match F with
    | .ifThen _ B => some B
    | .somehow A => some A
    | _ => none)).eraseDups.filter (fun F => Sl.contains F)

/-- Drop `d` elements from `Sl`, preferring "hot" ones. -/
def genDrop (Sl : List PLLFormula) (d : Nat) : Gen (List PLLFormula) := do
  let hot := hotOf Sl
  let cold := Sl.filter (fun F => !(hot.contains F))
  let mut chosen : List PLLFormula := []
  let mut pool := hot
  let mut rest := cold
  for _ in [0:d] do
    if pool.isEmpty then
      if rest.isEmpty then pure () else do
        let i ← pick rest.length
        let x := rest.getD i falsePLL
        chosen := x :: chosen
        rest := rest.filter (fun F => F != x)
    else do
      let i ← pick pool.length
      let x := pool.getD i falsePLL
      chosen := x :: chosen
      pool := pool.filter (fun F => F != x)
  pure chosen

/-! ## §3  A stratum's parameters, and the base instance it generates -/

/-- The axes a stratum fixes.  Everything else is drawn from the seed. -/
structure StratCfg where
  /-- Atom pool.  Three atoms keeps the battery's decoration count (and hence
  the cost of a quiet cell) inside seconds; see §6. -/
  pool : List String := ["a", "b", "c"]
  /-- `some k` = include a γ-clause `◯^k(body) ⊃ head`; `none` = no γ-clause. -/
  gammaDepth : Option Nat := some 1
  /-- Shape of the γ-clause body. -/
  gammaBody : BodyShape := .atom
  /-- Include an extra jump clause `(x ⊃ y) ⊃ z`. -/
  jumpExtra : Bool := false
  /-- Number of `∨`-members added to the seed (the `∨`-density axis). -/
  orCount : Nat := 0
  /-- Shape of the goal body `D` (the goal is `◯D`). -/
  goalShape : BodyShape := .atom
  /-- Extra `◯`s wrapped around the chosen goal body before the goal is
  formed: `goalBoxDepth = 1` at `goalShape := .jump` gives
  `D = ◯((x⊃y)⊃z)`, which is the shape of PROGRESS §62's three residual
  `JB2` cells; `2` is one level beyond them. -/
  goalBoxDepth : Nat := 0
  /-- Target defect (`|S ∖ Γ|`). -/
  defectTarget : Nat := 1
  /-- **Round 9.**  Generate the FRESH-ANTECEDENT shape instead of drawing the
  goal body out of the space: `D = (◯x ⊃ y) ⊃ z`, whose antecedent
  `C₁ = ◯x ⊃ y` is a `⊃◯`-clause, so the grown context `C₁ :: Γ` carries
  budget-GATED conjuncts — the configuration `AscRefute.not_ambGuardAscent`
  refutes the guard ascent at.  Everything else in `genBase` is bypassed;
  `gimp := false` leaves every campaign-1/2/g8 stratum byte-identical. -/
  gimp : Bool := false
  /-- Chain a γ-clause `◯w ⊃ x` in front of the goal body, sharing the atom
  `x` with the body's boxed antecedent — July's `Sk` verbatim. -/
  gimpGamma : Bool := true
  /-- Drop `C₁` from the context (the residue).  `false` keeps it — the
  PRESENT-antecedent control, whose goal disjunct lowers the guard. -/
  gimpFresh : Bool := true
  /-- Override the budget grid.  Empty = `budgetGrid room` as before.  The
  fresh-antecedent spaces have `room ≥ 5`, so the default grid would offer
  `b = 1` only and no `c < b` would exist to screen. -/
  bgridOverride : List Nat := []
  /-- Add a constant to BOTH fuels of every grid position.  `fuelGrid` ties
  `ft = b + 1`, which is right when the budget is what is being probed and
  wrong when the FUEL is: the round-9 refutation needs `ft = 5` at `b = 1`,
  a cell the tied grid cannot produce at any budget inside `ftCap`.  `0`
  (the default, and every campaign-1/2/g8 stratum's value) leaves the grid
  exactly as it was. -/
  fuelBump : Nat := 0
  deriving Inhabited

/-- A generated base instance: the space, the context, the goal body, and the
seed formulas that produced them. -/
structure Base where
  seeds : List PLLFormula
  Sl : List PLLFormula
  ctx : List PLLFormula
  dropped : List PLLFormula
  body : PLLFormula
  /-- Round 9: a stratum-fixed budget grid.  Empty (the default, and the
  value every campaign-1/2/g8 base carries) means `budgetGrid room`. -/
  bgrid : List Nat := []
  /-- Round 9: a constant added to both fuels of every grid position.  `0`
  is every campaign-1/2/g8 base's value. -/
  fbump : Nat := 0
  deriving Inhabited

def genBaseStd (cfg : StratCfg) : Gen Base := do
  let gam ← match cfg.gammaDepth with
    | none => pure ([] : List PLLFormula)
    | some k => do
        let A ← genBodyOf cfg.pool cfg.gammaBody
        let h ← genAtom cfg.pool
        pure [(boxK k A).ifThen h]
  -- A jump clause `(x⊃y)⊃z` alone can never make `liveJumpGates` fire: that
  -- instrument additionally demands `y⊃z ∈ Γ`, which the piece-closure of
  -- `(x⊃y)⊃z` does not contain.  Round 5's `S1` carries `b⊃c` for exactly
  -- this reason; the generator emits the companion clause too.
  let jmp ← if cfg.jumpExtra then do
      let (x, y, z) ← genTriple cfg.pool
      pure [((prop x).ifThen (prop y)).ifThen (prop z), (prop y).ifThen (prop z)]
    else pure []
  let mut ors : List PLLFormula := []
  for _ in [0:cfg.orCount] do
    let o ← genBodyOf cfg.pool .disj
    ors := o :: ors
  let seeds := gam ++ jmp ++ ors
  let S0 := closureOfSeeds seeds
  -- the goal body: an element of the space of the requested shape
  let cands := S0.filter (hasShape cfg.goalShape)
  let src := if cands.isEmpty then S0 else cands
  let i ← pick src.length
  let D := boxK cfg.goalBoxDepth (src.getD i falsePLL)
  -- `◯D` must be IN the space.  Re-closing the seeds together with `◯D` keeps
  -- the space piece-closed by construction.  At `goalBoxDepth = 0` this is
  -- byte-identical to appending `◯D` when it is absent, because `pieces` is
  -- transitive and the chosen body is already a piece of the seeds — so
  -- corpora recorded before this field existed still regenerate exactly.
  let Sl := closureOfSeeds (seeds ++ [D.somehow])
  let dropped ← genDrop Sl cfg.defectTarget
  pure { seeds, Sl, ctx := Sl.filter (fun F => !(dropped.contains F))
       , dropped, body := D, bgrid := cfg.bgridOverride
       , fbump := cfg.fuelBump }

/-- **Round 9: the fresh-antecedent base.**  `D = (◯x ⊃ y) ⊃ z` with the
antecedent `C₁ = ◯x ⊃ y` deleted from the context (`gimpFresh`), optionally
behind a chained γ-clause `◯w ⊃ x`.  At `pool = ["p","r","s","t"]`,
`gimpGamma := true`, `defectTarget := 0` and rotation `0` this is July's
`Skb`/`Gk` verbatim (up to the extra dropped pieces): the space whose
guard ascent `AscRefute.not_ambGuardAscent` kernel-refutes. -/
def genBaseGimp (cfg : StratCfg) : Gen Base := do
  let n := cfg.pool.length
  let i ← pick n
  let w := prop (cfg.pool.getD (i % n) "a")
  let x := prop (cfg.pool.getD ((i + 1) % n) "b")
  let y := prop (cfg.pool.getD ((i + 2) % n) "c")
  let z := prop (cfg.pool.getD ((i + 3) % n) "d")
  let ant := (w.somehow).ifThen x
  let c1 := (x.somehow).ifThen y
  let D := c1.ifThen z
  let mut ors : List PLLFormula := []
  for _ in [0:cfg.orCount] do
    let o ← genBodyOf cfg.pool .disj
    ors := o :: ors
  let seeds := (if cfg.gimpGamma then [ant] else []) ++ [D] ++ ors
  let Sl := closureOfSeeds (seeds ++ [D.somehow])
  let extra ← genDrop (Sl.filter (fun F => F != c1)) cfg.defectTarget
  let dropped := ((if cfg.gimpFresh then [c1] else []) ++ extra).eraseDups
  pure { seeds, Sl, ctx := Sl.filter (fun F => !(dropped.contains F))
       , dropped, body := D, bgrid := cfg.bgridOverride
       , fbump := cfg.fuelBump }

/-- The generator, dispatched.  `gimp := false` — every stratum of campaigns
1, 2 and g8 — runs `genBaseStd`, which is the pre-round-9 `genBase` verbatim,
so the recorded corpus regenerates byte-identically. -/
def genBase (cfg : StratCfg) : Gen Base :=
  if cfg.gimp then genBaseGimp cfg else genBaseStd cfg

/-! ## §4  The cell grid

One base instance yields up to nine cells: three budgets — the room floor,
one below it, and `1` — crossed with three fuel pairs.  `b = room` screens
BOTH statements; `b < room` screens `Round4.BoxDesc` only. -/

structure Cell extends Base where
  fs : Nat
  ft : Nat
  b : Nat
  gidx : Nat
  deriving Inhabited

def Cell.S (c : Cell) : Finset PLLFormula := c.Sl.toFinset
def Cell.defect (c : Cell) : Nat := PLLND.defect c.S c.ctx
def Cell.J (c : Cell) : Nat := (jumpGoals c.S).card
def Cell.room (c : Cell) : Nat := c.defect * (c.J + 2)

/-- **The fuel ceiling.**  The tables grow super-exponentially in the fuel:
at `|S| = 8` a cell at `ft = 5` weighs ~17 000 and its battery sweep costs
~12 s, while `ft = 4` is under a second.  Every fuel pair of the grid has
`ft = b + 1`, so this is equivalently a budget ceiling `b ≤ ftCap - 1`.

Consequence, recorded rather than hidden: a stratum whose room exceeds
`ftCap - 1` (defect ≥ 2, or `J ≥ 3`) contributes only SUB-ROOM cells, which
screen `Round4.BoxDesc` and not `cascade_boxgoal_pos`.  PROGRESS §62 reached
the same wall from the other side ("all defect ≥ 2 active bands (room ≥ 6
forces fuel ≥ 7)" were screened not at all). -/
def ftCap : Nat := 5

def budgetGrid (room : Nat) : List Nat :=
  ([room, room - 1, 1].filter (fun b => 1 ≤ b && b + 1 ≤ ftCap)).eraseDups

def fuelGrid (b : Nat) : List (Nat × Nat) :=
  [(b + 1, b + 1), (max 1 b, b + 1), (1, b + 1)].eraseDups

def gridOf (base : Base) : List Cell :=
  let S := base.Sl.toFinset
  let room := PLLND.defect S base.ctx * ((jumpGoals S).card + 2)
  let cells := (if base.bgrid.isEmpty then budgetGrid room else base.bgrid).flatMap (fun b =>
    (fuelGrid b).map (fun fp => (fp.1, fp.2, b)))
  cells.zipIdx.map (fun p =>
    { toBase := base, fs := p.1.1 + base.fbump, ft := p.1.2.1 + base.fbump
    , b := p.1.2.2, gidx := p.2 })

/-- Cells per base.  The seed is split as `seed / cellsPerBase` (which base)
and `seed % cellsPerBase` (which grid position), so a cell is a pure function
of `(stratum, seed, size)` and the corpus is replayable from those alone. -/
def cellsPerBase : Nat := 9

def genCell (cfg : StratCfg) : SeedGen Cell := fun seed size =>
  match runSeeded (seed / cellsPerBase) size (genBase cfg) with
  | none => none
  | some base => (gridOf base)[seed % cellsPerBase]?

/-! ## §5  The admissibility gate

Six machine checks, transcribed from the two statements' hypotheses.  The
first four are `Round5Refute`'s own instruments. -/

def gatePieceClosed : Gate Cell :=
  { name := "piece-closed", check := fun c => Round5Refute.pieceClosedB c.Sl }

def gateBoxGoalInS : Gate Cell :=
  { name := "box-goal-in-S", check := fun c => c.Sl.contains c.body.somehow }

def gateCtxInS : Gate Cell :=
  { name := "ctx-in-S", check := fun c => c.ctx.all (fun F => c.Sl.contains F) }

def gateDefectPos : Gate Cell :=
  { name := "defect-pos", check := fun c => 1 ≤ c.defect }

def gateFuelOrder : Gate Cell :=
  { name := "fs-le-ft", check := fun c => c.fs ≤ c.ft }

def gateBudgetPos : Gate Cell :=
  { name := "budget-pos", check := fun c => 1 ≤ c.b }

/-- The gate stack.  These are exactly the hypotheses `Round4.BoxDesc`
carries; the room is NOT a gate — it is recorded as the `stmt` column, so one
run screens the room-free statement everywhere and the room-carrying one
wherever the room holds. -/
def gates : List (Gate Cell) :=
  [gatePieceClosed, gateBoxGoalInS, gateCtxInS, gateDefectPos,
   gateFuelOrder, gateBudgetPos]

/-- Which statement(s) this cell is admissible for. -/
def Cell.stmt (c : Cell) : String :=
  if c.room ≤ c.b then "both" else "boxdesc"

/-! ## §6  The sequent, and countermodel-only triage -/

def pv : String := "p"

def Cell.src (c : Cell) : PLLFormula := itpA pv c.S c.fs (c.b + 1) c.ctx c.body.somehow
def Cell.amb (c : Cell) : PLLFormula := itpE pv c.S c.ft (c.b + 1) c.ctx
def Cell.tgt (c : Cell) : PLLFormula := itpA pv c.S c.ft c.b c.ctx c.body.somehow
/-- The target one budget up: `tgtUp ≠ tgt` is `act`, the test that the
target table actually READS the budget at this cell.  An `act = false` cell
has no budget-descent content (PROGRESS §62, structural finding A). -/
def Cell.tgtUp (c : Cell) : PLLFormula := itpA pv c.S c.ft (c.b + 1) c.ctx c.body.somehow

def Cell.sz (c : Cell) : Nat :=
  TowerKit.sz c.src + TowerKit.sz c.amb + TowerKit.sz c.tgt

/-! ### The two-stage size guard

Building `src`/`amb`/`tgt` is itself expensive when the cell is large — the
profile pass sees cells of weight 750 000 — so the weight cannot be the FIRST
test.  Stage 1 is a purely syntactic predictor: the tables recurse once per
live growth clause per fuel level, so `ft · (1 + liveGates)` tracks the
blow-up closely.  Measured against the profile: at `ft = 5`, one live gate
gives weights in the hundreds and two gives weights in the hundred
thousands.  Stage 2 is the actual weight against `szCap`.

Both stages record their reason in the corpus, so a cell that was never run
is visible as such and is never counted as quiet. -/

/-- Live growth clauses of the cell, by `Round5Refute`'s instruments. -/
def Cell.liveGates (c : Cell) : Nat :=
  Round5Refute.liveJumpGates c.Sl c.ctx + Round5Refute.liveBoxGates c.Sl c.ctx
    + Round5Refute.liveBoxEnv c.Sl c.ctx

/-- Stage-1 predictor. -/
def Cell.pred (c : Cell) : Nat := c.ft * (1 + c.liveGates)

/-- Stage-1 ceiling — a SAFETY VALVE, not the working filter.  Measurement:
inside `ftCap = 5` even a 460 000-weight cell is BUILT in ~60 ms, so stage 2
can afford to see it; the largest cells at `ft = 7` are 7 000 000 and are not
worth building at all.  `30` lets everything inside `ftCap` through and stops
the pathological corner. -/
def predCap : Nat := 30

/-- Countermodel-only configuration: the certified battery over round 5's
widened frame list, the closure emitter OFF (`emitClosureCap := 0`) and no
positive stage at all.  Deterministic; a verdict is a `FinCM.checkB`
certificate or silence. -/
def cfgCM : Config :=
  { frames := Round5Refute.xFrames ++ defaultFrames, emitClosureCap := 0 }

/-- The recorded columns of a cell. -/
def cols (c : Cell) : List (String × String) :=
  [ ("sf", String.intercalate " ⋄ " (c.seeds.map reprStr))
  , ("D", reprStr c.body)
  , ("drop", String.intercalate " ⋄ " (c.dropped.map reprStr))
  , ("nS", toString c.Sl.length)
  , ("d", toString c.defect)
  , ("J", toString c.J)
  , ("room", toString c.room)
  , ("b", toString c.b)
  , ("fs", toString c.fs)
  , ("ft", toString c.ft)
  , ("g", toString c.gidx)
  , ("lg", toString c.liveGates)
  , ("stmt", c.stmt) ]

/-- Triage one cell.  Stage 1 rejects predicted-huge cells without building
the tables; stage 2 rejects cells over the weight cap; otherwise the battery
is swept once and the verdict is `R!` (with the model recorded) or `quiet`. -/
def triage (cap : Nat) (c : Cell) : IO Outcome := do
  if c.pred > predCap then
    pure { triage := .skip, cols := [("why", "pred"), ("sz", "?"), ("act", "?")] }
  else do
  let n ← IO.lazyPure (fun _ => c.sz)
  if n > cap then
    pure { triage := .skip
         , cols := [("why", "size"), ("sz", toString n), ("act", "?")] }
  else do
    let act ← IO.lazyPure (fun _ => c.tgtUp != c.tgt)
    -- `triv` = the source and the target are the SAME formula, so the cell is
    -- an instance of identity and carries no content at all.  It happens
    -- whenever `fs = ft` and the budget is inactive; campaign 1 had 196 such
    -- cells out of 692, and they must not be counted as evidence.
    let triv ← IO.lazyPure (fun _ => c.src == c.tgt)
    let ats ← IO.lazyPure (fun _ => (atomsOf (c.tgt :: [c.src, c.amb])).length)
    let v ← IO.lazyPure (fun _ => refute? cfgCM [c.src, c.amb] c.tgt)
    let extra := [("why", "run"), ("sz", toString n), ("act", toString act),
                  ("triv", toString triv), ("at", toString ats)]
    match v with
    | some ⟨M, w, _⟩ =>
        pure { triage := .hit, cols := extra
             , cert := s!"w={w} M={reprStr M}" }
    | none => pure { triage := .quiet, cols := extra }

/-! ## §7  The strata

Fifteen strata along the axes the tables branch on.  `dN` names the
`◯`-nesting depth of the γ-clause body: `d1` is the swept region, `d2` the
round-6 frontier (`S3`), `d3` one level beyond it.  `J1` has no γ-clause at
all (a bare jump clause, `J = 1`); `or1`/`or2` raise the `∨`-density; `df2`
raises the defect. -/

def mkStratum (nm : String) (cfg : StratCfg) (samples : Nat) (seed0 : Nat)
    (note : String) : Stratum Cell :=
  { name := nm, gen := genCell cfg, samples, size := 4, seed0, note }

/-- Nesting depth 1 — the region round 4/5 swept. -/
def s_d1_atom : Stratum Cell :=
  mkStratum "d1-atom" { gammaDepth := some 1, gammaBody := .atom, goalShape := .atom }
    72 1000 "γ-clause ◯E⊃B, atomic body and goal"
def s_d1_jump : Stratum Cell :=
  mkStratum "d1-jump" { gammaDepth := some 1, gammaBody := .atom, goalShape := .jump }
    72 2000 "γ-clause ◯E⊃B, jump-shaped goal body"
def s_d1_nbox : Stratum Cell :=
  mkStratum "d1-nbox" { gammaDepth := some 1, gammaBody := .atom, goalShape := .nestedBox }
    72 3000 "γ-clause ◯E⊃B, nested-box goal body"

/-- Nesting depth 2 — the round-6 frontier: a γ-clause with a BOXED body,
`◯◯E ⊃ B`.  `S3` = piece-closure of `◯◯(a⊃b) ⊃ c` lives here. -/
def s_d2_imp : Stratum Cell :=
  mkStratum "d2-imp" { gammaDepth := some 2, gammaBody := .atom, goalShape := .nestedBox }
    72 4000 "γ-clause ◯◯E⊃B (THE S3 SHAPE), nested-box goal"
def s_d2_jumpbody : Stratum Cell :=
  mkStratum "d2-jumpbody" { gammaDepth := some 2, gammaBody := .jump, goalShape := .nestedBox }
    72 5000 "γ-clause ◯◯((x⊃y)⊃z)⊃B, nested-box goal"
def s_d2_atomgoal : Stratum Cell :=
  mkStratum "d2-atomgoal" { gammaDepth := some 2, gammaBody := .atom, goalShape := .atom }
    72 6000 "γ-clause ◯◯E⊃B, atomic goal body"

/-- Nesting depth 3 — one structural level BEYOND the current frontier. -/
def s_d3_imp : Stratum Cell :=
  mkStratum "d3-imp" { gammaDepth := some 3, gammaBody := .atom, goalShape := .nestedBox }
    72 7000 "γ-clause ◯◯◯E⊃B, nested-box goal"
def s_d3_atomgoal : Stratum Cell :=
  mkStratum "d3-atomgoal" { gammaDepth := some 3, gammaBody := .atom, goalShape := .atom }
    72 8000 "γ-clause ◯◯◯E⊃B, atomic goal body"

/-- `J = 1`: a bare jump clause, no γ-clause. -/
def s_j1 : Stratum Cell :=
  mkStratum "j1-nogamma"
    { gammaDepth := none, jumpExtra := true, goalShape := .jump }
    72 9000 "no γ-clause, one jump clause (J=1)"

/-- `J ≥ 3`: γ-clause AND a jump clause. -/
def s_j3 : Stratum Cell :=
  mkStratum "j3-both"
    { gammaDepth := some 2, gammaBody := .atom, jumpExtra := true, goalShape := .nestedBox }
    72 10000 "γ-clause ◯◯E⊃B plus a jump clause"

/-- `∨`-density 1 and 2. -/
def s_or1 : Stratum Cell :=
  mkStratum "or1"
    { gammaDepth := some 2, gammaBody := .atom, orCount := 1, goalShape := .disj }
    72 11000 "one ∨-member, ∨-carrying goal body"
def s_or2 : Stratum Cell :=
  mkStratum "or2"
    { gammaDepth := some 2, gammaBody := .atom, orCount := 2, goalShape := .nestedBox }
    72 12000 "two ∨-members, nested-box goal"

/-- Defect 2. -/
def s_df2_d1 : Stratum Cell :=
  mkStratum "df2-d1"
    { gammaDepth := some 1, gammaBody := .atom, goalShape := .atom, defectTarget := 2 }
    72 13000 "defect 2 at nesting depth 1"
def s_df2_d2 : Stratum Cell :=
  mkStratum "df2-d2"
    { gammaDepth := some 2, gammaBody := .atom, goalShape := .nestedBox, defectTarget := 2 }
    72 14000 "defect 2 at nesting depth 2 (the S3 shape)"

/-- The eliminated variable `p` INSIDE the space (round 5's `JBp`/`BBp`
variants): the tables' `p`-clauses become live. -/
def s_pv : Stratum Cell :=
  mkStratum "pvar"
    { pool := ["p", "b", "c"], gammaDepth := some 2, gammaBody := .atom
    , goalShape := .nestedBox }
    72 15000 "eliminated variable p occurs in S, γ-depth 2"

/-! ### Campaign-2 strata — the `J = 1` band, where the room-carrying
statement is actually reachable

Campaign 1 measured something the exhaustive sweeps could not: of 692
screened cells, only **12** were simultaneously admissible for
`cascade_boxgoal_pos` (room `≤ b`) and budget-ACTIVE, and all twelve were in
`j1-nogamma`.  The reason is arithmetic: any γ-clause `◯X ⊃ B` contributes
BOTH `X` and `◯X` to `jumpGoals`, so `J ≥ 2`, so the room is `≥ 4`, so the
room-carrying cells sit at `b = 4`, `ft = 5`, where the tables weigh
10⁵–10⁶ and are not decide-feasible.  `J = 1` — a jump clause and no
γ-clause — has room `3`, and its room-carrying cells are small.

These four strata put the nested-box GOAL shapes into that reachable band.
`jb1-nbox` is a randomised generalisation of PROGRESS §62's three residual
`JB2` cells (`D = ◯((a⊃b)⊃c)`, room 3, `b = 3`); `jb1-nbox2` is one `◯`
beyond them. -/

def s_jb1_imp : Stratum Cell :=
  mkStratum "jb1-imp"
    { gammaDepth := none, jumpExtra := true, goalShape := .jump }
    72 16000 "J=1, D=(x⊃y)⊃z — round 5's JB family"
def s_jb1_nbox : Stratum Cell :=
  mkStratum "jb1-nbox"
    { gammaDepth := none, jumpExtra := true, goalShape := .jump
    , goalBoxDepth := 1 }
    72 17000 "J=1, D=◯((x⊃y)⊃z) — THE JB2 RESIDUE SHAPE (§62)"
def s_jb1_nbox2 : Stratum Cell :=
  mkStratum "jb1-nbox2"
    { gammaDepth := none, jumpExtra := true, goalShape := .jump
    , goalBoxDepth := 2 }
    72 18000 "J=1, D=◯◯((x⊃y)⊃z) — one ◯ beyond the JB2 residue"
def s_jb1_atom2 : Stratum Cell :=
  mkStratum "jb1-atom2"
    { gammaDepth := none, jumpExtra := true, goalShape := .atom
    , goalBoxDepth := 2 }
    72 19000 "J=1, D=◯◯a — nested box over an atomic body"

/-! ### Round-8 strata — the §66(h) residue shape

`CompProd`'s goal-row case at jump-shaped UNBOXED bodies over a γ-carrying
space: `D = (x⊃y)⊃z` with `goalBoxDepth = 0`, a γ-clause present so the
walk's γ-tier is live.  A genuinely jump-shaped `D` needs `jumpExtra` (the
γ-seed's own closure contains no jump-shaped member, so without it the
generator falls back — `d1-jump`'s recorded `D` is the γ-clause itself).
The γ-clause plus the jump clause force `J ≥ 3`, so every cell here is
SUB-room: the standard triage screens the room-free `Round4.BoxDesc`
(a hit kills it outright), and the `wip/frontier_g8.lean` passes re-drive
the same cells at the round-8 goal-row sequents (`c < b`), where a hit is
a `CompProd`-level result (`Round7.not_boxDesc_of_not_compProd`). -/

def s_g8_d1jump : Stratum Cell :=
  mkStratum "g8-d1jump"
    { gammaDepth := some 1, gammaBody := .atom, jumpExtra := true
    , goalShape := .jump }
    72 20000 "γ-clause ◯E⊃B plus jump clause, D=(x⊃y)⊃z unboxed"
def s_g8_d2jump : Stratum Cell :=
  mkStratum "g8-d2jump"
    { gammaDepth := some 2, gammaBody := .atom, jumpExtra := true
    , goalShape := .jump }
    72 21000 "γ-clause ◯◯E⊃B (S3 shape) plus jump clause, D=(x⊃y)⊃z unboxed — THE ROUND-8 RESIDUE SHAPE"

/-! ### Round-9 strata — the §67(h) residue shape

The round-8 strata put a jump-shaped unboxed body `D = (x⊃y)⊃z` over a
γ-carrying space, but their antecedent `x⊃y` is COLD (`hotOf` prefers
implication consequents and box bodies), so `genDrop` leaves it in the
context and every cell realises the PRESENT-antecedent branch of
`itpAgoal` — the branch that lowers the target guard by one.  The residue is
the other branch.  These four strata force it: the body is
`D = (◯x ⊃ y) ⊃ z` and its antecedent `C₁ = ◯x ⊃ y` is deleted from the
context, so `C₁ ∉ Γ` and — because `C₁` is a `⊃◯`-clause — the grown context
`C₁ :: Γ` carries budget-gated conjuncts.  `g9-gimpP` is the matched control
with `C₁` kept. -/

def s_g9_gimp : Stratum Cell :=
  mkStratum "g9-gimp"
    { pool := ["p", "r", "s", "t"], gimp := true, gimpGamma := true
    , defectTarget := 0, bgridOverride := [3, 2, 1] }
    36 22000 "D=(◯x⊃y)⊃z, antecedent FRESH, chained γ-clause — July's Sk shape"
def s_g9_gimpX : Stratum Cell :=
  mkStratum "g9-gimpX"
    { pool := ["a", "b", "c", "d"], gimp := true, gimpGamma := true
    , defectTarget := 1, bgridOverride := [3, 2, 1] }
    36 23000 "D=(◯x⊃y)⊃z, antecedent FRESH plus one hot drop, chained γ-clause"
def s_g9_gimp0 : Stratum Cell :=
  mkStratum "g9-gimp0"
    { pool := ["a", "b", "c", "d"], gimp := true, gimpGamma := false
    , defectTarget := 1, bgridOverride := [3, 2, 1] }
    36 24000 "D=(◯x⊃y)⊃z, antecedent FRESH, no γ-clause"
def s_g9_gimpP : Stratum Cell :=
  mkStratum "g9-gimpP"
    { pool := ["a", "b", "c", "d"], gimp := true, gimpGamma := true
    , gimpFresh := false, defectTarget := 1, bgridOverride := [3, 2, 1] }
    36 25000 "CONTROL: the same shape with the antecedent PRESENT"

/-! ### Round-9 strata, second tier — THE DEFECT AXIS, to its end

Every campaign-1/2/g8 stratum drops one or two members of the space, so its
context is nearly all of `S` and its defect is 1 or 2.  The refutation round
9 found (`wip/round9pin.lean`) lives at the OTHER end of that axis: `Γ = []`,
defect `|S|`, where the ambient degenerates to `⊤` and the `itpAenv` tables
are empty.  `defectTarget := 99` drops everything `genDrop` can reach — the
context is emptied — and these strata put the region into the corpus. -/

def s_g9_bare : Stratum Cell :=
  mkStratum "g9-bare"
    { pool := ["a", "b", "c", "d"], gimp := true, gimpGamma := false
    , defectTarget := 99, bgridOverride := [3, 2, 1] }
    24 26000 "D=(◯x⊃y)⊃z, antecedent fresh, CONTEXT EMPTIED"
def s_g9_bareG : Stratum Cell :=
  mkStratum "g9-bareG"
    { pool := ["p", "r", "s", "t"], gimp := true, gimpGamma := true
    , defectTarget := 99, bgridOverride := [3, 2, 1] }
    24 27000 "July's Sk shape with the CONTEXT EMPTIED"
def s_g9_bareJ : Stratum Cell :=
  mkStratum "g9-bareJ"
    { gammaDepth := some 1, gammaBody := .atom, jumpExtra := true
    , goalShape := .jump, defectTarget := 99, bgridOverride := [3, 2, 1] }
    24 28000 "the ROUND-8 stratum shape with the CONTEXT EMPTIED"

/-! ### Round-9 strata, third tier — the FUEL axis, untied from the budget

The bare-context strata above still produce nothing: `fuelGrid` ties
`ft = b + 1`, so an emptied context at `b ≤ 3` is screened at `ft ≤ 4`, and
the refutation of `Round4.BoxDesc` at `Γ = []` first appears at `ft = 5`
(at `ft = 4` the same cell is provable — `wip/frontier_g9v.txt`).  The tie
is an assumption about where the content lives, and it was wrong.  These
three strata lift both fuels by three. -/

def s_g9_bareF : Stratum Cell :=
  mkStratum "g9-bareF"
    { pool := ["a", "b", "c", "d"], gimp := true, gimpGamma := false
    , defectTarget := 99, bgridOverride := [2, 1], fuelBump := 3 }
    24 29000 "emptied context, fuels lifted by 3 — THE ROUND-9 REFUTING REGION"
def s_g9_bareFG : Stratum Cell :=
  mkStratum "g9-bareFG"
    { pool := ["p", "r", "s", "t"], gimp := true, gimpGamma := true
    , defectTarget := 99, bgridOverride := [2, 1], fuelBump := 3 }
    24 30000 "July's Sk shape, emptied context, fuels lifted by 3"
def s_g9_bareFJ : Stratum Cell :=
  mkStratum "g9-bareFJ"
    { gammaDepth := some 1, gammaBody := .atom, jumpExtra := true
    , goalShape := .jump, defectTarget := 99, bgridOverride := [2, 1]
    , fuelBump := 3 }
    24 31000 "the round-8 stratum shape, emptied context, fuels lifted by 3"

def allStrata : List (Stratum Cell) :=
  [ s_d1_atom, s_d1_jump, s_d1_nbox
  , s_d2_imp, s_d2_jumpbody, s_d2_atomgoal
  , s_d3_imp, s_d3_atomgoal
  , s_j1, s_j3, s_or1, s_or2, s_df2_d1, s_df2_d2, s_pv
  , s_jb1_imp, s_jb1_nbox, s_jb1_nbox2, s_jb1_atom2
  , s_g8_d1jump, s_g8_d2jump
  , s_g9_gimp, s_g9_gimpX, s_g9_gimp0, s_g9_gimpP
  , s_g9_bare, s_g9_bareG, s_g9_bareJ
  , s_g9_bareF, s_g9_bareFG, s_g9_bareFJ ]

/-- Campaign 1's fifteen strata, kept separately so that campaign 1 can be
re-run exactly. -/
def campaign1Strata : List (Stratum Cell) := allStrata.take 15

/-- Campaign 2: the reachable `J = 1` band.  (`take 4` keeps this list's
value unchanged by the round-8 strata appended after it.) -/
def campaign2Strata : List (Stratum Cell) := (allStrata.drop 15).take 4

/-- Campaign g8: the round-8 residue shape.  (`take 2` keeps this list's
value unchanged by the round-9 strata appended after it.) -/
def campaignG8Strata : List (Stratum Cell) := (allStrata.drop 19).take 2

/-- Campaign g9: the round-9 fresh-antecedent residue shape. -/
def campaignG9Strata : List (Stratum Cell) := (allStrata.drop 21).take 4

/-- Campaign g9b: the defect axis to its end (the context emptied) — the
region the whole campaign-1/2/g8 corpus never sampled, and the one that
carries the refutation. -/
def campaignG9bStrata : List (Stratum Cell) := (allStrata.drop 25).take 3

/-- Campaign g9c: the same region with the FUEL untied from the budget. -/
def campaignG9cStrata : List (Stratum Cell) := allStrata.drop 28

/-- Look a stratum up by name — the replay side of `genCell`. -/
def stratumByName (nm : String) : Option (Stratum Cell) :=
  allStrata.find? (fun s => s.name == nm)

/-- Replay's regenerator: `(stratum, seed, size) ↦ cell`, the same pure
function the campaign used. -/
def regen (nm : String) (seed size : Nat) : Option Cell :=
  (stratumByName nm).bind (fun s => s.gen seed size)

/-! ## §8  Runners -/

def corpus : Ledger := { path := "wip/frontier_corpus.txt" }

/-- The live-fire calibration.  Round 4's UNBOXED control is `checkB`-certified
refutable; if the countermodel-only configuration cannot reproduce `R!` there,
every `quiet` in the corpus is meaningless. -/
def calibrate : IO Bool := do
  let t0 ← IO.monoMsNow
  let u ← IO.lazyPure (fun _ =>
    (refute? cfgCM [Round4Probe3.srcU, Round4Probe3.ambB] Round4Probe3.tgtU).isSome)
  let bx ← IO.lazyPure (fun _ =>
    (refute? cfgCM [Round4Probe3.srcB, Round4Probe3.ambB] Round4Probe3.tgtB).isSome)
  let t1 ← IO.monoMsNow
  corpus.comment s!"CALIB unboxed(expect R!)={u} boxed(expect quiet)={!bx} ({t1 - t0} ms)"
  pure (u && !bx)

/-! ### Replay

A cell is a pure function of `(stratum, seed, size)`, so the corpus can be
re-driven with no regeneration guesswork.  Two uses are implemented:

* `replayRegression` — regenerate every recorded admissible cell and check
  that its shape columns still match the corpus.  This is the determinism
  audit: if it disagrees, the generator or the instruments moved under the
  corpus and every stored verdict is suspect.
* `replayUnboxed` — screen a DIFFERENT statement over the same instances:
  the room-free descent at the UNBOXED goal `D` in place of `◯D`.  That
  statement is known false (`AscRefute.not_roomFreeDescent`,
  `Round4Probe3.unboxed_refuted`), so the corpus should produce hits; how
  many, and where, measures how load-bearing the `◯` is across the sampled
  region rather than at the single instance §60 checked. -/

def replayLedger : Ledger := { path := "wip/frontier_replay.txt" }

/-- The recorded shape columns, recomputed. -/
def shapeOf (c : Cell) : String :=
  s!"nS={c.Sl.length} d={c.defect} J={c.J} room={c.room} b={c.b} fs={c.fs} ft={c.ft}"

def shapeFromRec (r : Rec) : String :=
  let g (k : String) := (r.col? k).getD "?"
  let nS := g "nS"; let d := g "d"; let jj := g "J"; let rm := g "room"
  let bb := g "b"; let ff := g "fs"; let tt := g "ft"
  s!"nS={nS} d={d} J={jj} room={rm} b={bb} fs={ff} ft={tt}"

/-- The UNBOXED source and target: the same cell with the `◯` stripped from
the goal.  `Round4.BoxDesc` at an unboxed goal is the room-free descent, and
it is refuted in the repository's inventory. -/
def Cell.srcUn (c : Cell) : PLLFormula := itpA pv c.S c.fs (c.b + 1) c.ctx c.body
def Cell.tgtUn (c : Cell) : PLLFormula := itpA pv c.S c.ft c.b c.ctx c.body

/-- Paste-ready `decide +kernel` pin for a hit, in the style of
`wip/reparamRefute.lean` and `wip/round4probe3.lean`. -/
def pinSnippet (nm : String) (M : FinCM) (w : Nat) : String :=
  s!"theorem {nm} : FinCM.checkB ({reprStr M}) {w} [src, amb] tgt = true := by \
decide +kernel"

/-- Regression replay: no search, only regeneration and a shape comparison. -/
def replayRegression : IO Unit := do
  let r ← replay corpus regen (fun c rc => pure
    { triage := if shapeOf c == shapeFromRec rc then rc.triage else Triage.hit
    , cert := shapeOf c })
  replayLedger.comment s!"REGRESSION (shape agreement): {r.render}"
  for n in r.notes.take 20 do replayLedger.comment s!"  {n}"

/-- Re-aim replay: the UNBOXED room-free descent, over the corpus's own
instances.  Size-capped exactly like the campaign. -/
def replayUnboxed (cap : Nat) : IO Unit := do
  let r ← replay corpus regen (fun c rc => do
    if (rc.col? "why").getD "" != "run" then
      pure { triage := rc.triage }      -- never ran; agree by construction
    else do
      let n ← IO.lazyPure (fun _ =>
        TowerKit.sz c.srcUn + TowerKit.sz c.amb + TowerKit.sz c.tgtUn)
      if n > cap then pure { triage := rc.triage }
      else do
        let v ← IO.lazyPure (fun _ => refute? cfgCM [c.srcUn, c.amb] c.tgtUn)
        match v with
        | some ⟨M, w, _⟩ => pure { triage := .hit, cert := s!"w={w} M={reprStr M}" }
        | none => pure { triage := .quiet })
  replayLedger.comment s!"RE-AIM (unboxed room-free descent): {r.render}"
  for n in r.notes.take 30 do replayLedger.comment s!"  {n}"

/-- Re-aim replay II: the statement with the AMBIENT PREMISE DROPPED,
`A@(fs, b+1)(Γ, ◯D) ⊢ A@(ft, b)(Γ, ◯D)`.  The ambient `E@(ft, b+1)(Γ)` is
one of the two premises of `cascade_boxgoal_pos`; the premise-free form is
strictly stronger and is expected to be false.  Its purpose here is
methodological: it shows the corpus producing hits for a statement it was not
gathered for, at zero generation cost — which is the claim `replay` makes. -/
def replayNoAmbient (cap : Nat) : IO Unit := do
  let r ← replay corpus regen (fun c rc => do
    if (rc.col? "why").getD "" != "run" then pure { triage := rc.triage }
    else do
      let n ← IO.lazyPure (fun _ => TowerKit.sz c.src + TowerKit.sz c.tgt)
      if n > cap then pure { triage := rc.triage }
      else do
        let v ← IO.lazyPure (fun _ => refute? cfgCM [c.src] c.tgt)
        match v with
        | some ⟨M, w, _⟩ => pure { triage := .hit, cert := s!"w={w} M={reprStr M}" }
        | none => pure { triage := .quiet })
  replayLedger.comment s!"RE-AIM II (ambient premise dropped): {r.render}"
  for n in r.notes.take 12 do replayLedger.comment s!"  {n}"

/-- Run a campaign at a size cap. -/
def campaignOf (cap : Nat) (tag : String) (sts : List (Stratum Cell)) : IO Unit := do
  let ok ← calibrate
  if !ok then
    corpus.comment "CALIBRATION FAILED — screen is broken, results discarded"
  else do
    let _ ← runCampaign corpus tag sts gates cols (triage cap)
    pure ()

/-- Every stratum. -/
def campaign (cap : Nat) (tag : String) : IO Unit := campaignOf cap tag allStrata

/-- Profile pass: generate every cell of every stratum and record shape and
size ONLY (no search).  Used to calibrate the size cap.  Output goes through
a flushed ledger, so a killed profile keeps what it produced. -/
def profileLedger : Ledger := { path := "wip/frontier_profile.txt" }

/-- Re-fuel a cell (diagnostics only: the corpus never contains a cell that
was not produced by a generator). -/
def Cell.withFuel (c : Cell) (fs ft : Nat) : Cell := { c with fs, ft }

/-- **Budget-activity profile.**  `act` is the test that the target table
actually READS the budget.  It is the difference between screening the
statement's content and screening an identity, so the fuel grid must be
chosen to make it true.  This prints `act` and weight at `ft = b+1, b+2, b+3`
for the first bases of each stratum. -/
def actProfile : IO Unit := do
  for st in allStrata do
    for i in [0:3] do
      let sd := st.seed0 + i * cellsPerBase
      match st.gen sd st.size with
      | none => pure ()
      | some c0 =>
        for k in [1:4] do
          let c := c0.withFuel (c0.b + k) (c0.b + k)
          if c.pred > 18 then
            profileLedger.comment s!"{st.name}/{sd} b={c.b} ft={c.ft} PRED-SKIP lg={c.liveGates}"
          else do
            let z ← IO.lazyPure (fun _ => c.sz)
            let a ← IO.lazyPure (fun _ => c.tgtUp != c.tgt)
            profileLedger.comment s!"{st.name}/{sd} b={c.b} ft={c.ft} \
lg={c.liveGates} act={a} sz={z}"

/-- Per-cell profile: one line per generated cell, shape and weight only.
This is what calibrates the triage size cap. -/
def profileCells (szCap : Nat) : IO Unit := do
  for st in allStrata do
    for i in [0:st.samples] do
      match st.gen (st.seed0 + i) st.size with
      | none => pure ()
      | some c =>
        let gt := (firstFailure gates c).getD "ok"
        let z ← IO.lazyPure (fun _ => c.sz)
        profileLedger.comment s!"{st.name}/{st.seed0 + i} |S|={c.Sl.length} \
d={c.defect} J={c.J} room={c.room} b={c.b} fs={c.fs} ft={c.ft} \
stmt={c.stmt} gate={gt} sz={z} run={decide (z ≤ szCap)}"

def profile : IO Unit := do
  for st in allStrata do
    let mut tot := 0
    let mut n := 0
    let mut big := 0
    let mut gsum := 0
    let mut mx := 0
    let mut nogen := 0
    for i in [0:st.samples] do
      match st.gen (st.seed0 + i) st.size with
      | none => nogen := nogen + 1
      | some c =>
        if (firstFailure gates c).isSome then
          gsum := gsum + 1
        else do
          let z ← IO.lazyPure (fun _ => c.sz)
          n := n + 1
          tot := tot + z
          if z > mx then mx := z
          if z > 8000 then big := big + 1
    profileLedger.comment s!"{st.name}: cells={n} gated={gsum} no-cell={nogen} \
mean|s+a+t|={tot / (max 1 n)} max={mx} over8k={big}"

/-- One line per generated base of a stratum: what the generator actually
produced.  For eyeballing the strata before spending search time. -/
def showStratum (st : Stratum Cell) (howMany : Nat) : IO Unit := do
  profileLedger.comment s!"== {st.name} : {st.note}"
  for i in [0:howMany] do
    -- align to grid position 0 so short grids still display
    let sd := (st.seed0 / cellsPerBase + i) * cellsPerBase
    match st.gen sd st.size with
    | none => profileLedger.comment s!"  seed {sd}: (no cell)"
    | some c =>
      let sf := String.intercalate " ⋄ " (c.seeds.map reprStr)
      let dr := String.intercalate " ⋄ " (c.dropped.map reprStr)
      let gt := (firstFailure gates c).getD "ok"
      profileLedger.comment s!"  seed={sd} sf={sf} D={reprStr c.body} |S|={c.Sl.length} \
d={c.defect} J={c.J} room={c.room} b={c.b} fs={c.fs} ft={c.ft} lg={c.liveGates} \
drop={dr} gate={gt}"

def showAll (howMany : Nat) : IO Unit := do
  for st in allStrata do
    showStratum st howMany

end Frontier
end PLLND
