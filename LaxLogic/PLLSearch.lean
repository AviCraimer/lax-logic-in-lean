import LaxLogic.PLLCountermodelEmit

/-!
# `PLLND.Search` — a sound-both-ways, incomplete decision aid for PLL sequents

## Reading order

1. **`LaxLogic/PLLSearch.lean`** (this file) — the specification: what the
   staged procedure does, what is verified, what it costs.
2. **`LaxLogic/PLLSearchCmd.lean`** — the `#search` / `#refute` /
   `#refuteConf` commands.  Start here if you only want to *ask* about a
   sequent; they print the verdict, the evidence and a paste-ready theorem.
3. **`LaxLogic/PLLSearchEx.lean`** — worked examples: the thirteen Hilbert
   axioms run through the API, and the extraction lemma.
4. **`LaxLogic/PLLSearchConf.lean`** — the PCLL half (`ConfluentU.DerivU`):
   confluence-filtered refutation and its certificate theorem.
5. **`LaxLogic/PLLG4Term.lean`** — the engine: proof terms for G4iLL″ and the
   fuel-free (optionally budgeted) backward searcher.
6. `docs/search-manual.md` — the same material for a logician who knows PLL
   but not this codebase.

## What this module is

It packages a single entry point, `PLLND.Search.settle` (called `decide`
until the rename; `decide` survives as an alias), that attempts to settle a
propositional lax logic (PLL) sequent `Γ ⊢ C` **either way**: it looks for a
proof and, in parallel, for a finite countermodel.  Every non-`unknown`
verdict carries a *kernel-checkable certificate*:

* a `.proved` verdict carries a proof term `G4cTm Γ C` of the terminating,
  contraction-free calculus G4iLL″ — Lean's typechecker validates it, so
  correctness is the type system's job, not the search code's;
* a `.refuted` verdict carries a finite constraint model `M`, a world `w`,
  and a proof `FinCM.checkB M w Γ C = true` produced by the **verified**
  countermodel checker (`PLLCountermodelEmit.lean`).  The certificate
  theorem `FinCM.not_provable_of_check` upgrades it to a machine-checked
  `¬ Nonempty (LaxND Γ C)`;
* `.unknown` is explicit: it means only that the bounded stages below found
  nothing.  It never asserts anything about `Γ ⊢ C`.  `settleWhy` returns
  the richer `Verdict`, whose `.unknown` carries a `Reason` naming which
  bound bit (budget, closure cap, or "all stages ran and missed").

The intended use is as a *tool* in the tools-vs-proofs discipline: the
search itself may be fallible, but its accepted outputs are verified, so a
wrong internal guess can only degrade a verdict to `.unknown` — never
produce a false `.proved` or `.refuted`.

## How to use

Shortest route: the commands of `PLLSearchCmd.lean`, which print the
verdict, the evidence, and a paste-ready pinned theorem.

```
import LaxLogic.PLLSearchCmd
open PLLFormula PLLND PLLND.Search

#search [] ⊢ (prop "p").ifThen ((prop "p").somehow)
#refute [] ⊢ ((prop "p").somehow).ifThen (prop "p")
```

As functions there are two argument orders.  The *sequent-first* wrappers
(§10) default the configuration, and default it to `budgetedConfig` (node
budget on):

```
#eval (verdict [] someSequent).summary          -- one line
#eval (verdictWhy [] someSequent).summary       -- one line, with the reason
#eval (countermodel [] someSequent).map (·.render)
#eval (proof [] someSequent).map (·.pretty)
#eval (verdict Γ C (cfg := { findBudget := none })).summary   -- budget off
```

The *configuration-first* primitives keep the original signatures, so
`settle {} Γ C` (and its alias `decide {} Γ C`) behave exactly as `decide`
always did — in particular with **no** node budget:

```
open PLLND PLLND.Search

#eval (match settle {} [] (((PLLFormula.prop "p").somehow).ifThen (.prop "p")) with
        | .proved _      => "provable"
        | .refuted _ _ _ => "refuted by a finite countermodel"
        | .unknown       => "unknown")

-- Extract the kernel-checked underivability theorem from a refutation:
example : ¬ Nonempty (LaxND [] (((PLLFormula.prop "p").somehow).ifThen (.prop "p"))) :=
  match h : settle {} [] (((PLLFormula.prop "p").somehow).ifThen (.prop "p")) with
  | .refuted _ _ hc => refuted_sound hc
  | _               => by simp_all  -- (does not arise for this sequent)
```

Pass a custom `Config` to widen or narrow the search — most usefully to
supply extra frames for the countermodel battery:

```
-- A five-world chain added to the default battery.
def myCfg : Config :=
  { frames := ⟨5, [(0,1),(1,2),(2,3),(3,4),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)],
                  [(0,1)], [4]⟩ :: defaultFrames }
#eval (settle myCfg [] someSequent).toDecision
```

Cap the positive stage with a node budget when probing sequents that may
grind (unprovable but missed by the battery):

```
#eval (settle {findBudget := some 200000} Γ C).toDecision  -- fast, honest
#eval prove?Bounded 200000 Γ C                             -- positive engine only
```

## Cost profile

* **Successes are cheap.**  A true sequent is closed by the fuel-free
  backward searcher `G4cTm.find`, and a false sequent with a small
  countermodel is caught by the frame battery; both are observed to return
  effectively instantly, even at large formula weight.
* **The worst case is exponential.**  `G4cTm.find` is backward proof search
  over a terminating calculus, so it *always* halts, but no polynomial
  bound exists: provability is already PSPACE-hard for the `◯`-free
  intuitionistic fragment.  A false sequent that escapes the battery forces
  `find` to grind through its (finite, exponential) search space before
  failing.
* **Measured node counts** (nodes visited by `find`, i.e.
  `budget - remaining` from `G4cTm.findBounded`; re-measured on this tree,
  2026-07-27):

  | sequent | nodes | outcome |
  |---|---:|---|
  | `⊢ p ⊃ ◯p` | 3 | proved |
  | `⊢ ◯◯p ⊃ ◯p` | 7 | proved |
  | `⊢ (p ⊃ q ⊃ r) ⊃ (p ⊃ q) ⊃ p ⊃ r` | 8 | proved |
  | `⊢ ((p ⊃ q) ⊃ p) ⊃ p` (Peirce) | 8 | exhausted |
  | `⊢ (p ∧ ◯q) ⊃ ◯(p ∧ q)` | 18 | proved |
  | `◯((◯p ⊃ r) ⊃ ◯p), ◯p ⊃ r ⊢ r` (the gap sequent) | 136 | proved |

  The gap sequent used to cost 825 nodes; the order-canonical loop key and
  the failure memo have landed since, and the figure is now **136**.

* **How the grind grows.**  Three families of underivable sequents against
  an unreachable atom `z`, measured the same way (times are elapsed
  interpreter time on this machine, so read the ratios, not the absolutes):

  | family | k=1 | k=2 | k=3 | k=4 | k=5 | k=6 |
  |---|---:|---:|---:|---:|---:|---:|
  | A: `◯aᵢ ⊃ b` (k of them) with `◯cᵢ` (k of them) | 11 | 109 | 637 | 2801 | 10411 | 34693 |
  | B: chained `◯aᵢ ⊃ ◯aᵢ₊₁` with `◯a₀` | 34 | 596 | 7125 | 67608 | 544671 | >3·10⁶ |
  | C: `(pᵢ ⊃ q) ⊃ pᵢ` (Peirce shapes) | 7 | 49 | 277 | 1345 | 5921 | 24409 |

  Family B is the "◯-implication pool" the previous version of this header
  quoted at 7,256 nodes for k=3; the current figure is **7,125**.  Growth is
  about ×9 per premise for B, ×3.3 for A, ×4.2 for C.  Family B takes 26 s
  at k=5 and over three minutes at k=6 — so the multi-minute thrashes start
  at *six* chained premises, not the "~25" the old header claimed.

* **The grind is cappable.**  `Config.findBudget := some b` runs the
  positive stage under a global budget of `b` visited sequents
  (`G4cTm.findBounded`); exhaustion degrades the stage to `.unknown`.  The
  budget is shared across the whole search tree — a failed branch hands its
  remainder to the next alternative — so it bounds total work, not just
  depth.  Node throughput on the families above is 7,000–21,000 nodes per
  second (it falls as contexts grow), so `defaultFindBudget = 200000`, the
  budget the sequent-first wrappers and the commands use, bounds a grinding
  search at roughly 10–30 seconds.  Lower it for sweeps.
* **The battery is incomplete by design.**  It enumerates hereditary atom
  decorations of a fixed list of small frames (≤ 4 worlds by default) and
  stops any frame whose decoration count exceeds `comboCap`.  It is a
  cheap first filter, not a complete refuter.
* **`emit` is complete over the subformula closure, but exponential**, so
  it is gated by `emitClosureCap`: it is tried only when the closure is
  small enough to be affordable.

## Trust

Verified (kernel-checked):

* `FinCM.checkB` and the certificate theorem `FinCM.not_provable_of_check`
  — a `.refuted` answer's model genuinely refutes the sequent;
* the proof-term soundness chain `G4cTm.toG4c` ▸ `G4c.equiv_nd` — a
  `.proved` answer's term genuinely witnesses `Nonempty (LaxND Γ C)`.

Untrusted, but harmless:

* the fast vector scan `forceV` and the decoration enumeration.  They only
  ever *propose* candidate countermodels; every candidate must clear the
  verified `FinCM.checkB` before it is returned, so the scan can cause
  **misses**, never a wrong certificate;
* `G4cTm.find` returning `none` proves *nothing* — it is not a completeness
  oracle, only a (fuel-free, loop-checked) searcher.  Likewise
  `G4cTm.findBounded`: a budget cutoff (`(none, 0)`) is a mere truncation,
  and even its search-space-exhausted `none` (budget remaining) proves
  nothing more than `find`'s.

No component uses `native_decide`; the certificates reduce in the kernel.
-/

open PLLFormula

namespace PLLND.Search

/-! ## 0. Normalisation (optional PLL-equivalence preprocessing)

The rewrites below are all PLL equivalences — Heyting `⊥`/`⊤` laws together
with `◯⊤ ≡ ⊤` and `◯◯ ≡ ◯` — so they are valid on every constraint model: a
model refutes the normalised form iff it refutes the original, and
provability transfers both ways.  Their *only* role here is to shrink
formulas before the untrusted stages (the vector scan and `emit`).  Every
certificate is re-checked against the **original** `Γ`, `C`, so this
preprocessing can never be load-bearing for soundness. -/

/-- Is this literally `⊤` (i.e. `⊥ → ⊥`)? -/
def isTop : PLLFormula → Bool
  | .ifThen .falsePLL .falsePLL => true
  | _ => false

/-- One layer of PLL-equivalence simplification at the root of a formula. -/
def smash : PLLFormula → PLLFormula
  | .and A B =>
      if A == .falsePLL || B == .falsePLL then .falsePLL
      else if isTop A then B else if isTop B then A
      else if A == B then A
      else .and A B
  | .or A B =>
      if isTop A || isTop B then truePLL
      else if A == .falsePLL then B else if B == .falsePLL then A
      else if A == B then A
      else .or A B
  | .ifThen A B =>
      if A == .falsePLL || isTop B then truePLL
      else if isTop A then B
      else if A == B then truePLL
      else .ifThen A B
  | .somehow A =>
      if isTop A then truePLL
      else match A with
        | .somehow B => .somehow B
        | _ => .somehow A
  | F => F

/-- Recursive normaliser: `smash` applied bottom-up.  A PLL equivalence. -/
def nf : PLLFormula → PLLFormula
  | .and A B    => smash (.and (nf A) (nf B))
  | .or A B     => smash (.or (nf A) (nf B))
  | .ifThen A B => smash (.ifThen (nf A) (nf B))
  | .somehow A  => smash (.somehow (nf A))
  | F => F

/-! ## 1. Frames and the countermodel battery -/

/-- A finite intuitionistic-with-fallibility frame, as raw data.  Worlds are
`0, …, n-1`; `ri` lists the *strict* intuitionistic order (assumed
transitively closed, reflexivity added on use); `rm ⊆ ri` is the constraint
relation; `fall` lists the fallible worlds (which force everything). -/
structure Frame where
  /-- Number of worlds; the carrier is `{0, …, n-1}`. -/
  n : Nat
  /-- Strict part of the intuitionistic order `Rᵢ`, transitively closed. -/
  ri : List (Nat × Nat)
  /-- The constraint relation `Rₘ`, a subset of `ri`. -/
  rm : List (Nat × Nat)
  /-- The fallible worlds (they force every formula, `⊥` included). -/
  fall : List Nat

/-- The default battery: ten small frames — the generic shapes that refute
most non-theorems of PLL.  Reading the list: (1) the classical point;
(2) the fallible point; (3) a two-world chain with `Rₘ = Rᵢ`; (4) the same
chain with `Rₘ` empty (a *rigid* modal step); (5) the chain with no
fallible top; (6) a three-world chain, rigid except for the middle step;
(7) the full three-world chain; (8) a four-world fork; (9) a three-world
`V`/branch; (10) a doubled two-world chain.  They are deliberately small
(≤ 4 worlds) and cheap to decorate; a caller who needs more can prepend
their own to `Config.frames`. -/
def defaultFrames : List Frame :=
  [ ⟨1, [], [], []⟩
  , ⟨1, [], [], [0]⟩
  , ⟨2, [(0,1)], [(0,1)], [1]⟩
  , ⟨2, [(0,1)], [], [1]⟩
  , ⟨2, [(0,1)], [(0,1)], []⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [2]⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [(0,1),(1,2),(0,2)], [2]⟩
  , ⟨4, [(0,1),(0,2),(2,3),(0,3)], [(2,3)], [3]⟩
  , ⟨3, [(0,1),(0,2)], [(0,2)], [2]⟩
  , ⟨4, [(0,1),(0,2),(0,3),(1,3),(2,3)], [(1,3),(2,3)], [3]⟩
  -- 4-chain, Rₘ rigid except 2→3, top fallible: the frame that
  -- refutes ¬¬◯⊥-level premises against Peirce-shaped goals
  -- (added 2026-07-19 after it certified the frontier row
  -- ((p⊃◯⊥)⊃p)⊃p; the earlier battery missed that family).
  , ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(2,3)], [3]⟩ ]

/-- Strict `Rᵢ`-edge test on a `Frame`. -/
def riStep (f : Frame) (w v : Nat) : Bool := decide ((w, v) ∈ f.ri)

/-! ## 2. Search configuration -/

/-- Tuning parameters for `decide`.  All fields default, so `({} : Config)`
gives the standard search. -/
structure Config where
  /-- Frames used by the countermodel battery.  Defaults to `defaultFrames`;
  prepend your own frames (as extra shapes) to search a wider space. -/
  frames : List Frame := defaultFrames
  /-- Skip a battery frame when its number of admissible decorations, raised
  to the number of atoms, exceeds this cap.  Guards the enumeration against
  combinatorial blow-up on atom-rich sequents. -/
  comboCap : Nat := 200000
  /-- Skip the (complete-over-the-closure but exponential) `emit` stage when
  the subformula closure of the sequent is larger than this. -/
  emitClosureCap : Nat := 12
  /-- Node budget for the positive stage.  `none` (the default) runs the
  fuel-free `G4cTm.find` unchanged; `some b` caps the searcher at `b` visited
  sequents (`G4cTm.findBounded`), so a sequent whose search space is too big
  degrades to `.unknown` instead of grinding.  Budget exhaustion is never
  evidence of underivability.

  Note the deliberate asymmetry with the *sequent-first* wrappers of §11
  (`verdict`, `countermodel`, `proof`) and the `#search`/`#refute` commands:
  those default to `budgetedConfig`, which sets `findBudget := some
  defaultFindBudget`.  This field's own default stays `none` so that every
  existing caller of `decide {} …` / `settle {} …` keeps exactly the
  behaviour it had. -/
  findBudget : Option Nat := none
  /-- Extra acceptance test on a *candidate* countermodel, applied before the
  verified `FinCM.checkB` gate in both refutation stages.  The default accepts
  everything; `PLLSearchConf.lean` sets it to `RNC.confB` to keep only
  mutually confluent models, which is what a PCLL refutation needs.

  Untrusted like the rest of the proposer: narrowing it can only cause
  misses, never a wrong certificate. -/
  accept : FinCM → Bool := fun _ => true
  /-- Run a countermodel through `CounterEmit.simplify` before returning it
  (the default).  Both refutation stages propose models that are larger than
  the refutation needs — the battery decorates a fixed frame, and the closure
  emitter builds one world per prime closed subset of the closure, so twenty
  worlds for a two-atom sequent is routine.  Simplification deletes worlds,
  edges, valuation pairs and fallible flags for as long as the *verified*
  `FinCM.checkB` keeps certifying the result, so what comes back is the same
  refutation with nothing in it that the refutation does not use.

  The cost is a few hundred `checkB` calls on models this size, under a
  millisecond; set it to `false` if you want the raw proposal (to see what a
  stage actually produced) rather than the presentable one.

  Simplification is gated by `accept` as well as by `checkB`, so a
  confluence-filtered search (`RNC.refuteConf?`) stays confluent. -/
  simplify : Bool := true

/-- The standard configuration (all defaults). -/
def Config.default : Config := {}

/-- The default node budget used by the *sequent-first* wrappers of §11 and
by the `#search` / `#refute` commands — comfortably above every sequent in
the cost table of the module header, so it costs a verdict only on searches
that were going to grind. -/
def defaultFindBudget : Nat := 200000

/-- The configuration used by the sequent-first wrappers and the
`#search` / `#refute` commands: the standard search with the node budget
**on** at `defaultFindBudget`.  Pass `{ findBudget := none }` (or
`Config.default`) to turn the budget off again. -/
def budgetedConfig : Config := { findBudget := some defaultFindBudget }

instance : Inhabited Config := ⟨{}⟩

/-! ## 3. Fast untrusted evaluation: bottom-up world vectors

`FinCM.forceB` (the verified checker's forcing function) recomputes each
subformula once per visited world, so its cost is `n^depth` — prohibitive on
heavy formulas.  `forceV` instead evaluates each subformula *once* as a
Boolean vector over all worlds (total cost `weight × n²`).  It is untrusted:
the vectors are only used to *pick candidates*, which are then re-validated
by the verified `FinCM.checkB`. -/

/-- Reflexive `Rᵢ` test on a `FinCM`. -/
def riR (M : FinCM) (w v : Nat) : Bool :=
  decide ((w, v) ∈ M.ri) || decide (w = v)

/-- Reflexive `Rₘ` test on a `FinCM`. -/
def rmR (M : FinCM) (w v : Nat) : Bool :=
  decide ((w, v) ∈ M.rm) || decide (w = v)

/-- Forcing as a world-indexed Boolean vector.  Each entry `w` says whether
world `w` forces the formula; fallible worlds force everything.  This mirrors
`FinCM.forceB` but computes each subformula once. -/
def forceV (M : FinCM) : PLLFormula → Array Bool
  | .prop a => (Array.range M.n).map fun w =>
      decide ((w, a) ∈ M.val) || decide (w ∈ M.fall)
  | .falsePLL => (Array.range M.n).map fun w => decide (w ∈ M.fall)
  | .and A B =>
      let vA := forceV M A; let vB := forceV M B
      (Array.range M.n).map fun w => vA.getD w false && vB.getD w false
  | .or A B =>
      let vA := forceV M A; let vB := forceV M B
      (Array.range M.n).map fun w => vA.getD w false || vB.getD w false
  | .ifThen A B =>
      let vA := forceV M A; let vB := forceV M B
      (Array.range M.n).map fun w =>
        (List.range M.n).all fun v =>
          !(riR M w v) || !(vA.getD v false) || vB.getD v false
  | .somehow A =>
      let vA := forceV M A
      (Array.range M.n).map fun w =>
        (List.range M.n).all fun v =>
          !(riR M w v) ||
            (List.range M.n).any fun u => rmR M v u && vA.getD u false

/-! ## 4. Hereditary decorations of a frame

An atom's truth-set must be *hereditary* along `Rᵢ` (upward closed) and must
contain every fallible world.  We enumerate such truth-sets as `n`-bit masks,
then form all assignments of masks to the sequent's atoms. -/

/-- The admissible truth-sets of a frame, as bitmasks: hereditary along `ri`
and containing every fallible world. -/
def admissible (f : Frame) : List Nat :=
  (List.range (2 ^ f.n)).filter fun m =>
    ((List.range f.n).all fun w =>
      !(m.testBit w) ||
        (List.range f.n).all fun v => !(riStep f w v) || m.testBit v) &&
    (f.fall.all fun w => m.testBit w)

/-- All assignments of admissible masks to a list of atoms. -/
def assigns : List String → List Nat → List (List (String × Nat))
  | [], _ => [[]]
  | a :: as, adm =>
      (assigns as adm).flatMap fun rest => adm.map fun m => (a, m) :: rest

/-- Turn a frame together with a mask assignment into a concrete `FinCM`. -/
def toFinCM (f : Frame) (asgn : List (String × Nat)) : FinCM :=
  { n := f.n, ri := f.ri, rm := f.rm, fall := f.fall
    val := asgn.flatMap fun am =>
      (List.range f.n).filterMap fun w =>
        if am.2.testBit w then some (w, am.1) else none }

/-- The atoms occurring in a formula. -/
def atomList : PLLFormula → List String
  | .prop a => [a]
  | .falsePLL => []
  | .and A B | .or A B | .ifThen A B => atomList A ++ atomList B
  | .somehow A => atomList A

/-- The distinct atoms occurring in a list of formulas. -/
def atomsOf (l : List PLLFormula) : List String :=
  (l.flatMap atomList).eraseDups

/-! ## 5. The certified battery sweep

`sweepCert` scans the battery of frames, decorated over the sequent's atoms,
using the fast vector evaluator on the (normalised) formulas `Γ'`, `C'`.
Every scan hit is confirmed through a **dependent** application of the
verified `FinCM.checkB` **on the original** `Γ`, `C`, so the returned witness
carries a genuine proof `FinCM.checkB M w Γ C = true`.  A wrong scan can only
fail the gate and be skipped. -/

/-- A certified countermodel witness: a finite model `M`, a world `w`, and a
proof that the verified checker accepts it for the original sequent. -/
abbrev Witness (Γ : List PLLFormula) (C : PLLFormula) : Type :=
  (M : FinCM) × (w : Nat) ×' (FinCM.checkB M w Γ C = true)

/-- **Simplify a witness**: run `CounterEmit.simplify` on its model and
re-derive the certificate for the smaller one.

The simplifier is untrusted, so the result is not assumed to check: the
proof `h` is obtained afresh by a dependent `if`, and a model that
somehow failed to check would leave the original witness untouched.  A
simplified witness is therefore exactly as trustworthy as an unsimplified
one — the certificate is a fact about the model that is returned.

`accept` is threaded into the simplifier (see `CounterEmit.minimise`), so
a search that is filtering candidates by some property keeps it. -/
def Witness.simplify {Γ : List PLLFormula} {C : PLLFormula}
    (accept : FinCM → Bool := fun _ => true) (wit : Witness Γ C) :
    Witness Γ C :=
  let (M, w) := CounterEmit.simplify wit.1 wit.2.1 Γ C accept
  if h : FinCM.checkB M w Γ C = true then ⟨M, w, h⟩ else wit

/-- `Witness.simplify` under a `Config`: a no-op when `cfg.simplify` is
`false`. -/
def simplifyWith {Γ : List PLLFormula} {C : PLLFormula} (cfg : Config)
    (wit : Witness Γ C) : Witness Γ C :=
  if cfg.simplify then wit.simplify cfg.accept else wit

/-- Scan the battery for a certified countermodel.  Candidates are picked by
the fast scan on the normalised forms `Γ'`, `C'`, filtered by `cfg.accept`
(the identity filter by default); each candidate is gated by the verified
checker on the **original** `Γ`, `C`. -/
def sweepCert (cfg : Config)
    (Γ' : List PLLFormula) (C' : PLLFormula)
    (Γ : List PLLFormula) (C : PLLFormula) : Option (Witness Γ C) :=
  let ats := atomsOf (C' :: Γ')
  cfg.frames.findSome? fun f =>
    let adm := admissible f
    if adm.length ^ ats.length > cfg.comboCap then none
    else
      (assigns ats adm).findSome? fun asgn =>
        let M := toFinCM f asgn
        if !(cfg.accept M) then none else
        let vΓ := Γ'.map (forceV M)
        let vC := forceV M C'
        (List.range f.n).findSome? fun w =>
          if vΓ.all (fun v => v.getD w false) && !(vC.getD w false) then
            if h : FinCM.checkB M w Γ C = true then some ⟨M, w, h⟩ else none
          else none

/-! ## 6. The certified `emit` stage

`CounterEmit.emit` proposes a countermodel from the subformula closure (it is
complete over that closure, but exponential).  Run on the normalised forms
and re-gated on the original sequent. -/

/-- Run the closure-based emitter on `Γ'`, `C'`; gate any proposal through the
verified checker on the original `Γ`, `C`, returning a certified witness.

The trailing `accept` argument is the same untrusted pre-filter as
`Config.accept`; it defaults to the identity filter, so every existing call
site keeps its behaviour.  `budget` and `precheck` control the proof search
`emit` runs first (see `CounterEmit.emit`): `budget` is `Config.findBudget`
at both call sites here, so a `#refute` that reaches this stage is bounded
like a `#search`, and `settleWhy` passes `precheck := false` because its own
positive stage has just searched the same sequent to exhaustion. -/
def emitCert (Γ' : List PLLFormula) (C' : PLLFormula)
    (Γ : List PLLFormula) (C : PLLFormula)
    (accept : FinCM → Bool := fun _ => true)
    (budget : Option Nat := none) (precheck : Bool := true) :
    Option (Witness Γ C) :=
  match CounterEmit.emit Γ' C' budget precheck with
  | some (M, w) =>
      if !(accept M) then none
      else if h : FinCM.checkB M w Γ C = true then some ⟨M, w, h⟩ else none
  | none => none

/-! ## 7. The answer type and the decision procedure -/

/-- The result of a search, carrying its certificate.

* `proved t`      — `t : G4cTm Γ C` is a proof term of G4iLL″;
* `refuted M w h`  — `h` proves the verified checker accepts model `M` at
  world `w` as a countermodel to `Γ ⊢ C`;
* `unknown`        — the bounded stages found nothing; asserts nothing. -/
inductive Answer (Γ : List PLLFormula) (C : PLLFormula) where
  | proved  : G4cTm Γ C → Answer Γ C
  | refuted : (M : FinCM) → (w : Nat) → FinCM.checkB M w Γ C = true → Answer Γ C
  | unknown : Answer Γ C

/-! ### Why an answer was `unknown`

`Answer.unknown` says nothing about *which* bound bit, which is exactly the
information a user needs in order to know which knob to turn.  Rather than
give `Answer.unknown` an argument — which would break every existing
`match … | .unknown => …` in the probe files — the reason lives on a second,
richer result type, `Verdict`, of which `Answer` is the forgetful view. -/

/-- Why a search returned no verdict.  Each constructor names the knob. -/
inductive Reason where
  /-- The positive stage was truncated by `Config.findBudget` (the recorded
  `Nat` is the budget that ran out).  Raise `findBudget`, or set it to
  `none`; the search space was *not* exhausted, so nothing at all is known. -/
  | budgetExhausted (budget : Nat)
  /-- The `emit` stage was skipped because the subformula closure (first
  `Nat`) exceeded `Config.emitClosureCap` (second `Nat`).  Raise
  `emitClosureCap` if you are prepared to pay for the exponential stage. -/
  | closureTooBig (size cap : Nat)
  /-- Every stage ran to completion and none produced a certificate: the
  frame battery found no countermodel, the (search-space-exhausted) proof
  search found no proof, and the emitter proposed nothing that cleared
  `checkB`.  Widen `Config.frames`, or `Config.comboCap`. -/
  | allStagesMissed
  deriving Repr, DecidableEq, Inhabited

/-- A human-readable reading of a `Reason`, naming the knob to turn. -/
def Reason.describe : Reason → String
  | .budgetExhausted b =>
      s!"positive stage truncated: the node budget of {b} ran out \
(raise Config.findBudget, or set it to none)"
  | .closureTooBig size cap =>
      s!"emit stage skipped: subformula closure has {size} formulas, \
cap is {cap} (raise Config.emitClosureCap)"
  | .allStagesMissed =>
      "all stages ran and missed: no battery countermodel, no proof, \
no emitted countermodel (widen Config.frames or Config.comboCap)"

/-- The result of a search, carrying its certificate **and**, when there is
no verdict, the reason.  `Answer` is `Verdict` with the reason forgotten. -/
inductive Verdict (Γ : List PLLFormula) (C : PLLFormula) where
  /-- `t : G4cTm Γ C` is a proof term of G4iLL″. -/
  | proved  : G4cTm Γ C → Verdict Γ C
  /-- `h` proves the verified checker accepts `M` at `w`. -/
  | refuted : (M : FinCM) → (w : Nat) → FinCM.checkB M w Γ C = true → Verdict Γ C
  /-- No certificate; the `Reason` says which bound bit. -/
  | unknown : Reason → Verdict Γ C

/-- Forget the reason: the backward-compatible `Answer` view of a verdict. -/
def Verdict.toAnswer {Γ : List PLLFormula} {C : PLLFormula} :
    Verdict Γ C → Answer Γ C
  | .proved t      => .proved t
  | .refuted M w h => .refuted M w h
  | .unknown _     => .unknown

/-- The reason, when there is no verdict. -/
def Verdict.reason? {Γ : List PLLFormula} {C : PLLFormula} :
    Verdict Γ C → Option Reason
  | .unknown r => some r
  | _          => none

/-- **The staged decision procedure, with reasons.**  In order:

1. the certified battery sweep (`sweepCert`) — a cheap certified refutation;
2. the fuel-free backward searcher `G4cTm.find` on the **original** sequent —
   the positive engine, returning a kernel-checkable proof term for `Γ ⊢ C`
   (capped at `cfg.findBudget` visited nodes when that is set, via
   `G4cTm.findBounded`; exhaustion degrades this stage to a failed search,
   never to a negative verdict);
3. the closure emitter `emitCert`, gated by `emitClosureCap` — a
   complete-over-the-closure but exponential refuter;
4. `unknown`.

The normaliser feeds only stages 1 and 3 (the untrusted proposers); the
proof term from stage 2 and both refutation certificates are about the
original `Γ`, `C`.

The budget cutoff is told apart from a genuine search-space exhaustion by
the remainder returned by `G4cTm.findBounded`: remainder `0` is a cutoff. -/
def settleWhy (cfg : Config := {}) (Γ : List PLLFormula) (C : PLLFormula) :
    Verdict Γ C :=
  let Γ' := Γ.map nf
  let C' := nf C
  match (sweepCert cfg Γ' C' Γ C).map (simplifyWith cfg) with
  | some ⟨M, w, h⟩ => .refuted M w h
  | none =>
    let (res, cutoff) :=
      match cfg.findBudget with
      | none => (G4cTm.find Γ C, none)
      | some b =>
        let (r, rem) := G4cTm.findBounded b Γ C
        (r, if r.isNone && rem == 0 then some b else none)
    match res with
    | some t => .proved t
    | none =>
      let cloLen := (CounterEmit.closureOf Γ' C').length
      if cloLen ≤ cfg.emitClosureCap then
        -- `cutoff = none` means stage 2 exhausted the search space without
        -- finding a proof, so the emitter's own provability pre-check would
        -- repeat that work to the same end: skip it.  After a cutoff the
        -- pre-check is kept (the normalised sequent may be small enough to
        -- settle within the same budget) and the budget goes with it.
        match (emitCert Γ' C' Γ C cfg.accept cfg.findBudget
                cutoff.isSome).map (simplifyWith cfg) with
        | some ⟨M, w, h⟩ => .refuted M w h
        | none =>
          match cutoff with
          | some b => .unknown (.budgetExhausted b)
          | none   => .unknown .allStagesMissed
      else
        match cutoff with
        | some b => .unknown (.budgetExhausted b)
        | none   => .unknown (.closureTooBig cloLen cfg.emitClosureCap)

/-- **The staged decision procedure** (`settleWhy` with the reason
forgotten).  This is the two-sided entry point; it was called `decide` until
the rename, and `decide` remains as an alias below.

The stages, in order: the certified battery sweep, the (optionally
budgeted) backward searcher `G4cTm.find`, the closure emitter gated by
`emitClosureCap`, then `unknown`. -/
def settle (cfg : Config := {}) (Γ : List PLLFormula) (C : PLLFormula) :
    Answer Γ C :=
  (settleWhy cfg Γ C).toAnswer

/-- Compatibility alias for `settle`, under the name this entry point had
before the rename.

Kept as a plain definition rather than `@[deprecated]` on purpose: the name
is used at several dozen call sites across `wip/`, and a deprecation warning
at each of them would drown the build log.  New code should say `settle`
(or, better, the sequent-first `verdict` of §11): `PLLND.Search.decide`
shadows `Decidable.decide` under `open PLLND.Search`, which is exactly what
the rename fixes. -/
def decide (cfg : Config := {}) (Γ : List PLLFormula) (C : PLLFormula) :
    Answer Γ C :=
  settle cfg Γ C

/-! ## 8. Soundness — turning certificates into theorems

These are the two lemmas that make the interface trustworthy.  Each consumes
exactly the certificate that the corresponding `Answer` constructor carries,
so a user goes from a verdict to the corresponding (un)derivability theorem in
one application. -/

/-- A `.proved` certificate yields a natural-deduction derivation.  The chain
is `G4cTm.toG4c` (proof term ⇒ G4c derivation) followed by `G4c.equiv_nd`
(G4c = PLL natural deduction). -/
theorem proved_sound {Γ : List PLLFormula} {C : PLLFormula} (t : G4cTm Γ C) :
    Nonempty (LaxND Γ C) :=
  G4c.equiv_nd.mp t.toG4c

/-- A `.refuted` certificate yields underivability, by the certificate theorem
`FinCM.not_provable_of_check` (Kripke soundness of natural deduction). -/
theorem refuted_sound {Γ : List PLLFormula} {C : PLLFormula}
    {M : FinCM} {w : Nat} (h : FinCM.checkB M w Γ C = true) :
    ¬ Nonempty (LaxND Γ C) :=
  FinCM.not_provable_of_check h

/-- A certified verdict: the derivability status of `Γ ⊢ C` together with a
proof of it (or `dontKnow`). -/
inductive Decision (Γ : List PLLFormula) (C : PLLFormula) where
  | derivable   : Nonempty (LaxND Γ C) → Decision Γ C
  | underivable : ¬ Nonempty (LaxND Γ C) → Decision Γ C
  | dontKnow    : Decision Γ C

/-- Discharge an `Answer` into a certified `Decision` in one call. -/
def Answer.toDecision {Γ : List PLLFormula} {C : PLLFormula} :
    Answer Γ C → Decision Γ C
  | .proved t      => .derivable (proved_sound t)
  | .refuted _ _ h => .underivable (refuted_sound h)
  | .unknown       => .dontKnow

/-- Discharge a `Verdict` into a certified `Decision` in one call.  The
reason is dropped: a `Decision` is about the sequent, a `Reason` about the
search. -/
def Verdict.toDecision {Γ : List PLLFormula} {C : PLLFormula} :
    Verdict Γ C → Decision Γ C
  | .proved t      => .derivable (proved_sound t)
  | .refuted _ _ h => .underivable (refuted_sound h)
  | .unknown _     => .dontKnow

/-! ## 9. Convenience wrappers -/

/-- Positive engine only: the fuel-free backward searcher for `Γ ⊢ C`,
returning a proof term.  `none` proves nothing (see the trust note above). -/
def prove? (Γ : List PLLFormula) (C : PLLFormula) : Option (G4cTm Γ C) :=
  G4cTm.find Γ C

/-- Positive engine with a **node budget**: `G4cTm.findBounded` capped at
`budget` visited sequents.  A found term is kernel-checkable exactly as with
`prove?`; `none` means only "not settled within `budget` nodes" — an honest
unknown, never a negative verdict.  To tell a genuine search-space
exhaustion (the same `none` as `prove?`) from a budget cutoff, call
`G4cTm.findBounded` directly and inspect the remaining budget; the
difference `budget - remaining` also serves as a node-count profile for
tuning budgets. -/
def prove?Bounded (budget : Nat) (Γ : List PLLFormula) (C : PLLFormula) :
    Option (G4cTm Γ C) :=
  (G4cTm.findBounded budget Γ C).1

/-- Negative engines only (battery, then the closure emitter): a certified
countermodel witness, or `none`.

"No proof search" is true of this function but not of its second stage:
`CounterEmit.emit` runs a search of its own, to avoid building an
exponential model for a provable sequent.  `cfg.findBudget` is passed down
to cap it. -/
def refute? (cfg : Config := {}) (Γ : List PLLFormula) (C : PLLFormula) :
    Option (Witness Γ C) :=
  let Γ' := Γ.map nf
  let C' := nf C
  ((sweepCert cfg Γ' C' Γ C).orElse fun _ =>
    if (CounterEmit.closureOf Γ' C').length ≤ cfg.emitClosureCap then
      emitCert Γ' C' Γ C cfg.accept cfg.findBudget
    else none).map (simplifyWith cfg)

/-! ## 10. Sequent-first wrappers

The functions above take the configuration *first*, so a caller who wants
the defaults must still write `{}`.  The three wrappers here take `Γ` and
`C` first and default the configuration, so the common case is short:

```
#eval (verdict [] someSequent).summary
#eval (countermodel [] someSequent).map (·.render)
#eval (proof [] someSequent).map (·.pretty)
```

They default to `budgetedConfig`, **not** to `Config.default`: the node
budget is on (at `defaultFindBudget` = 200000 nodes), because the failure
mode a user actually hits is a run that never comes back.  To turn it off,
or to change anything else, pass the configuration by name:

```
#eval (verdict Γ C (cfg := { findBudget := none })).summary
#eval (verdict Γ C (cfg := { frames := myFrames :: defaultFrames })).summary
```

Nothing about the *existing* entry points changed: `decide {} Γ C` and
`settle {} Γ C` still run with `findBudget := none`, exactly as before. -/

/-- Sequent-first `settleWhy`: the two-sided procedure with reasons, with a
node budget on by default (`budgetedConfig`). -/
def verdictWhy (Γ : List PLLFormula) (C : PLLFormula)
    (cfg : Config := budgetedConfig) : Verdict Γ C :=
  settleWhy cfg Γ C

/-- Sequent-first `settle`: the two-sided procedure, with a node budget on by
default (`budgetedConfig`).  See §10 for the difference from `settle {} Γ C`. -/
def verdict (Γ : List PLLFormula) (C : PLLFormula)
    (cfg : Config := budgetedConfig) : Answer Γ C :=
  settle cfg Γ C

/-- Sequent-first `refute?`: the negative engines only (battery, then emit),
returning a certified countermodel witness. -/
def countermodel (Γ : List PLLFormula) (C : PLLFormula)
    (cfg : Config := budgetedConfig) : Option (Witness Γ C) :=
  refute? cfg Γ C

/-- Sequent-first positive engine, budgeted by default: `G4cTm.findBounded`
at `cfg.findBudget` nodes, or the fuel-free `G4cTm.find` when that is `none`.
`none` proves nothing (see the trust note in the module header). -/
def proof (Γ : List PLLFormula) (C : PLLFormula)
    (cfg : Config := budgetedConfig) : Option (G4cTm Γ C) :=
  match cfg.findBudget with
  | none   => G4cTm.find Γ C
  | some b => (G4cTm.findBounded b Γ C).1

/-! ## 11. Rendering: formulas as source, models compactly, and pinning
snippets

Everything in this section is presentation, entirely outside the trust
story.  Its point is to close the discover-then-pin loop: `Witness.snippet`
and `G4cTm.snippet` produce **paste-ready Lean source** for the theorem that
records what the search found, so the manual step of transcribing a `FinCM`
or a rule tree by hand disappears. -/

/-- A `PLLFormula` as Lean source that elaborates back to it.  Fully
qualified and fully parenthesised, so it can be pasted anywhere. -/
def srcOf : PLLFormula → String
  | .prop a      => s!"(PLLFormula.prop \"{a}\")"
  | .falsePLL    => "PLLFormula.falsePLL"
  | .and A B     => s!"({srcOf A}.and {srcOf B})"
  | .or A B      => s!"({srcOf A}.or {srcOf B})"
  | .ifThen A B  => s!"({srcOf A}.ifThen {srcOf B})"
  | .somehow A   => s!"({srcOf A}.somehow)"

/-- A hypothesis list as Lean source. -/
def srcOfCtx (Γ : List PLLFormula) : String :=
  "[" ++ String.intercalate ", " (Γ.map srcOf) ++ "]"

/-- A `FinCM` as Lean source (the anonymous-constructor form used in every
pinned countermodel in this repository). -/
def srcOfCM (M : FinCM) : String :=
  let pairs (l : List (Nat × Nat)) : String :=
    "[" ++ String.intercalate ", " (l.map fun p => s!"({p.1}, {p.2})") ++ "]"
  let nats (l : List Nat) : String :=
    "[" ++ String.intercalate ", " (l.map fun k => s!"{k}") ++ "]"
  let vals (l : List (Nat × String)) : String :=
    "[" ++ String.intercalate ", " (l.map fun p => s!"({p.1}, \"{p.2}\")") ++ "]"
  s!"⟨{M.n}, {pairs M.ri}, {pairs M.rm}, {nats M.fall}, {vals M.val}⟩"

/-! ### A compact text picture of a finite model

`repr` on a `FinCM` prints the raw structure, which for an emitted
twenty-world model runs to several screens of pair lists.  `renderCM` prints
one line per world: its `Rᵢ`-cover successors (the transitive reduction, so
the implied edges are not repeated), its `Rₘ` successors, and the atoms it
forces.  `LaxLogic/PLLDiagram.lean` draws the same information as a picture
(`Diagram.toTikz` / `Diagram.toSvg`, over the same transitive reduction
`Diagram.hasseRi`); the two are kept independent so that a user of the
search API need not import the figure machinery, which does file IO. -/

/-- Strict `Rᵢ`: below and not above. -/
private def strictRi' (M : FinCM) (i j : Nat) : Bool :=
  M.riB i j && !(M.riB j i)

/-- Cover (Hasse) edges of the strict part of `Rᵢ`, from world `i`. -/
private def coversFrom (M : FinCM) (i : Nat) : List Nat :=
  (List.range M.n).filter fun j =>
    strictRi' M i j &&
      !((List.range M.n).any fun k =>
          k != i && k != j && strictRi' M i k && strictRi' M k j)

/-- **Compact renderer for a finite constraint model.**  Header line, then
one line per world.  `w?` marks the refuting world.

```
3 worlds, refuting world 0; fallible {2}
  *w0  ⊑> {1}  ⊳ {1}  ⊩ p
   w1  ⊑> {2}  ⊳ {}   ⊩ p, q
   w2  ⊑> {}   ⊳ {}   ⊩ ⊥ (fallible)
```

`⊑>` lists the `Rᵢ`-**cover** successors (transitive reduction; reflexive
pairs suppressed), `⊳` the `Rₘ` successors, `⊩` the atoms forced; `*` marks
the refuting world.  A fallible world forces everything, so its atom list is
written `⊥`. -/
def renderCM (M : FinCM) (w? : Option Nat := none) : String :=
  let setOf (l : List Nat) : String :=
    "{" ++ String.intercalate "," (l.map fun k => s!"{k}") ++ "}"
  let idx := List.range M.n
  let head :=
    (if M.n == 1 then "1 world" else s!"{M.n} worlds") ++
    (match w? with | some w => s!", refuting world {w}" | none => "") ++
    (if M.fall.isEmpty then "" else s!"; fallible {setOf M.fall}")
  let covS := idx.map fun i => setOf (coversFrom M i)
  let rmS  := idx.map fun i =>
    setOf (idx.filter fun j => j != i && M.rmB i j)
  let padTo := fun (l : List String) => l.foldl (fun a s => max a s.length) 0
  let wCov := padTo covS
  let wRm := padTo rmS
  let pad (s : String) (k : Nat) : String :=
    s ++ String.ofList (List.replicate (k - s.length) ' ')
  let line (i : Nat) : String :=
    let ats :=
      if M.fall.contains i then "⊥ (fallible)"
      else
        let l := (M.val.filter fun p => p.1 == i).map (·.2)
        if l.isEmpty then "—" else String.intercalate ", " l
    let mark := if w? == some i then "*" else " "
    s!"  {mark}w{i}  ⊑> {pad (covS.getD i "{}") wCov}  \
⊳ {pad (rmS.getD i "{}") wRm}  ⊩ {ats}"
  String.intercalate "\n" (head :: idx.map line)

/-- A one-line summary of a model: worlds, refuting world, edge counts. -/
def summaryCM (M : FinCM) (w : Nat) : String :=
  (if M.n == 1 then "1 world" else s!"{M.n} worlds") ++
  s!", refuting world {w}, |Rᵢ| = {M.ri.length}, \
|Rₘ| = {M.rm.length}, fallible {M.fall.length}"

/-- The witness's model, rendered compactly by `renderCM`, with its refuting
world marked. -/
def Witness.render {Γ : List PLLFormula} {C : PLLFormula}
    (wit : Witness Γ C) : String :=
  renderCM wit.1 (some wit.2.1)

/-- One-line summary of the witness's model. -/
def Witness.summary {Γ : List PLLFormula} {C : PLLFormula}
    (wit : Witness Γ C) : String :=
  summaryCM wit.1 wit.2.1

/-! ### Pinning snippets -/

/-- The paste-ready underivability theorem certified by this witness: the
model copied into a `FinCM.not_provable_of_check` application, with the
`#print axioms` audit line.  Only `checkB` on concrete data remains, so the
`by decide` is a kernel evaluation and the search drops out entirely. -/
def Witness.snippet {Γ : List PLLFormula} {C : PLLFormula}
    (name : String := "underivable") (wit : Witness Γ C) : String :=
  let ⟨M, w, _⟩ := wit
  String.intercalate "\n"
    [ s!"theorem {name} :",
      s!"    ¬ Nonempty (LaxND {srcOfCtx Γ} {srcOf C}) :=",
      "  FinCM.not_provable_of_check",
      s!"    (M := {srcOfCM M}) (w := {w}) (by decide)",
      "",
      s!"#print axioms {name}" ]

/-- A proof term as the Lean source of the corresponding `G4cTm`
constructor tree.  The implicit formula arguments that the goal does *not*
determine — which hypothesis a left rule decomposes — are supplied by name,
so the term elaborates on its own; the side conditions are list memberships,
emitted as `(by decide)`. -/
def _root_.PLLND.G4cTm.src {Γ : List PLLFormula} {C : PLLFormula} :
    G4cTm Γ C → String
  | .init _              => "(.init (by decide))"
  | .botL _              => "(.botL (by decide))"
  | .andR a b            => s!"(.andR {a.src} {b.src})"
  | .orR1 a              => s!"(.orR1 {a.src})"
  | .orR2 a              => s!"(.orR2 {a.src})"
  | .impR a              => s!"(.impR {a.src})"
  | .laxR a              => s!"(.laxR {a.src})"
  | @G4cTm.laxL _ A _ _ a => s!"(.laxL (A := {srcOf A}) (by decide) {a.src})"
  | @G4cTm.andL _ A B _ _ a =>
      s!"(.andL (A := {srcOf A}) (B := {srcOf B}) (by decide) {a.src})"
  | @G4cTm.orL _ A B _ _ a b =>
      s!"(.orL (A := {srcOf A}) (B := {srcOf B}) (by decide) {a.src} {b.src})"
  | @G4cTm.impLProp _ a B _ _ _ t =>
      s!"(.impLProp (a := \"{a}\") (B := {srcOf B}) (by decide) (by decide) {t.src})"
  | @G4cTm.impLAnd _ A B D _ _ t =>
      s!"(.impLAnd (A := {srcOf A}) (B := {srcOf B}) (D := {srcOf D}) \
(by decide) {t.src})"
  | @G4cTm.impLOr _ A B D _ _ t =>
      s!"(.impLOr (A := {srcOf A}) (B := {srcOf B}) (D := {srcOf D}) \
(by decide) {t.src})"
  | @G4cTm.impLImp _ A B D _ _ t u =>
      s!"(.impLImp (A := {srcOf A}) (B := {srcOf B}) (D := {srcOf D}) \
(by decide) {t.src} {u.src})"
  | @G4cTm.impLLax _ A B _ _ t u =>
      s!"(.impLLax (A := {srcOf A}) (B := {srcOf B}) (by decide) {t.src} {u.src})"
  | @G4cTm.impLLaxLax _ A B X _ _ _ t u =>
      s!"(.impLLaxLax (A := {srcOf A}) (B := {srcOf B}) (X := {srcOf X}) \
(by decide) (by decide) {t.src} {u.src})"

/-- The paste-ready derivability theorem certified by this proof term, with
the `#print axioms` audit line.  Nothing but the term is kept: Lean's
typechecker revalidates it on paste. -/
def _root_.PLLND.G4cTm.snippet {Γ : List PLLFormula} {C : PLLFormula}
    (name : String := "derivable") (t : G4cTm Γ C) : String :=
  String.intercalate "\n"
    [ s!"theorem {name} :",
      s!"    Nonempty (LaxND {srcOfCtx Γ} {srcOf C}) :=",
      "  PLLND.Search.proved_sound",
      s!"    {t.src}",
      "",
      s!"#print axioms {name}" ]

/-- A one-line verdict summary, with the reason when there is none. -/
def Verdict.summary {Γ : List PLLFormula} {C : PLLFormula} :
    Verdict Γ C → String
  | .proved t      => s!"PROVED   {t.pretty}"
  | .refuted M w _ => s!"REFUTED  {summaryCM M w}"
  | .unknown r     => s!"UNKNOWN  {r.describe}"

/-- A one-line verdict summary for the reason-free `Answer`. -/
def Answer.summary {Γ : List PLLFormula} {C : PLLFormula} :
    Answer Γ C → String
  | .proved t      => s!"PROVED   {t.pretty}"
  | .refuted M w _ => s!"REFUTED  {summaryCM M w}"
  | .unknown       => "UNKNOWN"

/-! ## 12. Smoke tests and axiom audit

Both verdicts are exercised on tiny sequents, and the two soundness theorems
are audited: their axiom sets are subsets of
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`Lean.ofReduceBool` (hence no `native_decide`). -/

-- `⊢ p → p` is provable.
#guard (match decide {} [] ((PLLFormula.prop "p").ifThen (.prop "p")) with
          | .proved _ => true | _ => false)

-- `⊢ ◯p → p` is refuted by a finite countermodel from the battery.
#guard (match decide {} [] (((PLLFormula.prop "p").somehow).ifThen (.prop "p")) with
          | .refuted _ _ _ => true | _ => false)

-- `◯p ⊢ p` is refuted (the modality admits no escape).
#guard (match decide {} [(PLLFormula.prop "p").somehow] (PLLFormula.prop "p") with
          | .refuted _ _ _ => true | _ => false)

-- The node-budgeted positive engine: 3 nodes are honestly `unknown` on a
-- provable chain whose search visits 71 nodes; the default `prove?` finds
-- it, and an adequate budget recovers the same success.
#guard
  let Γ : List PLLFormula :=
    [ (PLLFormula.prop "b").ifThen ((PLLFormula.prop "p").or (.prop "q"))
    , (PLLFormula.prop "a").ifThen (.prop "b")
    , PLLFormula.prop "a" ]
  let C := ((PLLFormula.prop "p").or (.prop "q")).somehow
  (prove?Bounded 3 Γ C).isNone
    && (prove? Γ C).isSome
    && (prove?Bounded 1000 Γ C).isSome

-- The budget threads through `Config`: with it, `decide` degrades the
-- positive stage to `.unknown` (the sequent is provable, so no countermodel
-- stage can settle it); without it, `decide` proves it as before.
#guard
  let Γ : List PLLFormula :=
    [ (PLLFormula.prop "b").ifThen ((PLLFormula.prop "p").or (.prop "q"))
    , (PLLFormula.prop "a").ifThen (.prop "b")
    , PLLFormula.prop "a" ]
  let C := ((PLLFormula.prop "p").or (.prop "q")).somehow
  (match decide {findBudget := some 3} Γ C with
    | .unknown => true | _ => false)
    && (match decide {} Γ C with | .proved _ => true | _ => false)

/-- info: 'PLLND.Search.proved_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms proved_sound

/-- info: 'PLLND.Search.refuted_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refuted_sound

end PLLND.Search
