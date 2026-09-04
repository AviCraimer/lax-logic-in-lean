import LaxLogic.PLLG4Dec
import LaxLogic.PLLG4Gap
import LaxLogic.PLLRun

/-!
# The verified algorithms, running: a curated demonstration suite

Two machine-checked algorithms of this development, exercised on concrete
inputs with every verdict pinned by `#guard_msgs` so the claims are checked
on every build:

1. **The decider** (`PLLG4Dec.lean`).  Backward proof search for the
   complete, repaired calculus G4iLL″ (`G4c`), packaged as
   `decidableG4c : Decidable (G4c Γ C)` and
   `decidablePLL : Decidable (Nonempty (Tm Γ φ))` — F&M Theorem 2.8.

2. **The normaliser** (`PLLTopTop.lean`).  `Tm.normalize`, the total
   normaliser for the intrinsically-typed term calculus, certified against
   `Step` by `strong_normalisation` / `normalize_spec`.

A guided reading of this file (with wall-clock timings and the practical
frontier) is in `docs/demos.md`; the reduction-strategy analysis prompted
by the SN proof is in `docs/sn-strategy.md`.  `PLLRun.lean` carries the
minimal first demos (basic β, the `pll_g4c` tactic); this file grows them
into program-shaped examples and probes the engineering limits.

## The engineering headline

`decide (G4c Γ C)` routes through `decideFuel`, which computes a fuel
bound `2 ^ |enum| * |enum| + 1` from `PLLFormula.enum`, the weight-bounded
formula space.  The recent filter keeps the *stored* `enum` small (exactly
the weight-bounded set), so the fuel bignum is cheap — but merely reading
off `.card` still *constructs* `enum` level by level, and each level builds
`|enum|²` products and pays quadratic `Finset` deduplication before
filtering.  That construction is the sole bottleneck: profiling `⊢ ◯p → ◯p`
(weight 5) shows the whole ~6 s is in `enum` construction, the 54-digit fuel
bignum is free, and the **search adds nothing** on top.  Given a
hand-supplied fuel the search decides in tens of milliseconds sequents that
`decideFuel` cannot even set up.  The suite makes this visible:
`decide (G4c …)` is pinned only up to weight ≈ 4, while the same and much
heavier sequents run instantly through `search` with explicit fuel (`find`
below).  Full timings and the frontier are in `docs/demos.md`.
-/

open PLLFormula PLLND

namespace PLLDemos

private def p : PLLFormula := prop "p"
private def q : PLLFormula := prop "q"
private def r : PLLFormula := prop "r"

/-! ## Part 1 — the decider on PLL's signature (non)theorems

### 1a. The packaged decision procedure `decide (G4c …)`

These are pinned and run at build time, so all are weight ≤ 4 (see the
frontier discussion in `docs/demos.md`).  A `true`/`false` here is the
*complete* verdict: `G4c` = G4iLL″ proves exactly the PLL sequents
(`G4c.equiv_tm`), and the decision is kernel-honest (no `native_decide`). -/

-- ◯-unit: `p ⊢ ◯p`.  The monadic return.
/-- info: true -/
#guard_msgs in #eval decide (G4c [p] p.somehow)

-- No escape: `◯p ⊬ p`.  The defining constraint of a lax modality.
/-- info: false -/
#guard_msgs in #eval decide (G4c [p.somehow] p)

-- ◯-unit as a theorem: `⊢ p → ◯p`.
/-- info: true -/
#guard_msgs in #eval decide (G4c [] (p.ifThen p.somehow))

-- No escape as a (non)theorem: `⊬ ◯p → p`.
/-- info: false -/
#guard_msgs in #eval decide (G4c [] (p.somehow.ifThen p))

-- A plain intuitionistic (non-modal) theorem: modus ponens, `p→q, p ⊢ q`.
/-- info: true -/
#guard_msgs in #eval decide (G4c [p.ifThen q, p] q)

-- Its converse fails: `p→q, q ⊬ p`.
/-- info: false -/
#guard_msgs in #eval decide (G4c [p.ifThen q, q] p)

-- **F&M Theorem 2.8 at the term level.** `decidablePLL` decides
-- inhabitation of the proof-term calculus directly; `Nonempty (Tm [p] ◯p)`
-- is the ◯-unit again, now as "there is a program of this type".
/-- info: true -/
#guard_msgs in #eval decide (Nonempty (Tm [p] p.somehow))

/-! ### 1b. Heavier theorems via the search itself

`find` runs the *verified* backward search with a generous explicit fuel,
bypassing `decideFuel`'s `enum` construction.  By `search_sound` a `true`
verdict is sound — it exhibits a real `G4s` (hence PLL) derivation — for
*any* fuel; `10000` is far beyond the reachable depth of these sequents.
(A `false` from `find` would only mean "not found within fuel"; only the
`decideFuel` bound certifies underivability.  Every verdict below is
`true`.) -/

/-- Backward search with a hand-supplied fuel — sound on `true`. -/
def find (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) 10000 ∅ Γ C

-- ◯-multiplication: `⊢ ◯◯p → ◯p` (weight 6 — `decide` cannot set this up).
/-- info: true -/
#guard_msgs in #eval find [] (p.somehow.somehow.ifThen p.somehow)

-- Monad strength: `⊢ p ∧ ◯q → ◯(p ∧ q)` (weight 11).
/-- info: true -/
#guard_msgs in #eval find [] ((p.and q.somehow).ifThen (p.and q).somehow)

-- The converse of strength fails — you cannot pull `p` out of the box:
-- `⊢ ◯(p ∧ q) → p ∧ ◯q` is *not* PLL-valid.  (Shown as underivable by the
-- kernel decision below; `find` only certifies positives.)

-- A Dyckhoff-flavoured intuitionistic theorem the contraction-free rules
-- were built for: the S combinator `⊢ (p→q→r)→(p→q)→p→r` (weight 13).
/-- info: true -/
#guard_msgs in #eval find []
  ((p.ifThen (q.ifThen r)).ifThen ((p.ifThen q).ifThen (p.ifThen r)))

/-! ### 1c. The showcase: the repaired calculus closes the G4iLL gap

`PLLG4Gap.sc_but_not_G4` machine-checks that Iemhoff's *original* G4iLL
(our `G4`) misses the PLL-valid sequent

  `◯G', F' ⊢ r`,  where `F' = ◯p → r` and `G' = (◯p → r) → ◯p`

(Howe's duplication phenomenon one level up).  The repaired G4iLL″ (`G4c`)
proves it.  Same sequent, two calculi, opposite verdicts — both fast. -/

-- The complete calculus derives it (weight 8; via `find`, ≈ 70 ms):
/-- info: true -/
#guard_msgs in #eval find [PLLG4Gap.Ga.somehow, PLLG4Gap.Fa] r

-- Iemhoff's original calculus provably cannot (kernel-honest `decide`,
-- ≈ 45 ms — the old decider terminates by a multiset order, not `enum`):
/-- info: false -/
#guard_msgs in #eval decide (G4 [PLLG4Gap.Ga.somehow, PLLG4Gap.Fa] r)

/-! ## Part 2 — the normaliser on monadic programs

`Tm.pretty` renders proof terms in a compact λ-syntax: de Bruijn variables
`#n`, `val`/`let val•` for the `◯`-monad, `⟨_,_⟩` for pairs, `_.1`/`_.2`
for projections.  Each demo shows the term before and after `normalize`.
The normaliser is `Tm.step?` iterated to a fixed point (leftmost-innermost:
subterms first, head redex last — see `docs/sn-strategy.md`). -/

private def A : PLLFormula := prop "A"
private def B : PLLFormula := prop "B"

/-! ### 2a. A `let`-β cascade collapsing to nothing

A four-deep left-nested chain of trivial binds normalises all the way to
`val #0`: assoc re-associates the spine and each `let`-β fires. -/

/-- `let ⇐ (let ⇐ (let ⇐ (let ⇐ val #0 in val) in val) in val) in val`. -/
def cascade : Tm [A] A.somehow :=
  .bind (.bind (.bind (.bind (.val (.var .here)) (.val (.var .here)))
    (.val (.var .here))) (.val (.var .here))) (.val (.var .here))

/-- info: "(let val• := (let val• := (let val• := (let val• := val #0 in val #0) in val #0) in val #0) in val #0)" -/
#guard_msgs in #eval cascade.pretty
/-- info: "val #0" -/
#guard_msgs in #eval cascade.normalize.pretty

/-! ### 2b. A strength-style program with a real `let`-β

`let x ⇐ val #0 in let y ⇐ #2 in val ⟨x, y⟩` over `Γ = [A, ◯A]`.  The
outer `let ⇐ val …` fires (β), substituting `#0` for `x` and shifting
indices; the inner bind has a *neutral* scrutinee `#1` and so survives —
the residue is a genuine monadic computation. -/

def prog : Tm [A, A.somehow] (A.and A).somehow :=
  .bind (.val (.var .here))
    (.bind (.var (.there (.there .here)))
      (.val (.pair (.var (.there .here)) (.var .here))))

/-- info: "(let val• := val #0 in (let val• := #2 in val ⟨#1, #0⟩))" -/
#guard_msgs in #eval prog.pretty
/-- info: "(let val• := #1 in val ⟨#1, #0⟩)" -/
#guard_msgs in #eval prog.normalize.pretty

/-! ### 2c. β with projection and duplication

`(λx. ⟨x, x⟩) (⟨#0, #0⟩.1)`: the projection `⟨#0,#0⟩.1 ⟶ #0` fires, then
β substitutes it into both copies. -/

def dup : Tm [A] (A.and A) :=
  .app (.lam (.pair (.var .here) (.var .here)))
    (.fst (.pair (.var .here) (.var .here)))

/-- info: "((λ. ⟨#0, #0⟩) ⟨#0, #0⟩.1)" -/
#guard_msgs in #eval dup.pretty
/-- info: "⟨#0, #0⟩" -/
#guard_msgs in #eval dup.normalize.pretty

/-! ### 2d. A left-nested spine of right-units, collapsing to one

`let ⇐ (let ⇐ (let ⇐ #0 in val) in val) in val` over `Γ = [◯A]`.  The head
`#0` is neutral, so no β fires there, but assoc + the inner `let`-β collapse
three frames to a single residual bind `let ⇐ #0 in val #0`. -/

def spine : Tm [A.somehow] A.somehow :=
  .bind (.bind (.bind (.var .here) (.val (.var .here)))
    (.val (.var .here))) (.val (.var .here))

/-- info: "(let val• := (let val• := (let val• := #0 in val #0) in val #0) in val #0)" -/
#guard_msgs in #eval spine.pretty
/-- info: "(let val• := #0 in val #0)" -/
#guard_msgs in #eval spine.normalize.pretty

/-! ### 2e. The reduction boundary: `Step` has no η, no right-unit

`Step` is β for every connective plus `let`-β and `let`-assoc — and nothing
else.  Two equations that *hold semantically* but are deliberately **not**
reductions, so the terms below are already normal: -/

-- The **monad right-unit** law `m >>= return = m`: `let x ⇐ #0 in val x`
-- does NOT reduce to `#0`.  (`val x` sits in body position; only a `val`
-- in *scrutinee* position is a `let`-β redex.)
/-- info: "(let val• := #0 in val #0)" -/
#guard_msgs in
#eval (Tm.bind (.var .here) (.val (.var .here))
  : Tm [A.somehow] A.somehow).normalize.pretty

-- **Function η** `λx. f x`: `λ. (#1 #0)` does NOT reduce to `#1`.
/-- info: "(λ. (#1 #0))" -/
#guard_msgs in
#eval (Tm.lam (.app (.var (.there .here)) (.var .here))
  : Tm [A.ifThen B] (A.ifThen B)).normalize.pretty

end PLLDemos
