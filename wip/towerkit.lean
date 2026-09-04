import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch
import wip.rnEmbed

/-!
# `TowerKit` — the syntactic tower's quantifier tables, on the semantic
# ladder's battery

Two uniform-interpolation efforts live in this repository:

* **the tower** (syntactic, July): `LaxLogic/PLLG4UITrunc.lean` defines the
  computable, fuel- and budget-indexed quantifier tables `itpE`/`itpA`;
  `wip/packaging.lean` packages them as `existsP`/`forallP`, and
  `wip/final.lean` proves `uniform_interpolation_PLL` — modulo the single
  open lemma `cascade_low_pos_box` (`wip/absorb_base.lean:2273`);
* **the ladder** (semantic, this week): machine-checked *values* of `∃p.φ` /
  `∀p.C` for specific one-variable formulas, pinned sorry-free in
  `wip/postui.lean`, `wip/coverfail.lean`, `wip/mixedfail.lean`,
  `wip/phistar.lean`, `wip/branchdia.lean`, `wip/paramfork.lean`.

This module makes the two comparable: it exposes the tower's *computed*
answer on each ladder formula, so that `wip/towertest.lean` can decide
agreement with the pinned value two-sidedly.

## Transcribed definitions

`wip/absorb_base.lean`, `wip/adequacy.lean` and `wip/packaging.lean` use
root-level imports (`import absorb_base`) and are built standalone against a
`LEAN_PATH` dependency directory — they are not Lake targets, so they cannot
be imported here.  The three definitions the packaging layer contributes to
the *computation* (as opposed to the proofs) are therefore transcribed
verbatim below, with their sources named:

* `pieceClosure`  — `wip/packaging.lean` §1;
* `kcap`          — `wip/absorb_base.lean` (line 79);
* `uiFuel`        — `wip/packaging.lean` §2.

`wip/towerpin.lean` checks the transcriptions against the originals.

## The budget wall

`existsP p φ` runs `itpE` at budget `kcap (pieceClosure φ) + 1`, which for
`φ★` is `339`.  The tables' *output* grows by roughly one order of magnitude
per budget step (measured: 591, 16 498, 176 673, 1 480 640 nodes at
`b = 0,1,2,3` for `φ★`), so the prescribed budget is not computable — not
because of a strategy problem, but because the formula it denotes is
astronomically large.

What makes the experiment possible anyway is that the *conclusions transfer
upward*, using only sorry-free lemmas:

* `itp_budget_mono_le` (`LaxLogic/PLLG4UITrunc.lean`:1907, axiom-clean) —
  for `b ≤ b'`, `[itpE b'] ⊢ itpE b` and `[itpA b] ⊢ itpA b'`;
* `itp_sound` (same file, axiom-clean) — `Γ ⊢ itpE b Γ` and
  `itpA b Γ C ⊢ C`, at every fuel and budget.

Hence, writing `T b` for the tower's ∃-value and `v` for the pinned one:

* `v ⊢ T b` holds **for every budget**, free: `T b` is p-free (`itp_pfree`),
  `φ ⊢ T b` (`itp_sound`), and `v` is the *strongest* p-free consequence;
* if `T b ⊢ v` is certified at *some* budget `b`, then for every `b' ≥ b`,
  `T b' ⊢ T b ⊢ v` — so `T b' ⊣⊢ v` at **every** budget above `b`, the
  prescribed one included.

Dually on the ∀-side with `U b := itpA … [] C` and the pinned `w`:
`U b ⊢ w` is free, and `w ⊢ U b` at some `b` gives `w ⊣⊢ U b'` for all
`b' ≥ b`.

So each row needs exactly **one** search direction, at the **least** budget
that works; the other direction is a theorem, and the verdict propagates to
the prescribed budget.
-/

open PLLFormula PLLND PLLND.RNEmbed

namespace TowerKit

/-! ## 1.  Transcribed packaging definitions -/

/-- `pieceClosure`, verbatim from `wip/packaging.lean` §1. -/
def pieceClosure : PLLFormula → Finset PLLFormula
  | .prop a => {PLLFormula.prop a}
  | .falsePLL => {falsePLL}
  | .and A B => insert (A.and B) (pieceClosure A ∪ pieceClosure B)
  | .or A B => insert (A.or B) (pieceClosure A ∪ pieceClosure B)
  | .ifThen (.prop a) D =>
      insert ((PLLFormula.prop a).ifThen D)
        (pieceClosure (PLLFormula.prop a) ∪ pieceClosure D)
  | .ifThen .falsePLL D =>
      insert (falsePLL.ifThen D) (pieceClosure falsePLL ∪ pieceClosure D)
  | .ifThen (.and A B) D =>
      insert ((A.and B).ifThen D)
        (pieceClosure (A.and B) ∪ pieceClosure D
          ∪ pieceClosure (A.ifThen (B.ifThen D)))
  | .ifThen (.or A B) D =>
      insert ((A.or B).ifThen D)
        (pieceClosure (A.or B) ∪ pieceClosure D
          ∪ pieceClosure (A.ifThen D) ∪ pieceClosure (B.ifThen D))
  | .ifThen (.ifThen A B) D =>
      insert ((A.ifThen B).ifThen D)
        (pieceClosure (A.ifThen B) ∪ pieceClosure D
          ∪ pieceClosure (B.ifThen D))
  | .ifThen (.somehow X) D =>
      insert ((somehow X).ifThen D)
        (pieceClosure (somehow X) ∪ pieceClosure D)
  | .somehow χ => insert χ.somehow (pieceClosure χ)
termination_by φ => φ.weight
decreasing_by all_goals (simp only [PLLFormula.weight]; omega)

/-- `kcap`, verbatim from `wip/absorb_base.lean` (line 79). -/
def kcap (S : Finset PLLFormula) : Nat :=
  (2 * S.card + 4) * (S.card + 2)

/-- `uiFuel`, verbatim from `wip/packaging.lean` §2. -/
def uiFuel (S : Finset PLLFormula) (B slot : Nat) (Γ : List PLLFormula) : Nat :=
  mu S ((S.sup PLLFormula.weight) + slot) B slot Γ + 1

/-! ## 2.  The tower's answers, budget-parameterised

`packaging.existsP p φ` is `itpE p (pieceClosure φ) (eFuel φ) (eBudget φ) [φ]`
(with a p-free short circuit that none of the battery rows takes) and
`packaging.forallP p C` is `itpA p (pieceClosure C) (aFuel C) (aBudget C) [] C`.
The budget is the parameter we vary; the fuel is kept at the *prescribed*
value throughout, which is above `mu` for every budget `≤` the prescribed
one, hence fuel-indifferent (`wip/indiff.lean`). -/

/-- The prescribed ∃-side budget: `kcap (pieceClosure φ) + 1`. -/
def eBudget (φ : PLLFormula) : Nat := kcap (pieceClosure φ) + 1

/-- The prescribed ∃-side fuel. -/
def eFuel (φ : PLLFormula) : Nat :=
  uiFuel (pieceClosure φ) (eBudget φ) 0 [φ]

/-- The prescribed ∀-side budget. -/
def aBudget (C : PLLFormula) : Nat := kcap (pieceClosure C) + 1

/-- The prescribed ∀-side fuel. -/
def aFuel (C : PLLFormula) : Nat :=
  uiFuel (pieceClosure C) (aBudget C) C.weight []

/-- The tower's ∃-answer at budget `b` (prescribed fuel and space). -/
def eTower (φ : PLLFormula) (b : Nat) : PLLFormula :=
  itpE pv (pieceClosure φ) (eFuel φ) b [φ]

/-- The tower's ∀-answer at budget `b` (prescribed fuel and space). -/
def aTower (C : PLLFormula) (b : Nat) : PLLFormula :=
  itpA pv (pieceClosure C) (aFuel C) b [] C

/-- Node count. -/
def sz : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and a b => 1 + sz a + sz b
  | .or a b => 1 + sz a + sz b
  | .ifThen a b => 1 + sz a + sz b
  | .somehow a => 1 + sz a

/-! ## 3.  The battery

Every ∃-row's semantic value is pinned sorry-free; the pin is named in the
comment.  `φ♠`'s value is OPEN on the semantic side — the tower's answer
there is a *prediction*. -/

/-- `⊤`, as a formula. -/
abbrev Top : PLLFormula := truePLL

/-! ### Battery formulas, re-declared

`wip/postui.lean`'s import closure reaches `wip.rnc_probe`, which declares a
root-level `main`, so an *executable* root cannot import it (the same
constraint `wip/wsweep.lean` records).  The battery formulas are therefore
re-declared here, verbatim from their sources; `wip/towerpin.lean` — an
ordinary module, which *may* import them — checks every one of these by
`rfl` against the original. -/

/-- `¬A`, verbatim from `wip/postui.lean` (line 717). -/
def nt (A : PLLFormula) : PLLFormula := A.ifThen PLLFormula.falsePLL

/-- `p ∧ (p ⊃ t3)`, verbatim from `wip/postui.lean` (line 677). -/
def exLadder : PLLFormula :=
  (PLLFormula.prop pv).and ((PLLFormula.prop pv).ifThen (rnSub 3))

/-- `(p ⊃ ◯⊥) ∧ ¬¬p`, verbatim from `wip/postui.lean` (line 720). -/
def phiMix : PLLFormula :=
  ((PLLFormula.prop pv).ifThen oBot).and (nt (nt (PLLFormula.prop pv)))

/-- `p ∨ ¬p`, verbatim from `wip/postui.lean` (line 1274). -/
def wemP : PLLFormula := (PLLFormula.prop pv).or (nt (PLLFormula.prop pv))

/-- `φ★ = ((◯⊥ ⊃ p) ⊃ (◯⊥ ∧ p)) ∧ ¬¬p`, verbatim from
`wip/coverfail.lean` (line 331). -/
def phiStar : PLLFormula :=
  ((oBot.ifThen (PLLFormula.prop pv)).ifThen (oBot.and (PLLFormula.prop pv))).and
    (nt (nt (PLLFormula.prop pv)))

/-- `φ♦ = ((◯⊥ ⊃ p) ∨ ◯⊥ ∨ ¬p) ⊃ ((◯⊥ ∧ p) ∨ (◯⊥ ∧ ¬p))`, verbatim from
`wip/mixedfail.lean` (line 206). -/
def phiDia : PLLFormula :=
  ((oBot.ifThen (PLLFormula.prop pv)).or
      (oBot.or (nt (PLLFormula.prop pv)))).ifThen
    ((oBot.and (PLLFormula.prop pv)).or (oBot.and (nt (PLLFormula.prop pv))))

/-- `φ♣ = ((p ⊃ ◯⊥) ∨ (¬p ⊃ ◯⊥)) ⊃ (¬◯⊥ ∨ (◯⊥ ∧ p))`, verbatim from
`wip/paramfork.lean` (line 180). -/
def phiClub : PLLFormula :=
  (((PLLFormula.prop pv).ifThen oBot).or
      ((nt (PLLFormula.prop pv)).ifThen oBot)).ifThen
    ((nt oBot).or (oBot.and (PLLFormula.prop pv)))

/-- `ψ♣ = ¬¬◯⊥ ⊃ ◯⊥`, verbatim from `wip/paramfork.lean` (line 472). -/
def psiClub : PLLFormula := (nt (nt oBot)).ifThen oBot

/-- `φ♠ = (¬◯⊥ ⊃ (¬p ∨ p)) ⊃ (¬◯⊥ ∨ (◯⊥ ∧ p))`, verbatim from
`wip/paramfork.lean` (line 1629). -/
def phiSpade : PLLFormula :=
  ((nt oBot).ifThen ((nt (PLLFormula.prop pv)).or (PLLFormula.prop pv))).ifThen
    ((nt oBot).or (oBot.and (PLLFormula.prop pv)))

/-- A battery row: name, subject formula, pinned value (`none` = OPEN). -/
structure Row where
  name : String
  side : String          -- "E" or "A"
  subj : PLLFormula
  val  : Option PLLFormula
  pin  : String

def battery : List Row :=
  [ ⟨"p",        "E", PLLFormula.prop pv, some Top, "postui exists_p"⟩
  , ⟨"box p",    "E", (PLLFormula.prop pv).somehow, some Top, "postui exists_box_p"⟩
  , ⟨"box p > p","E", ((PLLFormula.prop pv).somehow).ifThen (PLLFormula.prop pv),
       some Top, "postui exists_boxp_imp_p"⟩
  , ⟨"exLadder", "E", exLadder, some (rnSub 3), "postui exists_exLadder"⟩
  , ⟨"phiMix",   "E", phiMix, some (nt (nt oBot)), "postui exists_phiMix"⟩
  , ⟨"phiStar",  "E", phiStar, some (nt (nt oBot)), "phistar postInterp_phiStar"⟩
  , ⟨"phiDia",   "E", phiDia, some (nt (nt oBot)), "branchdia postInterp_phiDia"⟩
  , ⟨"phiClub",  "E", phiClub, some psiClub, "paramfork postInterp_phiClub"⟩
  , ⟨"phiSpade", "E", phiSpade, none, "paramfork (OPEN)"⟩
  , ⟨"p",        "A", PLLFormula.prop pv, some PLLFormula.falsePLL, "postui forall_p"⟩
  , ⟨"box p",    "A", (PLLFormula.prop pv).somehow, some oBot, "postui forall_box_p"⟩
  , ⟨"wemP",     "A", wemP, some PLLFormula.falsePLL, "postui preInterp_wemP"⟩
  ]

/-- The tower's answer for a row at budget `b`. -/
def rowTower (r : Row) (b : Nat) : PLLFormula :=
  if r.side = "E" then eTower r.subj b else aTower r.subj b

end TowerKit
