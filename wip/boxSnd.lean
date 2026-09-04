import wip.atomForce
import wip.envDesc

/-!
# The boxed floor branch: the traversal, shape by shape

PROGRESS §102 leaves the boxed row needing one thing: from the source's second
component — a universal table at a grown context with the boxed goal `◯q` — reach the
*goal-clause* disjunct at some grown context, since `AtomForce.boxGoal_remap` then
carries it back to `Γ`.

§103 records why the natural abstraction ("the ambient at any larger context follows
from the ambient") must not be used: it is the existential ascent, and it is refuted.
The grown ambient has to be obtained **shape by shape**, and §103's table says how.

This file does the traversal.  The recursion is on the **defect**; at fuel `0` every
component is `⊤` or `⊥` and the boxed disjunct explodes.

**Status.**  `boxSnd_reaches` is now **unconditional** on its scope assumptions: the
four named obligations of §105 are all discharged (two proved, one shown to need no
measure, one retired as unprovable-as-stated with its content moved into the
traversal).  Sorry-free, `[propext, Classical.choice, Quot.sound]`.

## Scope

A `∨`-free space (inherited from `itpA_atom_forces`) and an **atom** boxed goal `◯q`
with `q ≠ p` — the shape the recursion reaches when the space's γ-heads are atomic.
-/

open PLLFormula

namespace PLLND
namespace BoxSnd

open GoalDesc AtomForce EnvDesc

/-- Project a conjunct out of a derivable `andAll`. -/
theorem projAll {Δ l : List PLLFormula} {φ : PLLFormula}
    (d : G4c Δ (andAll l)) (h : φ ∈ l) : G4c Δ φ :=
  G4c.cut d (G4c.andAll_elim h (G4c.identity_mem (.head _)))

/-- The target of the traversal: the boxed goal clause at `Γ`. -/
abbrev tgtClause (p : String) (S : Finset PLLFormula) (f c : Nat)
    (Γ : List PLLFormula) (q : String) : PLLFormula :=
  ((itpE p S f c Γ).ifThen (itpA p S (f + 1) (c + 1) Γ (prop q))).somehow

/-! ## The ungated projections

For each ungated context shape, the ambient's own clause for that formula is the
grown ambient at the context the `itpA` disjunct grows to.  These are pure
projections out of `itpEcls`; each is stated separately so the induction below reads
as the mathematics rather than as guard bookkeeping. -/

/-- `A ∧ B ∈ Γ'`: the ambient's clause **is** the grown ambient. -/
theorem grown_and (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {A B : PLLFormula}
    (hF : A.and B ∈ Γ') (h1 : ¬(A ∈ Γ' ∧ B ∈ Γ'))
    (h2 : (A ∈ Γ' ∨ A ∈ S) ∧ (B ∈ Γ' ∨ B ∈ S))
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ (itpE p S f (c + 2) (A :: B :: Γ')) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨A.and B, hF, ?_⟩
  simp only [if_neg h1, if_pos h2]
  exact List.mem_singleton.mpr rfl

/-- `(prop q') ⊃ B ∈ Γ'` with `prop q' ∈ Γ'`: the ambient's clause is the grown
ambient outright. -/
theorem grown_impAtom_pres (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {q' : String} {B : PLLFormula}
    (hF : (prop q').ifThen B ∈ Γ') (h1 : B ∉ Γ') (h2 : B ∈ S)
    (h3 : (prop q' : PLLFormula) ∈ Γ')
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ (itpE p S f (c + 2) (B :: Γ')) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(prop q').ifThen B, hF, ?_⟩
  simp only [if_neg h1, if_pos h2, if_pos h3]
  exact List.mem_singleton.mpr rfl

/-- `(prop q') ⊃ B ∈ Γ'` with `prop q' ∉ Γ'` and `q' ≠ p`: here the ambient's clause is
`prop q' ⇢ E@(c+2)(B::Γ')`, an **implication** — and the `itpA` disjunct for the same
context formula is `prop q' ∧ A@b(B::Γ', C)`, so it supplies the antecedent.  This is the
row of §103's table where the two tables' guards differ and the disjunct makes up the
difference. -/
theorem grown_impAtom_fresh (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {q' : String} {B : PLLFormula}
    (hF : (prop q').ifThen B ∈ Γ') (h1 : B ∉ Γ') (h2 : B ∈ S)
    (h3 : (prop q' : PLLFormula) ∉ Γ') (h4 : ¬(q' = p))
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ'))
    (hq' : G4c Δ (prop q')) :
    G4c Δ (itpE p S f (c + 2) (B :: Γ')) := by
  rw [itpE_succ] at hamb
  refine fire (projAll hamb ?_) hq'
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(prop q').ifThen B, hF, ?_⟩
  simp only [if_neg h1, if_pos h2, if_neg h3, if_neg h4]
  exact List.mem_singleton.mpr rfl

/-- `(A ∧ B) ⊃ D ∈ Γ'`: the ambient's clause is the grown ambient at the curried
context. -/
theorem grown_impAnd (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {A B D : PLLFormula}
    (hF : (A.and B).ifThen D ∈ Γ') (h1 : A.ifThen (B.ifThen D) ∉ Γ')
    (h2 : A.ifThen (B.ifThen D) ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ (itpE p S f (c + 2) (A.ifThen (B.ifThen D) :: Γ')) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(A.and B).ifThen D, hF, ?_⟩
  simp only [if_neg h1, if_pos h2]
  exact List.mem_singleton.mpr rfl

/-- `(A ∨ B) ⊃ D ∈ Γ'`: the ambient's clause is the grown ambient at the split
context. -/
theorem grown_impOr (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {A B D : PLLFormula}
    (hF : (A.or B).ifThen D ∈ Γ')
    (h1 : ¬(A.ifThen D ∈ Γ' ∧ B.ifThen D ∈ Γ'))
    (h2 : (A.ifThen D ∈ Γ' ∨ A.ifThen D ∈ S) ∧
      (B.ifThen D ∈ Γ' ∨ B.ifThen D ∈ S))
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ (itpE p S f (c + 2) (A.ifThen D :: B.ifThen D :: Γ')) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(A.or B).ifThen D, hF, ?_⟩
  simp only [if_neg h1, if_pos h2]
  exact List.mem_singleton.mpr rfl

/-- `◯χ ∈ Γ'`: the ambient's clause is the grown ambient **under a `◯`** — which is
the form the `itpA` disjunct for `◯χ` can use, since that disjunct is boxed too. -/
theorem grown_box (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {χ : PLLFormula}
    (hF : χ.somehow ∈ Γ') (h1 : ¬(χ ∈ Γ' ∨ χ ∉ S))
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ ((itpE p S f (c + 2) (χ :: Γ')).somehow) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨χ.somehow, hF, ?_⟩
  simp only [if_neg h1]
  exact List.mem_singleton.mpr rfl

/-! ## The named cases

Historically the traversal was proved modulo four named obligations (§105).  All four
are now discharged and `boxSnd_reaches` takes **none** of them:

| obligation | how it went |
|---|---|
| `ZeroFuelCase` | proved (`zeroFuelCase`, §106) |
| `BoxCtxCase` | proved (`boxCtxCase`, §112) |
| `TruncCase` | **needs no measure**: `box_open` onto the traversal's own others-analysis |
| `ImpCase` | **retired unproved**: unprovable as stated; the routing is done in the traversal |

The two `Prop`s that are still used (`BoxCtxCase`, `ZeroFuelCase`) are kept as the
statements of the corresponding lemmas; `TruncCase` and `ImpCase` are kept only as
the record of what was asked for, with the reasons in their docstrings. -/

/-- The `◯χ` environment family of the traversal. -/
def BoxCtxCase (p : String) (S : Finset PLLFormula) (q : String) : Prop :=
  ∀ (f c : Nat) (Γ Γ' Δ : List PLLFormula) (χ : PLLFormula),
    χ.somehow ∈ Γ' → χ ∈ S → χ ∉ Γ' → (∀ Y ∈ Γ', Y ∈ S) →
    G4c Δ ((itpE p S (f + 1) (c + 2) (χ :: Γ')).somehow) →
    G4c Δ (((itpE p S (f + 1) (c + 1) (χ :: Γ')).ifThen
      (itpA p S (f + 1) (c + 1) (χ :: Γ') ((prop q).somehow))).somehow) →
    -- the recursion, at strictly smaller defect and one fuel down
    (∀ (Δ' : List PLLFormula) (Γ'' : List PLLFormula) (w : PLLFormula),
      (∀ y ∈ Γ', y ∈ Γ'') → (∀ y ∈ Γ'', y ∈ S) →
      w ∈ S → w ∈ Γ'' → w ∉ Γ' →
      G4c Δ' (itpE p S (f + 1) (c + 2) Γ'') →
      G4c Δ' (itpA p S (f + 1) (c + 1) Γ'' ((prop q).somehow)) →
      G4c Δ' (tgtClause p S f c Γ q)) →
    G4c Δ (tgtClause p S (f + 1) c Γ q)

/-- The truncation disjunct of the traversal.

**DISCHARGED** (see `boxSnd_reaches` below, which no longer takes it as a
hypothesis): kept only as the record of what the obligation was.

PROGRESS §108 recorded the truncation as the one obligation that is *not* a step
of the defect recursion — its body is `⋁ others` at the **same** `Γ'` — and asked
whether it needs its own measure or `desc_of_oth`'s pairing move.  Neither: it
needs **no** measure at all.  The truncation's body is the others-table *without*
the truncation, so opening the box (`box_open`, legitimate since the conclusion is
`◯`-shaped) and firing the guard from the ambient lands exactly on the disjunct
analysis the traversal already performs, at the same fuel, budget, context and
defect.  What blocked it was the *structure* of the proof, not its content: the
others-analysis was inlined in the traversal's main case split rather than hoisted,
so it was unavailable to the truncation branch.  Hoisted (as `othersOne` /
`othersAll` inside `boxSnd_reaches`) the branch is three lines.

This is the same pattern as §§106, 111–112 and §108 itself: a statement problem
wearing the clothes of a proof problem. -/
def TruncCase (p : String) (S : Finset PLLFormula) (q : String) : Prop :=
  ∀ (f c : Nat) (Γ Γ' Δ : List PLLFormula),
    (∀ Y ∈ Γ', Y ∈ S) →
    G4c Δ (itpE p S (f + 1) (c + 2) Γ') →
    G4c Δ (((itpE p S f c Γ').ifThen
      (orAll (itpAoth p S f (c + 1) Γ' ((prop q).somehow)))).somehow) →
    G4c Δ (tgtClause p S f c Γ q)

/-- The `⊃`-headed environment families (`(prop q')⊃B`, `(A∧B)⊃D`, `(A∨B)⊃D`,
`(A⊃B)⊃D`, `◯A⊃B`).

**RETIRED, and not because it was proved.**  As stated it is *not provable*: its
membership hypothesis is `φ ∈ itpAenv p S (f+1) (c+1) Γ' (◯q)` — membership in the
WHOLE environment table — while the traversal knows something strictly stronger,
namely which context formula `F ∈ Γ'` produced `φ`.  From the weak form the proof
would have to re-handle the `◯χ`, `∧` and `∨` families as well, and it has neither
`BoxCtxCase` nor `∨`-freeness to do it with.  So this is a fourth instance of §112's
pattern (a statement problem), and the fix is the same as for `TruncCase`: the
routing is done **in the traversal**, where the per-clause membership is in hand.

Two further corrections came out of doing it (see the nine case lemmas below):

* the count of `⊃`-headed disjunct shapes is **nine**, not §110's six — the jump
  family `(A₁⊃B₁)⊃D` contributes two shapes and the γ family `◯A⊃B` contributes
  `2 + |{◯x ∈ Γ'}|`, not two;
* `impOr_case` fixes `A₁⊃D` as the fresh witness, but the `∨`-clause's guard only
  says the two are not *both* present, so the `B₁⊃D` witness needs the symmetric
  branch (inlined in the traversal). -/
def ImpCase (p : String) (S : Finset PLLFormula) (q : String) : Prop :=
  ∀ (f c : Nat) (Γ Γ' Δ : List PLLFormula) (A D : PLLFormula) (φ : PLLFormula),
    A.ifThen D ∈ Γ' → (∀ Y ∈ Γ', Y ∈ S) →
    φ ∈ itpAenv p S (f + 1) (c + 1) Γ' ((prop q).somehow) →
    G4c Δ (itpE p S (f + 2) (c + 2) Γ') → G4c Δ φ →
    -- the recursion, at strictly smaller defect and one fuel down
    (∀ (Γ'' : List PLLFormula) (w : PLLFormula),
      (∀ y ∈ Γ', y ∈ Γ'') → (∀ y ∈ Γ'', y ∈ S) →
      w ∈ S → w ∈ Γ'' → w ∉ Γ' →
      G4c Δ (itpE p S (f + 1) (c + 2) Γ'') →
      G4c Δ (itpA p S (f + 1) (c + 1) Γ'' ((prop q).somehow)) →
      G4c Δ (tgtClause p S f c Γ q)) →
    G4c Δ (tgtClause p S (f + 1) c Γ q)

/-- The fuel-`0` floor of the traversal: every component of every disjunct is `⊤` or
`⊥`, so each disjunct either explodes or is absurd.

The source budget `b + 1` and the target budget `c` are **independent**: every
branch of the proof reaches the conclusion from `⊥` or by `box_absurd`, neither of
which looks at the target.  (They were coupled only because the traversal happened
to couple them; the tight-budget traversal of `wip/boxSndTight.lean` needs them
apart.) -/
def ZeroFuelCase (p : String) (S : Finset PLLFormula) (q : String) : Prop :=
  ∀ (b c : Nat) (Γ Γ' Δ : List PLLFormula) (φ : PLLFormula),
    φ ∈ itpAenv p S 0 (b + 1) Γ' ((prop q).somehow) →
    G4c Δ φ → G4c Δ (tgtClause p S 0 c Γ q)

/-- **The target lifts in the fuel**, both conversions free: the guard converts
*down* (`fuelE_le`) and the value converts *up* (`itp_fuel_mono`), which is exactly
the direction each is free in. -/
theorem tgtClause_fuel_lift (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {q : String}
    (d : G4c Δ (tgtClause p S f c Γ q)) :
    G4c Δ (tgtClause p S (f + 1) c Γ q) := by
  refine box_remap_free d ?_ ?_
  · exact consume₁ (G4c.identity_mem (.head _)) (fuelE_le p S (Nat.le_succ f) c Γ)
  · exact consume₁ (G4c.identity_mem (.head _))
      ((itp_fuel_mono p S (f + 1)).2 (c + 1) Γ (prop q))

/-! ## The traversal -/


/-! ## Discharging the fuel-`0` floor

At fuel `0` every recursive component is `itpE p S 0 … = ⊤` or `itpA p S 0 … = ⊥`, so
each environment disjunct is `⊥`, a conjunction with a `⊥` component, a conjunction
whose first component is `⊤ ⇢ ⊥`, or the boxed `◯(⊤ ⇢ ⊥)` — and the last yields any
`◯`-conclusion by `box_absurd`.

Written shape by shape.  One counting point, which cost two failed attempts (PROGRESS
§105 addendum): the budget here is `c + 1`, a **literal successor**, so `split` does not
branch on the `match b with | 0 | b'+1` of a gated clause — it reduces.  A gated shape
therefore has one fewer `split` than the same shape has when the budget is a variable
(as in `AtomForce.atom_forces_aux`, where `b` is universally quantified). -/

private theorem byBot {Δ : List PLLFormula} {W : PLLFormula}
    (hd : G4c Δ falsePLL) : G4c Δ W :=
  G4c.cut hd (G4c.botL (.head _))

private theorem byBotR {Δ : List PLLFormula} {X W : PLLFormula}
    (hd : G4c Δ (X.and falsePLL)) : G4c Δ W :=
  byBot (projAnd₂ hd)

private theorem byImpBot {Δ : List PLLFormula} {Y W : PLLFormula}
    (hd : G4c Δ ((truePLL.ifThen falsePLL).and Y)) : G4c Δ W :=
  byBot (fire (projAnd₁ hd) (G4c.truePLL_intro _))

theorem zeroFuelCase (p : String) (S : Finset PLLFormula) {q : String}
    (hq : q ≠ p) : ZeroFuelCase p S q := by
  intro b c Γ Γ' Δ φ hφ hd
  simp only [itpAenv] at hφ
  obtain ⟨F, hFΓ', hin⟩ := List.mem_flatMap.mp hφ
  cases F with
  | prop q' =>
      simp only at hin
      split at hin
      next hc =>
          exfalso
          have h2 : (prop q : PLLFormula).somehow = prop p := hc.2
          exact absurd h2 (by simp)
      next => cases hin
  | falsePLL => cases hin
  | and A B =>
      simp only at hin
      split at hin
      next => cases hin
      next =>
          split at hin
          next =>
              rcases List.mem_singleton.mp hin with rfl
              simp only [itpA] at hd
              exact byBot hd
          next => cases hin
  | or A B =>
      simp only at hin
      split at hin
      next => cases hin
      next =>
          split at hin
          next =>
              rcases List.mem_singleton.mp hin with rfl
              simp only [itpA, itpE] at hd
              exact byImpBot hd
          next => cases hin
  | somehow χ =>
      simp only at hin
      split at hin
      next => cases hin
      next =>
          rcases List.mem_singleton.mp hin with rfl
          simp only [itpA, itpE] at hd
          exact box_absurd _ hd (G4c.truePLL_intro _)
  | ifThen A D =>
      cases A with
      | falsePLL => cases hin
      | prop q' =>
          simp only at hin
          split at hin
          next => cases hin
          next =>
              split at hin
              next =>
                  split at hin
                  next =>
                      rcases List.mem_singleton.mp hin with rfl
                      simp only [itpA] at hd
                      exact byBot hd
                  next =>
                      split at hin
                      next => cases hin
                      next =>
                          rcases List.mem_singleton.mp hin with rfl
                          simp only [itpA] at hd
                          exact byBotR hd
              next => cases hin
      | and A₁ B₁ =>
          simp only at hin
          split at hin
          next => cases hin
          next =>
              split at hin
              next =>
                  rcases List.mem_singleton.mp hin with rfl
                  simp only [itpA] at hd
                  exact byBot hd
              next => cases hin
      | or A₁ B₁ =>
          simp only at hin
          split at hin
          next => cases hin
          next =>
              split at hin
              next =>
                  rcases List.mem_singleton.mp hin with rfl
                  simp only [itpA] at hd
                  exact byBot hd
              next => cases hin
      | ifThen A₁ B₁ =>
          simp only at hin
          split at hin
          next => cases hin
          next =>
              split at hin
              next =>
                  split at hin
                  next =>
                      split at hin
                      next =>
                          rcases List.mem_singleton.mp hin with rfl
                          simp only [itpA] at hd
                          exact byBotR hd
                      next => cases hin
                  next =>
                      split at hin
                      next =>
                          rcases List.mem_singleton.mp hin with rfl
                          simp only [itpA] at hd
                          exact byBotR hd
                      next => cases hin
              next => cases hin
      | somehow A₁ =>
          simp only at hin
          split at hin
          next => cases hin
          next =>
              split at hin
              next =>
                rcases List.mem_append.mp hin with hL | hR
                · split at hL
                  next =>
                      rcases List.mem_cons.mp hL with rfl | hL'
                      · simp only [itpA] at hd
                        exact byBotR hd
                      · rcases List.mem_singleton.mp hL' with rfl
                        simp only [itpA] at hd
                        exact byBotR hd
                  next => cases hL
                · obtain ⟨X, hX, hXin⟩ := List.mem_filterMap.mp hR
                  cases X with
                  | somehow x =>
                      simp only at hXin
                      split at hXin
                      next => cases hXin
                      next =>
                          injection hXin with hXe
                          subst hXe
                          simp only [itpA] at hd
                          exact byBotR hd
                  | prop _ => cases hXin
                  | falsePLL => cases hXin
                  | and _ _ => cases hXin
                  | or _ _ => cases hXin
                  | ifThen _ _ => cases hXin
              next => cases hin

/-! ## Budget shift: the source's first components lift to what the ambient demands

A gated environment disjunct of `itpA p S f (c+1) Γ'` has its first component at budget
**`c`**, while the corresponding conjunct of the ambient `E@(c+2)(Γ')` has its antecedent
at budget **`c+1`**.  So firing the ambient with the disjunct's own first component — the
move of §98 — needs a one-step budget shift first.

It is free, and for the same reason `tgtClause_fuel_lift` is free: the shift is *up* on
the universal side, where tables weaken, and *down* on the existential side, where they
also weaken.  Both directions of `itp_budget_mono` point the right way. -/

/-- The jump clause's first component lifts one budget. -/
theorem shift_imp (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {X : PLLFormula}
    (hd : G4c Δ ((itpE p S f c Γ).ifThen (itpA p S f c Γ X))) :
    G4c Δ ((itpE p S f (c + 1) Γ).ifThen (itpA p S f (c + 1) Γ X)) := by
  refine G4c.impR ?_
  refine consume₁ (fire (hd.weaken _) ?_)
    ((itp_budget_mono p S f).2 c Γ X)
  exact consume₁ (G4c.identity_mem (.head _))
    ((itp_budget_mono p S f).1 c Γ)

/-- The γ-clause's **boxed** first component lifts one budget. -/
theorem shift_box (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {X : PLLFormula}
    (hd : G4c Δ (((itpE p S f c Γ).ifThen (itpA p S f c Γ X)).somehow)) :
    G4c Δ (((itpE p S f (c + 1) Γ).ifThen
      (itpA p S f (c + 1) Γ X)).somehow) := by
  refine box_remap_free hd ?_ ?_
  · exact consume₁ (G4c.identity_mem (.head _))
      ((itp_budget_mono p S f).1 c Γ)
  · exact consume₁ (G4c.identity_mem (.head _))
      ((itp_budget_mono p S f).2 c Γ X)

/-- The γ-clause's **plain** first component lifts one budget — this one is
`itp_budget_mono` outright, recorded here so the three shifts read together. -/
theorem shift_plain (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {X : PLLFormula}
    (hd : G4c Δ (itpA p S f c Γ X)) :
    G4c Δ (itpA p S f (c + 1) Γ X) :=
  consume₁ hd ((itp_budget_mono p S f).2 c Γ X)

/-! ## The gated environment shapes, wired up

With the shifts in place, §98's two firing lemmas apply to the disjunct's own first
component, so the gated shapes of `ImpCase` reduce to the recursion.  Stated as the
two composites the traversal will call. -/

/-- γ-clause, boxed disjunct: the grown ambient from the ambient and the disjunct's own
boxed first component, at the budget the disjunct actually carries. -/
theorem grownAmb_of_box_shifted (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {A B : PLLFormula}
    (hmem : A.somehow.ifThen B ∈ Γ) (hS : A.somehow.ifThen B ∈ S)
    (hB : B ∉ Γ) (hBS : B ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ))
    (hbox : G4c Δ (((itpE p S f c Γ).ifThen
      (itpA p S f c Γ A.somehow)).somehow)) :
    G4c Δ (itpE p S f (c + 2) (B :: Γ)) :=
  grownAmb_of_box p S hmem hS hB hBS hamb (shift_box p S hbox)

/-- γ-clause, plain disjunct: likewise. -/
theorem grownAmb_of_plain_shifted (p : String) (S : Finset PLLFormula)
    {f c : Nat} {Γ Δ : List PLLFormula} {A B : PLLFormula}
    (hmem : A.somehow.ifThen B ∈ Γ) (hS : A.somehow.ifThen B ∈ S)
    (hB : B ∉ Γ) (hBS : B ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ))
    (hval : G4c Δ (itpA p S f c Γ A)) :
    G4c Δ (itpE p S f (c + 2) (B :: Γ)) :=
  grownAmb_of_plain p S hmem hS hB hBS hamb (shift_plain p S hval)

/-! ## `ImpCase`'s five shapes, as lemmas

`ImpCase` is an assembly of five cases plus the membership bookkeeping.  The five cases
are the mathematical content and are recorded here; each is three lines, because §§98,
104, 107 and 109 have already done the work.

`Step` abbreviates the recursion `boxSnd_reaches` supplies. -/

/-- The recursion hypothesis, as the traversal passes it. -/
abbrev Step (p : String) (S : Finset PLLFormula) (q : String) (f c : Nat)
    (Γ Γ' Δ : List PLLFormula) : Prop :=
  ∀ (Γ'' : List PLLFormula) (w : PLLFormula),
    (∀ y ∈ Γ', y ∈ Γ'') → (∀ y ∈ Γ'', y ∈ S) →
    w ∈ S → w ∈ Γ'' → w ∉ Γ' →
    G4c Δ (itpE p S (f + 1) (c + 2) Γ'') →
    G4c Δ (itpA p S (f + 1) (c + 1) Γ'' ((prop q).somehow)) →
    G4c Δ (tgtClause p S f c Γ q)

/-- `(A₁ ∧ B₁) ⊃ D`: the ambient's clause is the grown ambient at the curried context. -/
theorem impAnd_case (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Γ' Δ : List PLLFormula} {A₁ B₁ D : PLLFormula} {q : String}
    (hF : (A₁.and B₁).ifThen D ∈ Γ')
    (h1 : A₁.ifThen (B₁.ifThen D) ∉ Γ') (h2 : A₁.ifThen (B₁.ifThen D) ∈ S)
    (hΓ'S : ∀ Y ∈ Γ', Y ∈ S)
    (hamb : G4c Δ (itpE p S (f + 2) (c + 2) Γ'))
    (hd : G4c Δ (itpA p S (f + 1) (c + 1)
      (A₁.ifThen (B₁.ifThen D) :: Γ') ((prop q).somehow)))
    (step : Step p S q f c Γ Γ' Δ) :
    G4c Δ (tgtClause p S (f + 1) c Γ q) :=
  tgtClause_fuel_lift p S
    (step (A₁.ifThen (B₁.ifThen D) :: Γ') (A₁.ifThen (B₁.ifThen D))
      (fun y hy => .tail _ hy)
      (by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h2
        · exact hΓ'S y hy)
      h2 (.head _) h1 (grown_impAnd p S hF h1 h2 hamb) hd)

/-- `(A₁ ∨ B₁) ⊃ D`: likewise at the split context. -/
theorem impOr_case (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Γ' Δ : List PLLFormula} {A₁ B₁ D : PLLFormula} {q : String}
    (hF : (A₁.or B₁).ifThen D ∈ Γ')
    (h1 : ¬(A₁.ifThen D ∈ Γ' ∧ B₁.ifThen D ∈ Γ'))
    (h2 : (A₁.ifThen D ∈ Γ' ∨ A₁.ifThen D ∈ S) ∧
      (B₁.ifThen D ∈ Γ' ∨ B₁.ifThen D ∈ S))
    (hΓ'S : ∀ Y ∈ Γ', Y ∈ S)
    (hADΓ : A₁.ifThen D ∉ Γ') (hADS : A₁.ifThen D ∈ S)
    (hamb : G4c Δ (itpE p S (f + 2) (c + 2) Γ'))
    (hd : G4c Δ (itpA p S (f + 1) (c + 1)
      (A₁.ifThen D :: B₁.ifThen D :: Γ') ((prop q).somehow)))
    (step : Step p S q f c Γ Γ' Δ) :
    G4c Δ (tgtClause p S (f + 1) c Γ q) :=
  tgtClause_fuel_lift p S
    (step (A₁.ifThen D :: B₁.ifThen D :: Γ') (A₁.ifThen D)
      (fun y hy => .tail _ (.tail _ hy))
      (by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hADS
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (h2.2.elim (fun h => hΓ'S _ h) id)
        · exact hΓ'S y hy)
      hADS (.head _) hADΓ (grown_impOr p S hF h1 h2 hamb) hd)

/-- `(prop q') ⊃ B` with the atom **present**: the ambient's clause is the grown
ambient. -/
theorem impAtom_pres_case (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Γ' Δ : List PLLFormula} {q' : String} {B : PLLFormula} {q : String}
    (hF : (prop q').ifThen B ∈ Γ') (h1 : B ∉ Γ') (h2 : B ∈ S)
    (h3 : (prop q' : PLLFormula) ∈ Γ') (hΓ'S : ∀ Y ∈ Γ', Y ∈ S)
    (hamb : G4c Δ (itpE p S (f + 2) (c + 2) Γ'))
    (hd : G4c Δ (itpA p S (f + 1) (c + 1) (B :: Γ') ((prop q).somehow)))
    (step : Step p S q f c Γ Γ' Δ) :
    G4c Δ (tgtClause p S (f + 1) c Γ q) :=
  tgtClause_fuel_lift p S
    (step (B :: Γ') B (fun y hy => .tail _ hy)
      (by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h2
        · exact hΓ'S y hy)
      h2 (.head _) h1 (grown_impAtom_pres p S hF h1 h2 h3 hamb) hd)

/-- `(prop q') ⊃ B` with the atom **fresh**: the ambient's clause is an implication, and
the disjunct's own `prop q'` conjunct fires it (§109). -/
theorem impAtom_fresh_case (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Γ' Δ : List PLLFormula} {q' : String} {B : PLLFormula} {q : String}
    (hF : (prop q').ifThen B ∈ Γ') (h1 : B ∉ Γ') (h2 : B ∈ S)
    (h3 : (prop q' : PLLFormula) ∉ Γ') (h4 : ¬(q' = p))
    (hΓ'S : ∀ Y ∈ Γ', Y ∈ S)
    (hamb : G4c Δ (itpE p S (f + 2) (c + 2) Γ'))
    (hq' : G4c Δ (prop q'))
    (hd : G4c Δ (itpA p S (f + 1) (c + 1) (B :: Γ') ((prop q).somehow)))
    (step : Step p S q f c Γ Γ' Δ) :
    G4c Δ (tgtClause p S (f + 1) c Γ q) :=
  tgtClause_fuel_lift p S
    (step (B :: Γ') B (fun y hy => .tail _ hy)
      (by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h2
        · exact hΓ'S y hy)
      h2 (.head _) h1 (grown_impAtom_fresh p S hF h1 h2 h3 h4 hamb hq') hd)

/-- `◯A ⊃ B`, the γ-clause, **boxed** disjunct: the ambient is fired with the disjunct's
own boxed first component after the free budget shift (§§98, 107). -/
theorem gammaBox_case (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Γ' Δ : List PLLFormula} {A B : PLLFormula} {q : String}
    (hF : A.somehow.ifThen B ∈ Γ') (hS : A.somehow.ifThen B ∈ S)
    (h1 : B ∉ Γ') (h2 : B ∈ S) (hΓ'S : ∀ Y ∈ Γ', Y ∈ S)
    (hamb : G4c Δ (itpE p S (f + 2) (c + 2) Γ'))
    (hbox : G4c Δ (((itpE p S (f + 1) c Γ').ifThen
      (itpA p S (f + 1) c Γ' A.somehow)).somehow))
    (hd : G4c Δ (itpA p S (f + 1) (c + 1) (B :: Γ') ((prop q).somehow)))
    (step : Step p S q f c Γ Γ' Δ) :
    G4c Δ (tgtClause p S (f + 1) c Γ q) :=
  tgtClause_fuel_lift p S
    (step (B :: Γ') B (fun y hy => .tail _ hy)
      (by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h2
        · exact hΓ'S y hy)
      h2 (.head _) h1
      (grownAmb_of_box_shifted p S hF hS h1 h2 hamb hbox) hd)

/-- `◯A ⊃ B`, **plain** disjunct: likewise with the plain first component. -/
theorem gammaPlain_case (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Γ' Δ : List PLLFormula} {A B : PLLFormula} {q : String}
    (hF : A.somehow.ifThen B ∈ Γ') (hS : A.somehow.ifThen B ∈ S)
    (h1 : B ∉ Γ') (h2 : B ∈ S) (hΓ'S : ∀ Y ∈ Γ', Y ∈ S)
    (hamb : G4c Δ (itpE p S (f + 2) (c + 2) Γ'))
    (hval : G4c Δ (itpA p S (f + 1) c Γ' A))
    (hd : G4c Δ (itpA p S (f + 1) (c + 1) (B :: Γ') ((prop q).somehow)))
    (step : Step p S q f c Γ Γ' Δ) :
    G4c Δ (tgtClause p S (f + 1) c Γ q) :=
  tgtClause_fuel_lift p S
    (step (B :: Γ') B (fun y hy => .tail _ hy)
      (by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h2
        · exact hΓ'S y hy)
      h2 (.head _) h1
      (grownAmb_of_plain_shifted p S hF hS h1 h2 hamb hval) hd)

/-! ## The three ⊃-shapes §110's table missed

PROGRESS §§105/109/110 counted the `⊃`-headed environment families as **five**, with
six disjunct shapes.  Reading the clause table against the traversal (the discipline
§112 prescribes) the count is wrong in two places, and both are shapes with no lemma:

* the **jump family** `(A₁⊃B₁)⊃D ∈ Γ'` contributes two disjuncts — one with
  `B₁⊃D ∈ Γ'` (budget-gated, first component at `c`) and one with `B₁⊃D ∉ Γ'`
  (ungated, first component at `c+1` in the grown context `B₁⊃D::Γ'`).  §109's
  table lists it as an "implication the disjunct's own first component fires", but
  no lemma was written;
* the **γ family** `◯A⊃B ∈ Γ'` contributes not two disjuncts but `2 + |{◯x ∈ Γ'}|`:
  besides the plain and boxed gated pair there is one *continuation* per boxed
  context member, `◯( E@(c+1)(x::Γ') ⇢ A@(c+1)(x::Γ', ◯A) ) ∧ A@(c+1)(B::Γ', ◯q)`.

All three are the same move as §98's, at a different clause of `itpEcls`: the
ambient's matching conjunct is an implication whose antecedent is the disjunct's own
first component, one budget below what the ambient demands, and `shift_imp`/
`shift_box` (§107) supply that step free.  So they cost three membership lemmas and
three three-line composites, and nothing mathematical. -/

/-- The ambient's jump-conjunct with `B₁⊃D` **present**: its antecedent is the
disjunct's own first component, one budget up. -/
theorem amb_jump_mem_pres (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ : List PLLFormula} {A₁ B₁ D : PLLFormula}
    (hmem : (A₁.ifThen B₁).ifThen D ∈ Γ) (hD : D ∉ Γ) (hDS : D ∈ S)
    (hBD : B₁.ifThen D ∈ Γ) (hS : (A₁.ifThen B₁).ifThen D ∈ S) :
    (((itpE p S f (c + 1) Γ).ifThen
        (itpA p S f (c + 1) Γ (A₁.ifThen B₁))).ifThen
      (itpE p S f (c + 2) (D :: Γ))) ∈ itpEcls p S f (c + 2) Γ := by
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(A₁.ifThen B₁).ifThen D, hmem, ?_⟩
  simp only [if_neg hD, if_pos hDS, if_pos hBD, if_pos hS]
  exact List.mem_singleton.mpr rfl

/-- The ambient's jump-conjunct with `B₁⊃D` **fresh**. -/
theorem amb_jump_mem_fresh (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ : List PLLFormula} {A₁ B₁ D : PLLFormula}
    (hmem : (A₁.ifThen B₁).ifThen D ∈ Γ) (hD : D ∉ Γ) (hDS : D ∈ S)
    (hBD : B₁.ifThen D ∉ Γ) (hBDS : B₁.ifThen D ∈ S) :
    (((itpE p S f (c + 2) (B₁.ifThen D :: Γ)).ifThen
        (itpA p S f (c + 2) (B₁.ifThen D :: Γ) (A₁.ifThen B₁))).ifThen
      (itpE p S f (c + 2) (D :: Γ))) ∈ itpEcls p S f (c + 2) Γ := by
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(A₁.ifThen B₁).ifThen D, hmem, ?_⟩
  simp only [if_neg hD, if_pos hDS, if_neg hBD, if_pos hBDS]
  exact List.mem_singleton.mpr rfl

/-- The ambient's γ-**continuation** conjunct, one per `◯x ∈ Γ`. -/
theorem amb_gammaCont_mem (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ : List PLLFormula} {A B x : PLLFormula}
    (hmem : A.somehow.ifThen B ∈ Γ) (hB : B ∉ Γ) (hBS : B ∈ S)
    (hx : x.somehow ∈ Γ) (hxc : ¬(x ∈ Γ ∨ x ∉ S)) :
    ((((itpE p S f (c + 2) (x :: Γ)).ifThen
        (itpA p S f (c + 2) (x :: Γ) A.somehow)).somehow).ifThen
      (itpE p S f (c + 2) (B :: Γ))) ∈ itpEcls p S f (c + 2) Γ := by
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨A.somehow.ifThen B, hmem, ?_⟩
  simp only [if_neg hB, if_pos hBS]
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_filterMap.mpr ⟨x.somehow, hx, ?_⟩
  simp only [if_neg hxc]

/-- Jump clause, `B₁⊃D` present: the ambient fires on the shifted first
component. -/
theorem grownAmb_of_jump_pres (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {A₁ B₁ D : PLLFormula}
    (hmem : (A₁.ifThen B₁).ifThen D ∈ Γ) (hD : D ∉ Γ) (hDS : D ∈ S)
    (hBD : B₁.ifThen D ∈ Γ) (hS : (A₁.ifThen B₁).ifThen D ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ))
    (hfst : G4c Δ ((itpE p S f c Γ).ifThen
      (itpA p S f c Γ (A₁.ifThen B₁)))) :
    G4c Δ (itpE p S f (c + 2) (D :: Γ)) := by
  rw [itpE_succ] at hamb
  exact fire (G4c.cut hamb
    (G4c.andAll_elim (amb_jump_mem_pres p S hmem hD hDS hBD hS)
      (G4c.identity_mem (.head _)))) (shift_imp p S hfst)

/-- Jump clause, `B₁⊃D` fresh: likewise, at the grown context. -/
theorem grownAmb_of_jump_fresh (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {A₁ B₁ D : PLLFormula}
    (hmem : (A₁.ifThen B₁).ifThen D ∈ Γ) (hD : D ∉ Γ) (hDS : D ∈ S)
    (hBD : B₁.ifThen D ∉ Γ) (hBDS : B₁.ifThen D ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ))
    (hfst : G4c Δ ((itpE p S f (c + 1) (B₁.ifThen D :: Γ)).ifThen
      (itpA p S f (c + 1) (B₁.ifThen D :: Γ) (A₁.ifThen B₁)))) :
    G4c Δ (itpE p S f (c + 2) (D :: Γ)) := by
  rw [itpE_succ] at hamb
  exact fire (G4c.cut hamb
    (G4c.andAll_elim (amb_jump_mem_fresh p S hmem hD hDS hBD hBDS)
      (G4c.identity_mem (.head _)))) (shift_imp p S hfst)

/-- γ-clause **continuation** disjunct: the ambient fires on the shifted boxed
component at the boxed context member's context. -/
theorem grownAmb_of_gammaCont (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {A B x : PLLFormula}
    (hmem : A.somehow.ifThen B ∈ Γ) (hB : B ∉ Γ) (hBS : B ∈ S)
    (hx : x.somehow ∈ Γ) (hxc : ¬(x ∈ Γ ∨ x ∉ S))
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ))
    (hbox : G4c Δ (((itpE p S f (c + 1) (x :: Γ)).ifThen
      (itpA p S f (c + 1) (x :: Γ) A.somehow)).somehow)) :
    G4c Δ (itpE p S f (c + 2) (B :: Γ)) := by
  rw [itpE_succ] at hamb
  exact fire (G4c.cut hamb
    (G4c.andAll_elim (amb_gammaCont_mem p S hmem hB hBS hx hxc)
      (G4c.identity_mem (.head _)))) (shift_box p S hbox)

/-- `(A₁⊃B₁)⊃D` with `B₁⊃D` **present** (the budget-gated jump disjunct). -/
theorem impJump_pres_case (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Γ' Δ : List PLLFormula} {A₁ B₁ D : PLLFormula} {q : String}
    (hF : (A₁.ifThen B₁).ifThen D ∈ Γ') (hD : D ∉ Γ') (hDS : D ∈ S)
    (hBD : B₁.ifThen D ∈ Γ') (hS : (A₁.ifThen B₁).ifThen D ∈ S)
    (hΓ'S : ∀ Y ∈ Γ', Y ∈ S)
    (hamb : G4c Δ (itpE p S (f + 2) (c + 2) Γ'))
    (hfst : G4c Δ ((itpE p S (f + 1) c Γ').ifThen
      (itpA p S (f + 1) c Γ' (A₁.ifThen B₁))))
    (hd : G4c Δ (itpA p S (f + 1) (c + 1) (D :: Γ') ((prop q).somehow)))
    (step : Step p S q f c Γ Γ' Δ) :
    G4c Δ (tgtClause p S (f + 1) c Γ q) :=
  tgtClause_fuel_lift p S
    (step (D :: Γ') D (fun y hy => .tail _ hy)
      (by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hDS
        · exact hΓ'S y hy)
      hDS (.head _) hD
      (grownAmb_of_jump_pres p S hF hD hDS hBD hS hamb hfst) hd)

/-- `(A₁⊃B₁)⊃D` with `B₁⊃D` **fresh** (the ungated jump disjunct). -/
theorem impJump_fresh_case (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Γ' Δ : List PLLFormula} {A₁ B₁ D : PLLFormula} {q : String}
    (hF : (A₁.ifThen B₁).ifThen D ∈ Γ') (hD : D ∉ Γ') (hDS : D ∈ S)
    (hBD : B₁.ifThen D ∉ Γ') (hBDS : B₁.ifThen D ∈ S)
    (hΓ'S : ∀ Y ∈ Γ', Y ∈ S)
    (hamb : G4c Δ (itpE p S (f + 2) (c + 2) Γ'))
    (hfst : G4c Δ ((itpE p S (f + 1) (c + 1) (B₁.ifThen D :: Γ')).ifThen
      (itpA p S (f + 1) (c + 1) (B₁.ifThen D :: Γ') (A₁.ifThen B₁))))
    (hd : G4c Δ (itpA p S (f + 1) (c + 1) (D :: Γ') ((prop q).somehow)))
    (step : Step p S q f c Γ Γ' Δ) :
    G4c Δ (tgtClause p S (f + 1) c Γ q) :=
  tgtClause_fuel_lift p S
    (step (D :: Γ') D (fun y hy => .tail _ hy)
      (by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hDS
        · exact hΓ'S y hy)
      hDS (.head _) hD
      (grownAmb_of_jump_fresh p S hF hD hDS hBD hBDS hamb hfst) hd)

/-- `◯A ⊃ B`, the **continuation** disjunct for a boxed context member `◯x`. -/
theorem gammaCont_case (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Γ' Δ : List PLLFormula} {A B x : PLLFormula} {q : String}
    (hF : A.somehow.ifThen B ∈ Γ') (h1 : B ∉ Γ') (h2 : B ∈ S)
    (hx : x.somehow ∈ Γ') (hxc : ¬(x ∈ Γ' ∨ x ∉ S))
    (hΓ'S : ∀ Y ∈ Γ', Y ∈ S)
    (hamb : G4c Δ (itpE p S (f + 2) (c + 2) Γ'))
    (hbox : G4c Δ (((itpE p S (f + 1) (c + 1) (x :: Γ')).ifThen
      (itpA p S (f + 1) (c + 1) (x :: Γ') A.somehow)).somehow))
    (hd : G4c Δ (itpA p S (f + 1) (c + 1) (B :: Γ') ((prop q).somehow)))
    (step : Step p S q f c Γ Γ' Δ) :
    G4c Δ (tgtClause p S (f + 1) c Γ q) :=
  tgtClause_fuel_lift p S
    (step (B :: Γ') B (fun y hy => .tail _ hy)
      (by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h2
        · exact hΓ'S y hy)
      h2 (.head _) h1
      (grownAmb_of_gammaCont p S hF h1 h2 hx hxc hamb hbox) hd)

/-! ## Discharging `BoxCtxCase`

The `◯χ` family does its work inside two boxes: the grown ambient arrives boxed
(`grown_box`) and the disjunct is boxed.  Both are opened — legitimate, because the
conclusion `tgtClause` is itself `◯`-shaped — and the recursion is applied at the
`⊳`-successor, which is why its hypothesis has to be context-polymorphic (§111). -/

theorem boxCtxCase (p : String) (S : Finset PLLFormula) (q : String) :
    BoxCtxCase p S q := by
  intro f c Γ Γ' Δ χ hχΓ' hχS hχfresh hΓ'S hgb hdb step
  -- open the boxed grown ambient
  refine G4c.cut hgb (G4c.laxL (.head _) ?_)
  -- open the disjunct, firing its guard from the grown ambient by budget monotonicity
  refine box_open (wksub (fun ψ h => .tail _ (.tail _ h)) hdb)
    (ambE p S (Nat.le_refl _) (Nat.le_succ _) rfl
      (G4c.identity_mem (.head _))) ?_
  -- recurse at `χ :: Γ'`, of strictly smaller defect, then lift the fuel
  refine tgtClause_fuel_lift p S ?_
  exact step _ (χ :: Γ') χ (fun y hy => .tail _ hy)
    (by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hχS
      · exact hΓ'S y hy)
    hχS (.head _) hχfresh
    (G4c.identity_mem (.tail _ (.head _)))
    (G4c.identity_mem (.head _))

/-! ## The traversal

Every obligation is now discharged in place: the `⊃`-headed environment families are
routed to the nine case lemmas above (§110's six plus the three §110 miscounted), the
`◯χ` family to `boxCtxCase`, the fuel-`0` floor to `zeroFuelCase`, and the truncation
to the traversal's own others-analysis.  So the traversal is **hypothesis-free** apart
from the standing scope assumptions (`∨`-free space, `q ≠ p`, `◯`-subformula closure). -/

set_option maxHeartbeats 4000000 in
/-- **The traversal.**  From the ambient and the second component at a grown context
`Γ'`, reach the boxed goal clause at `Γ`.  Recursion on the defect.

The mathematically substantive case is the **goal clause** (`boxGoal_remap`); the
environment families arrive by the grown-ambient table (§§98, 104, 107, 109 and the
three shapes added above); the truncation opens onto the others-analysis; the fuel-`0`
floor explodes. -/
theorem boxSnd_reaches (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S) :
    ∀ (d : Nat) (f c : Nat) (Γ Γ' Δ : List PLLFormula),
      defect S Γ' ≤ d → (∀ Y ∈ Γ', Y ∈ S) →
      G4c Δ (itpE p S (f + 1) (c + 2) Γ') →
      G4c Δ (itpA p S (f + 1) (c + 1) Γ' ((prop q).somehow)) →
      G4c Δ (tgtClause p S f c Γ q) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro f c Γ Γ' Δ hd hΓ'S hamb hsnd
  -- The disjunct-wise analysis of the *others* table, hoisted and made
  -- context-polymorphic so that the truncation branch can call it too.
  have othersOne : ∀ (Δ₀ : List PLLFormula) (φ : PLLFormula),
      φ ∈ itpAoth p S f (c + 1) Γ' ((prop q).somehow) →
      G4c Δ₀ (itpE p S (f + 1) (c + 2) Γ') → G4c Δ₀ φ →
      G4c Δ₀ (tgtClause p S f c Γ q) := by
    intro Δ₀ φ hoth hA hφd
    simp only [itpAoth] at hoth
    rcases List.mem_append.mp hoth with hgoal | henv
    · -- THE GOAL CLAUSE — the substantive case
      simp only [itpAgoal] at hgoal
      rcases List.mem_singleton.mp hgoal with rfl
      exact boxGoal_remap p S hOr hq hΓ'S
        (ambE p S (Nat.le_succ _) (Nat.le_refl _) rfl hA) hφd
    · cases f with
      | zero => exact zeroFuelCase p S hq c c Γ Γ' _ φ henv hφd
      | succ f' =>
          have step : Step p S q f' c Γ Γ' Δ₀ := by
            intro Γ'' w hsub hΓ''S hwS hwΓ'' hwΓ' hg'' hs''
            exact ihd (defect S Γ'')
              (by
                have := defect_lt_of_witness hsub hwS hwΓ'' hwΓ'
                omega)
              f' c Γ Γ'' Δ₀ (Nat.le_refl _) hΓ''S hg'' hs''
          simp only [itpAenv] at henv
          obtain ⟨F, hFΓ', hin⟩ := List.mem_flatMap.mp henv
          have hFS : F ∈ S := hΓ'S F hFΓ'
          cases F with
          | prop q' =>
              simp only at hin
              split at hin
              next hc =>
                exfalso
                have h2 : (prop q : PLLFormula).somehow = prop p := hc.2
                exact absurd h2 (by simp)
              next => cases hin
          | falsePLL => cases hin
          | or A B => exact absurd hFS (hOr A B)
          | somehow χ =>
              simp only at hin
              split at hin
              next => cases hin
              next hcond =>
                rcases List.mem_singleton.mp hin with rfl
                refine boxCtxCase p S q f' c Γ Γ' _ χ hFΓ' (hsome hFS)
                  (fun h => hcond (Or.inl h)) hΓ'S
                  (grown_box p S hFΓ' hcond hA) hφd ?_
                intro Δ' Γ'' w hsub hΓ''S hwS hwΓ'' hwΓ' hg'' hs''
                exact ihd (defect S Γ'')
                  (by
                    have := defect_lt_of_witness hsub hwS hwΓ'' hwΓ'
                    omega)
                  f' c Γ Γ'' Δ' (Nat.le_refl _) hΓ''S hg'' hs''
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  by_cases hAin : A ∈ Γ'
                  · have hB : B ∉ Γ' := fun hB => h1 ⟨hAin, hB⟩
                    have hBS : B ∈ S := h2.2.resolve_left hB
                    exact step (A :: B :: Γ') B
                      (fun y hy => .tail _ (.tail _ hy))
                      (by
                        intro y hy
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact hΓ'S _ hAin
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact hBS
                        · exact hΓ'S y hy)
                      hBS (.tail _ (.head _)) hB
                      (grown_and p S hFΓ' h1 h2 hA) hφd |> tgtClause_fuel_lift p S
                  · have hAS : A ∈ S := h2.1.resolve_left hAin
                    exact step (A :: B :: Γ') A
                      (fun y hy => .tail _ (.tail _ hy))
                      (by
                        intro y hy
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact hAS
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact (h2.2.elim (fun h => hΓ'S _ h) id)
                        · exact hΓ'S y hy)
                      hAS (.head _) hAin
                      (grown_and p S hFΓ' h1 h2 hA) hφd |> tgtClause_fuel_lift p S
                next => cases hin
          | ifThen A D =>
              -- THE `⊃`-HEADED FAMILIES: routing, shape by shape.  The budget is
              -- `c + 1`, a literal successor, so a gated shape has ONE FEWER `split`
              -- than the same shape has at a variable budget (PROGRESS §106).
              cases A with
              | falsePLL => cases hin
              | prop q' =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      split at hin
                      next h3 =>
                        rcases List.mem_singleton.mp hin with rfl
                        exact impAtom_pres_case p S hFΓ' h1 h2 h3 hΓ'S hA hφd step
                      next h3 =>
                        split at hin
                        next => cases hin
                        next h4 =>
                          rcases List.mem_singleton.mp hin with rfl
                          exact impAtom_fresh_case p S hFΓ' h1 h2 h3 h4 hΓ'S hA
                            (projAnd₁ hφd) (projAnd₂ hφd) step
                    next => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      exact impAnd_case p S hFΓ' h1 h2 hΓ'S hA hφd step
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      by_cases hAD : A₁.ifThen D ∈ Γ'
                      · have hBD : B₁.ifThen D ∉ Γ' := fun h => h1 ⟨hAD, h⟩
                        have hBDS : B₁.ifThen D ∈ S := h2.2.resolve_left hBD
                        exact step (A₁.ifThen D :: B₁.ifThen D :: Γ')
                          (B₁.ifThen D) (fun y hy => .tail _ (.tail _ hy))
                          (by
                            intro y hy
                            rcases List.mem_cons.mp hy with rfl | hy
                            · exact hΓ'S _ hAD
                            rcases List.mem_cons.mp hy with rfl | hy
                            · exact hBDS
                            · exact hΓ'S y hy)
                          hBDS (.tail _ (.head _)) hBD
                          (grown_impOr p S hFΓ' h1 h2 hA) hφd
                            |> tgtClause_fuel_lift p S
                      · have hADS : A₁.ifThen D ∈ S := h2.1.resolve_left hAD
                        exact impOr_case p S hFΓ' h1 h2 hΓ'S hAD hADS hA hφd step
                    next => cases hin
              | ifThen A₁ B₁ =>
                  -- deterministic: the `∈ S` guard is `hFS` itself, so rewrite
                  -- rather than `split` (which resolves it and throws the count)
                  simp only at hin
                  by_cases h1 : D ∈ Γ'
                  · simp only [if_pos h1] at hin; cases hin
                  simp only [if_neg h1] at hin
                  by_cases h2 : D ∈ S
                  case neg => simp only [if_neg h2] at hin; cases hin
                  simp only [if_pos h2] at hin
                  by_cases h3 : B₁.ifThen D ∈ Γ'
                  · simp only [if_pos h3, if_pos hFS] at hin
                    rcases List.mem_singleton.mp hin with rfl
                    exact impJump_pres_case p S hFΓ' h1 h2 h3 hFS hΓ'S hA
                      (projAnd₁ hφd) (projAnd₂ hφd) step
                  · simp only [if_neg h3] at hin
                    by_cases h4 : B₁.ifThen D ∈ S
                    · simp only [if_pos h4] at hin
                      rcases List.mem_singleton.mp hin with rfl
                      exact impJump_fresh_case p S hFΓ' h1 h2 h3 h4 hΓ'S hA
                        (projAnd₁ hφd) (projAnd₂ hφd) step
                    · simp only [if_neg h4] at hin; cases hin
              | somehow A₁ =>
                  simp only at hin
                  by_cases h1 : D ∈ Γ'
                  · simp only [if_pos h1] at hin; cases hin
                  simp only [if_neg h1] at hin
                  by_cases h2 : D ∈ S
                  case neg => simp only [if_neg h2] at hin; cases hin
                  simp only [if_pos h2, if_pos hFS] at hin
                  rcases List.mem_append.mp hin with hL | hR
                  · rcases List.mem_cons.mp hL with rfl | hL'
                    · exact gammaPlain_case p S hFΓ' hFS h1 h2 hΓ'S hA
                        (projAnd₁ hφd) (projAnd₂ hφd) step
                    · rcases List.mem_singleton.mp hL' with rfl
                      exact gammaBox_case p S hFΓ' hFS h1 h2 hΓ'S hA
                        (projAnd₁ hφd) (projAnd₂ hφd) step
                  · obtain ⟨X, hXΓ', hXin⟩ := List.mem_filterMap.mp hR
                    cases X with
                    | prop _ => cases hXin
                    | falsePLL => cases hXin
                    | and _ _ => cases hXin
                    | or _ _ => cases hXin
                    | ifThen _ _ => cases hXin
                    | somehow x =>
                        simp only at hXin
                        by_cases hx : x ∈ Γ' ∨ x ∉ S
                        · simp only [if_pos hx] at hXin
                          cases hXin
                        · simp only [if_neg hx] at hXin
                          rcases Option.some_inj.mp hXin with rfl
                          exact gammaCont_case p S hFΓ' h1 h2 hXΓ' hx hΓ'S hA
                            (projAnd₁ hφd) (projAnd₂ hφd) step
  -- the whole others-disjunction, from the same analysis
  have othersAll : ∀ (Δ₀ : List PLLFormula),
      G4c Δ₀ (itpE p S (f + 1) (c + 2) Γ') →
      G4c Δ₀ (orAll (itpAoth p S f (c + 1) Γ' ((prop q).somehow))) →
      G4c Δ₀ (tgtClause p S f c Γ q) := by
    intro Δ₀ hA hor
    refine G4c.cut hor (G4c.orAll_elim ?_)
    intro φ hφ
    exact othersOne (φ :: Δ₀) φ hφ (hA.weaken φ) (G4c.identity_mem (.head _))
  rw [itpA_succ] at hsnd
  refine G4c.cut hsnd (G4c.orAll_elim ?_)
  intro φ hφ
  have hA : G4c (φ :: Δ) (itpE p S (f + 1) (c + 2) Γ') := hamb.weaken φ
  have hφd : G4c (φ :: Δ) φ := G4c.identity_mem (.head _)
  simp only [itpAfull] at hφ
  rcases List.mem_append.mp hφ with hoth | htr
  · exact othersOne (φ :: Δ) φ hoth hA hφd
  · -- THE TRUNCATION.  Its body is the others-table *without* the truncation,
    -- so opening the box against the `◯`-shaped target and firing the guard
    -- from the ambient lands on `othersAll` — no measure, no pairing.
    by_cases he : (itpAoth p S f (c + 1) Γ' ((prop q).somehow)).isEmpty = true
    · rw [if_pos he] at htr; cases htr
    · rw [if_neg he] at htr
      rcases List.mem_singleton.mp htr with rfl
      refine box_open hφd (ambE p S (Nat.le_succ _) (by omega) rfl hA) ?_
      exact othersAll _ (hA.weaken _) (G4c.identity_mem (.head _))


end BoxSnd
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.BoxSnd.grown_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.BoxSnd.grown_and

/-- info: 'PLLND.BoxSnd.grown_box' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.BoxSnd.grown_box

/--
info: 'PLLND.BoxSnd.boxSnd_reaches' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.boxSnd_reaches

/--
info: 'PLLND.BoxSnd.zeroFuelCase' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.zeroFuelCase

/--
info: 'PLLND.BoxSnd.shift_box' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.shift_box

/--
info: 'PLLND.BoxSnd.grownAmb_of_box_shifted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.grownAmb_of_box_shifted

/-- info: 'PLLND.BoxSnd.boxCtxCase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.BoxSnd.boxCtxCase

/-! The three `⊃`-shapes §110's table missed. -/

/--
info: 'PLLND.BoxSnd.grownAmb_of_jump_pres' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.grownAmb_of_jump_pres

/--
info: 'PLLND.BoxSnd.grownAmb_of_jump_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.grownAmb_of_jump_fresh

/--
info: 'PLLND.BoxSnd.grownAmb_of_gammaCont' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.grownAmb_of_gammaCont

/--
info: 'PLLND.BoxSnd.impJump_pres_case' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.impJump_pres_case

/--
info: 'PLLND.BoxSnd.impJump_fresh_case' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.impJump_fresh_case

/--
info: 'PLLND.BoxSnd.gammaCont_case' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.gammaCont_case

/-! **The traversal is unconditional.**  Pinned as a statement check: the type below
mentions only the scope assumptions (`∨`-free `S`, `q ≠ p`, `◯`-subformula closure),
no `BoxCtxCase`/`TruncCase`/`ImpCase`/`ZeroFuelCase` hypothesis. -/

/--
info: PLLND.BoxSnd.boxSnd_reaches (p : String) (S : Finset PLLFormula) (hOr : ∀ (A B : PLLFormula), A.or B ∉ S) {q : String}
  (hq : q ≠ p) (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S) (d f c : ℕ) (Γ Γ' Δ : List PLLFormula) :
  PLLND.defect S Γ' ≤ d →
    (∀ Y ∈ Γ', Y ∈ S) →
      PLLND.G4c Δ (PLLND.itpE p S (f + 1) (c + 2) Γ') →
        PLLND.G4c Δ (PLLND.itpA p S (f + 1) (c + 1) Γ' (prop q).somehow) →
          PLLND.G4c Δ (PLLND.BoxSnd.tgtClause p S f c Γ q)
-/
#guard_msgs in
#check PLLND.BoxSnd.boxSnd_reaches
