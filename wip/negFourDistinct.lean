import LaxLogic.PLLCountermodelEmit
import wip.negFour

/-!
# The four are distinct, so the booleanization is EXACTLY four

`wip/negFour.lean` proves `¬A` is always one of `⊥, ¬◯⊥, ¬¬◯⊥, ⊤`.  This file
proves those four pairwise non-interderivable, which upgrades "at most four"
to "exactly four".

Matthew's argument, 2026-08-07, which needs only two models and one syntactic
step:

* `¬◯⊥` is valid in every **infallible** model, and `⊥` is valid in none — so
  they are not interderivable, or soundness breaks;
* `¬◯⊥` is invalid in some **fallible** model, and `⊤` is valid everywhere —
  so `¬◯⊥ ≠ ⊤`;
* infallible models invalidate `¬¬◯⊥`, so `¬¬◯⊥ ≠ ⊤`; and `¬¬◯⊥` is valid in
  some fallible model while `⊥` is not, so `¬¬◯⊥ ≠ ⊥`;
* `¬◯⊥ ≠ ¬¬◯⊥`: if `¬◯⊥ ⊢ ¬¬◯⊥` then, since `¬¬◯⊥` **is** `¬(¬◯⊥)`, we get
  `¬◯⊥ ⊢ ⊥` and hence `⊢ ¬¬◯⊥`, which the previous clause just excluded.
  So this one is syntactic, given the model facts;
* `⊥ ≠ ⊤` needs no argument.

Two models suffice.

    M₁ = one world, no fallible worlds        (infallible)
    M₂ = 0 ⊑ 1 with 1 fallible and 0 Rₘ 1     (◯⊥ holds at 0, ⊥ does not)

`M₁` alone gives four of the six facts.
-/

open PLLFormula PLLND

namespace NegFourDistinct

/-- `¬◯⊥`. -/
def nb : PLLFormula := (falsePLL.somehow).ifThen falsePLL
/-- `¬¬◯⊥`. -/
def nnb : PLLFormula := nb.ifThen falsePLL

/-- One world, nothing fallible.  `◯⊥` fails, so `¬◯⊥` holds and `¬¬◯⊥` fails;
`⊥` fails because there is no fallible world. -/
def M₁ : FinCM := ⟨1, [], [], [], []⟩

/-- `0 ⊑ 1` with `1` fallible and `0 Rₘ 1`.  At `0`: `⊥` fails, `◯⊥` holds, so
`¬◯⊥` fails and `¬¬◯⊥` holds. -/
def M₂ : FinCM := ⟨2, [(0,1)], [(0,1)], [1], []⟩

/-! ## The six underivabilities -/

/-- `¬◯⊥ ⊬ ⊥` — the infallible model forces `¬◯⊥` and not `⊥`. -/
theorem nb_not_bot : ¬ Nonempty (LaxND [nb] falsePLL) :=
  FinCM.not_provable_of_check (M := M₁) (w := 0) (by decide)

/-- `⊬ ¬¬◯⊥` — infallible models invalidate it. -/
theorem not_nnb : ¬ Nonempty (LaxND [] nnb) :=
  FinCM.not_provable_of_check (M := M₁) (w := 0) (by decide)

/-- `¬◯⊥ ⊬ ¬¬◯⊥`, directly. -/
theorem nb_not_nnb : ¬ Nonempty (LaxND [nb] nnb) :=
  FinCM.not_provable_of_check (M := M₁) (w := 0) (by decide)

/-- `⊬ ⊥` — consistency. -/
theorem not_bot : ¬ Nonempty (LaxND [] falsePLL) :=
  FinCM.not_provable_of_check (M := M₁) (w := 0) (by decide)

/-- `⊬ ¬◯⊥` — F&M's "no D axiom", here from the fallible model. -/
theorem not_nb : ¬ Nonempty (LaxND [] nb) :=
  FinCM.not_provable_of_check (M := M₂) (w := 0) (by decide)

/-- `¬¬◯⊥ ⊬ ⊥` — the fallible model forces `¬¬◯⊥` and not `⊥`. -/
theorem nnb_not_bot : ¬ Nonempty (LaxND [nnb] falsePLL) :=
  FinCM.not_provable_of_check (M := M₂) (w := 0) (by decide)

/-! ## The `⊤`-side versions, so every pair is stated the same way -/

/-- `⊤ ⊬ ⊥`. -/
theorem top_not_bot : ¬ Nonempty (LaxND [truePLL] falsePLL) :=
  FinCM.not_provable_of_check (M := M₁) (w := 0) (by decide)

/-- `⊤ ⊬ ¬¬◯⊥`. -/
theorem top_not_nnb : ¬ Nonempty (LaxND [truePLL] nnb) :=
  FinCM.not_provable_of_check (M := M₁) (w := 0) (by decide)

/-- `⊤ ⊬ ¬◯⊥`. -/
theorem top_not_nb : ¬ Nonempty (LaxND [truePLL] nb) :=
  FinCM.not_provable_of_check (M := M₂) (w := 0) (by decide)

/-! ## The classification, assembled -/

/-- Interderivability in plain PLL. -/
def Interd' (A B : PLLFormula) : Prop :=
  Nonempty (LaxND [A] B) ∧ Nonempty (LaxND [B] A)

/-- **The four values of `¬` on the closed fragment are pairwise distinct.**
With `neg_exactly_four` (`wip/negFour.lean`), which says every `¬A` is one of
them, this makes the booleanization `𝔟⊥` of RN(◯,{}) **exactly four
elements** — the free boolean algebra on one generator. -/
theorem four_pairwise_distinct :
    ¬ Interd' falsePLL nb ∧ ¬ Interd' falsePLL nnb ∧ ¬ Interd' falsePLL truePLL ∧
      ¬ Interd' nb nnb ∧ ¬ Interd' nb truePLL ∧ ¬ Interd' nnb truePLL :=
  ⟨fun h => nb_not_bot h.2,
   fun h => nnb_not_bot h.2,
   fun h => top_not_bot h.2,
   fun h => nb_not_nnb h.1,
   fun h => top_not_nb h.2,
   fun h => top_not_nnb h.2⟩

end NegFourDistinct

/-! ### Axiom audit — measured and pinned on creation (2026-08-07). -/

/-- info: 'NegFourDistinct.nb_not_bot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NegFourDistinct.nb_not_bot

/-- info: 'NegFourDistinct.not_nnb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NegFourDistinct.not_nnb

/-- info: 'NegFourDistinct.not_nb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NegFourDistinct.not_nb

/-- info: 'NegFourDistinct.four_pairwise_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NegFourDistinct.four_pairwise_distinct
