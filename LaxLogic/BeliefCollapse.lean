import Mathlib

/-!
# Classical belief is degenerate: every nucleus on a Boolean algebra is closed

This mechanises the hinge of the "classical belief is degenerate" argument
(handover §2A / §3b-1).  Reading `◯M` as "M is believed", a believer is a
**nucleus** `j` on the algebra of propositions: an inflationary, idempotent,
meet-preserving map.  This is `Mathlib`'s `Nucleus`.

The result: on a Boolean algebra every nucleus is the **closed** nucleus

    j x = x ⊔ j ⊥.

So a classical believer believes exactly the truths together with one fixed
proposition `a = j ⊥` (a "dogma") and its consequences — the one-parameter
family `c_a(x) = x ⊔ a`.  The two extremes are the doxastic poles:

* `j ⊥ = ⊥`  gives  `j = id`         — the **total sceptic** (`◯M ⟺ M`);
* `j ⊥ = ⊤`  gives  `j = fun _ ↦ ⊤`  — the **totally credulous** (`◯M ⟺ ⊤`).

The proof uses only the Boolean law `x ⊔ xᶜ = ⊤`, distributivity, and the
nucleus laws (inflationarity + meet-preservation); idempotence is not needed.
-/

namespace BeliefLax

section Heyting
variable {H : Type*} [HeytingAlgebra H]

/-- The **closed** nucleus `c_b(x) = x ⊔ b` — dogmatic belief in `b`.
(Shared base definition; `BeliefBooleanIso` and `BeliefOpenClosed` build on
it.) -/
def closedNucleus (b : H) : Nucleus H where
  toFun x := x ⊔ b
  map_inf' x y := by rw [sup_inf_right]
  le_apply' x := le_sup_left
  idempotent' x := le_of_eq (by rw [sup_assoc, sup_idem])

@[simp] lemma closedNucleus_apply (b x : H) : closedNucleus b x = x ⊔ b := rfl

end Heyting

variable {B : Type*} [BooleanAlgebra B]

/-- **The Boolean collapse.**  Every nucleus on a Boolean algebra `B` is the
closed nucleus `x ↦ x ⊔ j ⊥`. -/
theorem nucleus_eq_sup_bot (j : Nucleus B) (x : B) : j x = x ⊔ j ⊥ := by
  apply le_antisymm
  · -- `j x = (j x ⊓ x) ⊔ (j x ⊓ xᶜ) = x ⊔ (j x ⊓ xᶜ) ≤ x ⊔ j ⊥`.
    have hsplit : j x = x ⊔ (j x ⊓ xᶜ) := by
      calc j x = j x ⊓ ⊤ := by rw [inf_top_eq]
        _ = j x ⊓ (x ⊔ xᶜ) := by rw [sup_compl_eq_top]
        _ = (j x ⊓ x) ⊔ (j x ⊓ xᶜ) := by rw [inf_sup_left]
        _ = x ⊔ (j x ⊓ xᶜ) := by rw [inf_eq_right.mpr j.le_apply]
    -- meet-preservation pins the second summand below `j ⊥`.
    have hle : j x ⊓ xᶜ ≤ j ⊥ := by
      have h1 : j x ⊓ xᶜ ≤ j x ⊓ j xᶜ := inf_le_inf le_rfl j.le_apply
      have h2 : j x ⊓ j xᶜ = j ⊥ := by rw [← j.map_inf, inf_compl_eq_bot]
      exact h1.trans_eq h2
    calc j x = x ⊔ (j x ⊓ xᶜ) := hsplit
      _ ≤ x ⊔ j ⊥ := sup_le_sup_left hle x
  · -- `x ⊔ j ⊥ ≤ j x`: inflationarity gives `x ≤ j x`, monotonicity `j ⊥ ≤ j x`.
    exact sup_le j.le_apply (j.monotone bot_le)

/-- The **total sceptic**: `j ⊥ = ⊥` forces `j = id`, i.e. `◯M ⟺ M`. -/
theorem eq_id_of_bot_eq_bot (j : Nucleus B) (h : j ⊥ = ⊥) (x : B) : j x = x := by
  rw [nucleus_eq_sup_bot j x, h, sup_bot_eq]

/-- The **totally credulous** believer: `j ⊥ = ⊤` forces `j x = ⊤`, i.e. `◯M ⟺ ⊤`. -/
theorem eq_top_of_bot_eq_top (j : Nucleus B) (h : j ⊥ = ⊤) (x : B) : j x = ⊤ := by
  rw [nucleus_eq_sup_bot j x, h, sup_top_eq]

end BeliefLax

#print axioms BeliefLax.nucleus_eq_sup_bot
#print axioms BeliefLax.eq_id_of_bot_eq_bot
#print axioms BeliefLax.eq_top_of_bot_eq_top
