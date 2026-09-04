import Mathlib

/-!
# Believers on small Heyting algebras, machine-computed (§3b-5)

A believer is a nucleus `j` — inflationary, idempotent, meet-preserving.  On a
finite `SemilatticeInf` this is a *decidable* predicate, so we enumerate the
believers on small algebras and exhibit sceptic / credulous / intermediate ones
side by side.

`decide` (kernel-checked, axiom-clean) is used where it is fast; the two
enumerations over 256-element function spaces use `native_decide`, which adds the
`Lean.ofReduceBool` axiom to *those two* audits — flagged, per the mandate.
-/

namespace BeliefLax

/-- `j` is a **nucleus** (believer): inflationary, idempotent, meet-preserving. -/
abbrev IsNucleusFun {H : Type*} [SemilatticeInf H] [Fintype H] [DecidableEq H]
    [DecidableLE H] (j : H → H) : Prop :=
  (∀ x, x ≤ j x) ∧ (∀ x, j (j x) = j x) ∧ (∀ x y, j (x ⊓ y) = j x ⊓ j y)

/-! ### The 3-element chain `Fin 3` (`⊥ < m < ⊤`): exactly four believers -/

/-- The 3-chain has exactly **four** nuclei. -/
theorem chain3_card :
    (Finset.univ.filter fun j : Fin 3 → Fin 3 => IsNucleusFun j).card = 4 := by decide

/-- Total **sceptic** `j = id` (`◯M ⟺ M`). -/
theorem chain3_sceptic : IsNucleusFun (id : Fin 3 → Fin 3) := by decide
/-- Totally **credulous** `j = fun _ => ⊤` (`◯M ⟺ ⊤`). -/
theorem chain3_credulous : IsNucleusFun (fun _ => (2 : Fin 3)) := by decide
/-- **Closed** (dogmatic) `c_m(x) = x ⊔ m`, i.e. `[0↦1, 1↦1, 2↦2]`. -/
theorem chain3_closed : IsNucleusFun (![1, 1, 2] : Fin 3 → Fin 3) := by decide
/-- **Open** (hypothetical) `u_m(x) = m ⇨ x`, i.e. `[0↦0, 1↦2, 2↦2]`. -/
theorem chain3_open : IsNucleusFun (![0, 2, 2] : Fin 3 → Fin 3) := by decide
/-- Open ≠ closed *already on the 3-chain* — constructive richness (cf. §3b-2). -/
theorem chain3_open_ne_closed : (![0, 2, 2] : Fin 3 → Fin 3) ≠ ![1, 1, 2] := by decide

/-! ### The 4-element chain `Fin 4`: eight believers -/

/-- The 4-chain has exactly **eight** nuclei. -/
theorem chain4_card :
    (Finset.univ.filter fun j : Fin 4 → Fin 4 => IsNucleusFun j).card = 8 := by native_decide

/-! ### The 2×2 Boolean algebra `Fin 2 × Fin 2` (non-linear): four believers -/

/-- The 4-element Boolean algebra `2 × 2` has exactly **four** nuclei = its four
elements — a machine-computed instance of the collapse `N(B) ≅ B` (§3b-1). -/
theorem boolean22_card :
    (Finset.univ.filter fun j : Fin 2 × Fin 2 → Fin 2 × Fin 2 => IsNucleusFun j).card = 4 := by
  native_decide

end BeliefLax

#print axioms BeliefLax.chain3_card
#print axioms BeliefLax.chain3_open_ne_closed
#print axioms BeliefLax.chain4_card
#print axioms BeliefLax.boolean22_card
