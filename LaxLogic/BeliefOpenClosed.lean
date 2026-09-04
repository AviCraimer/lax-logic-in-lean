import LaxLogic.BeliefCollapse

/-!
# Open vs closed nuclei: hypothetical belief is invisible classically (§3b-2)

Two standard families of nuclei (believers) on a Heyting algebra `H`:

* **closed**  `c_b(x) = x ⊔ b`   — dogmatic belief in `b`;
* **open**    `u_a(x) = a ⇨ x`   — *hypothetical* belief ("I would believe x given a").

On a **Boolean** algebra the open family collapses into the closed one,
`a ⇨ x = x ⊔ aᶜ`, so `u_a = c_{aᶜ}` — hypothetical belief is invisible
classically (`openNucleus_eq_closedNucleus`).  On a Heyting algebra `u_a` and
`c_{aᶜ}` agree at `a` *only if* excluded middle holds at `a`
(`em_of_openNucleus_eq_closedNucleus`); where it fails they differ, as on the
3-element chain `Fin 3` (`open_ne_closed_Fin3`).  So hypothetical belief is a
genuinely distinct attitude constructively.
-/

namespace BeliefLax

section Heyting
variable {H : Type*} [HeytingAlgebra H]

/-- The **open** nucleus `u_a(x) = a ⇨ x` — hypothetical belief. -/
def openNucleus (a : H) : Nucleus H where
  toFun x := a ⇨ x
  map_inf' x y := himp_inf_distrib a x y
  le_apply' x := le_himp_iff.mpr inf_le_left
  idempotent' x := le_of_eq (by rw [himp_himp, inf_idem])

-- `closedNucleus` and `closedNucleus_apply` come from `BeliefCollapse`
-- (the shared base module).

@[simp] lemma openNucleus_apply (a x : H) : openNucleus a x = a ⇨ x := rfl

/-- If the open nucleus `u_a` equals the closed nucleus `c_{aᶜ}`, then excluded
middle holds at `a`: `a ⊔ aᶜ = ⊤`.  (Evaluate at `a`; `a ⇨ a = ⊤`.) -/
theorem em_of_openNucleus_eq_closedNucleus (a : H)
    (h : openNucleus a = closedNucleus aᶜ) : a ⊔ aᶜ = ⊤ := by
  have h2 := DFunLike.congr_fun h a
  simp only [openNucleus_apply, closedNucleus_apply, himp_self] at h2
  exact h2.symm

end Heyting

/-- **Open = closed on a Boolean algebra.**  Hypothetical belief `u_a` collapses
to dogmatic belief `c_{aᶜ}`: `a ⇨ x = x ⊔ aᶜ`, so `u_a = c_{aᶜ}`. -/
theorem openNucleus_eq_closedNucleus {B : Type*} [BooleanAlgebra B] (a : B) :
    openNucleus a = closedNucleus aᶜ := by
  ext x
  simp only [openNucleus_apply, closedNucleus_apply, himp_eq]

end BeliefLax

#print axioms BeliefLax.openNucleus
#print axioms BeliefLax.closedNucleus
#print axioms BeliefLax.em_of_openNucleus_eq_closedNucleus
#print axioms BeliefLax.openNucleus_eq_closedNucleus

/-- **Open ≠ closed on a non-Boolean Heyting algebra.**  On the 3-element chain
`Fin 3`, `u_1 ≠ c_{1ᶜ}`, since `1 ⊔ 1ᶜ = 1 ≠ ⊤`: hypothetical belief is a
genuinely distinct attitude constructively. -/
theorem BeliefLax.open_ne_closed_Fin3 :
    BeliefLax.openNucleus (1 : Fin 3) ≠ BeliefLax.closedNucleus (1 : Fin 3)ᶜ := by
  intro h
  have := BeliefLax.em_of_openNucleus_eq_closedNucleus (1 : Fin 3) h
  revert this
  decide

#print axioms BeliefLax.open_ne_closed_Fin3
