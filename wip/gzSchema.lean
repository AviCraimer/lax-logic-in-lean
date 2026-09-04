import wip.collapse

/-!
# The Ghilardi–Zawadowski shape, family-general — and the exact verdict on the analogy

**All PLL.**  This file formalises the observation that drove the
2026-08-03/04 campaign: that the RN(◯,{}) chain/antichain
constructions instantiate "the same conditions" as the
Ghilardi–Zawadowski (GZ) refutation of uniform interpolation in S4 —
and records precisely which half of that observation was TRUE and
which half is now REFUTED.

**The GZ shape** (S4, classical; Ghilardi–Zawadowski, Studia Logica
55 (1995) 259–271; exposition in Bílková's thesis §3.1).  A witness
formula `B` entails every member of an infinite strictly descending
chain `D 0 > D 1 > …` of formulas in the RETAINED fragment, while no
retained-fragment formula lies in the consequence filter below the
whole chain; hence the filter has no minimum and the post-interpolant
`∃p̄.B` does not exist.  The schema below states exactly this
implication for an arbitrary ℕ-indexed variable-free family `D` — it
is the family-general form of `no_post_interp_schema`
(wip/uiObstruct.lean), and its proof is the same three lines.  Note
what the schema does and does not need: it needs `D` to be
variable-free and `φ` to dominate it (`hg`) with an empty landing set
(`hL`); it does NOT need `D` to be a chain, an antichain, or
descending — that structure is only needed to make `hL` PLAUSIBLE,
never to run the argument.

**The verdict on the analogy**, in two levels:

* AMBIENT level — the retained fragment contains the GZ order
  structure — TRUE and PROVED: the descending chain
  (`Gmeet_desc_strict`), its floorlessness (`gap_no_glb`), infinite
  width (`gap_incomparable`).  RN(◯,{}) has everything the
  one-variable q-fragment of S4 has.
* FILTER level — some φ's consequence filter contains the descent
  with an empty landing set — REFUTED at the gap family:
  `gz_gap_uninhabited` below (a restatement of
  `post_interp_schema_vacuous`, i.e. of the collapse theorem) shows
  the gap instance of the schema can NEVER fire.  In S4 the analogous
  instance DOES fire: the GZ witness
  `B = p₁ ∧ □(p₁→◇p₂) ∧ □(p₂→◇p₁) ∧ □(p₁→q) ∧ □(p₂→¬q)` dominates
  the q-alternation chain `Eₙ` on a two-element cluster
  (w₁ ⇄ w₂), which realises INFINITE alternation depth in a finite
  model.  PLL's intuitionistic frames have no such clusters —
  heredity forces rank to descend — and `rank_bound`/`collapse` are
  the theorem form of that prohibition.

So the observation was sound as a SCHEMA (it compiles, axiom-free,
below) and sound at the ambient level; the conjecture that the gap
instance was inhabitable is what died, and it died as a theorem, not
as a retreat.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-- **The GZ ∃-side schema, family-general**: if `φ` dominates an
arbitrary variable-free family `D` and no variable-free formula below
the whole family is a consequence of `φ`, then `φ` has no uniform
post-interpolant.  No order structure on `D` is needed. -/
theorem no_post_interp_schema_family {φ : PLLFormula} (D : Nat → PLLFormula)
    (hDa : ∀ k, atomFree (D k) = true)
    (hg : ∀ k, Deriv [φ] (D k))
    (hL : ∀ χ, atomFree χ = true → (∀ k, Deriv [χ] (D k)) → ¬ Deriv [φ] χ) :
    ¬ ∃ ψ, IsPostInterp φ ψ := by
  rintro ⟨ψ, hψa, hφψ, hmin⟩
  exact hL ψ hψa (fun k => hmin (D k) (hDa k) (hg k)) hφψ

/-- **The GZ ∀-side schema, family-general** (the dual). -/
theorem no_pre_interp_schema_family {φ : PLLFormula} (D : Nat → PLLFormula)
    (hDa : ∀ k, atomFree (D k) = true)
    (hc : ∀ k, Deriv [D k] φ)
    (hU : ∀ χ, atomFree χ = true → (∀ k, Deriv [D k] χ) → ¬ Deriv [χ] φ) :
    ¬ ∃ ψ, IsPreInterp φ ψ := by
  rintro ⟨ψ, hψa, hψφ, hmax⟩
  exact hU ψ hψa (fun k => hmax (D k) (hDa k) (hc k)) hψφ

/-- The gap antichain is an instance of the family schema (the schema
the campaign actually ran, `no_post_interp_schema`, is this at
`D k = gap (k+1)`). -/
theorem gap_family_instance {φ : PLLFormula}
    (hg : ∀ k, Deriv [φ] (gap (k + 1)))
    (hL : ∀ χ, atomFree χ = true → (∀ k, Deriv [χ] (gap (k + 1))) →
      ¬ Deriv [φ] χ) :
    ¬ ∃ ψ, IsPostInterp φ ψ :=
  no_post_interp_schema_family (fun k => gap (k + 1))
    (fun k => gap_atomFree (k + 1)) hg hL

/-- **The verdict, ∃-side**: at the gap family the schema's hypotheses
are jointly CONTRADICTORY — the collapse theorem in the family
schema's own indexing.  The GZ shape is correct; the gap instance can
never fire. -/
theorem gz_gap_uninhabited {φ : PLLFormula}
    (hg : ∀ k, Deriv [φ] (gap (k + 1)))
    (hL : ∀ χ, atomFree χ = true → (∀ k, Deriv [χ] (gap (k + 1))) →
      ¬ Deriv [φ] χ) : False := by
  refine post_interp_schema_vacuous (φ := φ) ?_ ?_
  · intro k hk
    match k, hk with
    | (j + 1), _ => exact hg j
  · intro ψ ha hψ
    exact hL ψ ha (fun k => hψ (k + 1) (by omega))

/-- **The verdict, ∀-side**: at the c-chain the dual schema's
hypotheses are jointly contradictory (`rungbound`'s theorem in the
family indexing). -/
theorem gz_chain_uninhabited {φ : PLLFormula}
    (hc : ∀ k, Deriv [chainF k] φ)
    (hU : ∀ χ, atomFree χ = true → (∀ k, Deriv [chainF k] χ) →
      ¬ Deriv [χ] φ) : False :=
  pre_interp_schema_vacuous hc hU

/-! ## Axiom audits — sorry-free, all PLL -/

/-- info: 'PLLND.RNEmbed.no_post_interp_schema_family' does not depend on any axioms -/
#guard_msgs in
#print axioms no_post_interp_schema_family

/-- info: 'PLLND.RNEmbed.no_pre_interp_schema_family' does not depend on any axioms -/
#guard_msgs in
#print axioms no_pre_interp_schema_family

/-- info: 'PLLND.RNEmbed.gap_family_instance' does not depend on any axioms -/
#guard_msgs in
#print axioms gap_family_instance

/-- info: 'PLLND.RNEmbed.gz_gap_uninhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gz_gap_uninhabited

/-- info: 'PLLND.RNEmbed.gz_chain_uninhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gz_chain_uninhabited

end RNEmbed
end PLLND
