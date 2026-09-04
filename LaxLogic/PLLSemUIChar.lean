import LaxLogic.PLLSemUIFrag

/-!
# Characters over the finite fragment

The pointwise ingredients of the repaired pillar 2 (their Theorem
4.7, in the escape form): for a world `w` and a representative list
`L` of the rank-bounded p-free fragment, the CHARACTERS

  θ⁺ := ⋀ { D ∈ L | w ⊩ D },    θ⁻ := ⋁ { D ∈ L | w ⊮ D }

capture `w`'s fragment type: `w` forces θ⁺ (`force_charPos`); a
NON-fallible `w` refutes θ⁻ (`not_force_charNeg` — a fallible world
forces everything, which is exactly the refuted obstruction and why
the escape clauses carve fallible targets out); and any world forcing
θ⁺ while refuting θ⁻ agrees with `w` on the whole list
(`agree_of_char`).  With `frag_reps_exist'` supplying `L`, these are
the raw material for `Z α := agreement at rank α` satisfying the
`LayeredBisimE` clauses — that induction is the recorded next step.
-/

open PLLFormula

namespace PLLND
namespace SemUI

attribute [local instance] Classical.propDecidable

/-! ## Semantic forcing of the finite connectives -/

/-- Forcing `bigAnd` is forcing every conjunct (the empty conjunction
is `⊤` = `⊥ → ⊥`, forced everywhere). -/
theorem force_bigAnd_iff (C : ConstraintModel) (w : C.W) :
    ∀ (T : List PLLFormula),
      (C.force w (bigAnd T) ↔ ∀ D ∈ T, C.force w D) := by
  intro T
  induction T with
  | nil =>
      simp only [bigAnd]
      constructor
      · intro _ D hD
        exact absurd hD (List.not_mem_nil)
      · intro _ v _ h
        exact h
  | cons φ l ih =>
      cases l with
      | nil =>
          simp only [bigAnd]
          constructor
          · intro h D hD
            rcases List.mem_singleton.mp hD with rfl
            exact h
          · intro h
            exact h φ (List.mem_singleton_self _)
      | cons ψ l' =>
          have hstep : C.force w (bigAnd (φ :: ψ :: l')) ↔
              C.force w φ ∧ C.force w (bigAnd (ψ :: l')) := Iff.rfl
          rw [hstep, ih]
          constructor
          · rintro ⟨h1, h2⟩ D hD
            rcases List.mem_cons.mp hD with rfl | hD
            · exact h1
            · exact h2 D hD
          · intro h
            exact ⟨h φ (List.mem_cons_self ..),
              fun D hD => h D (List.mem_cons_of_mem _ hD)⟩

/-- Forcing a member of a list forces its `bigOr`. -/
theorem force_bigOr_of_mem {C : ConstraintModel} {w : C.W}
    {S : List PLLFormula} {τ : PLLFormula} (hm : τ ∈ S)
    (hτ : C.force w τ) : C.force w (bigOr S) := by
  induction S with
  | nil => exact absurd hm (List.not_mem_nil)
  | cons σ S ih =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Or.inl hτ
      · exact Or.inr (ih hm)

/-! ## Characters -/

/-- The positive character of `w` on the list `L`: the conjunction of
the members it forces. -/
noncomputable def charPos (C : ConstraintModel) (w : C.W)
    (L : List PLLFormula) : PLLFormula :=
  bigAnd (L.filter (fun D => decide (C.force w D)))

/-- The negative character: the disjunction of the members it
refutes. -/
noncomputable def charNeg (C : ConstraintModel) (w : C.W)
    (L : List PLLFormula) : PLLFormula :=
  bigOr (L.filter (fun D => decide (¬ C.force w D)))

/-- A world forces its own positive character. -/
theorem force_charPos (C : ConstraintModel) (w : C.W)
    (L : List PLLFormula) : C.force w (charPos C w L) := by
  rw [charPos, force_bigAnd_iff]
  intro D hD
  exact of_decide_eq_true (List.mem_filter.mp hD).2

/-- A NON-fallible world refutes its own negative character.  (The
fallibility hypothesis is essential — the machine-checked obstruction
`layered_of_frag_agree_refuted` lives exactly here.) -/
theorem not_force_charNeg (C : ConstraintModel) {w : C.W}
    (hw : w ∉ C.F) (L : List PLLFormula) :
    ¬ C.force w (charNeg C w L) := by
  intro h
  rcases force_bigOr_cases h with ⟨τ, hm, hτ⟩ | hF
  · exact of_decide_eq_true (List.mem_filter.mp hm).2 hτ
  · exact hw hF

/-- **Character transfer**: a world forcing `w`'s positive character
and refuting its negative character agrees with `w` on the whole
list. -/
theorem agree_of_char {C N : ConstraintModel} {w : C.W} {v : N.W}
    {L : List PLLFormula}
    (hpos : N.force v (charPos C w L))
    (hneg : ¬ N.force v (charNeg C w L)) :
    ∀ D ∈ L, (C.force w D ↔ N.force v D) := by
  intro D hD
  constructor
  · intro hf
    exact (force_bigAnd_iff N v _).mp hpos D
      (List.mem_filter.mpr ⟨hD, decide_eq_true hf⟩)
  · intro hf
    by_contra hnf
    exact hneg (force_bigOr_of_mem
      (List.mem_filter.mpr ⟨hD, decide_eq_true hnf⟩) hf)

/-! ## Character bounds and derivability transfer -/

/-- Forcing respects derivability (soundness at a point). -/
theorem force_of_deriv {χ D : PLLFormula} (h : Nonempty (LaxND [χ] D))
    {C : ConstraintModel} {x : C.W} (hf : C.force x χ) : C.force x D := by
  obtain ⟨d⟩ := h
  refine soundness d C x ?_
  intro ψ hψ
  rcases List.mem_singleton.mp hψ with rfl
  exact hf

theorem crank_charPos_le {C : ConstraintModel} {w : C.W}
    {L : List PLLFormula} {r : Nat} (hL : ∀ D ∈ L, crank D ≤ r) :
    crank (charPos C w L) ≤ r + 1 := by
  rw [charPos]
  cases hfe : L.filter (fun D => decide (C.force w D)) with
  | nil =>
      show crank (bigAnd []) ≤ r + 1
      have h1 : crank (bigAnd ([] : List PLLFormula)) = 1 := rfl
      omega
  | cons E l =>
      rw [← hfe]
      have h1 : crank (bigAnd (L.filter (fun D => decide (C.force w D)))) ≤ r :=
        crank_bigAnd_le (by simp [hfe])
          (fun D hD => hL D (List.mem_of_mem_filter hD))
      omega

theorem crank_charNeg_le {C : ConstraintModel} {w : C.W}
    {L : List PLLFormula} {r : Nat} (hL : ∀ D ∈ L, crank D ≤ r) :
    crank (charNeg C w L) ≤ r := by
  rw [charNeg]
  exact crank_bigOr_le (fun D hD => hL D (List.mem_of_mem_filter hD))

theorem atoms_charPos {C : ConstraintModel} {w : C.W}
    {L : List PLLFormula} {Q : String → Prop}
    (hL : ∀ D ∈ L, ∀ a ∈ D.atoms, Q a) :
    ∀ a ∈ (charPos C w L).atoms, Q a := by
  rw [charPos]
  exact atoms_bigAnd (fun D hD => hL D (List.mem_of_mem_filter hD))

theorem atoms_charNeg {C : ConstraintModel} {w : C.W}
    {L : List PLLFormula} {Q : String → Prop}
    (hL : ∀ D ∈ L, ∀ a ∈ D.atoms, Q a) :
    ∀ a ∈ (charNeg C w L).atoms, Q a := by
  rw [charNeg]
  exact atoms_bigOr (fun D hD => hL D (List.mem_of_mem_filter hD))

/-! ## The i-clauses of the repaired pillar 2 — PROVED

The character argument: the implication θ⁺ ⊃ θ⁻ of a NON-fallible
successor fails at the base world (the successor itself witnesses),
its complexity fits the budget 2α+2, agreement transfers the failure,
and the failing instance on the other side is the sought partner —
agreeing on every rank-2α formula through the representative list and
soundness. -/

/-- Escape-form i-forth from fragment-agreement. -/
theorem agree_iforth {V : Finset String} {α : Nat}
    {M N : ConstraintModel} {w : M.W} {w' : N.W}
    (h : ∀ χ : PLLFormula, crank χ ≤ 2 * α + 2 →
      (∀ a ∈ χ.atoms, a ∈ V) → (M.force w χ ↔ N.force w' χ))
    {v : M.W} (hv : M.Ri w v) (hvF : v ∉ M.F) :
    ∃ v', N.Ri w' v' ∧
      ∀ χ : PLLFormula, crank χ ≤ 2 * α →
        (∀ a ∈ χ.atoms, a ∈ V) → (M.force v χ ↔ N.force v' χ) := by
  classical
  obtain ⟨L, hL, hrep⟩ := frag_reps_exist' V (2 * α)
  set ξ : PLLFormula := (charPos M v L).ifThen (charNeg M v L) with hξ
  have hξc : crank ξ ≤ 2 * α + 2 := by
    have h1 : crank (charPos M v L) ≤ 2 * α + 1 :=
      crank_charPos_le (fun D hD => (hL D hD).1)
    have h2 : crank (charNeg M v L) ≤ 2 * α :=
      crank_charNeg_le (fun D hD => (hL D hD).1)
    have h3 : crank ξ =
        max (crank (charPos M v L)) (crank (charNeg M v L)) + 1 := rfl
    omega
  have hξa : ∀ a ∈ ξ.atoms, a ∈ V := by
    intro a ha
    rw [hξ] at ha
    rcases (by simpa using ha :
        a ∈ (charPos M v L).atoms ∨ a ∈ (charNeg M v L).atoms) with h1 | h1
    · exact atoms_charPos (fun D hD => (hL D hD).2) a h1
    · exact atoms_charNeg (fun D hD => (hL D hD).2) a h1
  have hwfail : ¬ M.force w ξ := by
    intro hall
    exact not_force_charNeg M hvF L (hall v hv (force_charPos M v L))
  have hw'fail : ¬ N.force w' ξ := fun hf => hwfail ((h ξ hξc hξa).mpr hf)
  have hex : ∃ v', N.Ri w' v' ∧
      N.force v' (charPos M v L) ∧ ¬ N.force v' (charNeg M v L) := by
    by_contra hno
    exact hw'fail (fun v' hv' hp => by
      by_contra hng
      exact hno ⟨v', hv', hp, hng⟩)
  obtain ⟨v', hv', hpos, hneg⟩ := hex
  refine ⟨v', hv', ?_⟩
  intro χ hχc hχa
  obtain ⟨D, hD, h1, h2⟩ := hrep χ hχc hχa
  have hagree := agree_of_char hpos hneg D hD
  constructor
  · intro hf
    exact force_of_deriv h2 (hagree.mp (force_of_deriv h1 hf))
  · intro hf
    exact force_of_deriv h2 (hagree.mpr (force_of_deriv h1 hf))

/-- Escape-form i-back from fragment-agreement (symmetric). -/
theorem agree_iback {V : Finset String} {α : Nat}
    {M N : ConstraintModel} {w : M.W} {w' : N.W}
    (h : ∀ χ : PLLFormula, crank χ ≤ 2 * α + 2 →
      (∀ a ∈ χ.atoms, a ∈ V) → (M.force w χ ↔ N.force w' χ))
    {v' : N.W} (hv' : N.Ri w' v') (hv'F : v' ∉ N.F) :
    ∃ v, M.Ri w v ∧
      ∀ χ : PLLFormula, crank χ ≤ 2 * α →
        (∀ a ∈ χ.atoms, a ∈ V) → (M.force v χ ↔ N.force v' χ) := by
  classical
  obtain ⟨L, hL, hrep⟩ := frag_reps_exist' V (2 * α)
  set ξ : PLLFormula := (charPos N v' L).ifThen (charNeg N v' L) with hξ
  have hξc : crank ξ ≤ 2 * α + 2 := by
    have h1 : crank (charPos N v' L) ≤ 2 * α + 1 :=
      crank_charPos_le (fun D hD => (hL D hD).1)
    have h2 : crank (charNeg N v' L) ≤ 2 * α :=
      crank_charNeg_le (fun D hD => (hL D hD).1)
    have h3 : crank ξ =
        max (crank (charPos N v' L)) (crank (charNeg N v' L)) + 1 := rfl
    omega
  have hξa : ∀ a ∈ ξ.atoms, a ∈ V := by
    intro a ha
    rw [hξ] at ha
    rcases (by simpa using ha :
        a ∈ (charPos N v' L).atoms ∨ a ∈ (charNeg N v' L).atoms) with h1 | h1
    · exact atoms_charPos (fun D hD => (hL D hD).2) a h1
    · exact atoms_charNeg (fun D hD => (hL D hD).2) a h1
  have hw'fail : ¬ N.force w' ξ := by
    intro hall
    exact not_force_charNeg N hv'F L (hall v' hv' (force_charPos N v' L))
  have hwfail : ¬ M.force w ξ := fun hf => hw'fail ((h ξ hξc hξa).mp hf)
  have hex : ∃ v, M.Ri w v ∧
      M.force v (charPos N v' L) ∧ ¬ M.force v (charNeg N v' L) := by
    by_contra hno
    exact hwfail (fun v hv hp => by
      by_contra hng
      exact hno ⟨v, hv, hp, hng⟩)
  obtain ⟨v, hv, hpos, hneg⟩ := hex
  refine ⟨v, hv, ?_⟩
  intro χ hχc hχa
  obtain ⟨D, hD, h1, h2⟩ := hrep χ hχc hχa
  have hagree := agree_of_char hpos hneg D hD
  constructor
  · intro hf
    exact force_of_deriv h2 (hagree.mpr (force_of_deriv h1 hf))
  · intro hf
    exact force_of_deriv h2 (hagree.mp (force_of_deriv h1 hf))

/-- **The repaired pillar 2, assembled** — sorry-footprint exactly the
two m-clauses (probe-backed: 2324 agreeing pairs, 0 violations of the
non-fallible forth-m; the character derivation for the row is the one
open piece).  `Z α` := agreement at rank 2α. -/
theorem layered_of_frag_agree_W (V : Finset String) (n : Nat)
    (M N : ConstraintModel) (w : M.W) (w' : N.W)
    (h : ∀ χ : PLLFormula, crank χ ≤ 2 * n + 2 →
      (∀ a ∈ χ.atoms, a ∈ V) → (M.force w χ ↔ N.force w' χ)) :
    ∃ B : LayeredBisimW (fun a => a ∈ V) M N, B.Z n w w' := by
  classical
  refine ⟨⟨fun α w₁ w₁' => ∀ χ : PLLFormula, crank χ ≤ 2 * α →
      (∀ a ∈ χ.atoms, a ∈ V) → (M.force w₁ χ ↔ N.force w₁' χ),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- mono
    intro α w₁ w₁' hZ χ hc ha
    exact hZ χ (by omega) ha
  · -- atoms
    intro α w₁ w₁' hZ a haV
    have := hZ (.prop a) (by simp [crank]) (by
      intro b hb
      rcases (by simpa using hb : b = a) with rfl
      exact haV)
    simpa [ConstraintModel.force] using this
  · -- fall
    intro α w₁ w₁' hZ
    have := hZ .falsePLL (by simp [crank]) (by intro b hb; simp at hb)
    simpa [ConstraintModel.force] using this
  · -- iforth
    intro α w₁ w₁' hZ v hv
    by_cases hvF : v ∈ M.F
    · exact .inr hvF
    · exact .inl (agree_iforth (fun χ hc ha => hZ χ (by omega) ha) hv hvF)
  · -- iback
    intro α w₁ w₁' hZ v' hv'
    by_cases hv'F : v' ∈ N.F
    · exact .inr hv'F
    · exact .inl (agree_iback (fun χ hc ha => hZ χ (by omega) ha) hv' hv'F)
  · -- mforth: THE open clause (probe-backed)
    intro α w₁ w₁' hZ u hu
    by_cases huF : u ∈ M.F
    · exact .inr huF
    · exact .inl (by sorry)
  · -- mback: symmetric open clause
    intro α w₁ w₁' hZ u' hu'
    by_cases hu'F : u' ∈ N.F
    · exact .inr hu'F
    · exact .inl (by sorry)
  · -- the root
    intro χ hc ha
    exact h χ (by omega) ha

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SemUI.agree_of_char' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms agree_of_char

/--
info: 'PLLND.SemUI.not_force_charNeg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_force_charNeg

/--
info: 'PLLND.SemUI.agree_iforth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms agree_iforth

/--
info: 'PLLND.SemUI.agree_iback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms agree_iback

end SemUI
end PLLND
