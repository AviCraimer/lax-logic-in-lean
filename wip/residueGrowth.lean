import wip.witTripleC
import wip.crankC

/-!
# Growth propagation at the residue — the boundary theorem and the
non-vacuity construction

Branch `ui-confluence`.  Three results about `MforthResidue`:

1. `residue_growth_boundary` (PROVED): over a RANKED link (what
   fragment-agreement delivers definitionally), every p-FREE formula in
   the growth `trace kv ∖ val Δ` of a residue configuration has
   `crankC ≥ 2d`.  Growth strictly below the boundary propagates to the
   `mback`-partner and contradicts its same-trace hypothesis.  So a
   residue configuration's growth is p-laden or sits exactly on the
   crank boundary — the machine-checked form of "the one-level descent
   is sharp", and the exact PLL location of the mechanism that KILLS
   uniform interpolation for S4/K4 (bisimulation rank outrunning any
   fixed interpolant rank).

2. `residue_config_satisfiable` (PROVED): the residue configuration IS
   satisfiable — a two-point confluent chain with the quantified atom
   `p` at the top, the full link family, and the ◯-adequate closure
   `{⊥, p, ◯⊥, ◯p}` realise every hypothesis, with growth `{p}`
   (pure p-ladenness, invisible to the atoms clause; `◯p` is already in
   `val Δ` — reflexive `Rₘ` validates `χ ⊃ ◯χ` pointwise — which is
   exactly the anticipation the resolution uses).  Consequence: the
   vacuity route (`mforthResidue_of_config_absurd`) is DEAD in general —
   the earlier probe's "0 configurations" was an artifact of its
   closures containing no `p`.

3. `residue_config_example_resolves` (PROVED): in that same instance the
   residue's CONCLUSION also holds (the grown answer; the p-growth was
   promised: `◯p ∈ val Δ`).  So the construction does not refute `MforthResidue`;
   it shows the Prop is contentful, and locates the open question at:
   p-laden or boundary-crank growth whose ◯-anticipation fails.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp
open ConfluentU

variable {p : String} {K M : ConstraintModel}

/-! ## 1. The ranked growth-propagation boundary -/

/-- A layered link is **ranked** when level-`n` links transfer p-free
formulas of `crankC ≤ n`.  For the link fragment-agreement constructs
(`Z n :=` agreement at rank `n`), this is definitional. -/
def Ranked (p : String) (B : LayeredBisimWit (fun a => a ≠ p) K M) : Prop :=
  ∀ {n : Nat} {φ : PLLFormula} {k : K.W} {m : M.W},
    B.Z n k m → crankC φ ≤ n → (∀ a ∈ φ.atoms, a ≠ p) →
    (K.force k φ ↔ M.force m φ)

/-- **The growth boundary** (growth propagation, provable half): in any
residue configuration over a ranked link, a p-free tracked formula
validated by the `iback`-partner `kv` but not by `Δ` has
`crankC ≥ 2d`.  Below the boundary it crosses to `u` (level `2d`) and
back to the `mback`-partner `κ` (level `2d−1`), contradicting
`trace κ = val Δ`.  So sub-boundary p-free growth PROPAGATES, and a
genuine residue configuration distinguishes its partners only by
p-laden or boundary-crank formulas. -/
theorem residue_growth_boundary {cl : Finset PLLFormula}
    {B : LayeredBisimWit (fun a => a ≠ p) K M} (hR : Ranked p B)
    {Δ : (canonFinC cl).W} {kv κ : K.W} {u : M.W}
    (hZkv : B.Z (2 * canonDepthC cl Δ) kv u)
    (hZκ : B.Z (2 * canonDepthC cl Δ - 1) κ u)
    (hκsame : (traceT K cl κ).val = Δ.1.val)
    {ψ : PLLFormula} (hψv : ψ ∈ (traceT K cl kv).val) (hψΔ : ψ ∉ Δ.1.val)
    (hpfree : ∀ a ∈ ψ.atoms, a ≠ p) :
    2 * canonDepthC cl Δ - 1 < crankC ψ := by
  by_contra hgt
  have hle : crankC ψ ≤ 2 * canonDepthC cl Δ - 1 := Nat.not_lt.mp hgt
  obtain ⟨hψcl, hfv⟩ := mem_traceT_val.mp hψv
  have hu : M.force u ψ :=
    (hR hZkv (le_trans hle (Nat.sub_le _ _)) hpfree).mp hfv
  have hκf : K.force κ ψ := (hR hZκ hle hpfree).mpr hu
  have : ψ ∈ Δ.1.val := by
    rw [← hκsame]
    exact mem_traceT_val.mpr ⟨hψcl, hκf⟩
  exact hψΔ this

/-! ## 2. The residue configuration is satisfiable

The two-point confluent chain with `p` at the top.  All atoms other
than `p` are nowhere true, both worlds are infallible, and `Rₘ = Rᵢ`
is the chain order — mutually confluent.  The FULL link family (every
pair at every level) is a lawful `LayeredBisimE` off `p`: the atoms
clause only inspects protected atoms, and there are no fallible
worlds. -/

/-- Two-point chain, `p` true exactly at the top, no fallible worlds,
`Rₘ = Rᵢ` = the chain order. -/
def chainP : ConstraintModel where
  W := Bool
  Ri := fun x y => x = y ∨ (x = false ∧ y = true)
  Rm := fun x y => x = y ∨ (x = false ∧ y = true)
  F := {_x | False}
  V := fun a => {x | a = "p" ∧ x = true}
  refl_i := fun _ => .inl rfl
  trans_i := by
    intro a b c h₁ h₂
    rcases h₁ with rfl | ⟨rfl, rfl⟩
    · exact h₂
    · rcases h₂ with rfl | ⟨h, -⟩
      · exact .inr ⟨rfl, rfl⟩
      · exact absurd h (by decide)
  refl_m := fun _ => .inl rfl
  trans_m := by
    intro a b c h₁ h₂
    rcases h₁ with rfl | ⟨rfl, rfl⟩
    · exact h₂
    · rcases h₂ with rfl | ⟨h, -⟩
      · exact .inr ⟨rfl, rfl⟩
      · exact absurd h (by decide)
  sub_mi := fun h => h
  hered_F := by
    intro a b _ hF
    exact hF.elim
  hered_V := by
    intro x a b h hV
    rcases h with rfl | ⟨-, rfl⟩
    · exact hV
    · exact ⟨hV.1, rfl⟩
  full_F := fun hF => hF.elim

theorem chainP_confluent : MutuallyConfluent chainP := by
  intro x w v _ _
  refine ⟨true, ?_, ?_⟩
  · cases w with
    | false => exact .inr ⟨rfl, rfl⟩
    | true => exact .inl rfl
  · cases v with
    | false => exact .inr ⟨rfl, rfl⟩
    | true => exact .inl rfl

/-- The full link family is a lawful `LayeredBisimE` off `p` on
`chainP`: no protected atom is ever true, no world is fallible, and
every zigzag is answered reflexively. -/
def fullE : LayeredBisimE (fun a => a ≠ "p") chainP chainP where
  Z := fun _ _ _ => True
  mono := fun _ => trivial
  atoms := by
    intro n w w' _ a ha
    constructor
    · intro h
      exact absurd h.1 ha
    · intro h
      exact absurd h.1 ha
  fall := by
    intro n w w' _
    exact Iff.rfl
  iforth := by
    intro n w w' _ v _
    exact .inl ⟨w', .inl rfl, trivial⟩
  iback := by
    intro n w w' _ v' _
    exact .inl ⟨w, .inl rfl, trivial⟩
  mforth := by
    intro n w w' _ u _
    exact ⟨w', .inl rfl, .inl trivial⟩
  mback := by
    intro n w w' _ u' _
    exact ⟨w, .inl rfl, .inl trivial⟩

/-- The ◯-adequate subformula-closed closure `{⊥, p, ◯⊥, ◯p}`. -/
def clP : Finset PLLFormula :=
  {PLLFormula.falsePLL, PLLFormula.prop "p",
   PLLFormula.somehow PLLFormula.falsePLL,
   PLLFormula.somehow (PLLFormula.prop "p")}

theorem clP_subClosed : SubClosed clP := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ ψ h
    simp [clP] at h
  · intro φ ψ h
    simp [clP] at h
  · intro φ ψ h
    simp [clP] at h
  · intro φ ψ h
    simp [clP] at h
  · intro φ ψ h
    simp [clP] at h
  · intro φ ψ h
    simp [clP] at h
  · intro φ h
    simp only [clP, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · obtain rfl := PLLFormula.somehow.inj h
      decide
    · obtain rfl := PLLFormula.somehow.inj h
      decide

/-! forcing facts on `chainP` -/

theorem chainP_force_top_p : chainP.force true (PLLFormula.prop "p") :=
  ⟨rfl, rfl⟩

theorem chainP_not_force_bot_p : ¬ chainP.force false (PLLFormula.prop "p") :=
  fun h => absurd h.2 (by decide)

theorem chainP_force_box_p (w : Bool) :
    chainP.force w (PLLFormula.somehow (PLLFormula.prop "p")) := by
  intro v _
  refine ⟨true, ?_, rfl, rfl⟩
  cases v with
  | false => exact .inr ⟨rfl, rfl⟩
  | true => exact .inl rfl

theorem chainP_not_force_box_bot (w : Bool) :
    ¬ chainP.force w (PLLFormula.somehow PLLFormula.falsePLL) := by
  intro h
  obtain ⟨u, -, hu⟩ := h w (chainP.refl_i w)
  exact hu.elim

/-- **The residue configuration is satisfiable** — every hypothesis of
`MforthResidue` (for `p := "p"`) is realised on `chainP` with the full
link family and the closure `{⊥, p, ◯⊥, ◯p}`.  The growth is
`{p, ◯p}`: pure p-ladenness, invisible to the atoms clause.  So the
configuration cannot be refuted abstractly, and the vacuity route to
the residue is closed. -/
theorem residue_config_satisfiable :
    ∃ (K M : ConstraintModel) (B : LayeredBisimWit (fun a => a ≠ "p") K M)
      (cl : Finset PLLFormula) (_hK : MutuallyConfluent K)
      (Δ : (canonFinC cl).W) (k' k kv κ : K.W) (m' m u : M.W),
      SubClosed cl ∧
      PLLFormula.falsePLL ∉ Δ.1.val ∧
      (traceT K cl k).val = Δ.1.val ∧
      (traceT K cl k').val = Δ.1.val ∧
      K.Ri k' k ∧
      M.Ri m' m ∧ M.Rm m u ∧ u ∉ M.F ∧
      B.Z (2 * canonDepthC cl Δ + 1) k' m' ∧
      B.Z (2 * canonDepthC cl Δ) k m ∧
      K.Ri k' kv ∧ B.Z (2 * canonDepthC cl Δ) kv u ∧
      (traceT K cl kv).val ≠ Δ.1.val ∧
      K.Rm k κ ∧ B.Z (2 * canonDepthC cl Δ - 1) κ u ∧
      (traceT K cl κ).val = Δ.1.val := by
  refine ⟨chainP, chainP, fullE.toWit, clP, chainP_confluent,
    traceC chainP_confluent clP false, false, false, true, false,
    false, false, true,
    clP_subClosed, ?_, rfl, rfl, .inl rfl, .inl rfl, .inr ⟨rfl, rfl⟩, ?_,
    trivial, trivial, .inr ⟨rfl, rfl⟩, trivial, ?_, .inl rfl, trivial, rfl⟩
  · intro h
    exact (mem_traceT_val.mp h).2.elim
  · intro h
    exact h.elim
  · intro hEq
    have h1 : PLLFormula.prop "p" ∈ (traceT chainP clP true).val :=
      mem_traceT_val.mpr ⟨by decide, chainP_force_top_p⟩
    rw [hEq] at h1
    exact chainP_not_force_bot_p (mem_traceT_val.mp h1).2

/-- **The instance resolves**: in the configuration above, the residue's
conclusion holds — the grown answer `trace kv = {p, ◯p}` is
◯-ANTICIPATED at `Δ = {◯p}` (the p-growth is promised), and `(kv, u)`
serves as its own base and reservoir.  So the construction does not
refute `MforthResidue`; it locates the open content at growth whose
◯-anticipation fails. -/
theorem residue_config_example_resolves :
    ∃ Δ' : (canonFinC clP).W,
      (canonFinC clP).Rm (traceC chainP_confluent clP false) Δ' ∧
      WitTripleC clP fullE.toWit Δ' true := by
  refine ⟨traceC chainP_confluent clP true, ⟨?_, ?_⟩, ?_⟩
  · -- persistence: trace false ⊆ trace true
    intro φ hφ
    obtain ⟨hcl, hf⟩ := mem_traceT_val.mp hφ
    exact mem_traceT_val.mpr
      ⟨hcl, chainP.force_hered (.inr ⟨rfl, rfl⟩) hf⟩
  · -- anticipation: everything the top validates is ◯-promised below
    intro χ hbox hχ
    obtain ⟨hχcl, hχf⟩ := mem_traceT_val.mp hχ
    cases χ with
    | somehow χ₀ =>
        -- boxOf (◯χ₀) = ◯χ₀ ∈ clP: it is ◯⊥ (refuted at the top) or ◯p
        rw [boxOf_somehow] at hbox ⊢
        simp only [clP, Finset.mem_insert, Finset.mem_singleton] at hbox
        rcases hbox with h | h | h | h
        · exact absurd h (by simp)
        · exact absurd h (by simp)
        · rw [h] at hχf
          exact absurd hχf (chainP_not_force_box_bot true)
        · rw [h]
          exact mem_traceT_val.mpr ⟨by decide, chainP_force_box_p false⟩
    | falsePLL =>
        exact absurd hχf (fun h => h.elim)
    | prop a =>
        -- boxOf (prop a) = ◯(prop a) ∈ clP forces a = "p"
        have ha : a = "p" := by
          revert hbox
          show PLLFormula.somehow (PLLFormula.prop a) ∈ clP → a = "p"
          intro hb
          rcases Finset.mem_insert.mp hb with h | hb
          · exact absurd h (by simp)
          rcases Finset.mem_insert.mp hb with h | hb
          · exact absurd h (by simp)
          rcases Finset.mem_insert.mp hb with h | hb
          · exact absurd h (by simp)
          · have := Finset.mem_singleton.mp hb
            exact PLLFormula.prop.inj (PLLFormula.somehow.inj this)
        subst ha
        exact mem_traceT_val.mpr ⟨by decide, chainP_force_box_p false⟩
    | and a b =>
        simp [clP] at hχcl
    | or a b =>
        simp [clP] at hχcl
    | ifThen a b =>
        simp [clP] at hχcl
  · exact .proper true true true rfl rfl (chainP.refl_i true) trivial trivial
      (chainP.refl_i true)


/-- **The fixpoint-regime rescue**: if the level hierarchy has collapsed
by `2d−1` at the `mback`-partner's link (true throughout the
greatest-fixpoint regime — on the corrected probe's battery this held at
every one of 36,588,835 configurations), then the residue holds
outright: `κ` itself is the same-trace base, and the old reservoir
persists.  The genuinely open zone is therefore exactly the
STRICTLY-DESCENDING regime: links below the stabilisation level of the
Z-hierarchy, with small canonical depth — the alternation-tower
territory of the cross-route experiment. -/
theorem mforthResidue_of_stabilised (cl : Finset PLLFormula)
    (B : LayeredBisimWit (fun a => a ≠ p) K M)
    (h : ∀ {Δ : (canonFinC cl).W} {κ : K.W} {u : M.W},
      B.Z (2 * canonDepthC cl Δ - 1) κ u →
      B.Z (2 * canonDepthC cl Δ) κ u) :
    MforthResidue cl B := by
  intro hK Δ k' k kv κ m' m u _hcl hbot hΔk hΔk' hik him hmu huF hZ' hZ
    hk'kv hZkv hsame hkκ hZκ hκsame
  exact ⟨Δ, (canonFinC cl).refl_m Δ,
    .proper k' κ m' hκsame hΔk' (M.trans_i him (M.sub_mi hmu)) hZ' (h hZκ)
      (K.trans_i hik (K.sub_mi hkκ))⟩

/--
info: 'PLLND.SemUI.mforthResidue_of_stabilised' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mforthResidue_of_stabilised

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.residue_growth_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms residue_growth_boundary

/--
info: 'PLLND.SemUI.residue_config_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms residue_config_satisfiable

/--
info: 'PLLND.SemUI.residue_config_example_resolves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms residue_config_example_resolves

end SemUI
end PLLND
