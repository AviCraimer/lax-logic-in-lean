import wip.bandW
import wip.rnEmbed

/-!
# The band collapse is REFUTED, the dictionary is uninstantiable, and
the p-pure formulation trivialises

Branch `ui-confluence`.  Three closures, all kernel-checked, landing
the same night the witness pipeline was built:

1. `global_collapse_of_band` — PROGRESS §46's rebuild induction, now
   Lean: a band collapse `BandCollapse R E` with `E ≥ R + 2` bootstraps
   to GLOBAL collapse (every variable-free formula is interderivable
   with one of crank ≤ R).  The band width need only cover one
   reassembled connective (∧/∨ free, ⊃ costs 1, ◯ costs 2).

2. `bandCollapse_refuted` — combining 1 with the Rieger–Nishimura
   embedding's `rank_escape_pll` (wip/rnEmbed.lean: for every rank
   some substituted rung is interderivable with NO variable-free
   formula of that rank): **`BandCollapse R E` is FALSE for every
   `R` and every `E ≥ R + 2`** — in particular at the character
   width `E = 2R + 2` for every `R`.  The band route is closed
   negatively; `restricted_amalgamation_oneVar_band'` /
   `restricted_amalgamation_oneVar_wit` keep their (true) conditional
   content with antecedents now known unsatisfiable.  The surviving
   route is the RANKED one (wip/rankedM.lean), which never used the
   band.

3. `rnDict_false` — the `RNDict` interface is UNINSTANTIABLE: a
   certified connective-closed dictionary would give a band collapse
   at its crank bound (`bandCollapse_of_dict`), refuted.  The
   dictionary-closure program (the partial 15-class instantiation,
   603/690 cells) cannot complete — machine-checked, so no further
   certification effort should be spent there.

4. `ppure_ffree` + `ppure_oneVar_trivial` — a formulation audit with
   teeth: `full_F` (fallible worlds validate every atom) forces a
   `PPure` model to be infallible, so between p-pure models the
   one-variable amalgamation holds UNCONDITIONALLY
   (`infallible_amalgamation` with no agreement hypothesis at all).
   The p-pure hypotheses of the banded/dictionary chains therefore
   trivialised their statements.  The corrected one-variable purity is
   `POnly` (`V a ⊆ F` off `p` — only the mandatory `full_F`
   decoration), adopted by the ranked chain in wip/rankedM.lean, under
   which fallible one-variable models are genuinely in scope.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp
open ConfluentU
open RNEmbed

variable {p : String} {K M : ConstraintModel}

/-! ## 1. The rebuild induction (PROGRESS §46, mechanised) -/

/-- **One band bootstraps globally**: `BandCollapse R E` with
`E ≥ R + 2` collapses EVERY variable-free formula to crank ≤ R.
Structural induction; the collapsed pieces reassemble at crank
≤ R + 2 ≤ E and collapse once more. -/
theorem global_collapse_of_band {R E : Nat} (hE : R + 2 ≤ E)
    (hband : BandCollapse R E) :
    ∀ φ : PLLFormula, φ.atoms = ∅ →
      ∃ ρ : PLLFormula, ρ.atoms = ∅ ∧ crank ρ ≤ R ∧ Interd φ ρ := by
  intro φ
  induction φ with
  | prop a =>
      intro h
      rw [atoms_prop] at h
      exact absurd h (by simp)
  | falsePLL =>
      intro _
      exact hband PLLFormula.falsePLL atoms_false (Nat.zero_le E)
  | and A B ihA ihB =>
      intro h
      rw [atoms_and] at h
      obtain ⟨ρA, haA, hcA, hiA⟩ := ihA (atoms_empty_left h)
      obtain ⟨ρB, haB, hcB, hiB⟩ := ihB (atoms_empty_right h)
      obtain ⟨σ, hσa, hσc, hσI⟩ := hband (ρA.and ρB)
        (by rw [atoms_and]; exact Finset.union_eq_empty.mpr ⟨haA, haB⟩)
        (le_trans (Nat.max_le.mpr ⟨hcA, hcB⟩) (by omega))
      exact ⟨σ, hσa, hσc, (Interd.and_congr hiA hiB).trans hσI⟩
  | or A B ihA ihB =>
      intro h
      rw [atoms_or] at h
      obtain ⟨ρA, haA, hcA, hiA⟩ := ihA (atoms_empty_left h)
      obtain ⟨ρB, haB, hcB, hiB⟩ := ihB (atoms_empty_right h)
      obtain ⟨σ, hσa, hσc, hσI⟩ := hband (ρA.or ρB)
        (by rw [atoms_or]; exact Finset.union_eq_empty.mpr ⟨haA, haB⟩)
        (le_trans (Nat.max_le.mpr ⟨hcA, hcB⟩) (by omega))
      exact ⟨σ, hσa, hσc, (Interd.or_congr hiA hiB).trans hσI⟩
  | ifThen A B ihA ihB =>
      intro h
      rw [atoms_ifThen] at h
      obtain ⟨ρA, haA, hcA, hiA⟩ := ihA (atoms_empty_left h)
      obtain ⟨ρB, haB, hcB, hiB⟩ := ihB (atoms_empty_right h)
      have hc : crank (ρA.ifThen ρB) ≤ E := by
        show max (crank ρA) (crank ρB) + 1 ≤ E
        have := Nat.max_le.mpr ⟨hcA, hcB⟩
        omega
      obtain ⟨σ, hσa, hσc, hσI⟩ := hband (ρA.ifThen ρB)
        (by rw [atoms_ifThen]; exact Finset.union_eq_empty.mpr ⟨haA, haB⟩)
        hc
      exact ⟨σ, hσa, hσc, (Interd.imp_congr hiA hiB).trans hσI⟩
  | somehow A ihA =>
      intro h
      obtain ⟨ρA, haA, hcA, hiA⟩ := ihA h
      have hc : crank (PLLFormula.somehow ρA) ≤ E := by
        show crank ρA + 2 ≤ E
        omega
      obtain ⟨σ, hσa, hσc, hσI⟩ := hband (PLLFormula.somehow ρA) haA hc
      exact ⟨σ, hσa, hσc, (Interd.box_congr hiA).trans hσI⟩

/-! ## 2. The refutation -/

/-- **The band collapse is refuted** for every floor `R` and every
width `E ≥ R + 2` (in particular at the character width `2R + 2`):
the bootstrapped global collapse contradicts the ladder's rank
escape. -/
theorem bandCollapse_refuted {R E : Nat} (hE : R + 2 ≤ E) :
    ¬ BandCollapse R E := by
  intro hband
  obtain ⟨n, hn⟩ := rank_escape_pll R
  obtain ⟨ρ, hρa, hρc, hρI⟩ :=
    global_collapse_of_band hE hband (rnSub n) (rnSub_atoms n)
  exact hn ρ hρa hρc hρI

/-- **The dictionary interface is uninstantiable**: an `RNDict` would
band-collapse at its crank bound. -/
theorem rnDict_false : RNDict → False := fun D =>
  bandCollapse_refuted (R := D.crankBound) (E := D.crankBound + 2)
    (le_refl _) (bandCollapse_of_dict D _)

/-! ## 3. The p-pure trivialisation -/

/-- `full_F` forces a `PPure` model to be infallible: a fallible world
would validate every atom, and `PPure` leaves no atom off `p` to
validate. -/
theorem ppure_ffree {C : ConstraintModel} (h : PPure p C) : FFree C := by
  intro w hw
  by_cases hp : p = "a"
  · exact h "b" (by rw [hp]; decide) w (C.full_F hw)
  · exact h "a" (fun ha => hp ha.symm) w (C.full_F hw)

/-- **The p-pure one-variable amalgamation is trivial**: between
p-pure models (K mutually confluent) the full conclusion holds with NO
agreement hypothesis — `PPure` implies `FFree`, and
`infallible_amalgamation` does the rest.  The banded and dictionary
chains' p-pure statements were therefore contentless; the ranked chain
now uses the corrected purity `POnly`. -/
theorem ppure_oneVar_trivial (cl : Finset PLLFormula)
    (hcl : SubClosed cl) (hadeq : OBoxAdeq cl)
    (hK : MutuallyConfluent K) (hPK : PPure p K) (hPM : PPure p M)
    (k₀ : K.W) (m₀ : M.W) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ) :=
  infallible_amalgamation cl hcl hadeq hK hPK hPM
    (ppure_ffree hPK) (ppure_ffree hPM) k₀ m₀

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.global_collapse_of_band' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms global_collapse_of_band

/--
info: 'PLLND.SemUI.bandCollapse_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bandCollapse_refuted

/--
info: 'PLLND.SemUI.rnDict_false' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rnDict_false

/--
info: 'PLLND.SemUI.ppure_ffree' does not depend on any axioms
-/
#guard_msgs in
#print axioms ppure_ffree

/--
info: 'PLLND.SemUI.ppure_oneVar_trivial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ppure_oneVar_trivial

end SemUI
end PLLND
