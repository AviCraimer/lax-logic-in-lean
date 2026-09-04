import wip.bandM
import wip.witOut

/-!
# The banded amalgamation, witness form: `BandMback` leaves the ledger

Branch `ui-confluence`.  The cascade of wip/witOut.lean instantiated at
the banded constant link:

1. `BandMwitM` + `bandMwitM_of_collapse` (PROVED): the M-side witness
   clause, by the SYMMETRIC maximal-type ascent — `bandAgree` is
   symmetric, so the K-side ascent applied to the swapped pair delivers
   the M-side clause verbatim.

2. `restricted_amalgamation_oneVar_wit` (PROVED): the one-variable
   amalgamation for p-pure mutually confluent `K` and `M`, from the
   band collapse `BandCollapse R (2R+2)` and root agreement at rank
   `R` — and NOTHING ELSE.  Both m-clauses are paid by the ascent, the
   witness residue by stabilisation, and the output is the witness-form
   p-variant `PBisimWit` carrying full p-free transfer at the root.

   Compare `restricted_amalgamation_oneVar_band'`: its `BandMback`
   hypothesis — the last unproved m-obligation of the route — is GONE.
   In this setting the entire route now rests on the single hypothesis
   `BandCollapse R (2R+2)`, which (PROGRESS §46) is equivalent to
   finiteness of the variable-free fragment with a rank-`R`
   representative bound.  The conditional is now clean:

       fragment finiteness  ⟹  one-variable amalgamation, in full.

   The negative side (the fragment is likely infinite: 15 classes
   certified and growing, the injectivity transfer in flight) stands
   unchanged; the surviving unconditional shape is the per-instance
   relativisation of the same ascent.

3. `restricted_amalgamation_oneVar_wit_dict` (PROVED): the global
   dictionary special case through `bandCollapse_of_dict`.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp
open ConfluentU

variable {p : String} {K M : ConstraintModel}

/-! ## 1. The M-side witness clause, by the symmetric ascent -/

/-- The M-side witness form of the banded m-clause: an M-row witness
for `ψ` is answered by SOME M-row witness with a K-side `Rₘ`-partner.
The mirror image of `BandMwit`; strictly weaker than `BandMback`. -/
def BandMwitM (R : Nat) (K M : ConstraintModel) : Prop :=
  ∀ {k : K.W} {m : M.W}, bandAgree R K M k m → ∀ {ψ : PLLFormula},
    (∃ u', M.Rm m u' ∧ M.force u' ψ) →
      ∃ u' κ, M.Rm m u' ∧ M.force u' ψ ∧ K.Rm k κ ∧
        (bandAgree R K M κ u' ∨ (κ ∈ K.F ∧ u' ∈ M.F))

/-- Band agreement is symmetric. -/
theorem bandAgree_symm {R : Nat} {K M : ConstraintModel}
    {k : K.W} {m : M.W} (h : bandAgree R K M k m) :
    bandAgree R M K m k :=
  fun ρ hρ hc => (h ρ hρ hc).symm

/-- `BandMback` pays the witness clause (answer the given witness). -/
theorem bandMwitM_of_bandMback {R : Nat} {K M : ConstraintModel}
    (h : BandMback R K M) : BandMwitM R K M := by
  intro k m hZ ψ hex
  obtain ⟨u', hmu', hψ⟩ := hex
  obtain ⟨u, hku, hres⟩ := h hZ hmu'
  exact ⟨u', u, hmu', hψ, hku, hres⟩

/-- **The M-side witness clause is DISCHARGED under the band** — the
maximal-type ascent, run on the mirror pair: `bandAgree` is symmetric,
so `bandMwit_of_collapse` for `(M, K)` delivers exactly the M-side
clause for `(K, M)` after flipping the agreement and the fallible
pair. -/
theorem bandMwitM_of_collapse {R : Nat} (hR : 1 ≤ R)
    (hband : BandCollapse R (2 * R + 2))
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M) :
    BandMwitM R K M := by
  intro k m hZ ψ hex
  obtain ⟨u', κ, hmu', hu'ψ, hkκ, hres⟩ :=
    bandMwit_of_collapse (K := M) (M := K) hR hband hM hK
      (bandAgree_symm hZ) hex
  refine ⟨u', κ, hmu', hu'ψ, hkκ, ?_⟩
  rcases hres with h | ⟨h1, h2⟩
  · exact .inl (bandAgree_symm h)
  · exact .inr ⟨h2, h1⟩

/-! ## 2. The banded link pays every obligation of the witness pipeline -/

/-- The banded constant link satisfies the M-side witness clause. -/
theorem bandB_mwitM (R : Nat) (hband : BandCollapse R (2 * R + 2))
    (hPK : PPure p K) (hPM : PPure p M)
    (hmf : BandMwit R K M) (hmwm : BandMwitM R K M) :
    (bandB R hband hPK hPM hmf).MWitM := by
  intro n k m hZ ψ hex
  exact hmwm hZ hex

/-- The banded constant link pays the witness residue (constant family
⇒ level collapse). -/
theorem bandB_mwitResidue (cl : Finset PLLFormula) (R : Nat)
    (hband : BandCollapse R (2 * R + 2))
    (hPK : PPure p K) (hPM : PPure p M)
    (hmf : BandMwit R K M) :
    MwitResidue cl (bandB R hband hPK hPM hmf) :=
  mwitResidue_of_stabilised cl (bandB R hband hPK hPM hmf) (fun h => h)

/-! ## 3. The headline: the amalgamation from the band collapse alone -/

/-- **The banded one-variable amalgamation, witness form** — from the
band collapse and root agreement at rank `R`, NOTHING ELSE: both
m-clauses are paid by the maximal-type ascent (K-side and mirrored
M-side), the i-clauses by the character argument across the band, the
witness residue by stabilisation.  `BandMback` has left the ledger.
The output is the witness-form p-variant with closure agreement at the
distinguished world and full p-free transfer at the root. -/
theorem restricted_amalgamation_oneVar_wit (cl : Finset PLLFormula)
    (R : Nat) (hR : 1 ≤ R) (hband : BandCollapse R (2 * R + 2))
    (hcl : SubClosed cl) (hadeq : OBoxAdeq cl)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M)
    (k₀ : K.W) (m₀ : M.W)
    (hagree : bandAgree R K M k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisimWit p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ (∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ)) ∧
      (∀ χ : PLLFormula, (∀ a ∈ χ.atoms, a ≠ p) →
        (M.force m₀ χ ↔ N.force n₀ χ)) := by
  have hmf : BandMwit R K M := bandMwit_of_collapse hR hband hK hM
  obtain ⟨N, C, n₀, hZ, hcls, htrans⟩ :=
    amalgamation_assembledW cl (bandB R hband hPK hPM hmf) hcl hadeq hK
      (bandB_mwitM R hband hPK hPM hmf (bandMwitM_of_collapse hR hband hK hM))
      (bandB_mwitResidue cl R hband hPK hPM hmf)
      k₀ m₀ hagree
  exact ⟨N, C, n₀, hZ, hcls, htrans hM⟩

/-- The global-dictionary special case, through `bandCollapse_of_dict`. -/
theorem restricted_amalgamation_oneVar_wit_dict (cl : Finset PLLFormula)
    (D : RNDict) (hR : 1 ≤ D.crankBound)
    (hcl : SubClosed cl) (hadeq : OBoxAdeq cl)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M)
    (k₀ : K.W) (m₀ : M.W)
    (hagree : bandAgree D.crankBound K M k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisimWit p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ (∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ)) ∧
      (∀ χ : PLLFormula, (∀ a ∈ χ.atoms, a ≠ p) →
        (M.force m₀ χ ↔ N.force n₀ χ)) :=
  restricted_amalgamation_oneVar_wit cl D.crankBound hR
    (bandCollapse_of_dict D _) hcl hadeq hK hM hPK hPM k₀ m₀ hagree

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.bandMwitM_of_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bandMwitM_of_collapse

/--
info: 'PLLND.SemUI.restricted_amalgamation_oneVar_wit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms restricted_amalgamation_oneVar_wit

/--
info: 'PLLND.SemUI.restricted_amalgamation_oneVar_wit_dict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms restricted_amalgamation_oneVar_wit_dict

end SemUI
end PLLND
