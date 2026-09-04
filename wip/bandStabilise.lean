import wip.stabilise

/-!
# The rank-relative stabilisation lemma

Branch `ui-confluence`.  The global (constant-link) chain of
`wip/stabilise.lean` needed the whole variable-free fragment to collapse
onto finitely many classes — now known REFUTED at 15 classes and open in
general.  This file re-derives the entire chain from a strictly weaker,
rank-relative hypothesis: a **band collapse**

    `BandCollapse R E`:  every variable-free formula of crank ≤ E is
    interderivable with one of crank ≤ R,

with the band width dictated by the character argument's budget:
`E = 2R+2` is exactly what the i-clauses consume.  Equivalently: the
class-counting function of the variable-free fragment has a PLATEAU of
width `R+2` starting at `R`.  No finiteness, no representative lists, no
closure tables — those were only ever certification apparatus.

* `band_agree_stab` (PROVED): under `BandCollapse R E`, agreement at
  rank `R` is agreement at rank `E` — the stabilisation lemma,
  rank-relative form.
* `bandB` (PROVED modulo the two m-clauses): the constant family
  `Z n := bandAgree R` is a lawful `LayeredBisimE` between p-pure
  models given `BandCollapse R (2R+2)` — the i-clauses upgrade their
  input through the band before spending the `2α+2` character budget.
* `bandB_mforthResidue` (PROVED): the residue is paid, as for any
  constant family.
* `restricted_amalgamation_oneVar_band` (PROVED): the one-variable
  amalgamation at entry rank `R`, from `BandCollapse R (2R+2)` +
  the m-clauses.  The global theorem is the special case through
  `bandCollapse_of_dict`.

THE OPEN CORE, sharpened: exhibit ONE `R` with `BandCollapse R (2R+2)`.
Strictly weaker than fragment finiteness (a plateau suffices; the
fragment may resume growing above the band).  This is the semantic form
of the syntactic stabilisation question H2: the alternation tower's
class growth must pause for one band.  The refutation of the 15-class
closure shows growth through cranks 6–7, so any witnessing `R` sits at
least there; the dictionary-mapping session's class-count curve is
exactly the data that locates or excludes a plateau.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp
open ConfluentU

variable {p : String} {K M : ConstraintModel}

/-! ## 1. Band collapse and band agreement -/

/-- **Band collapse**: every variable-free formula of crank ≤ `E` is
interderivable with one of crank ≤ `R`.  The rank-relative
stabilisation hypothesis — a plateau of the class structure on the
band `[R, E]`. -/
def BandCollapse (R E : Nat) : Prop :=
  ∀ φ : PLLFormula, φ.atoms = ∅ → crank φ ≤ E →
    ∃ ρ : PLLFormula, ρ.atoms = ∅ ∧ crank ρ ≤ R ∧ Interd φ ρ

/-- A certified global dictionary collapses every band: the global
chain is the special case. -/
theorem bandCollapse_of_dict (D : RNDict) (E : Nat) :
    BandCollapse D.crankBound E := by
  intro φ hφ _
  obtain ⟨i, hi⟩ := dict_collapse D φ hφ
  exact ⟨D.rep i, D.rep_varFree i, D.rep_crank_le i, hi⟩

/-- Variable-free agreement up to rank `R`. -/
def bandAgree (R : Nat) (K M : ConstraintModel) (k : K.W) (m : M.W) : Prop :=
  ∀ ρ : PLLFormula, ρ.atoms = ∅ → crank ρ ≤ R → (K.force k ρ ↔ M.force m ρ)

/-- **The rank-relative stabilisation lemma**: under a band collapse,
agreement at the band's floor is agreement across the band. -/
theorem band_agree_stab {R E : Nat} (hband : BandCollapse R E)
    {k : K.W} {m : M.W} (h : bandAgree R K M k m) :
    bandAgree E K M k m := by
  intro φ hφ hcr
  obtain ⟨ρ, hρa, hρc, hi⟩ := hband φ hφ hcr
  exact (interd_force_iff hi K k).trans
    ((h ρ hρa hρc).trans (interd_force_iff hi M m).symm)

/-! ## 2. The banded constant link -/

/-- The m-clauses of the banded constant family — the pillar-2
obligation, rank-relative form. -/
def BandMforth (R : Nat) (K M : ConstraintModel) : Prop :=
  ∀ {k : K.W} {m : M.W}, bandAgree R K M k m → ∀ {u : K.W}, K.Rm k u →
    ∃ u', M.Rm m u' ∧ (bandAgree R K M u u' ∨ (u ∈ K.F ∧ u' ∈ M.F))

/-- The WITNESS form of the banded m-forth obligation — all the
amalgamation consumes; strictly weaker than `BandMforth`. -/
def BandMwit (R : Nat) (K M : ConstraintModel) : Prop :=
  ∀ {k : K.W} {m : M.W}, bandAgree R K M k m → ∀ {ψ : PLLFormula},
    (∃ κ, K.Rm k κ ∧ K.force κ ψ) →
      ∃ κ u', K.Rm k κ ∧ K.force κ ψ ∧ M.Rm m u' ∧
        (bandAgree R K M κ u' ∨ (κ ∈ K.F ∧ u' ∈ M.F))

theorem bandMwit_of_bandMforth {R : Nat} {K M : ConstraintModel}
    (h : BandMforth R K M) : BandMwit R K M := by
  intro k m hZ ψ hex
  obtain ⟨κ, hkκ, hκψ⟩ := hex
  obtain ⟨u', hmu', hres⟩ := h hZ hkκ
  exact ⟨κ, u', hkκ, hκψ, hmu', hres⟩

def BandMback (R : Nat) (K M : ConstraintModel) : Prop :=
  ∀ {k : K.W} {m : M.W}, bandAgree R K M k m → ∀ {u' : M.W}, M.Rm m u' →
    ∃ u, K.Rm k u ∧ (bandAgree R K M u u' ∨ (u ∈ K.F ∧ u' ∈ M.F))

/-- **The banded constant link**: `Z n := bandAgree R`, a lawful
`LayeredBisimE` off `p` between p-pure models, given the band collapse
at width `2R+2`.  The i-clauses upgrade their input across the band
(`band_agree_stab`) before spending the character budget `2α+2` with
`α := R`; the partner returns at rank `2R ≥ R`. -/
def bandB (R : Nat) (hband : BandCollapse R (2 * R + 2))
    (hPK : PPure p K) (hPM : PPure p M)
    (hmf : BandMwit R K M) :
    LayeredBisimWit (fun a => a ≠ p) K M where
  Z := fun _ k m => bandAgree R K M k m
  mono := fun h => h
  atoms := by
    intro n k m _ a ha
    exact iff_of_false (hPK a ha k) (hPM a ha m)
  fall := by
    intro n k m hZ
    exact hZ PLLFormula.falsePLL atoms_false (Nat.zero_le R)
  iforth := by
    intro n k m hZ v hv
    by_cases hvF : v ∈ K.F
    · exact .inr hvF
    · obtain ⟨v', hv', hagr⟩ :=
        agree_iforth (V := (∅ : Finset String)) (α := R)
          (fun χ hχc hA =>
            band_agree_stab hband hZ χ
              (Finset.eq_empty_iff_forall_notMem.mpr
                (fun a ha => Finset.notMem_empty a (hA a ha))) hχc)
          hv hvF
      refine .inl ⟨v', hv', fun ρ hρ hcr => ?_⟩
      exact hagr ρ (le_trans hcr (by omega)) (fun a ha => by
        rw [hρ] at ha
        exact ha)
  iback := by
    intro n k m hZ v' hv'
    by_cases hvF : v' ∈ M.F
    · exact .inr hvF
    · obtain ⟨v, hv, hagr⟩ :=
        agree_iback (V := (∅ : Finset String)) (α := R)
          (fun χ hχc hA =>
            band_agree_stab hband hZ χ
              (Finset.eq_empty_iff_forall_notMem.mpr
                (fun a ha => Finset.notMem_empty a (hA a ha))) hχc)
          hv' hvF
      refine .inl ⟨v, hv, fun ρ hρ hcr => ?_⟩
      exact hagr ρ (le_trans hcr (by omega)) (fun a ha => by
        rw [hρ] at ha
        exact ha)
  mwit := by
    intro n k m hZ ψ hex
    exact hmf hZ hex

/-- The adversarial side condition, from `BandMback`. -/
theorem bandB_mback (R : Nat) (hband : BandCollapse R (2 * R + 2))
    (hPK : PPure p K) (hPM : PPure p M)
    (hmf : BandMwit R K M) (hmb : BandMback R K M) :
    (bandB R hband hPK hPM hmf).MBack := by
  intro n k m hZ u' hu'
  exact hmb hZ hu'

/-! ## 3. The residue is paid; the banded amalgamation -/

/-- Constant family ⇒ level collapse ⇒ the residue holds. -/
theorem bandB_mforthResidue (cl : Finset PLLFormula) (R : Nat)
    (hband : BandCollapse R (2 * R + 2))
    (hPK : PPure p K) (hPM : PPure p M)
    (hmf : BandMwit R K M) :
    MforthResidue cl (bandB R hband hPK hPM hmf) :=
  mforthResidue_of_stabilised cl (bandB R hband hPK hPM hmf)
    (fun h => h)

/-- **The one-variable amalgamation, rank-relative form**: from a band
collapse at `(R, 2R+2)` and root agreement at rank `R`, the full
p-variant conclusion — no residue hypothesis, no global dictionary,
entry budget `R`.  What remains: `BandCollapse R (2R+2)` (the plateau)
and the two m-clauses. -/
theorem restricted_amalgamation_oneVar_band (cl : Finset PLLFormula)
    (R : Nat) (hband : BandCollapse R (2 * R + 2))
    (hcl : SubClosed cl) (hadeq : OBoxAdeq cl)
    (hK : MutuallyConfluent K) (hPK : PPure p K) (hPM : PPure p M)
    (hmf : BandMwit R K M) (hmb : BandMback R K M)
    (k₀ : K.W) (m₀ : M.W)
    (hagree : bandAgree R K M k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ) :=
  amalgamation_assembledC cl (bandB R hband hPK hPM hmf) hcl hadeq hK
    (bandB_mback R hband hPK hPM hmf hmb)
    (bandB_mforthResidue cl R hband hPK hPM hmf) k₀ m₀ hagree

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.bandCollapse_of_dict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bandCollapse_of_dict

/--
info: 'PLLND.SemUI.band_agree_stab' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms band_agree_stab

/--
info: 'PLLND.SemUI.bandB_mforthResidue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bandB_mforthResidue

/--
info: 'PLLND.SemUI.restricted_amalgamation_oneVar_band' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms restricted_amalgamation_oneVar_band

end SemUI
end PLLND
