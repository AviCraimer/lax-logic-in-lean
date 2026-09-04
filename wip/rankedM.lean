import wip.bandW

/-!
# The ranked ascent: pillar 2 closes with NO band and NO finiteness

Branch `ui-confluence`.  The decisive observation, extracted from the
maximal-type ascent: its finiteness input is `frag_reps_exist'` — the
PER-RANK finiteness of the variable-free fragment (pillar 1, proved
long ago) — NOT finiteness of the whole fragment.  The band collapse
entered the proof at exactly one point: lifting the link agreement
from rank `R` to the boxed-character rank `R + 3`.  If the link
DIRECTLY provides agreement at rank `α + 3`, the ascent needs nothing
else.  Hence:

1. `rankedMwit` (PROVED, UNCONDITIONAL over mutually confluent
   models): variable-free agreement at rank `α + 3` yields, for every
   K-row witness of any `ψ`, a K-row witness of `ψ` whose M-row
   partner agrees with it at rank `α` — with NO fallible escape.  The
   m-witness clause costs a rank spend of `+3`, CHEAPER than the
   i-clauses' `2α + 2` halving.

2. `rankedMwitM` (PROVED): the mirror clause, by symmetry.

3. `rankedB` (PROVED): the layered witness link `Z n := ` variable-free
   agreement at rank `rslope n` (`rslope 0 = 0`,
   `rslope (n+1) = 2·rslope n + 3` — one halving for the i-clauses,
   `+3` for the m-clauses, both covered) is a lawful
   `LayeredBisimWit` off `p` between one-variable (`POnly` — the
   CORRECTED purity: `V a ⊆ F` off `p`; the stricter `PPure` secretly
   forces infallibility, wip/bandRefute.lean) mutually confluent
   models, and satisfies `MWitM` — EVERY clause of the witness
   pipeline's input, from pure rank-bounded agreement.  PILLAR 2 IS
   CLOSED in the ranked setting: no band, no dictionary, no fragment
   finiteness.

4. `restricted_amalgamation_oneVar_ranked` (PROVED modulo
   `MwitResidue`): the one-variable amalgamation from root agreement
   at the FIXED rank `rslope (2·cl.card + 1)` — tower-exponential in
   the closure size, but determined by it.  The single open Prop of
   the entire unconditional route is now `MwitResidue` for the ranked
   link: the two-degenerate-partners configuration, whose geography is
   already mapped (`residue_growth_boundary`: sub-boundary p-free
   growth propagates, so genuine configurations are p-laden or sit on
   the crank boundary — the exact S4/K4 UI-killing mechanism, now
   isolated as the last wall).

5. `bandMwit_of_collapse'`: the band ascent factors through the ranked
   one — band collapse = stabilisation feeding the ranked clause.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp
open ConfluentU

variable {p : String} {K M : ConstraintModel}

/-- Band agreement restricts down the rank. -/
theorem bandAgree_mono {α β : Nat} (hαβ : α ≤ β)
    {k : K.W} {m : M.W} (h : bandAgree β K M k m) :
    bandAgree α K M k m :=
  fun ρ hρ hc => h ρ hρ (le_trans hc hαβ)

/-! ## 1. The ranked m-witness clause -/

/-- **The ranked m-witness clause** — the maximal-type ascent with
per-rank finiteness only: over mutually confluent `K`, `M`,
variable-free agreement at rank `α + 3` answers every K-row witness by
one whose M-partner agrees at rank `α`.  No band, no escape.  The
`+3` pays for boxing the positive rank-`α` character
(`crank (◯ charPos) = α + 3`); termination is the strict growth of
the witness's representative type under the confluence square. -/
theorem rankedMwit {α : Nat}
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    {k : K.W} {m : M.W} (hZ : bandAgree (α + 3) K M k m)
    {ψ : PLLFormula} (hex : ∃ κ, K.Rm k κ ∧ K.force κ ψ) :
    ∃ κ u', K.Rm k κ ∧ K.force κ ψ ∧ M.Rm m u' ∧
      bandAgree α K M κ u' := by
  classical
  obtain ⟨L, hL, hrep⟩ := frag_reps_exist' (∅ : Finset String) α
  -- forward character step: K-row world → M-row partner covering its type
  have hforward : ∀ {κ : K.W}, K.Rm k κ →
      ∃ u', M.Rm m u' ∧ ∀ D ∈ L, K.force κ D → M.force u' D := by
    intro κ hkκ
    set χ : PLLFormula := charPos K κ L with hχdef
    have hχa : χ.atoms = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (fun a ha =>
        Finset.notMem_empty a
          (atoms_charPos (fun D hD => (hL D hD).2) a ha))
    have hχc : crank χ ≤ α + 1 :=
      crank_charPos_le (fun D hD => (hL D hD).1)
    have hkbox : K.force k (PLLFormula.somehow χ) := by
      rw [force_somehow_iff_of_confluent hK]
      exact ⟨κ, hkκ, force_charPos K κ L⟩
    have hmbox : M.force m (PLLFormula.somehow χ) := by
      refine (hZ (PLLFormula.somehow χ) ?_ ?_).mp hkbox
      · show χ.atoms = ∅
        exact hχa
      · show crank χ + 2 ≤ α + 3
        omega
    rw [force_somehow_iff_of_confluent hM] at hmbox
    obtain ⟨u', hmu', hχu'⟩ := hmbox
    refine ⟨u', hmu', fun D hD hκD => ?_⟩
    exact (force_bigAnd_iff M u' _).mp hχu' D
      (List.mem_filter.mpr ⟨hD, decide_eq_true hκD⟩)
  -- backward character step: M-row world → K-row partner covering its type
  have hbackward : ∀ {u' : M.W}, M.Rm m u' →
      ∃ κ', K.Rm k κ' ∧ ∀ D ∈ L, M.force u' D → K.force κ' D := by
    intro u' hmu'
    set χ : PLLFormula := charPos M u' L with hχdef
    have hχa : χ.atoms = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (fun a ha =>
        Finset.notMem_empty a
          (atoms_charPos (fun D hD => (hL D hD).2) a ha))
    have hχc : crank χ ≤ α + 1 :=
      crank_charPos_le (fun D hD => (hL D hD).1)
    have hmbox : M.force m (PLLFormula.somehow χ) := by
      rw [force_somehow_iff_of_confluent hM]
      exact ⟨u', hmu', force_charPos M u' L⟩
    have hkbox : K.force k (PLLFormula.somehow χ) := by
      refine (hZ (PLLFormula.somehow χ) ?_ ?_).mpr hmbox
      · show χ.atoms = ∅
        exact hχa
      · show crank χ + 2 ≤ α + 3
        omega
    rw [force_somehow_iff_of_confluent hK] at hkbox
    obtain ⟨κ', hkκ', hχκ'⟩ := hkbox
    refine ⟨κ', hkκ', fun D hD hu'D => ?_⟩
    exact (force_bigAnd_iff K κ' _).mp hχκ' D
      (List.mem_filter.mpr ⟨hD, decide_eq_true hu'D⟩)
  -- the ascent over the finite representative type
  suffices main : ∀ (n : Nat) (κ : K.W), K.Rm k κ → K.force κ ψ →
      L.length ≤ L.countP (fun D => decide (K.force κ D)) + n →
      ∃ κ' u', K.Rm k κ' ∧ K.force κ' ψ ∧ M.Rm m u' ∧
        bandAgree α K M κ' u' by
    obtain ⟨κ₀, hkκ₀, hκ₀ψ⟩ := hex
    exact main L.length κ₀ hkκ₀ hκ₀ψ (Nat.le_add_left _ _)
  intro n
  induction n with
  | zero =>
      intro κ hkκ hκψ hcount
      obtain ⟨u', hmu', hpres⟩ := hforward hkκ
      have hall : ∀ D ∈ L, K.force κ D := fun D hD =>
        of_decide_eq_true (all_of_countP_ge (by omega) D hD)
      refine ⟨κ, u', hkκ, hκψ, hmu', fun ρ hρa hρc => ?_⟩
      obtain ⟨D, hDL, hd₁, hd₂⟩ := hrep ρ hρc
        (fun a ha => by rw [hρa] at ha; exact absurd ha (Finset.notMem_empty a))
      have hI : Interd ρ D := ⟨hd₁, hd₂⟩
      exact iff_of_true
        ((interd_force_iff hI K κ).mpr (hall D hDL))
        ((interd_force_iff hI M u').mpr (hpres D hDL (hall D hDL)))
  | succ n ih =>
      intro κ hkκ hκψ hcount
      obtain ⟨u', hmu', hpres⟩ := hforward hkκ
      by_cases hsub : ∀ D ∈ L, M.force u' D → K.force κ D
      · -- exact type match: rank-α agreement
        refine ⟨κ, u', hkκ, hκψ, hmu', fun ρ hρa hρc => ?_⟩
        obtain ⟨D, hDL, hd₁, hd₂⟩ := hrep ρ hρc
          (fun a ha => by rw [hρa] at ha; exact absurd ha (Finset.notMem_empty a))
        have hI : Interd ρ D := ⟨hd₁, hd₂⟩
        exact ((interd_force_iff hI K κ).trans
          (Iff.intro (hpres D hDL) (hsub D hDL))).trans
            (interd_force_iff hI M u').symm
      · -- overshoot at D₀: ascend through the confluence square
        push_neg at hsub
        obtain ⟨D₀, hD₀L, hD₀u, hD₀κ⟩ := hsub
        obtain ⟨κ', hkκ', hpres'⟩ := hbackward hmu'
        obtain ⟨y, hκy, hκ'y⟩ := hK hkκ (K.sub_mi hkκ')
        have hky : K.Rm k y := K.trans_m hkκ' hκ'y
        have hyψ : K.force y ψ := K.force_hered hκy hκψ
        have hchain : ∀ D ∈ L, K.force κ D → K.force y D := fun D hD h =>
          K.force_hered (K.sub_mi hκ'y) (hpres' D hD (hpres D hD h))
        have hyD₀ : K.force y D₀ :=
          K.force_hered (K.sub_mi hκ'y) (hpres' D₀ hD₀L hD₀u)
        have hlt : L.countP (fun D => decide (K.force κ D)) <
            L.countP (fun D => decide (K.force y D)) := by
          refine countP_lt_of_witness
            (fun D hD h => decide_eq_true (hchain D hD (of_decide_eq_true h)))
            hD₀L (decide_eq_true hyD₀) ?_
          simp only [decide_eq_true_eq]
          exact hD₀κ
        exact ih y hky hyψ (by omega)

/-- The mirror clause, by symmetry of variable-free agreement. -/
theorem rankedMwitM {α : Nat}
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    {k : K.W} {m : M.W} (hZ : bandAgree (α + 3) K M k m)
    {ψ : PLLFormula} (hex : ∃ u', M.Rm m u' ∧ M.force u' ψ) :
    ∃ u' κ, M.Rm m u' ∧ M.force u' ψ ∧ K.Rm k κ ∧
      bandAgree α K M κ u' := by
  obtain ⟨u₁, κ₁, hmu₁, hu₁ψ, hkκ₁, hagr⟩ :=
    rankedMwit (K := M) (M := K) hM hK (bandAgree_symm hZ) hex
  exact ⟨u₁, κ₁, hmu₁, hu₁ψ, hkκ₁, bandAgree_symm hagr⟩

/-- The band ascent factors through the ranked one: band collapse =
stabilisation feeding `rankedMwit` (needs `1 ≤ R` for
`R + 3 ≤ 2R + 2`). -/
theorem bandMwit_of_collapse' {R : Nat} (hR : 1 ≤ R)
    (hband : BandCollapse R (2 * R + 2))
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M) :
    BandMwit R K M := by
  intro k m hZ ψ hex
  have hZ3 : bandAgree (R + 3) K M k m := fun ρ hρa hρc =>
    band_agree_stab hband hZ ρ hρa (by omega)
  obtain ⟨κ, u', hkκ, hκψ, hmu', hagr⟩ := rankedMwit hK hM hZ3 hex
  exact ⟨κ, u', hkκ, hκψ, hmu', .inl (bandAgree_mono (by omega) hagr)⟩

/-! ## 2. The ranked layered link: pillar 2, closed -/

/-- **The corrected one-variable purity**: off `p`, atoms carry only
the decoration `full_F` mandates (`V a ⊆ F`).  The stricter `PPure`
(`V a = ∅` off `p`) secretly forces infallibility
(`ppure_ffree`, wip/bandRefute.lean) and so trivialised the p-pure
statements; under `POnly`, fallible one-variable models are genuinely
in scope, and the atoms clause reduces to the fallibility clause. -/
def POnly (p : String) (C : ConstraintModel) : Prop :=
  ∀ a, a ≠ p → ∀ w : C.W, w ∈ C.V a → w ∈ C.F

/-- The old purity implies the corrected one (vacuously off `p`). -/
theorem POnly.of_pPure {C : ConstraintModel} (h : PPure p C) :
    POnly p C :=
  fun a ha w hw => absurd hw (h a ha w)

/-- The rank slope: one halving for the i-clauses (`2α + 2`), a `+3`
for the m-clauses — `2·s + 3` covers both. -/
def rslope : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * rslope n + 3

theorem rslope_succ (n : Nat) : rslope (n + 1) = 2 * rslope n + 3 := rfl

theorem rslope_le_succ (n : Nat) : rslope n ≤ rslope (n + 1) := by
  rw [rslope_succ]
  omega

/-- **The ranked witness link — pillar 2 is CLOSED**: between
one-variable (`POnly`) mutually confluent models, `Z n := `
variable-free agreement at rank `rslope n` is a lawful
`LayeredBisimWit` off `p`, from NOTHING but the agreement itself:
atoms by the corrected purity through the fallibility clause (rank 0),
the i-clauses by the character argument, the m-witness clause by the
ranked ascent. -/
def rankedB (hPK : POnly p K) (hPM : POnly p M)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M) :
    LayeredBisimWit (fun a => a ≠ p) K M where
  Z := fun n k m => bandAgree (rslope n) K M k m
  mono := by
    intro n k m h
    exact bandAgree_mono (rslope_le_succ n) h
  atoms := by
    intro n k m hZ a ha
    have hfall : k ∈ K.F ↔ m ∈ M.F :=
      hZ PLLFormula.falsePLL atoms_false (Nat.zero_le _)
    constructor
    · intro hv
      exact M.full_F (hfall.mp (hPK a ha k hv))
    · intro hv
      exact K.full_F (hfall.mpr (hPM a ha m hv))
  fall := by
    intro n k m hZ
    exact hZ PLLFormula.falsePLL atoms_false (Nat.zero_le _)
  iforth := by
    intro n k m hZ v hv
    by_cases hvF : v ∈ K.F
    · exact .inr hvF
    · obtain ⟨v', hv', hagr⟩ :=
        agree_iforth (V := (∅ : Finset String)) (α := rslope n)
          (fun χ hχc hA =>
            hZ χ (Finset.eq_empty_iff_forall_notMem.mpr
              (fun a ha => Finset.notMem_empty a (hA a ha)))
              (le_trans hχc (by rw [rslope_succ]; omega)))
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
        agree_iback (V := (∅ : Finset String)) (α := rslope n)
          (fun χ hχc hA =>
            hZ χ (Finset.eq_empty_iff_forall_notMem.mpr
              (fun a ha => Finset.notMem_empty a (hA a ha)))
              (le_trans hχc (by rw [rslope_succ]; omega)))
          hv' hvF
      refine .inl ⟨v, hv, fun ρ hρ hcr => ?_⟩
      exact hagr ρ (le_trans hcr (by omega)) (fun a ha => by
        rw [hρ] at ha
        exact ha)
  mwit := by
    intro n k m hZ ψ hex
    obtain ⟨κ, u', hkκ, hκψ, hmu', hagr⟩ :=
      rankedMwit (α := rslope n) hK hM
        (bandAgree_mono (by rw [rslope_succ]; omega) hZ) hex
    exact ⟨κ, u', hkκ, hκψ, hmu', .inl hagr⟩

/-- The ranked link satisfies the M-side witness clause — the mirror
ascent.  With this, EVERY input obligation of the witness pipeline is
paid from rank-bounded agreement alone. -/
theorem rankedB_mwitM (hPK : POnly p K) (hPM : POnly p M)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M) :
    (rankedB hPK hPM hK hM).MWitM := by
  intro n k m hZ ψ hex
  obtain ⟨u', κ, hmu', hψ, hkκ, hagr⟩ :=
    rankedMwitM (α := rslope n) hK hM
      (bandAgree_mono (by rw [rslope_succ]; omega) hZ) hex
  exact ⟨u', κ, hmu', hψ, hkκ, .inl hagr⟩

/-! ## 3. The amalgamation from rank-bounded agreement alone -/

/-- **The one-variable amalgamation, ranked form**: for one-variable
(`POnly`, fallible worlds genuinely in scope) mutually confluent `K`
and `M` whose roots agree on variable-free formulas up to the FIXED
rank `rslope (2·cl.card + 1)` — determined by the closure,
tower-exponential in its size — the full witness-form p-variant
conclusion, modulo the ONE open Prop `MwitResidue` of the ranked
link.  No band, no dictionary, no fragment finiteness: after the
ranked ascent, the residue is the entire unproved content of the
route. -/
theorem restricted_amalgamation_oneVar_ranked (cl : Finset PLLFormula)
    (hcl : SubClosed cl) (hadeq : OBoxAdeq cl)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : POnly p K) (hPM : POnly p M)
    (hres : MwitResidue cl (rankedB hPK hPM hK hM))
    (k₀ : K.W) (m₀ : M.W)
    (hagree : bandAgree (rslope (2 * cl.card + 1)) K M k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisimWit p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ (∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ)) ∧
      (∀ χ : PLLFormula, (∀ a ∈ χ.atoms, a ≠ p) →
        (M.force m₀ χ ↔ N.force n₀ χ)) := by
  obtain ⟨N, C, n₀, hZ, hcls, htrans⟩ :=
    amalgamation_assembledW cl (rankedB hPK hPM hK hM) hcl hadeq hK
      (rankedB_mwitM hPK hPM hK hM) hres k₀ m₀ hagree
  exact ⟨N, C, n₀, hZ, hcls, htrans hM⟩

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.rankedMwit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rankedMwit

/--
info: 'PLLND.SemUI.rankedMwitM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rankedMwitM

/--
info: 'PLLND.SemUI.bandMwit_of_collapse'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bandMwit_of_collapse'

/--
info: 'PLLND.SemUI.rankedB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rankedB

/--
info: 'PLLND.SemUI.rankedB_mwitM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rankedB_mwitM

/--
info: 'PLLND.SemUI.restricted_amalgamation_oneVar_ranked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms restricted_amalgamation_oneVar_ranked

end SemUI
end PLLND
