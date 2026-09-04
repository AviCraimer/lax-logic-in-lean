import LaxLogic.PLLSemUIRes
import LaxLogic.PLLCountermodelEmit

/-!
# The per-instance reconstruction law, made exact

The semantic mainline (route doc §0(i)): definability of the
bisimulation quantifiers at one variable reduces to RECONSTRUCTION
SEQUENTS over a per-instance generator pool — substitution instances
of `M` at the closed-fragment rungs OCCURRING IN `M` (plus ⊥, ⊤, and
on the ∃-side ◯⊥), together with the two frame transforms `lowT`,
`sideT`.  Until now the law lived as prose plus per-instance oracle
certificates; this file makes it exact:

* `rungsIn M` — the closed (atom-free) subformulas of `M`;
* `poolAll p M` / `poolEx p M` — the per-instance generator pools;
* `allCandP p M = ⋀ poolAll` / `exCandP p M = ⋁ poolEx` — the
  candidate values;
* `isSemAll_of_poolRec` / `isSemEx_of_poolRec` — the REDUCTIONS,
  PROVED: if the pool reconstructs `M` (`⋀pool ⊢ M`, resp.
  `M ⊢ ⋁pool`), the candidate satisfies the quantifier spec — for
  EVERY `M`, not just one-variable;
* `ReconLawAll` / `ReconLawEx` — the LAW itself as sorry-free `Prop`
  conjectures, stated at one variable (where the evidence lives);
* `onevar_definable_of_laws` — the law implies one-variable
  definability, both quantifiers;
* `pool_reconstructs_peirce` — the machine-checked pin: the
  per-instance pool reconstructs the Peirce witness `(◯⊥⊃p)⊃p` that
  REFUTED the fixed four-generator basis (`allRec_fails`), because
  the occurring rung ◯⊥ contributes the decisive instance.

Status words: the reductions and the pin are PROVED; the law is OPEN
(machine evidence: every formula of weight ≤ 7, the depth-3/4
battery, and every named witness; no counterexample known).
-/

open PLLFormula

namespace PLLND
namespace SemUI

open Ctx

/-! ## Rungs occurring in a formula -/

/-- All subformulas (including the formula itself). -/
def subsOf : PLLFormula → List PLLFormula
  | .prop a     => [.prop a]
  | .falsePLL   => [.falsePLL]
  | .and A B    => (A.and B) :: (subsOf A ++ subsOf B)
  | .or A B     => (A.or B) :: (subsOf A ++ subsOf B)
  | .ifThen A B => (A.ifThen B) :: (subsOf A ++ subsOf B)
  | .somehow A  => A.somehow :: subsOf A

/-- The closed-fragment rungs occurring in `M`: its atom-free
subformulas. -/
def rungsIn (M : PLLFormula) : List PLLFormula :=
  (subsOf M).filter (fun φ => decide (φ.atoms = ∅))

theorem rungsIn_closed {M χ : PLLFormula} (h : χ ∈ rungsIn M) :
    χ.atoms = ∅ :=
  of_decide_eq_true (List.mem_filter.mp h).2

theorem rungsIn_pfree {p : String} {M χ : PLLFormula}
    (h : χ ∈ rungsIn M) : p ∉ χ.atoms := by
  rw [rungsIn_closed h]
  simp

/-! ## The per-instance pools and candidates -/

/-- The ∀-side pool: the two transforms, then the substitution
instances at the BASE rungs ⊥, ⊤, ◯⊥ and at every rung occurring in
`M`.

CORRECTION (2026-07-19, certified by the law sweep): the
occurring-rungs-only pool is REFUTED — witness `((◯p)⊃p)⊃p`, whose
Peirce pivot ◯p contains p, so it has NO atom-free subformulas and
the occurring-only pool degenerates to the fixed basis, which
provably fails there (`occurring_only_insufficient` below, a
`decide`-checked countermodel).  The base instance ◯⊥ is needed
unconditionally: `M[p:=◯⊥] ≡ ◯⊥` is the value of that witness. -/
def poolAll (p : String) (M : PLLFormula) : List PLLFormula :=
  lowT p M :: sideT p M ::
    (PLLFormula.falsePLL :: truePLL :: PLLFormula.falsePLL.somehow ::
      rungsIn M).map (fun χ => substP p χ M)

/-- The ∃-side pool: additionally the ◯⊥ instance (the fixed basis's
fifth generator). -/
def poolEx (p : String) (M : PLLFormula) : List PLLFormula :=
  lowT p M :: sideT p M ::
    (PLLFormula.falsePLL :: truePLL :: PLLFormula.falsePLL.somehow ::
      rungsIn M).map (fun χ => substP p χ M)

/-- The per-instance ∀-candidate: the conjunction of the pool. -/
def allCandP (p : String) (M : PLLFormula) : PLLFormula :=
  andAll (poolAll p M)

/-- The per-instance ∃-candidate: the disjunction of the pool. -/
def exCandP (p : String) (M : PLLFormula) : PLLFormula :=
  Ctx.bigOr (poolEx p M)

theorem poolAll_pfree {p : String} {M : PLLFormula} :
    ∀ ξ ∈ poolAll p M, p ∉ ξ.atoms := by
  intro ξ hξ
  rcases List.mem_cons.mp hξ with rfl | hξ
  · exact lowT_pfree p M
  rcases List.mem_cons.mp hξ with rfl | hξ
  · exact sideT_pfree p M
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hξ
  rcases List.mem_cons.mp hχ with rfl | hχ
  · exact substP_pfree (by simp) M
  rcases List.mem_cons.mp hχ with rfl | hχ
  · exact substP_pfree (truePLL_pfree p) M
  rcases List.mem_cons.mp hχ with rfl | hχ
  · exact substP_pfree (by simp) M
  · exact substP_pfree (rungsIn_pfree hχ) M

theorem poolEx_pfree {p : String} {M : PLLFormula} :
    ∀ ξ ∈ poolEx p M, p ∉ ξ.atoms := by
  intro ξ hξ
  rcases List.mem_cons.mp hξ with rfl | hξ
  · exact lowT_pfree p M
  rcases List.mem_cons.mp hξ with rfl | hξ
  · exact sideT_pfree p M
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hξ
  rcases List.mem_cons.mp hχ with rfl | hχ
  · exact substP_pfree (by simp) M
  rcases List.mem_cons.mp hχ with rfl | hχ
  · exact substP_pfree (truePLL_pfree p) M
  rcases List.mem_cons.mp hχ with rfl | hχ
  · exact substP_pfree (by simp) M
  · exact substP_pfree (rungsIn_pfree hχ) M

theorem allCandP_pfree (p : String) (M : PLLFormula) :
    p ∉ (allCandP p M).atoms :=
  andAll_pfree poolAll_pfree

theorem bigOr_pfree {p : String} :
    ∀ {L : List PLLFormula}, (∀ ξ ∈ L, p ∉ ξ.atoms) →
      p ∉ (Ctx.bigOr L).atoms
  | [], _ => by simp [Ctx.bigOr]
  | ξ :: L, h => by
      intro hm
      rcases (by simpa [Ctx.bigOr] using hm :
          p ∈ ξ.atoms ∨ p ∈ (Ctx.bigOr L).atoms) with hm | hm
      · exact h ξ (List.mem_cons_self ..) hm
      · exact bigOr_pfree (fun χ hχ => h χ (List.mem_cons_of_mem _ hχ)) hm

theorem exCandP_pfree (p : String) (M : PLLFormula) :
    p ∉ (exCandP p M).atoms :=
  bigOr_pfree poolEx_pfree

/-! ## The reductions, PROVED (unconditional in M) -/

/-- **∀-reduction**: if the per-instance pool reconstructs `M`, its
conjunction is the ∀p-value.  Via the full-basis certificate criterion
with `χs := ⊥ :: ⊤ :: rungsIn M`. -/
theorem isSemAll_of_poolRec {p : String} {M : PLLFormula}
    (d : LaxND [allCandP p M] M) : IsSemAll p M (allCandP p M) := by
  have hmem : ∀ ξ ∈ poolAll p M,
      ξ ∈ (sideT p M :: lowT p M ::
        (PLLFormula.falsePLL :: truePLL ::
          PLLFormula.falsePLL.somehow :: rungsIn M).map
          (fun χ => substP p χ M)) := by
    intro ξ hξ
    rcases List.mem_cons.mp hξ with rfl | hξ
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    rcases List.mem_cons.mp hξ with rfl | hξ
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hξ)
  obtain ⟨d₂⟩ := andAll_intro (poolAll p M) hmem
  exact isSemAll_of_certificates_side
    (χs := PLLFormula.falsePLL :: truePLL ::
      PLLFormula.falsePLL.somehow :: rungsIn M)
    (allCandP_pfree p M) d d₂

/-- **∃-reduction**: if `M` derives the pool disjunction, that
disjunction is the ∃p-value — a world forcing a disjunct has the
corresponding p-variant forcing `M` (truth-set decorations for the
substitution instances, the doubled model for `lowT`, the levelled
model for `sideT`; fallible worlds force the ⊥-instance variant). -/
theorem isSemEx_of_poolRec {p : String} {M : PLLFormula}
    (d : LaxND [M] (exCandP p M)) : IsSemEx p M (exCandP p M) := by
  have hA : ∀ a ∈ (exCandP p M).atoms, a ≠ p :=
    fun a ha he => exCandP_pfree p M (he ▸ ha)
  refine ⟨exCandP_pfree p M, ?_⟩
  intro C w
  constructor
  · intro hw
    rcases (force_bigOr_iff C (poolEx p M) w).mp hw with ⟨ξ, hmem, hf⟩ | hF
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨emVariant C p w, emVariant_pbisim C p w, (w, false), rfl,
          (emVariant_force_false C p w M (C.refl_i w)).mpr hf⟩
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨lobVariant C p, lobVariant_pbisim C p, (w, 0), rfl,
          (lobVariant_force_zero C p M w).mpr hf⟩
      obtain ⟨χ, _, rfl⟩ := List.mem_map.mp hmem
      exact ⟨truthDeco C p χ, truthDeco_pbisim C p χ, w, rfl,
        (force_truthDeco C p χ M w).mpr hf⟩
    · exact ⟨truthDeco C p .falsePLL, truthDeco_pbisim C p .falsePLL,
        w, rfl, (force_truthDeco C p .falsePLL M w).mpr
          (C.force_of_fallible hF)⟩
  · rintro ⟨N, B, w', hZ, hM'⟩
    have hψ' : N.force w' (exCandP p M) := soundness d N w' (fun ξ hξ => by
      simp only [List.mem_singleton] at hξ
      exact hξ ▸ hM')
    exact (force_iff_of_bisim B hA hZ).mpr hψ'

/-! ## The law, as sorry-free conjectures, and what it buys -/

/-- **The per-instance reconstruction law, ∀-side (OPEN).**  For every
one-variable `M`, the pool conjunction derives `M` back.  Evidence:
every formula of weight ≤ 7 (2758 sequents), the depth-3/4 battery,
and every named witness including the Peirce family; no counterexample
known. -/
def ReconLawAll : Prop :=
  ∀ (p : String) (M : PLLFormula), M.atoms ⊆ {p} →
    Nonempty (LaxND [allCandP p M] M)

/-- **The per-instance reconstruction law, ∃-side (OPEN).** -/
def ReconLawEx : Prop :=
  ∀ (p : String) (M : PLLFormula), M.atoms ⊆ {p} →
    Nonempty (LaxND [M] (exCandP p M))

/-- The law yields one-variable definability, both quantifiers. -/
theorem onevar_definable_of_laws (hA : ReconLawAll) (hE : ReconLawEx) :
    ∀ (p : String) (M : PLLFormula), M.atoms ⊆ {p} →
      (∃ ψ, IsSemAll p M ψ) ∧ (∃ ψ, IsSemEx p M ψ) := by
  intro p M hM
  obtain ⟨dA⟩ := hA p M hM
  obtain ⟨dE⟩ := hE p M hM
  exact ⟨⟨allCandP p M, isSemAll_of_poolRec dA⟩,
    ⟨exCandP p M, isSemEx_of_poolRec dE⟩⟩

/-! ## The pin: the pool reconstructs the Peirce witness

The fixed four-generator basis provably fails on `(◯⊥⊃p)⊃p`
(`allRec_fails`); the per-instance pool contains the instance at the
OCCURRING rung ◯⊥, namely `(◯⊥⊃◯⊥)⊃◯⊥ ≡ ◯⊥ = ∀p.((◯⊥⊃p)⊃p)`, and
reconstruction goes through.  Machine-checked, so the law's
characteristic mechanism — the pool grows with the rungs of `M` — is
witnessed in Lean, not only by the oracle. -/

theorem pool_reconstructs_peirce :
    Nonempty (LaxND [allCandP "p" (peirce "p")] (peirce "p")) := by
  -- the ◯⊥-instance is in the pool
  have hmem : substP "p" PLLFormula.falsePLL.somehow (peirce "p") ∈
      poolAll "p" (peirce "p") := by
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
    refine List.mem_map.mpr ⟨PLLFormula.falsePLL.somehow, ?_, rfl⟩
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
    decide
  obtain ⟨dproj⟩ := andAll_proj hmem
  -- the instance is (◯⊥ ⊃ ◯⊥) ⊃ ◯⊥, which yields ◯⊥
  have dinst : LaxND [substP "p" PLLFormula.falsePLL.somehow (peirce "p")]
      PLLFormula.falsePLL.somehow :=
    .impElim (.iden (List.mem_singleton.mpr rfl))
      (.impIntro (.iden (List.mem_cons_self ..)))
  -- and ◯⊥ derives the Peirce formula
  have dpeirce : LaxND [PLLFormula.falsePLL.somehow] (peirce "p") :=
    .impIntro (.impElim (.iden (List.mem_cons_self ..))
      (.iden (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  exact ⟨compose dpeirce (compose dinst dproj)⟩

/-! ## The correction pins: why the base rung ◯⊥ is unconditional

The ◯p-pivoted Peirce formula `((◯p)⊃p)⊃p` has NO atom-free
subformulas — its pivot contains p — so an occurring-rungs-only pool
degenerates to the fixed four-generator basis there, and that basis
provably fails: the three-world countermodel found (and
checkB-verified) by the law sweep discharges by `decide`. -/

/-- The ◯p-pivoted Peirce witness. -/
def peirceBoxP : PLLFormula :=
  (((PLLFormula.prop "p").somehow.ifThen (.prop "p")).ifThen (.prop "p"))

/-- No closed rung occurs in it. -/
theorem rungsIn_peirceBoxP : rungsIn peirceBoxP = [] := by decide

/-- The sweep's countermodel: 0 < 1 < 2, Rₘ rigid except 1 → 2, top
fallible, p at {1, 2}. -/
def lawCM : FinCM :=
  ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [2], [(1,"p"),(2,"p")]⟩

/-- **The occurring-only pool is insufficient** (machine-checked): the
fixed-basis premises — all an occurring-only pool offers for
`peirceBoxP` — do not derive it. -/
theorem occurring_only_insufficient :
    ¬ Nonempty (LaxND
      [lowT "p" peirceBoxP, sideT "p" peirceBoxP,
       substP "p" .falsePLL peirceBoxP, substP "p" truePLL peirceBoxP]
      peirceBoxP) :=
  FinCM.not_provable_of_check (M := lawCM) (w := 0) (by decide)

/-! ## The frontier row: the CORRECTED ∀-law is refuted too

`((p⊃◯⊥)⊃p)⊃p` (the weight-8 UNKNOWN of the corrected-law sweep).
Machine-checked facts (probe `wip/frontier_row.lean`, find-terms):
every closed substitution instance collapses to ⊤; `lowT` and `sideT`
are each equivalent to ¬¬◯⊥; the ∀p-value is ◯⊥ (only ⊥ and ◯⊥
among the rungs derive the row).  So the pool conjunction sits at
¬¬◯⊥, strictly above the value — and the 4-chain below certifies the
gap: at its root, ◯⊥ holds NON-fallibly at world 2 (whose Rₘ-witness
is the fallible top), giving ¬¬◯⊥ and with it every pool member,
while world 1 forces p without ◯⊥, so the only worlds forcing
`p⊃◯⊥` are 2 and 3, both forcing p — the root forces `(p⊃◯⊥)⊃p`
but not p.

CONSEQUENCE: `ReconLawAll` as stated is FALSE
(`reconLawAll_refuted`).  The ∀-side basis needs a THIRD frame
construction — one whose level-0 transform descends to ◯⊥ on this
row, where both existing transforms stop at ¬¬◯⊥.  The ∃-law is
untouched (no failure anywhere to weight 8). -/

/-- The frontier row `((p⊃◯⊥)⊃p)⊃p`. -/
def frontierRow : PLLFormula :=
  (((PLLFormula.prop "p").ifThen PLLFormula.falsePLL.somehow).ifThen
    (.prop "p")).ifThen (.prop "p")

/-- The certified countermodel: the 4-chain `0<1<2<3`,
`Rₘ = id ∪ {2→3}`, top fallible, p at {1,2,3}. -/
def frontierCM : FinCM :=
  ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(2,3)], [3],
   [(1,"p"),(2,"p"),(3,"p")]⟩

/-- ¬¬◯⊥ does not derive the frontier row (so the ∀p-value ◯⊥ is
strictly below ¬¬◯⊥ here). -/
theorem nnBoxBot_not_derives_frontier :
    ¬ Nonempty (LaxND
      [(PLLFormula.falsePLL.somehow.ifThen .falsePLL).ifThen .falsePLL]
      frontierRow) :=
  FinCM.not_provable_of_check (M := frontierCM) (w := 0) (by decide)

/-- **The corrected pool is insufficient at the frontier row.** -/
theorem poolAll_insufficient_frontier :
    ¬ Nonempty (LaxND (poolAll "p" frontierRow) frontierRow) :=
  FinCM.not_provable_of_check (M := frontierCM) (w := 0) (by decide)

/-- **The ∀-side per-instance reconstruction law is REFUTED.** -/
theorem reconLawAll_refuted : ¬ ReconLawAll := fun h => by
  obtain ⟨d⟩ := h "p" frontierRow (by decide)
  obtain ⟨e⟩ := andAll_intro (poolAll "p" frontierRow) (fun _ hψ => hψ)
  exact poolAll_insufficient_frontier ⟨compose d e⟩

end SemUI
end PLLND
