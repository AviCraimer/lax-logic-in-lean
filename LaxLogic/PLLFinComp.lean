import LaxLogic.PLLCompleteness
import LaxLogic.PLLFiniteModel
import LaxLogic.PLLG4Dec
import LaxLogic.PLLCountermodelEmit

/-!
# Finitary completeness for PLL — the canonical model without Zorn

This file rebuilds the canonical-model completeness proof of
`PLLCompleteness.lean` over a *finite* subformula closure, with the Zorn
Lindenbaum lemma replaced by an **iterated decided extension**: at each
closure formula the decision "add to `val` or add to `fal`" is made by the
mechanised decision procedure (`decidablePLL`), and the else-branch is
justified by the same disjunction-combination argument that classically
proves `mem_val_or_mem_fal`.

Contents (mirroring F&M §4 / `PLLCompleteness.lean` case for case):

1. **Part 1 (foundation)** — finite theory triples `FTheory`
   (`val`/`fal`/`mfal` as `Finset`s), consistency reused verbatim from the
   classical development through `FTheory.toTheory`, its *decidability*
   (`cons_iff_check`: consistency of a finite triple is one derivability
   check on the full selection, decided by `decidablePLL`), the extension
   dichotomy `cons_insVal_or_insFal`, and the **constructive Lindenbaum**
   `lindenbaum`: a computable fold extending any consistent triple to a
   closure-total one, leaving `mfal` untouched.
2. Part 2 — the finite Lemma 4.2 suite (`ded_closed`, `or_mem`, `imp_mem`,
   `fal_or`, `fal_and`, `mfal_sub_fal`, …) relative to a subformula-closed
   `cl`, by the classical proofs with `∈ cl` side conditions (maximality is
   consumed *only* through the extension-failure witnesses, which
   closure-totality supplies).
3. Part 3 — the truth lemma on the finite canonical model (worlds = the
   closure-total consistent triples; `Rᵢ` = inclusion on `val`; `Rₘ` =
   inclusion on `val` and `mfal`), with the three Lindenbaum extension
   steps of the classical proof replaced by `lindenbaum`.
4. Part 4 — enumeration of the (finitely many) worlds into a `FinCM`,
   `checkB` certification, and **emitter completeness**: every underivable
   sequent has a checked countermodel.  The composition with the
   presented-strategy squeeze lives in `PLLRealCompleteness.lean`.

Audit note (re-measured 2026-07-18, after the choice-scrub): the
mathematics here is finitary (no Zorn anywhere), and the whole
development now audits **`[propext, Quot.sound]`** — see the guards at
the foot for `lindenbaum`, `cons_insVal_or_insFal`, `truth_lemma`,
`finite_canonical_countermodel` and `emitter_completeness`.  The three
former `Classical.choice` sources were removed structurally:

1. the decidability infrastructure (`decidablePLL`, `G4c_iff_search`)
   now runs on the choice-free `Finset` toolkit
   (`PLLFinsetKit.lean`) and the height-bounded decider `G4sh.dec`
   (`PLLG4Set.lean`) — see the audit note in `PLLG4Dec.lean`;
2. consistency of a triple is decided by the Boolean `consB`, lifted
   over `Prop`-level representative lists of `fal`/`mfal`
   (`Quotient.liftOn` with `disjOf_mono` as permutation-invariance) —
   no `Finset.toList`; the world enumeration for the emitter is
   likewise parameterised over listed worlds (`canonCMof`), supplied
   inside the proof from `exists_rep`;
3. the extension dichotomy `cons_insVal_or_insFal` extracts its
   failure witnesses by decidable case analysis on the representative
   check — no `push_neg`, no `not_consistent_iff`.

The only remaining choice-tainted results in this file are the legacy
`Finset.toList`-phrased forms (`setDeriv_coe_iff`, `cons_iff_check`,
`worldFinset`/`worldList`/`canonFinCM` and their `Charac` lemmas,
including `transfer`): their *statements* mention `Finset.toList`
(`Classical.choice` by definition) or are built on it, so they cannot
audit choice-free however proved.  Nothing in the clean chain uses
them.
-/

open PLLFormula

namespace PLLND
namespace FinComp

/-! ## Finite theory triples -/

/-- A finite theory triple: `val`idated / `fal`sified / `mfal` = falsified
at every `Rₘ`-successor, all finite. -/
structure FTheory where
  val : Finset PLLFormula
  fal : Finset PLLFormula
  mfal : Finset PLLFormula
  deriving DecidableEq

namespace FTheory

/-- The associated (set-valued) theory of the classical development. -/
def toTheory (T : FTheory) : Theory := ⟨↑T.val, ↑T.fal, ↑T.mfal⟩

@[simp] theorem toTheory_val (T : FTheory) : T.toTheory.val = ↑T.val := rfl
@[simp] theorem toTheory_fal (T : FTheory) : T.toTheory.fal = ↑T.fal := rfl
@[simp] theorem toTheory_mfal (T : FTheory) : T.toTheory.mfal = ↑T.mfal := rfl

/-- Consistency, reused from the classical development. -/
def Cons (T : FTheory) : Prop := Consistent T.toTheory

/-- Componentwise inclusion. -/
def le (T T' : FTheory) : Prop :=
  T.val ⊆ T'.val ∧ T.fal ⊆ T'.fal ∧ T.mfal ⊆ T'.mfal

theorem le_refl (T : FTheory) : T.le T := ⟨subset_rfl, subset_rfl, subset_rfl⟩

theorem le_trans {T₁ T₂ T₃ : FTheory} (h : T₁.le T₂) (h' : T₂.le T₃) :
    T₁.le T₃ :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

/-- Insert into the validated part. -/
def insVal (φ : PLLFormula) (T : FTheory) : FTheory :=
  ⟨insert φ T.val, T.fal, T.mfal⟩

/-- Insert into the falsified part. -/
def insFal (φ : PLLFormula) (T : FTheory) : FTheory :=
  ⟨T.val, insert φ T.fal, T.mfal⟩

end FTheory

/-! ## Decidability of consistency -/

/-- Set-derivability from a finset coercion is list-derivability from its
`toList`. -/
theorem setDeriv_coe_iff {V : Finset PLLFormula} {φ : PLLFormula} :
    (↑V : Set PLLFormula) ⊩ φ ↔ Nonempty (LaxND V.toList φ) := by
  constructor
  · rintro ⟨L, hL, ⟨p⟩⟩
    exact ⟨p.rename fun ψ hψ => Finset.mem_toList.mpr (hL ψ hψ)⟩
  · rintro ⟨p⟩
    exact ⟨V.toList, fun ψ hψ => Finset.mem_toList.mp hψ, ⟨p⟩⟩

/-- Set-derivability from a finset coercion, as a Boolean: lift
`decide (Nonempty (Tm l φ))` over any representative list of the
underlying multiset — the value is permutation-invariant because
derivability is stable under renaming, and `decidablePLL` decides each
representative.  Choice-free, unlike the `Finset.toList` route. -/
def setDerivB (V : Finset PLLFormula) (φ : PLLFormula) : Bool :=
  Quotient.liftOn V.val (fun l => decide (Nonempty (Tm l φ)))
    (fun l₁ l₂ p =>
      decide_eq_decide.mpr
        ⟨fun h => curry_howard.mpr
            ((curry_howard.mp h).elim fun q =>
              ⟨q.rename fun ψ hψ => p.mem_iff.mp hψ⟩),
         fun h => curry_howard.mpr
            ((curry_howard.mp h).elim fun q =>
              ⟨q.rename fun ψ hψ => p.mem_iff.mpr hψ⟩)⟩)

theorem setDerivB_iff (V : Finset PLLFormula) (φ : PLLFormula) :
    setDerivB V φ = true ↔ (↑V : Set PLLFormula) ⊩ φ := by
  rcases V with ⟨m, hm⟩
  induction m using Quotient.inductionOn with
  | h l =>
      show decide (Nonempty (Tm l φ)) = true ↔ _
      rw [decide_eq_true_eq, curry_howard]
      constructor
      · rintro ⟨q⟩
        exact ⟨l, fun ψ hψ => hψ, ⟨q⟩⟩
      · rintro ⟨L, hL, ⟨q⟩⟩
        exact ⟨q.rename fun ψ hψ => hL ψ hψ⟩

instance (V : Finset PLLFormula) (φ : PLLFormula) :
    Decidable ((↑V : Set PLLFormula) ⊩ φ) :=
  decidable_of_iff _ (setDerivB_iff V φ)

/-- Consistency of a finite triple is a single derivability check on the
full selection (empty selections aside): `disjOf` is monotone, so the full
lists are the worst case. -/
theorem cons_iff_check (T : FTheory) :
    T.Cons ↔ (T.fal = ∅ ∧ T.mfal = ∅) ∨
      ¬ (↑T.val : Set PLLFormula) ⊩ disjOf T.fal.toList T.mfal.toList := by
  constructor
  · intro hT
    by_cases he : T.fal = ∅ ∧ T.mfal = ∅
    · exact .inl he
    · refine .inr (hT T.fal.toList T.mfal.toList
        (fun ψ hψ => Finset.mem_toList.mp hψ)
        (fun ψ hψ => Finset.mem_toList.mp hψ) ?_)
      intro hnil
      rcases List.append_eq_nil_iff.mp hnil with ⟨h₁, h₂⟩
      exact he ⟨Finset.toList_eq_nil.mp h₁, Finset.toList_eq_nil.mp h₂⟩
  · rintro (⟨he₁, he₂⟩ | hnd) Ds Ts hDs hTs hg hder
    · cases Ds with
      | nil =>
          cases Ts with
          | nil => exact hg rfl
          | cons K Ts =>
              have := hTs K (List.mem_cons_self ..)
              rw [FTheory.toTheory_mfal, he₂] at this
              simp at this
      | cons D Ds =>
          have := hDs D (List.mem_cons_self ..)
          rw [FTheory.toTheory_fal, he₁] at this
          simp at this
    · refine hnd (disjOf_mono ?_ ?_ hder)
      · exact fun ψ hψ => Finset.mem_toList.mpr (hDs ψ hψ)
      · exact fun ψ hψ => Finset.mem_toList.mpr (hTs ψ hψ)

/-- The consistency check phrased over *any* lists enumerating `fal`
and `mfal` (membership is all the proof consumes, so duplicates and
order are irrelevant).  This is the choice-free replacement for the
`Finset.toList`-phrased `cons_iff_check`. -/
theorem cons_iff_rep (T : FTheory) {lf lm : List PLLFormula}
    (hlf : ∀ x, x ∈ lf ↔ x ∈ T.fal) (hlm : ∀ x, x ∈ lm ↔ x ∈ T.mfal) :
    T.Cons ↔ (lf = [] ∧ lm = []) ∨
      ¬ (↑T.val : Set PLLFormula) ⊩ disjOf lf lm := by
  constructor
  · intro hT
    by_cases he : lf = [] ∧ lm = []
    · exact .inl he
    · refine .inr (hT lf lm
        (fun ψ hψ => Finset.mem_coe.mpr ((hlf ψ).mp hψ))
        (fun ψ hψ => Finset.mem_coe.mpr ((hlm ψ).mp hψ)) ?_)
      intro hnil
      rcases List.append_eq_nil_iff.mp hnil with ⟨h₁, h₂⟩
      exact he ⟨h₁, h₂⟩
  · rintro (⟨he₁, he₂⟩ | hnd) Ds Ts hDs hTs hg hder
    · cases Ds with
      | nil =>
          cases Ts with
          | nil => exact hg rfl
          | cons K Ts =>
              have hK : K ∈ T.mfal := by
                have := hTs K (List.mem_cons_self ..)
                rw [FTheory.toTheory_mfal] at this
                exact Finset.mem_coe.mp this
              have := (hlm K).mpr hK
              rw [he₂] at this
              cases this
      | cons D Ds =>
          have hD : D ∈ T.fal := by
            have := hDs D (List.mem_cons_self ..)
            rw [FTheory.toTheory_fal] at this
            exact Finset.mem_coe.mp this
          have := (hlf D).mpr hD
          rw [he₁] at this
          cases this
    · refine hnd (disjOf_mono ?_ ?_ hder)
      · exact fun ψ hψ => (hlf ψ).mpr (Finset.mem_coe.mp (hDs ψ hψ))
      · exact fun ψ hψ => (hlm ψ).mpr (Finset.mem_coe.mp (hTs ψ hψ))

private theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) :
    a = b := by
  cases a <;> cases b <;> simp_all

/-- Consistency of a finite triple, as a Boolean — lifted over
representatives of `fal` and `mfal`; permutation-invariance is by
`disjOf_mono` (membership-monotonicity of the consistency formula). -/
def consB (T : FTheory) : Bool :=
  Quotient.liftOn₂ T.fal.val T.mfal.val
    (fun lf lm =>
      (decide (lf = []) && decide (lm = [])) ||
        !setDerivB T.val (disjOf lf lm))
    (fun lf₁ lm₁ lf₂ lm₂ pf pm => by
      have hf : lf₁ = [] ↔ lf₂ = [] := by
        rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff,
          pf.length_eq]
      have hm : lm₁ = [] ↔ lm₂ = [] := by
        rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff,
          pm.length_eq]
      have hd : setDerivB T.val (disjOf lf₁ lm₁)
          = setDerivB T.val (disjOf lf₂ lm₂) :=
        bool_eq_of_iff (by
          rw [setDerivB_iff, setDerivB_iff]
          exact ⟨disjOf_mono (fun φ h => pf.mem_iff.mp h)
              (fun φ h => pm.mem_iff.mp h),
            disjOf_mono (fun φ h => pf.mem_iff.mpr h)
              (fun φ h => pm.mem_iff.mpr h)⟩)
      rw [decide_eq_decide.mpr hf, decide_eq_decide.mpr hm, hd])

theorem consB_iff (T : FTheory) : consB T = true ↔ T.Cons := by
  obtain ⟨lf, hlf⟩ := exists_rep_val T.fal
  obtain ⟨lm, hlm⟩ := exists_rep_val T.mfal
  have hlf' : ∀ x, x ∈ lf ↔ x ∈ T.fal := fun x => by
    rw [← Multiset.mem_coe, hlf]
    exact Iff.rfl
  have hlm' : ∀ x, x ∈ lm ↔ x ∈ T.mfal := fun x => by
    rw [← Multiset.mem_coe, hlm]
    exact Iff.rfl
  have hred : consB T =
      ((decide (lf = []) && decide (lm = [])) ||
        !setDerivB T.val (disjOf lf lm)) := by
    unfold consB
    rw [← hlf, ← hlm]
    rfl
  rw [hred]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', ← Bool.not_eq_true, setDerivB_iff]
  exact (cons_iff_rep T hlf' hlm').symm

instance (T : FTheory) : Decidable T.Cons :=
  decidable_of_iff _ (consB_iff T)

/-! ## The extension dichotomy -/

/-- **The decided extension is safe**: a consistent triple stays consistent
when a formula is added to `val` or, failing that, to `fal` — the finite
mirror of the classical `mem_val_or_mem_fal` combination argument. -/
theorem cons_insVal_or_insFal {T : FTheory} (hT : T.Cons) (φ : PLLFormula) :
    (T.insVal φ).Cons ∨ (T.insFal φ).Cons := by
  by_cases h1 : (T.insVal φ).Cons
  · exact .inl h1
  by_cases h2 : (T.insFal φ).Cons
  · exact .inr h2
  exfalso
  -- Enumerate `fal`/`mfal` (Prop-level representatives, no choice) and
  -- turn the two failed checks into explicit full-selection derivations
  -- by decidable case analysis — no `push_neg`, no `not_consistent_iff`.
  obtain ⟨lf, -, hlf⟩ := exists_rep T.fal
  obtain ⟨lm, -, hlm⟩ := exists_rep T.mfal
  have hlf₂ : ∀ x, x ∈ φ :: lf ↔ x ∈ (T.insFal φ).fal := fun x => by
    rw [List.mem_cons, hlf x]
    exact (Finset.mem_insert).symm
  have hc1 : ¬((lf = [] ∧ lm = []) ∨
      ¬ (↑(insert φ T.val) : Set PLLFormula) ⊩ disjOf lf lm) :=
    fun hc => h1 ((cons_iff_rep (T.insVal φ) hlf hlm).mpr hc)
  have hc2 : ¬((φ :: lf = [] ∧ lm = []) ∨
      ¬ (↑T.val : Set PLLFormula) ⊩ disjOf (φ :: lf) lm) :=
    fun hc => h2 ((cons_iff_rep (T.insFal φ) hlf₂ hlm).mpr hc)
  have hg₁ : ¬(lf = [] ∧ lm = []) := fun hA => hc1 (.inl hA)
  have hd₁ : (↑(insert φ T.val) : Set PLLFormula) ⊩ disjOf lf lm := by
    by_cases hD : (↑(insert φ T.val) : Set PLLFormula) ⊩ disjOf lf lm
    · exact hD
    · exact absurd (.inr hD) hc1
  have hd₂ : (↑T.val : Set PLLFormula) ⊩ disjOf (φ :: lf) lm := by
    by_cases hD : (↑T.val : Set PLLFormula) ⊩ disjOf (φ :: lf) lm
    · exact hD
    · exact absurd (.inr hD) hc2
  rw [coeInsert] at hd₁
  have hd : (↑T.val : Set PLLFormula) ⊩
      disjOf (lf ++ rmv φ (φ :: lf)) (lm ++ lm) := by
    refine disjOf_transform hd₂ (fun ψ hψ => ?_)
      (fun ψ hψ => List.mem_append.mpr (.inr hψ))
    by_cases he : ψ = φ
    · subst he
      exact disjOf_mono
        (fun χ hχ => List.mem_append.mpr (.inl hχ))
        (fun χ hχ => List.mem_append.mpr (.inl hχ)) hd₁
    · exact disjOf_intro_fal
        (List.mem_append.mpr (.inr (mem_rmv_iff.mpr ⟨hψ, he⟩)))
        (SetDeriv.of_mem (Set.mem_insert ..))
  refine hT _ _ ?_ ?_ ?_ hd
  · intro ψ hψ
    rcases List.mem_append.mp hψ with h | h
    · exact Finset.mem_coe.mpr ((hlf ψ).mp h)
    · obtain ⟨hin, hne⟩ := mem_rmv_iff.mp h
      rcases List.mem_cons.mp hin with rfl | h'
      · exact absurd rfl hne
      · exact Finset.mem_coe.mpr ((hlf ψ).mp h')
  · intro ψ hψ
    rcases List.mem_append.mp hψ with h | h
    exacts [Finset.mem_coe.mpr ((hlm ψ).mp h),
      Finset.mem_coe.mpr ((hlm ψ).mp h)]
  · intro hnil
    rcases List.append_eq_nil_iff.mp hnil with ⟨hA, hB⟩
    rcases List.append_eq_nil_iff.mp hA with ⟨hA₁, -⟩
    rcases List.append_eq_nil_iff.mp hB with ⟨hB₁, -⟩
    exact hg₁ ⟨hA₁, hB₁⟩

/-! ## The constructive Lindenbaum extension -/

/-- One decided extension step: add `φ` to `val` if that is consistent,
otherwise to `fal` — the decision by the computable, choice-free
consistency check `consB`. -/
def extendStep (T : FTheory) (φ : PLLFormula) : FTheory :=
  if (T.insVal φ).Cons then T.insVal φ else T.insFal φ

/-- Fold the decided extension over a list of formulas. -/
def extendAll (T : FTheory) (l : List PLLFormula) : FTheory :=
  l.foldl extendStep T

theorem extendStep_cons {T : FTheory} (hT : T.Cons) (φ : PLLFormula) :
    (extendStep T φ).Cons := by
  unfold extendStep
  split
  · assumption
  · exact (cons_insVal_or_insFal hT φ).resolve_left (by assumption)

theorem extendStep_le (T : FTheory) (φ : PLLFormula) :
    T.le (extendStep T φ) := by
  unfold extendStep
  split
  · exact ⟨Finset.subset_insert .., subset_rfl, subset_rfl⟩
  · exact ⟨subset_rfl, Finset.subset_insert .., subset_rfl⟩

theorem extendStep_mem (T : FTheory) (φ : PLLFormula) :
    φ ∈ (extendStep T φ).val ∨ φ ∈ (extendStep T φ).fal := by
  unfold extendStep
  split
  · exact .inl (Finset.mem_insert_self ..)
  · exact .inr (Finset.mem_insert_self ..)

theorem extendStep_mfal (T : FTheory) (φ : PLLFormula) :
    (extendStep T φ).mfal = T.mfal := by
  unfold extendStep
  split <;> rfl

theorem extendAll_cons {T : FTheory} (hT : T.Cons) (l : List PLLFormula) :
    (extendAll T l).Cons := by
  induction l generalizing T with
  | nil => exact hT
  | cons φ l ih => exact ih (extendStep_cons hT φ)

theorem extendAll_le (T : FTheory) (l : List PLLFormula) :
    T.le (extendAll T l) := by
  induction l generalizing T with
  | nil => exact FTheory.le_refl T
  | cons φ l ih =>
      exact FTheory.le_trans (extendStep_le T φ) (ih (extendStep T φ))

theorem extendAll_mfal (T : FTheory) (l : List PLLFormula) :
    (extendAll T l).mfal = T.mfal := by
  induction l generalizing T with
  | nil => rfl
  | cons φ l ih =>
      rw [extendAll, List.foldl_cons, ← extendAll, ih, extendStep_mfal]

theorem extendAll_total (T : FTheory) (l : List PLLFormula) :
    ∀ φ ∈ l, φ ∈ (extendAll T l).val ∨ φ ∈ (extendAll T l).fal := by
  induction l generalizing T with
  | nil => intro φ h; cases h
  | cons ψ l ih =>
      intro φ h
      rw [extendAll, List.foldl_cons, ← extendAll]
      rcases List.mem_cons.mp h with rfl | h'
      · rcases extendStep_mem T φ with hv | hf
        · exact .inl ((extendAll_le (extendStep T φ) l).1 hv)
        · exact .inr ((extendAll_le (extendStep T φ) l).2.1 hf)
      · exact ih (extendStep T ψ) φ h'

/-! ## Closure-maximal triples and the Lindenbaum theorem -/

/-- All three components inside the closure. -/
def InCl (cl : Finset PLLFormula) (T : FTheory) : Prop :=
  T.val ⊆ cl ∧ T.fal ⊆ cl ∧ T.mfal ⊆ cl

/-- Closure-maximality: consistent, inside the closure, and total on it —
every closure formula is validated or falsified.  (This is what the
classical Lemma 4.2 suite actually consumes: extension-failure witnesses
for closure formulas are derivable from totality plus consistency.) -/
def MaxIn (cl : Finset PLLFormula) (T : FTheory) : Prop :=
  T.Cons ∧ InCl cl T ∧ ∀ φ ∈ cl, φ ∈ T.val ∨ φ ∈ T.fal

/-- **Constructive Lindenbaum**: every consistent triple inside the closure
extends — by a computable fold of decided steps, no Zorn — to a
closure-maximal one with the *same* promises (`mfal` untouched, as the
truth-lemma constructions require). -/
theorem lindenbaum {cl : Finset PLLFormula} {T : FTheory}
    (hT : T.Cons) (hIn : InCl cl T) :
    ∃ T', T.le T' ∧ MaxIn cl T' ∧ T'.mfal = T.mfal := by
  obtain ⟨lcl, -, hlcl⟩ := exists_rep cl
  refine ⟨extendAll T lcl, extendAll_le T _,
    ⟨extendAll_cons hT _, ?_, fun φ hφ =>
      extendAll_total T _ φ ((hlcl φ).mpr hφ)⟩,
    extendAll_mfal T _⟩
  -- the extension stays inside the closure
  have step : ∀ (T' : FTheory) (l : List PLLFormula), InCl cl T' →
      (∀ φ ∈ l, φ ∈ cl) → InCl cl (extendAll T' l) := by
    intro T' l
    induction l generalizing T' with
    | nil => intro h _; exact h
    | cons ψ l ih =>
        intro h hl
        rw [extendAll, List.foldl_cons, ← extendAll]
        refine ih _ ?_ (fun φ hφ => hl φ (List.mem_cons_of_mem _ hφ))
        have hψ : ψ ∈ cl := hl ψ (List.mem_cons_self ..)
        unfold extendStep
        split
        · exact ⟨insertSubset hψ h.1, h.2.1, h.2.2⟩
        · exact ⟨h.1, insertSubset hψ h.2.1, h.2.2⟩
  exact step T lcl hIn (fun φ hφ => (hlcl φ).mp hφ)

/-! ## Part 2: the Lemma 4.2 suite, closure-relative

With totality in hand, the classical witness-combination proofs collapse:
every extension-failure witness is a singleton selection. -/

open SetDeriv

namespace MaxIn

variable {cl : Finset PLLFormula} {T : FTheory}

/-- Derivability of a falsified formula is absurd. -/
theorem not_fal_deriv (hM : MaxIn cl T) {φ : PLLFormula} (hφ : φ ∈ T.fal)
    (hd : (↑T.val : Set PLLFormula) ⊩ φ) : False := by
  refine hM.1 [φ] [] (by simpa using hφ) (by simp) (by simp) ?_
  rw [disjOf_nil_right]
  exact bigOr_intro (List.mem_cons_self ..) hd

theorem not_mem_fal_of_mem_val (hM : MaxIn cl T) {φ : PLLFormula}
    (hv : φ ∈ T.val) : φ ∉ T.fal :=
  fun hf => hM.not_fal_deriv hf (of_mem (Finset.mem_coe.mpr hv))

/-- Deductive closure on the closure. -/
theorem ded_closed (hM : MaxIn cl T) {φ : PLLFormula} (hφcl : φ ∈ cl)
    (hd : (↑T.val : Set PLLFormula) ⊩ φ) : φ ∈ T.val := by
  rcases hM.2.2 φ hφcl with hv | hf
  · exact hv
  · exact (hM.not_fal_deriv hf hd).elim

/-- Primeness of the validated part. -/
theorem or_mem (hM : MaxIn cl T) (hcl : SubClosed cl) {φ ψ : PLLFormula}
    (h : φ.or ψ ∈ T.val) : φ ∈ T.val ∨ ψ ∈ T.val := by
  obtain ⟨hCons, ⟨hvcl, hfcl, hmcl⟩, htot⟩ := hM
  rcases htot φ (hcl.or_left (hvcl h)) with hv | hf
  · exact .inl hv
  rcases htot ψ (hcl.or_right (hvcl h)) with hv | hf'
  · exact .inr hv
  exfalso
  refine hCons [φ, ψ] [] ?_ (by simp) (by simp) ?_
  · intro χ hχ
    rcases List.mem_cons.mp hχ with rfl | hχ
    · simpa using hf
    · rcases List.mem_cons.mp hχ with rfl | hχ
      · simpa using hf'
      · cases hχ
  · rw [disjOf_nil_right]
    refine orE (of_mem (Finset.mem_coe.mpr h)) ?_ ?_
    · exact bigOr_intro (List.mem_cons_self ..) (of_mem (Set.mem_insert ..))
    · exact bigOr_intro (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (of_mem (Set.mem_insert ..))

/-- Implication decomposition. -/
theorem imp_mem (hM : MaxIn cl T) (hcl : SubClosed cl) {φ ψ : PLLFormula}
    (h : φ.ifThen ψ ∈ T.val) : φ ∈ T.fal ∨ ψ ∈ T.val := by
  have hφcl := hcl.imp_left (hM.2.1.1 h)
  have hψcl := hcl.imp_right (hM.2.1.1 h)
  rcases hM.2.2 φ hφcl with hv | hf
  · refine .inr (hM.ded_closed hψcl ?_)
    exact mp (of_mem (Finset.mem_coe.mpr h)) (of_mem (Finset.mem_coe.mpr hv))
  · exact .inl hf

/-- Falsified disjunctions decompose conjunctively. -/
theorem fal_or (hM : MaxIn cl T) (hcl : SubClosed cl) {φ ψ : PLLFormula}
    (h : φ.or ψ ∈ T.fal) : φ ∈ T.fal ∧ ψ ∈ T.fal := by
  have hocl : φ.or ψ ∈ cl := hM.2.1.2.1 h
  constructor
  · rcases hM.2.2 φ (hcl.or_left hocl) with hv | hf
    · exact (hM.not_fal_deriv h (orL _ (of_mem (Finset.mem_coe.mpr hv)))).elim
    · exact hf
  · rcases hM.2.2 ψ (hcl.or_right hocl) with hv | hf
    · exact (hM.not_fal_deriv h (orR _ (of_mem (Finset.mem_coe.mpr hv)))).elim
    · exact hf

/-- Falsified conjunctions decompose disjunctively. -/
theorem fal_and (hM : MaxIn cl T) (hcl : SubClosed cl) {φ ψ : PLLFormula}
    (h : φ.and ψ ∈ T.fal) : φ ∈ T.fal ∨ ψ ∈ T.fal := by
  have hacl : φ.and ψ ∈ cl := hM.2.1.2.1 h
  rcases hM.2.2 φ (hcl.and_left hacl) with hv | hf
  · rcases hM.2.2 ψ (hcl.and_right hacl) with hv' | hf'
    · exact (hM.not_fal_deriv h (map₂ (fun p₁ p₂ => .andIntro p₁ p₂)
        (of_mem (Finset.mem_coe.mpr hv))
        (of_mem (Finset.mem_coe.mpr hv')))).elim
    · exact .inr hf'
  · exact .inl hf

/-- Modally falsified formulas are falsified. -/
theorem mfal_sub_fal (hM : MaxIn cl T) {φ : PLLFormula} (h : φ ∈ T.mfal) :
    φ ∈ T.fal := by
  rcases hM.2.2 φ (hM.2.1.2.2 h) with hv | hf
  · exfalso
    refine hM.1 [] [φ] (by simp) (by simpa using h) (by simp) ?_
    rw [disjOf_nil_left]
    refine map (fun p => .laxIntro p) ?_
    exact bigOr_intro (List.mem_cons_self ..) (of_mem (Finset.mem_coe.mpr hv))
  · exact hf

end MaxIn

/-! ## Part 3: the finite canonical model and the truth lemma -/

/-- The finite canonical model over a closure: worlds are the
closure-maximal triples; `Rᵢ` is inclusion on `val`, `Rₘ` inclusion on
`val` and `mfal`; atoms outside the closure hold everywhere (the
filtration's convention, needed for `full_F`). -/
def canonFin (cl : Finset PLLFormula) : ConstraintModel where
  W := {T : FTheory // MaxIn cl T}
  Ri T T' := T.1.val ⊆ T'.1.val
  Rm T T' := T.1.val ⊆ T'.1.val ∧ T.1.mfal ⊆ T'.1.mfal
  F := {T | PLLFormula.falsePLL ∈ T.1.val}
  V a := {T | PLLFormula.prop a ∉ cl ∨ PLLFormula.prop a ∈ T.1.val}
  refl_i _ := subset_rfl
  trans_i h h' := h.trans h'
  refl_m _ := ⟨subset_rfl, subset_rfl⟩
  trans_m h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩
  sub_mi h := h.1
  hered_F h hw := h hw
  hered_V h hw := hw.imp_right (fun h' => h h')
  full_F {a} {T} hw := by
    by_cases hcl : PLLFormula.prop a ∈ cl
    · exact .inr (T.2.ded_closed hcl
        (falso _ (of_mem (Finset.mem_coe.mpr hw))))
    · exact .inl hcl

private theorem not_mem_coe_empty {K : PLLFormula}
    (h : K ∈ (↑(∅ : Finset PLLFormula) : Set PLLFormula)) : False :=
  Finset.notMem_empty K (Finset.mem_coe.mp h)

private theorem eq_of_mem_coe_singleton {K ψ : PLLFormula}
    (h : K ∈ (↑({ψ} : Finset PLLFormula) : Set PLLFormula)) : K = ψ :=
  Finset.mem_singleton.mp (Finset.mem_coe.mp h)

/-- **The truth lemma**, finitely: on the finite canonical model over a
subformula-closed closure, membership in `val` forces and membership in
`fal` refutes — with all three extension steps supplied by the
constructive `lindenbaum`. -/
theorem truth_lemma {cl : Finset PLLFormula} (hcl : SubClosed cl) :
    ∀ (φ : PLLFormula), φ ∈ cl → ∀ T : (canonFin cl).W,
      (φ ∈ T.1.val → (canonFin cl).force T φ) ∧
        (φ ∈ T.1.fal → ¬ (canonFin cl).force T φ) := by
  intro φ
  induction φ with
  | prop a =>
      intro hφ T
      refine ⟨fun h => .inr h, fun h hf => ?_⟩
      rcases hf with hout | hv
      · exact hout (T.2.2.1.2.1 h)
      · exact T.2.not_fal_deriv h (of_mem (Finset.mem_coe.mpr hv))
  | falsePLL =>
      intro hφ T
      refine ⟨fun h => h, fun h hf => ?_⟩
      exact T.2.not_fal_deriv h (of_mem (Finset.mem_coe.mpr hf))
  | and φ ψ ihφ ihψ =>
      intro hφ T
      have hφ₁ := hcl.and_left hφ
      have hψ₁ := hcl.and_right hφ
      constructor
      · intro h
        have h₁ : φ ∈ T.1.val := T.2.ded_closed hφ₁
          (map (fun p => .andElim1 p) (of_mem (Finset.mem_coe.mpr h)))
        have h₂ : ψ ∈ T.1.val := T.2.ded_closed hψ₁
          (map (fun p => .andElim2 p) (of_mem (Finset.mem_coe.mpr h)))
        exact ⟨(ihφ hφ₁ T).1 h₁, (ihψ hψ₁ T).1 h₂⟩
      · intro h hf
        rcases T.2.fal_and hcl h with h' | h'
        · exact (ihφ hφ₁ T).2 h' hf.1
        · exact (ihψ hψ₁ T).2 h' hf.2
  | or φ ψ ihφ ihψ =>
      intro hφ T
      have hφ₁ := hcl.or_left hφ
      have hψ₁ := hcl.or_right hφ
      constructor
      · intro h
        rcases T.2.or_mem hcl h with h' | h'
        · exact .inl ((ihφ hφ₁ T).1 h')
        · exact .inr ((ihψ hψ₁ T).1 h')
      · intro h hf
        obtain ⟨h₁, h₂⟩ := T.2.fal_or hcl h
        rcases hf with hf | hf
        · exact (ihφ hφ₁ T).2 h₁ hf
        · exact (ihψ hψ₁ T).2 h₂ hf
  | ifThen φ ψ ihφ ihψ =>
      intro hφ T
      have hφ₁ := hcl.imp_left hφ
      have hψ₁ := hcl.imp_right hφ
      constructor
      · intro h T' hle hfφ
        rcases T'.2.imp_mem hcl (hle h) with h'' | h''
        · exact absurd hfφ ((ihφ hφ₁ T').2 h'')
        · exact (ihψ hψ₁ T').1 h''
      · intro h hf
        -- extend ⟨insert φ val, {ψ}, ∅⟩ by the constructive Lindenbaum
        have hcons : (⟨insert φ T.1.val, {ψ}, ∅⟩ : FTheory).Cons := by
          intro Ds Ts hDs hTs hg hder
          have hTs' : Ts = [] := by
            cases Ts with
            | nil => rfl
            | cons K Ts =>
                exact absurd (hTs K (List.mem_cons_self ..)) not_mem_coe_empty
          subst hTs'
          rw [disjOf_nil_right, FTheory.toTheory_val, coeInsert] at hder
          have hψd : (insert φ (↑T.1.val : Set PLLFormula)) ⊩ ψ := by
            refine bigOr_collapse (fun χ hχ => ?_) hder
            exact eq_of_mem_coe_singleton (hDs χ hχ)
          exact T.2.not_fal_deriv h (deduct hψd)
        obtain ⟨T', hle, hM', _⟩ := lindenbaum hcons
          ⟨insertSubset hφ₁ T.2.2.1.1,
           singletonSubset hψ₁, Finset.empty_subset _⟩
        have hRi : T.1.val ⊆ T'.val :=
          (Finset.subset_insert ..).trans hle.1
        have hfφ' : (canonFin cl).force ⟨T', hM'⟩ φ :=
          (ihφ hφ₁ ⟨T', hM'⟩).1 (hle.1 (Finset.mem_insert_self ..))
        have hfψ' : ¬ (canonFin cl).force ⟨T', hM'⟩ ψ :=
          (ihψ hψ₁ ⟨T', hM'⟩).2 (hle.2.1 (Finset.mem_singleton_self ..))
        exact hfψ' (hf ⟨T', hM'⟩ hRi hfφ')
  | somehow φ ih =>
      intro hφ T
      have hφ₁ := hcl.lax hφ
      constructor
      · intro h T₁ hle
        -- ◯φ ∈ val ⊆ val₁; extend ⟨insert φ val₁, ∅, mfal₁⟩
        have hcons : (⟨insert φ T₁.1.val, ∅, T₁.1.mfal⟩ : FTheory).Cons := by
          intro Ds Ts hDs hTs hg hder
          have hDs' : Ds = [] := by
            cases Ds with
            | nil => rfl
            | cons D Ds =>
                exact absurd (hDs D (List.mem_cons_self ..)) not_mem_coe_empty
          subst hDs'
          cases Ts with
          | nil => exact hg rfl
          | cons K Ts =>
              rw [disjOf_nil_left, FTheory.toTheory_val, coeInsert] at hder
              have himp : (↑T₁.1.val : Set PLLFormula) ⊩
                  φ.ifThen (.somehow (bigOr (K :: Ts))) :=
                deduct hder
              have hlax : (↑T₁.1.val : Set PLLFormula) ⊩
                  .somehow (bigOr (K :: Ts)) :=
                somehow_bind (of_mem (Finset.mem_coe.mpr (hle h))) himp
              refine T₁.2.1 [] (K :: Ts) (fun φ' hφ' => nomatch hφ') hTs
                (List.cons_ne_nil _ _) ?_
              rwa [disjOf_nil_left]
        obtain ⟨T₂, hle₂, hM₂, hmf₂⟩ := lindenbaum hcons
          ⟨insertSubset hφ₁ T₁.2.2.1.1, Finset.empty_subset _,
           T₁.2.2.1.2.2⟩
        refine ⟨⟨T₂, hM₂⟩,
          ⟨(Finset.subset_insert ..).trans hle₂.1, hmf₂ ▸ subset_rfl⟩, ?_⟩
        exact (ih hφ₁ ⟨T₂, hM₂⟩).1 (hle₂.1 (Finset.mem_insert_self ..))
      · intro h hf
        -- extend ⟨val, ∅, {φ}⟩: its Rₘ-successors all refute φ
        have hcons : (⟨T.1.val, ∅, {φ}⟩ : FTheory).Cons := by
          intro Ds Ts hDs hTs hg hder
          have hDs' : Ds = [] := by
            cases Ds with
            | nil => rfl
            | cons D Ds =>
                exact absurd (hDs D (List.mem_cons_self ..)) not_mem_coe_empty
          subst hDs'
          cases Ts with
          | nil => exact hg rfl
          | cons K Ts =>
              rw [disjOf_nil_left] at hder
              have hφd : (↑T.1.val : Set PLLFormula) ⊩ .somehow φ := by
                refine somehow_mono hder ?_
                refine bigOr_collapse (fun χ hχ => ?_)
                  (of_mem (Set.mem_insert ..))
                exact eq_of_mem_coe_singleton (hTs χ hχ)
              exact T.2.not_fal_deriv h hφd
        obtain ⟨T', hle, hM', hmf'⟩ := lindenbaum hcons
          ⟨T.2.2.1.1, Finset.empty_subset _,
           singletonSubset hφ₁⟩
        obtain ⟨T₂, hRm, hfφ⟩ := hf ⟨T', hM'⟩ hle.1
        have hmem : φ ∈ T₂.1.mfal :=
          hRm.2 (hmf' ▸ Finset.mem_singleton_self ..)
        exact (ih hφ₁ T₂).2 (T₂.2.mfal_sub_fal hmem) hfφ

/-! ## The closure of a sequent, and countermodel existence -/

/-- The subformula closure of a sequent, `⊥` included. -/
def clOf (Γ : List PLLFormula) (C : PLLFormula) : Finset PLLFormula :=
  insert .falsePLL ((C :: Γ).foldr (fun φ s => finUnion (subF φ) s) ∅)

theorem mem_foldr_subF {l : List PLLFormula} {φ : PLLFormula} :
    φ ∈ l.foldr (fun φ s => finUnion (subF φ) s) ∅ ↔ ∃ χ ∈ l, φ ∈ subF χ := by
  induction l with
  | nil => simp
  | cons ψ l ih => simp [ih]

theorem mem_clOf {Γ : List PLLFormula} {C : PLLFormula} :
    ∀ φ ∈ C :: Γ, φ ∈ clOf Γ C := by
  intro φ hφ
  exact Finset.mem_insert_of_mem
    (mem_foldr_subF.mpr ⟨φ, hφ, self_mem_subF φ⟩)

theorem clOf_subClosed (Γ : List PLLFormula) (C : PLLFormula) :
    SubClosed (clOf Γ C) := by
  have step : ∀ {φ ψ : PLLFormula}, ψ ∈ subF φ → φ ∈ clOf Γ C →
      ψ ∈ clOf Γ C := by
    intro φ ψ hψ hφ
    rcases Finset.mem_insert.mp hφ with rfl | hφ
    · simp only [subF, Finset.mem_singleton] at hψ
      subst hψ
      exact Finset.mem_insert_self ..
    · obtain ⟨χ, hχ, hφχ⟩ := mem_foldr_subF.mp hφ
      exact Finset.mem_insert_of_mem
        (mem_foldr_subF.mpr ⟨χ, hχ, subF_trans χ hφχ hψ⟩)
  refine ⟨Finset.mem_insert_self .., ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (intro φ ψ h; exact step (by simp [subF]) h)
      | (intro φ h; exact step (by simp [subF]) h)

/-- **Countermodel existence, finitely and without Zorn**: every
underivable sequent is refuted at a world of its finite canonical model —
the hypotheses forced, the conclusion not. -/
theorem finite_canonical_countermodel {Γ : List PLLFormula} {C : PLLFormula}
    (h : ¬ Nonempty (LaxND Γ C)) :
    ∃ T : (canonFin (clOf Γ C)).W,
      (∀ ψ ∈ Γ, (canonFin (clOf Γ C)).force T ψ) ∧
        ¬ (canonFin (clOf Γ C)).force T C := by
  have hcons : (⟨toFin Γ, {C}, ∅⟩ : FTheory).Cons := by
    intro Ds Ts hDs hTs hg hder
    have hTs' : Ts = [] := by
      cases Ts with
      | nil => rfl
      | cons K Ts =>
          exact absurd (hTs K (List.mem_cons_self ..)) not_mem_coe_empty
    subst hTs'
    rw [disjOf_nil_right] at hder
    have hd : (↑(toFin Γ) : Set PLLFormula) ⊩ C := by
      refine bigOr_collapse (fun χ hχ => ?_) hder
      exact eq_of_mem_coe_singleton (hDs χ hχ)
    obtain ⟨L, hL, ⟨p⟩⟩ := hd
    exact h ⟨p.rename fun ψ hψ => mem_toFin.mp (Finset.mem_coe.mp (hL ψ hψ))⟩
  obtain ⟨T, hle, hM, _⟩ := lindenbaum hcons
    ⟨fun ψ hψ => mem_clOf ψ (List.mem_cons_of_mem _
        (mem_toFin.mp hψ)),
     singletonSubset (mem_clOf C (List.mem_cons_self ..)),
     Finset.empty_subset _⟩
  refine ⟨⟨T, hM⟩, fun ψ hψ => ?_, ?_⟩
  · exact (truth_lemma (clOf_subClosed Γ C) ψ
      (mem_clOf ψ (List.mem_cons_of_mem _ hψ)) ⟨T, hM⟩).1
      (hle.1 (mem_toFin.mpr hψ))
  · exact (truth_lemma (clOf_subClosed Γ C) C
      (mem_clOf C (List.mem_cons_self ..)) ⟨T, hM⟩).2
      (hle.2.1 (Finset.mem_singleton_self ..))

/-! ## Part 4: enumeration into a `FinCM`, and emitter completeness -/

instance : Inhabited FTheory := ⟨⟨∅, ∅, ∅⟩⟩

instance (cl : Finset PLLFormula) :
    DecidablePred (MaxIn cl) := fun T => by
  unfold MaxIn InCl
  infer_instance

/-- All closure-maximal triples, as a finset. -/
noncomputable def worldFinset (cl : Finset PLLFormula) : Finset FTheory :=
  ((cl.powerset ×ˢ cl.powerset ×ˢ cl.powerset).image
    fun p => (⟨p.1, p.2.1, p.2.2⟩ : FTheory)).filter (MaxIn cl)

theorem mem_worldFinset {cl : Finset PLLFormula} {T : FTheory} :
    T ∈ worldFinset cl ↔ MaxIn cl T := by
  simp only [worldFinset, Finset.mem_filter, Finset.mem_image,
    Finset.mem_product]
  constructor
  · rintro ⟨_, hM⟩
    exact hM
  · intro hM
    exact ⟨⟨(T.val, T.fal, T.mfal),
      ⟨Finset.mem_powerset.mpr hM.2.1.1,
       Finset.mem_powerset.mpr hM.2.1.2.1,
       Finset.mem_powerset.mpr hM.2.1.2.2⟩, rfl⟩, hM⟩

/-- The enumerated worlds. -/
noncomputable def worldList (cl : Finset PLLFormula) : List FTheory :=
  (worldFinset cl).toList

theorem mem_worldList {cl : Finset PLLFormula} {T : FTheory} :
    T ∈ worldList cl ↔ MaxIn cl T := by
  rw [worldList, Finset.mem_toList, mem_worldFinset]

/-- The finite canonical model as checker data. -/
noncomputable def canonFinCM (cl : Finset PLLFormula) : FinCM :=
  { n := (worldList cl).length
    ri := (List.range (worldList cl).length).flatMap fun i =>
      (List.range (worldList cl).length).filterMap fun j =>
        if (worldList cl)[i]!.val ⊆ (worldList cl)[j]!.val then
          some (i, j) else none
    rm := (List.range (worldList cl).length).flatMap fun i =>
      (List.range (worldList cl).length).filterMap fun j =>
        if (worldList cl)[i]!.val ⊆ (worldList cl)[j]!.val ∧
            (worldList cl)[i]!.mfal ⊆ (worldList cl)[j]!.mfal then
          some (i, j) else none
    fall := (List.range (worldList cl).length).filter fun i =>
      decide (PLLFormula.falsePLL ∈ (worldList cl)[i]!.val)
    val := (List.range (worldList cl).length).flatMap fun i =>
      (worldList cl)[i]!.val.toList.filterMap fun φ =>
        match φ with | .prop a => some (i, a) | _ => none }

@[simp] theorem canonFinCM_n (cl : Finset PLLFormula) :
    (canonFinCM cl).n = (worldList cl).length := rfl

/-! ### Characterisation of the built data -/

section Charac

variable {cl : Finset PLLFormula}

private theorem wl_get_eq {i : Nat} (hi : i < (worldList cl).length) :
    (worldList cl)[i]! = (worldList cl)[i] := by
  exact getElem!_pos (worldList cl) i hi

theorem ri_mem_iff {i j : Nat} :
    (i, j) ∈ (canonFinCM cl).ri ↔
      i < (worldList cl).length ∧ j < (worldList cl).length ∧
        (worldList cl)[i]!.val ⊆ (worldList cl)[j]!.val := by
  simp only [canonFinCM, List.mem_flatMap, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨i', hi', j', hj', hif⟩
    split at hif
    · simp only [Option.some.injEq, Prod.mk.injEq] at hif
      obtain ⟨rfl, rfl⟩ := hif
      exact ⟨hi', hj', by assumption⟩
    · cases hif
  · rintro ⟨hi, hj, hsub⟩
    exact ⟨i, hi, j, hj, if_pos hsub⟩

theorem rm_mem_iff {i j : Nat} :
    (i, j) ∈ (canonFinCM cl).rm ↔
      i < (worldList cl).length ∧ j < (worldList cl).length ∧
        ((worldList cl)[i]!.val ⊆ (worldList cl)[j]!.val ∧
          (worldList cl)[i]!.mfal ⊆ (worldList cl)[j]!.mfal) := by
  simp only [canonFinCM, List.mem_flatMap, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨i', hi', j', hj', hif⟩
    split at hif
    · simp only [Option.some.injEq, Prod.mk.injEq] at hif
      obtain ⟨rfl, rfl⟩ := hif
      exact ⟨hi', hj', by assumption⟩
    · cases hif
  · rintro ⟨hi, hj, hsub⟩
    exact ⟨i, hi, j, hj, if_pos hsub⟩

theorem fall_mem_iff {i : Nat} :
    i ∈ (canonFinCM cl).fall ↔
      i < (worldList cl).length ∧
        PLLFormula.falsePLL ∈ (worldList cl)[i]!.val := by
  simp only [canonFinCM, List.mem_filter, List.mem_range,
    decide_eq_true_eq]

theorem valPair_mem_iff {i : Nat} {a : String} :
    (i, a) ∈ (canonFinCM cl).val ↔
      i < (worldList cl).length ∧
        PLLFormula.prop a ∈ (worldList cl)[i]!.val := by
  simp only [canonFinCM, List.mem_flatMap, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨i', hi', φ, hφ, hmatch⟩
    cases φ with
    | prop b =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hmatch
        obtain ⟨rfl, rfl⟩ := hmatch
        exact ⟨hi', Finset.mem_toList.mp hφ⟩
    | falsePLL => cases hmatch
    | and _ _ => cases hmatch
    | or _ _ => cases hmatch
    | ifThen _ _ => cases hmatch
    | somehow _ => cases hmatch
  · rintro ⟨hi, hmem⟩
    exact ⟨i, hi, .prop a, Finset.mem_toList.mpr hmem, rfl⟩

theorem maxIn_get {i : Nat} (hi : i < (worldList cl).length) :
    MaxIn cl (worldList cl)[i]! := by
  rw [wl_get_eq hi]
  exact mem_worldList.mp (List.getElem_mem ..)

theorem riB_iff {i j : Nat} (hi : i < (worldList cl).length)
    (hj : j < (worldList cl).length) :
    (canonFinCM cl).riB i j = true ↔
      (worldList cl)[i]!.val ⊆ (worldList cl)[j]!.val := by
  simp only [FinCM.riB, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (hmem | rfl)
    · exact (ri_mem_iff.mp hmem).2.2
    · exact subset_rfl
  · intro h
    exact .inl (ri_mem_iff.mpr ⟨hi, hj, h⟩)

theorem rmB_iff {i j : Nat} (hi : i < (worldList cl).length)
    (hj : j < (worldList cl).length) :
    (canonFinCM cl).rmB i j = true ↔
      ((worldList cl)[i]!.val ⊆ (worldList cl)[j]!.val ∧
        (worldList cl)[i]!.mfal ⊆ (worldList cl)[j]!.mfal) := by
  simp only [FinCM.rmB, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (hmem | rfl)
    · exact (rm_mem_iff.mp hmem).2.2
    · exact ⟨subset_rfl, subset_rfl⟩
  · intro h
    exact .inl (rm_mem_iff.mpr ⟨hi, hj, h⟩)

theorem fallB_iff {i : Nat} (hi : i < (worldList cl).length) :
    (canonFinCM cl).fallB i = true ↔
      PLLFormula.falsePLL ∈ (worldList cl)[i]!.val := by
  simp only [FinCM.fallB, decide_eq_true_eq]
  constructor
  · intro h
    exact (fall_mem_iff.mp h).2
  · intro h
    exact fall_mem_iff.mpr ⟨hi, h⟩

theorem valB_of_mem {i : Nat} {a : String}
    (hi : i < (worldList cl).length)
    (h : PLLFormula.prop a ∈ (worldList cl)[i]!.val) :
    (canonFinCM cl).valB i a = true := by
  simp only [FinCM.valB, Bool.or_eq_true, decide_eq_true_eq]
  exact .inl (valPair_mem_iff.mpr ⟨hi, h⟩)

theorem valB_iff {i : Nat} {a : String} (hi : i < (worldList cl).length)
    (ha : PLLFormula.prop a ∈ cl) :
    (canonFinCM cl).valB i a = true ↔
      PLLFormula.prop a ∈ (worldList cl)[i]!.val := by
  constructor
  · intro h
    simp only [FinCM.valB, FinCM.fallB, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with hmem | hfall
    · exact (valPair_mem_iff.mp hmem).2
    · exact (maxIn_get hi).ded_closed ha (falso _ (of_mem
        (Finset.mem_coe.mpr ((fall_mem_iff.mp hfall).2))))
  · exact valB_of_mem hi

/-- The built model satisfies the frame conditions. -/
theorem canonFinCM_wf : (canonFinCM cl).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw v hv u hu h₁ h₂
    exact (riB_iff hw hu).mpr
      (((riB_iff hw hv).mp h₁).trans ((riB_iff hv hu).mp h₂))
  · intro w hw v hv u hu h₁ h₂
    obtain ⟨ha₁, hb₁⟩ := (rmB_iff hw hv).mp h₁
    obtain ⟨ha₂, hb₂⟩ := (rmB_iff hv hu).mp h₂
    exact (rmB_iff hw hu).mpr ⟨ha₁.trans ha₂, hb₁.trans hb₂⟩
  · intro w hw v hv h
    exact (riB_iff hw hv).mpr ((rmB_iff hw hv).mp h).1
  · intro w hw v hv h hf
    exact (fallB_iff hv).mpr ((riB_iff hw hv).mp h ((fallB_iff hw).mp hf))
  · intro p hp v hv h
    obtain ⟨hi, hmem⟩ := valPair_mem_iff.mp hp
    exact valB_of_mem hv ((riB_iff hi hv).mp h hmem)

/-- The world of an index. -/
noncomputable def wAt (i : Fin (canonFinCM cl).n) : (canonFin cl).W :=
  ⟨(worldList cl)[i.1]!, maxIn_get i.2⟩

theorem exists_idx (T : (canonFin cl).W) :
    ∃ i : Fin (canonFinCM cl).n, (worldList cl)[i.1]! = T.1 := by
  have hmem : T.1 ∈ worldList cl := mem_worldList.mpr T.2
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
  exact ⟨⟨i, hi⟩, by rw [wl_get_eq hi]; exact heq⟩

/-- **The transfer lemma**: on closure formulas, forcing in the checker
model coincides with forcing in the finite canonical model. -/
theorem transfer (hcl : SubClosed cl) :
    ∀ φ, φ ∈ cl → ∀ i : Fin (canonFinCM cl).n,
      ((canonFinCM cl).toModel canonFinCM_wf).force i φ ↔
        (canonFin cl).force (wAt i) φ := by
  intro φ
  induction φ with
  | prop a =>
      intro hφ i
      constructor
      · intro h
        exact .inr ((valB_iff i.2 hφ).mp h)
      · rintro (hout | hv)
        · exact absurd hφ hout
        · exact (valB_iff i.2 hφ).mpr hv
  | falsePLL =>
      intro hφ i
      exact fallB_iff i.2
  | and φ ψ ihφ ihψ =>
      intro hφ i
      exact and_congr (ihφ (hcl.and_left hφ) i) (ihψ (hcl.and_right hφ) i)
  | or φ ψ ihφ ihψ =>
      intro hφ i
      exact or_congr (ihφ (hcl.or_left hφ) i) (ihψ (hcl.or_right hφ) i)
  | ifThen φ ψ ihφ ihψ =>
      intro hφ i
      have hφ₁ := hcl.imp_left hφ
      have hψ₁ := hcl.imp_right hφ
      constructor
      · intro H T' hle hφ'
        obtain ⟨j, hj⟩ := exists_idx T'
        have hwj : wAt j = T' := Subtype.ext hj
        have hri : (canonFinCM cl).riB i.1 j.1 = true :=
          (riB_iff i.2 j.2).mpr (by rw [hj]; exact hle)
        have hφj : ((canonFinCM cl).toModel canonFinCM_wf).force j φ :=
          (ihφ hφ₁ j).mpr (by rw [hwj]; exact hφ')
        have := (ihψ hψ₁ j).mp (H j hri hφj)
        rwa [hwj] at this
      · intro H v hri hφv
        have hsub := (riB_iff i.2 v.2).mp hri
        exact (ihψ hψ₁ v).mpr (H (wAt v) hsub ((ihφ hφ₁ v).mp hφv))
  | somehow φ ih =>
      intro hφ i
      have hφ₁ := hcl.lax hφ
      constructor
      · intro H T' hle
        obtain ⟨j, hj⟩ := exists_idx T'
        have hwj : wAt j = T' := Subtype.ext hj
        have hri : (canonFinCM cl).riB i.1 j.1 = true :=
          (riB_iff i.2 j.2).mpr (by rw [hj]; exact hle)
        obtain ⟨u, hrm, hu⟩ := H j hri
        refine ⟨wAt u, ?_, (ih hφ₁ u).mp hu⟩
        have := (rmB_iff j.2 u.2).mp hrm
        rw [← hwj]
        exact this
      · intro H v hri
        have hsub := (riB_iff i.2 v.2).mp hri
        obtain ⟨T₂, hRm, hf⟩ := H (wAt v) hsub
        obtain ⟨u, hu⟩ := exists_idx T₂
        have hwu : wAt u = T₂ := Subtype.ext hu
        refine ⟨u, (rmB_iff v.2 u.2).mpr (by rw [hu]; exact hRm), ?_⟩
        exact (ih hφ₁ u).mpr (by rw [hwu]; exact hf)

end Charac

/-! ### Choice-free world enumeration and emitter completeness

The legacy layer above extracts its world list by `Finset.toList` —
`Classical.choice` by definition.  The clean chain instead parameterises
the checker model over *any* explicit list of worlds, each paired with a
list enumerating its `val`-component (the atom table's source); the
countermodel proof supplies such a list from `Prop`-level
representatives (`exists_rep`), never choosing one canonically. -/

section CleanEmitter

variable {cl : Finset PLLFormula}

/-- The checker model over an explicitly listed world enumeration. -/
def canonCMof (wl : List (FTheory × List PLLFormula)) : FinCM :=
  { n := wl.length
    ri := (List.range wl.length).flatMap fun i =>
      (List.range wl.length).filterMap fun j =>
        if (wl[i]!).1.val ⊆ (wl[j]!).1.val then some (i, j) else none
    rm := (List.range wl.length).flatMap fun i =>
      (List.range wl.length).filterMap fun j =>
        if (wl[i]!).1.val ⊆ (wl[j]!).1.val ∧
            (wl[i]!).1.mfal ⊆ (wl[j]!).1.mfal then some (i, j) else none
    fall := (List.range wl.length).filter fun i =>
      decide (PLLFormula.falsePLL ∈ (wl[i]!).1.val)
    val := (List.range wl.length).flatMap fun i =>
      (wl[i]!).2.filterMap fun φ =>
        match φ with | .prop a => some (i, a) | _ => none }

variable (wl : List (FTheory × List PLLFormula))

theorem riL_mem_iff {i j : Nat} :
    (i, j) ∈ (canonCMof wl).ri ↔
      i < wl.length ∧ j < wl.length ∧
        (wl[i]!).1.val ⊆ (wl[j]!).1.val := by
  simp only [canonCMof, List.mem_flatMap, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨i', hi', j', hj', hif⟩
    split at hif
    · simp only [Option.some.injEq, Prod.mk.injEq] at hif
      obtain ⟨rfl, rfl⟩ := hif
      exact ⟨hi', hj', by assumption⟩
    · cases hif
  · rintro ⟨hi, hj, hsub⟩
    exact ⟨i, hi, j, hj, if_pos hsub⟩

theorem rmL_mem_iff {i j : Nat} :
    (i, j) ∈ (canonCMof wl).rm ↔
      i < wl.length ∧ j < wl.length ∧
        ((wl[i]!).1.val ⊆ (wl[j]!).1.val ∧
          (wl[i]!).1.mfal ⊆ (wl[j]!).1.mfal) := by
  simp only [canonCMof, List.mem_flatMap, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨i', hi', j', hj', hif⟩
    split at hif
    · simp only [Option.some.injEq, Prod.mk.injEq] at hif
      obtain ⟨rfl, rfl⟩ := hif
      exact ⟨hi', hj', by assumption⟩
    · cases hif
  · rintro ⟨hi, hj, hsub⟩
    exact ⟨i, hi, j, hj, if_pos hsub⟩

theorem fallL_mem_iff {i : Nat} :
    i ∈ (canonCMof wl).fall ↔
      i < wl.length ∧ PLLFormula.falsePLL ∈ (wl[i]!).1.val := by
  simp only [canonCMof, List.mem_filter, List.mem_range,
    decide_eq_true_eq]

theorem valPairL_mem_iff
    (hval : ∀ p ∈ wl, ∀ x, x ∈ p.2 ↔ x ∈ p.1.val) {i : Nat} {a : String} :
    (i, a) ∈ (canonCMof wl).val ↔
      i < wl.length ∧ PLLFormula.prop a ∈ (wl[i]!).1.val := by
  simp only [canonCMof, List.mem_flatMap, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨i', hi', φ, hφ, hmatch⟩
    cases φ with
    | prop b =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hmatch
        obtain ⟨rfl, rfl⟩ := hmatch
        have hmem : wl[i']! ∈ wl := by
          rw [getElem!_pos wl i' hi']
          exact List.getElem_mem ..
        exact ⟨hi', (hval _ hmem _).mp hφ⟩
    | falsePLL => cases hmatch
    | and _ _ => cases hmatch
    | or _ _ => cases hmatch
    | ifThen _ _ => cases hmatch
    | somehow _ => cases hmatch
  · rintro ⟨hi, hmem⟩
    have hmemL : wl[i]! ∈ wl := by
      rw [getElem!_pos wl i hi]
      exact List.getElem_mem ..
    exact ⟨i, hi, .prop a, (hval _ hmemL _).mpr hmem, rfl⟩

theorem maxIn_getL (hw : ∀ p ∈ wl, MaxIn cl p.1) {i : Nat}
    (hi : i < wl.length) : MaxIn cl (wl[i]!).1 := by
  rw [getElem!_pos wl i hi]
  exact hw _ (List.getElem_mem ..)

theorem riBL_iff {i j : Nat} (hi : i < wl.length) (hj : j < wl.length) :
    (canonCMof wl).riB i j = true ↔
      (wl[i]!).1.val ⊆ (wl[j]!).1.val := by
  simp only [FinCM.riB, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (hmem | rfl)
    · exact ((riL_mem_iff wl).mp hmem).2.2
    · exact subset_rfl
  · intro h
    exact .inl ((riL_mem_iff wl).mpr ⟨hi, hj, h⟩)

theorem rmBL_iff {i j : Nat} (hi : i < wl.length) (hj : j < wl.length) :
    (canonCMof wl).rmB i j = true ↔
      ((wl[i]!).1.val ⊆ (wl[j]!).1.val ∧
        (wl[i]!).1.mfal ⊆ (wl[j]!).1.mfal) := by
  simp only [FinCM.rmB, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (hmem | rfl)
    · exact ((rmL_mem_iff wl).mp hmem).2.2
    · exact ⟨subset_rfl, subset_rfl⟩
  · intro h
    exact .inl ((rmL_mem_iff wl).mpr ⟨hi, hj, h⟩)

theorem fallBL_iff {i : Nat} (hi : i < wl.length) :
    (canonCMof wl).fallB i = true ↔
      PLLFormula.falsePLL ∈ (wl[i]!).1.val := by
  simp only [FinCM.fallB, decide_eq_true_eq]
  constructor
  · intro h
    exact ((fallL_mem_iff wl).mp h).2
  · intro h
    exact (fallL_mem_iff wl).mpr ⟨hi, h⟩

theorem valBL_of_mem
    (hval : ∀ p ∈ wl, ∀ x, x ∈ p.2 ↔ x ∈ p.1.val) {i : Nat} {a : String}
    (hi : i < wl.length)
    (h : PLLFormula.prop a ∈ (wl[i]!).1.val) :
    (canonCMof wl).valB i a = true := by
  simp only [FinCM.valB, Bool.or_eq_true, decide_eq_true_eq]
  exact .inl ((valPairL_mem_iff wl hval).mpr ⟨hi, h⟩)

theorem valBL_iff (hw : ∀ p ∈ wl, MaxIn cl p.1)
    (hval : ∀ p ∈ wl, ∀ x, x ∈ p.2 ↔ x ∈ p.1.val) {i : Nat} {a : String}
    (hi : i < wl.length) (ha : PLLFormula.prop a ∈ cl) :
    (canonCMof wl).valB i a = true ↔
      PLLFormula.prop a ∈ (wl[i]!).1.val := by
  constructor
  · intro h
    simp only [FinCM.valB, FinCM.fallB, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with hmem | hfall
    · exact ((valPairL_mem_iff wl hval).mp hmem).2
    · exact (maxIn_getL wl hw hi).ded_closed ha (falso _ (of_mem
        (Finset.mem_coe.mpr ((fallL_mem_iff wl).mp hfall).2)))
  · exact valBL_of_mem wl hval hi

/-- The parametric model satisfies the frame conditions. -/
theorem canonCMof_wf
    (hval : ∀ p ∈ wl, ∀ x, x ∈ p.2 ↔ x ∈ p.1.val) :
    (canonCMof wl).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw v hv u hu h₁ h₂
    exact (riBL_iff wl hw hu).mpr
      (((riBL_iff wl hw hv).mp h₁).trans ((riBL_iff wl hv hu).mp h₂))
  · intro w hw v hv u hu h₁ h₂
    obtain ⟨ha₁, hb₁⟩ := (rmBL_iff wl hw hv).mp h₁
    obtain ⟨ha₂, hb₂⟩ := (rmBL_iff wl hv hu).mp h₂
    exact (rmBL_iff wl hw hu).mpr ⟨ha₁.trans ha₂, hb₁.trans hb₂⟩
  · intro w hw v hv h
    exact (riBL_iff wl hw hv).mpr ((rmBL_iff wl hw hv).mp h).1
  · intro w hw v hv h hf
    exact (fallBL_iff wl hv).mpr
      ((riBL_iff wl hw hv).mp h ((fallBL_iff wl hw).mp hf))
  · intro p hp v hv h
    obtain ⟨hi, hmem⟩ := (valPairL_mem_iff wl hval).mp hp
    exact valBL_of_mem wl hval hv ((riBL_iff wl hi hv).mp h hmem)

/-- The world of an index. -/
def wAtL (hw : ∀ p ∈ wl, MaxIn cl p.1) (i : Fin (canonCMof wl).n) :
    (canonFin cl).W :=
  ⟨(wl[i.1]!).1, maxIn_getL wl hw i.2⟩

theorem exists_idxL (hcov : ∀ T : FTheory, MaxIn cl T → ∃ p ∈ wl, p.1 = T)
    (T : (canonFin cl).W) :
    ∃ i : Fin (canonCMof wl).n, (wl[i.1]!).1 = T.1 := by
  obtain ⟨p, hp, hpT⟩ := hcov T.1 T.2
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hp
  refine ⟨⟨i, hi⟩, ?_⟩
  rw [getElem!_pos wl i hi, heq, hpT]

/-- **The transfer lemma**, parametric: on closure formulas, forcing in
the listed checker model coincides with forcing in the finite canonical
model. -/
theorem transferL (hw : ∀ p ∈ wl, MaxIn cl p.1)
    (hval : ∀ p ∈ wl, ∀ x, x ∈ p.2 ↔ x ∈ p.1.val)
    (hcov : ∀ T : FTheory, MaxIn cl T → ∃ p ∈ wl, p.1 = T)
    (hcl : SubClosed cl) :
    ∀ φ, φ ∈ cl → ∀ i : Fin (canonCMof wl).n,
      ((canonCMof wl).toModel (canonCMof_wf wl hval)).force i φ ↔
        (canonFin cl).force (wAtL wl hw i) φ := by
  intro φ
  induction φ with
  | prop a =>
      intro hφ i
      constructor
      · intro h
        exact .inr ((valBL_iff wl hw hval i.2 hφ).mp h)
      · rintro (hout | hv)
        · exact absurd hφ hout
        · exact (valBL_iff wl hw hval i.2 hφ).mpr hv
  | falsePLL =>
      intro hφ i
      exact fallBL_iff wl i.2
  | and φ ψ ihφ ihψ =>
      intro hφ i
      exact and_congr (ihφ (hcl.and_left hφ) i) (ihψ (hcl.and_right hφ) i)
  | or φ ψ ihφ ihψ =>
      intro hφ i
      exact or_congr (ihφ (hcl.or_left hφ) i) (ihψ (hcl.or_right hφ) i)
  | ifThen φ ψ ihφ ihψ =>
      intro hφ i
      have hφ₁ := hcl.imp_left hφ
      have hψ₁ := hcl.imp_right hφ
      constructor
      · intro H T' hle hφ'
        obtain ⟨j, hj⟩ := exists_idxL wl hcov T'
        have hwj : wAtL wl hw j = T' := Subtype.ext hj
        have hri : (canonCMof wl).riB i.1 j.1 = true :=
          (riBL_iff wl i.2 j.2).mpr (by rw [hj]; exact hle)
        have hφj : ((canonCMof wl).toModel (canonCMof_wf wl hval)).force j φ :=
          (ihφ hφ₁ j).mpr (by rw [hwj]; exact hφ')
        have := (ihψ hψ₁ j).mp (H j hri hφj)
        rwa [hwj] at this
      · intro H v hri hφv
        have hsub := (riBL_iff wl i.2 v.2).mp hri
        exact (ihψ hψ₁ v).mpr (H (wAtL wl hw v) hsub ((ihφ hφ₁ v).mp hφv))
  | somehow φ ih =>
      intro hφ i
      have hφ₁ := hcl.lax hφ
      constructor
      · intro H T' hle
        obtain ⟨j, hj⟩ := exists_idxL wl hcov T'
        have hwj : wAtL wl hw j = T' := Subtype.ext hj
        have hri : (canonCMof wl).riB i.1 j.1 = true :=
          (riBL_iff wl i.2 j.2).mpr (by rw [hj]; exact hle)
        obtain ⟨u, hrm, hu⟩ := H j hri
        refine ⟨wAtL wl hw u, ?_, (ih hφ₁ u).mp hu⟩
        have := (rmBL_iff wl j.2 u.2).mp hrm
        rw [← hwj]
        exact this
      · intro H v hri
        have hsub := (riBL_iff wl i.2 v.2).mp hri
        obtain ⟨T₂, hRm, hf⟩ := H (wAtL wl hw v) hsub
        obtain ⟨u, hu⟩ := exists_idxL wl hcov T₂
        have hwu : wAtL wl hw u = T₂ := Subtype.ext hu
        refine ⟨u, (rmBL_iff wl v.2 u.2).mpr (by rw [hu]; exact hRm), ?_⟩
        exact (ih hφ₁ u).mpr (by rw [hwu]; exact hf)

end CleanEmitter

/-- **Emitter completeness**: every underivable sequent has a finite
countermodel *as checker data* — a `FinCM` and a world passing the
verified `checkB`.  The world list is produced inside the proof from
`Prop`-level representatives of the closure (sublists of an enumerating
list, filtered by the decidable `MaxIn`) — no `Finset.toList`, no
choice.  Composed with `realP_refutes_sequent` (`PLLEvidence.lean`),
this closes the completeness of PLL for `⊩ᵖ`-realisability over
decorated finite models — see `PLLRealCompleteness.lean`. -/
theorem emitter_completeness {Γ : List PLLFormula} {C : PLLFormula}
    (h : ¬ Nonempty (LaxND Γ C)) :
    ∃ (M : FinCM) (w : Nat), FinCM.checkB M w Γ C = true := by
  obtain ⟨T, hΓ, hC⟩ := finite_canonical_countermodel h
  obtain ⟨lcl, -, hlcl⟩ := exists_rep (clOf Γ C)
  let cand : List (FTheory × List PLLFormula) :=
    lcl.sublists.flatMap fun lv =>
      lcl.sublists.flatMap fun lf =>
        lcl.sublists.map fun lm => (⟨toFin lv, toFin lf, toFin lm⟩, lv)
  let wl := cand.filter fun p => decide (MaxIn (clOf Γ C) p.1)
  have hw : ∀ p ∈ wl, MaxIn (clOf Γ C) p.1 := fun p hp =>
    of_decide_eq_true (List.mem_filter.mp hp).2
  have hval : ∀ p ∈ wl, ∀ x, x ∈ p.2 ↔ x ∈ p.1.val := by
    intro p hp x
    obtain ⟨lv, hlv, hrest⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
    obtain ⟨lf, hlf, hrest⟩ := List.mem_flatMap.mp hrest
    obtain ⟨lm, hlm, hpe⟩ := List.mem_map.mp hrest
    cases hpe
    exact mem_toFin.symm
  have hcov : ∀ T' : FTheory, MaxIn (clOf Γ C) T' → ∃ p ∈ wl, p.1 = T' := by
    intro T' hT'
    have hsub : ∀ s : Finset PLLFormula, s ⊆ clOf Γ C →
        ∃ ls ∈ lcl.sublists, toFin ls = s := by
      intro s hs
      refine ⟨lcl.filter (fun x => decide (x ∈ s)), ?_, ?_⟩
      · rw [List.mem_sublists]
        exact List.filter_sublist
      · refine subAntisymm (fun a ha => ?_) (fun a ha => ?_)
        · rw [mem_toFin, List.mem_filter, decide_eq_true_eq] at ha
          exact ha.2
        · rw [mem_toFin, List.mem_filter, decide_eq_true_eq]
          exact ⟨(hlcl a).mpr (hs ha), ha⟩
    obtain ⟨lv, hlv, hveq⟩ := hsub T'.val hT'.2.1.1
    obtain ⟨lf, hlf, hfeq⟩ := hsub T'.fal hT'.2.1.2.1
    obtain ⟨lm, hlm, hmeq⟩ := hsub T'.mfal hT'.2.1.2.2
    refine ⟨(⟨toFin lv, toFin lf, toFin lm⟩, lv), ?_, ?_⟩
    · refine List.mem_filter.mpr ⟨?_, ?_⟩
      · exact List.mem_flatMap.mpr ⟨lv, hlv,
          List.mem_flatMap.mpr ⟨lf, hlf,
            List.mem_map.mpr ⟨lm, hlm, rfl⟩⟩⟩
      · rw [decide_eq_true_eq, hveq, hfeq, hmeq]
        exact hT'
    · rw [hveq, hfeq, hmeq]
  obtain ⟨i, hieq⟩ := exists_idxL wl hcov T
  have hwT : wAtL wl hw i = T := Subtype.ext hieq
  refine ⟨canonCMof wl, i.1,
    FinCM.checkB_intro (canonCMof_wf wl hval) i.2 ?_ ?_⟩
  · intro ψ hψ
    refine (transferL wl hw hval hcov (clOf_subClosed Γ C) ψ
      (mem_clOf ψ (List.mem_cons_of_mem _ hψ)) i).mpr ?_
    rw [hwT]
    exact hΓ ψ hψ
  · intro hf
    refine hC ?_
    rw [← hwT]
    exact (transferL wl hw hval hcov (clOf_subClosed Γ C) C
      (mem_clOf C (List.mem_cons_self ..)) i).mp hf


end FinComp
end PLLND

/-- info: 'PLLND.FinComp.lindenbaum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.FinComp.lindenbaum

/--
info: 'PLLND.FinComp.cons_insVal_or_insFal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.FinComp.cons_insVal_or_insFal

/-- info: 'PLLND.FinComp.truth_lemma' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.FinComp.truth_lemma

/--
info: 'PLLND.FinComp.finite_canonical_countermodel' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.FinComp.finite_canonical_countermodel

/--
info: 'PLLND.FinComp.emitter_completeness' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.FinComp.emitter_completeness
