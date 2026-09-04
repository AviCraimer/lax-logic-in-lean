import wip.rnSep
import wip.rnDictRefute

/-!
# The §40 witnesses collapse to ONE class — RN(◯,{}) has exactly 16
certified classes at this round

Hand-authored certificates (2026-07-26).  The four §40 closure-failure
witnesses

  w1 = q8 ∧ q10,  w2 = q9 ⊃ q4,  w3 = q12 ⊃ q4,  w4 = q14 ⊃ q4

are pairwise INTERDERIVABLE (`coll_w1_w2`, `coll_w2_w3`,
`coll_w3_w4`, and the `trans` corollaries): they form ONE new
interderivability class beyond the 15.  The searcher could not find
several of these derivations (they need cut-style composition through
q8 ∧ q10 and the ◯-monotonicity steps), so they are written by hand at
the `Deriv` level; the kernel checks them like any other term.

The proofs hinge on three observations:

* `q9 ⊃ q4 ≡ (q5 ⊃ q4) ∧ (q6 ⊃ q4)` (⊃ distributes over the
  disjunction `q9 = q5 ∨ q6`), and `q6 ⊃ q4 ≡ q6 ⊃ q2 = q10` (in the
  q3-branch of `q4`, `q6 = ¬q3` refutes it), giving `w2 ≡ w1`;
* from `◯q7` one can derive `◯q3 = q5` by case analysis inside the
  modality (`q7 = q3 ∨ q6`; the `q6` branch reaches `q4` through
  either `w2`-hypothesis material and collapses to `⊥` or `◯⊥`),
  giving `w3 ≡ w2`;
* from `◯q7` one can also derive `q14 = q10 ⊃ q5` (same case
  analysis, using the hypothesis `q10` directly), giving `w4 ≡ w3`;
  and `[w1] ⊢ w4` is the two-step modus-ponens
  `q10, q14 ⊢ q5`, `q8, q5 ⊢ q4`.

Combined with `wip/rnSep.lean` (the 15 base classes pairwise distinct,
5-world countermodels included) and `wip/rnDictRefute.lean` (the
witness class distinct from every base class), the aggregate
`rep16_pairwise_distinct` below pins the kernel-checked statement:

  **the variable-free fragment RN(◯,{}) has AT LEAST 16
  interderivability classes**, with `q15 := q9 ⊃ q4` the
  representative of the 16th.
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND

/-! ## The one-step derivations, by hand -/

/-- `[w2] ⊢ w1`: both conjuncts of `q8 ∧ q10` follow from `q9 ⊃ q4`. -/
theorem d_w2_w1 : Deriv [w2] w1 := by
  refine Deriv.andIntro ?h8 ?h10
  · -- q8 = q5 ⊃ q4: from q5, inject into q9 and apply w2
    exact Deriv.impIntro
      (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.orIntro1 (Deriv.iden (.head _))))
  · -- q10 = q6 ⊃ q2: from q6 get q4 via w2; its q3-branch is refuted by q6
    refine Deriv.impIntro ?_
    have hq4 : Deriv [q6, w2] q4 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.orIntro2 (Deriv.iden (.head _)))
    exact Deriv.orElim hq4 (Deriv.iden (.head _))
      (Deriv.falsoElim q2
        (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
          (Deriv.iden (.head _))))

/-- `[w1] ⊢ w2`: case analysis on `q9 = q5 ∨ q6`, one conjunct each. -/
theorem d_w1_w2 : Deriv [w1] w2 := by
  refine Deriv.impIntro ?_
  refine Deriv.orElim (Deriv.iden (.head _)) ?c5 ?c6
  · -- q5 case: q8 = q5 ⊃ q4 fires
    exact Deriv.impElim
      (Deriv.andElim1 (Deriv.iden (.tail _ (.tail _ (.head _)))))
      (Deriv.iden (.head _))
  · -- q6 case: q10 = q6 ⊃ q2 fires, then inject q2 into q4
    exact Deriv.orIntro1
      (Deriv.impElim
        (Deriv.andElim2 (Deriv.iden (.tail _ (.tail _ (.head _)))))
        (Deriv.iden (.head _)))

/-- `[w3] ⊢ w2`: either `q9`-branch reaches `q12 = ◯q7`. -/
theorem d_w3_w2 : Deriv [w3] w2 := by
  refine Deriv.impIntro ?_
  refine Deriv.orElim (Deriv.iden (.head _)) ?c5 ?c6
  · -- q5 = ◯q3 case: ◯-monotonicity q3 ⤳ q7 gives q12, then w3
    refine Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _)))) ?_
    exact dSomehowElim (Deriv.iden (.head _))
      (dSomehowIntro (Deriv.orIntro1 (Deriv.iden (.head _))))
  · -- q6 case: ◯-intro of the right q7-disjunct gives q12, then w3
    exact Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
      (dSomehowIntro (Deriv.orIntro2 (Deriv.iden (.head _))))

/-- The key extraction: from `q12 = ◯q7` and `w2 = q9 ⊃ q4`, derive
`q5 = ◯q3` by case analysis inside the modality.  In the `q6`-branch,
`w2` yields `q4`; its `q2 = ◯⊥`-branch collapses under `◯`, and its
`q3`-branch is refuted by `q6`. -/
theorem d_key_q5 : Deriv [q12, w2] q5 := by
  refine dSomehowElim (Deriv.iden (.head _)) ?_
  refine Deriv.orElim (Deriv.iden (.head _)) ?c3 ?c6
  · -- q3 branch: ◯-intro
    exact dSomehowIntro (Deriv.iden (.head _))
  · -- q6 branch
    have hq4 : Deriv [q6, q7, q12, w2] q4 :=
      Deriv.impElim
        (Deriv.iden (.tail _ (.tail _ (.tail _ (.head _)))))
        (Deriv.orIntro2 (Deriv.iden (.head _)))
    refine Deriv.orElim hq4 ?c2 ?c3'
    · -- q2 = ◯⊥ branch: ex falso inside ◯
      exact dSomehowElim (Deriv.iden (.head _))
        (Deriv.falsoElim _ (Deriv.iden (.head _)))
    · -- q3 branch: q6 refutes q3
      exact Deriv.falsoElim _
        (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
          (Deriv.iden (.head _)))

/-- `[w2] ⊢ w3`: from `q12`, extract `q5` (`d_key_q5`), inject into
`q9`, and apply `w2`. -/
theorem d_w2_w3 : Deriv [w2] w3 :=
  Deriv.impIntro
    (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
      (Deriv.orIntro1 d_key_q5))

/-- From `q12 = ◯q7` alone, derive `q14 = q10 ⊃ q5` (the same
inside-◯ case analysis, with the hypothesis `q10` closing the
`q6`-branch). -/
theorem d_q12_q14 : Deriv [q12, w4] q14 := by
  refine Deriv.impIntro ?_
  refine dSomehowElim (Deriv.iden (.tail _ (.head _))) ?_
  refine Deriv.orElim (Deriv.iden (.head _)) ?c3 ?c6
  · exact dSomehowIntro (Deriv.iden (.head _))
  · -- q6 branch: q10 gives q2 = ◯⊥, then ex falso inside ◯
    refine dSomehowElim
      (Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
        (Deriv.iden (.head _))) ?_
    exact Deriv.falsoElim _ (Deriv.iden (.head _))

/-- `[w4] ⊢ w3`. -/
theorem d_w4_w3 : Deriv [w4] w3 :=
  Deriv.impIntro
    (Deriv.impElim (Deriv.iden (.tail _ (.head _))) d_q12_q14)

/-- `[w1] ⊢ w4`: the two modus-ponens steps `q10, q14 ⊢ q5` and
`q8, q5 ⊢ q4`. -/
theorem d_w1_w4 : Deriv [w1] w4 := by
  refine Deriv.impIntro ?_
  have h10 : Deriv [q14, w1] q10 :=
    Deriv.andElim2 (Deriv.iden (.tail _ (.head _)))
  have h5 : Deriv [q14, w1] q5 :=
    Deriv.impElim (Deriv.iden (.head _)) h10
  exact Deriv.impElim
    (Deriv.andElim1 (Deriv.iden (.tail _ (.head _)))) h5

/-- `[w3] ⊢ w4`, by cut through `w2` and `w1`. -/
theorem d_w3_w4 : Deriv [w3] w4 :=
  Deriv.cutHead d_w3_w2 (Deriv.cutHead d_w2_w1 d_w1_w4)

/-! ## The collapse -/

theorem coll_w1_w2 : Interd w1 w2 := ⟨d_w1_w2, d_w2_w1⟩
theorem coll_w2_w3 : Interd w2 w3 := ⟨d_w2_w3, d_w3_w2⟩
theorem coll_w3_w4 : Interd w3 w4 := ⟨d_w3_w4, d_w4_w3⟩
theorem coll_w1_w3 : Interd w1 w3 := coll_w1_w2.trans coll_w2_w3
theorem coll_w2_w4 : Interd w2 w4 := coll_w2_w3.trans coll_w3_w4
theorem coll_w1_w4 : Interd w1 w4 := coll_w1_w3.trans coll_w3_w4

/-! ## The 16-class aggregate -/

/-- The 16 certified class representatives: the 15 dictionary classes
and `q15 := w2 = q9 ⊃ q4`, the class of all four §40 witnesses. -/
def repsL16 : List PLLFormula :=
  [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, w2]

def rep16 : Fin 16 → PLLFormula := fun i => repsL16.getD i.val .falsePLL

/-- **RN(◯,{}) has at least 16 interderivability classes**: the 16
representatives are pairwise non-interderivable.  Pairs inside the 15
are separated by the pinned countermodels of `wip/rnSep.lean`; the
witness class is separated from every base class by
`wip/rnDictRefute.lean` (`refute_cImp_9_4`). -/
theorem rep16_pairwise_distinct :
    ∀ i j : Fin 16, i ≠ j → ¬ Interd (rep16 i) (rep16 j) :=
  fun i j hne => match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hne
  | ⟨0, _⟩, ⟨1, _⟩ => sep_0_1
  | ⟨0, _⟩, ⟨2, _⟩ => sep_0_2
  | ⟨0, _⟩, ⟨3, _⟩ => sep_0_3
  | ⟨0, _⟩, ⟨4, _⟩ => sep_0_4
  | ⟨0, _⟩, ⟨5, _⟩ => sep_0_5
  | ⟨0, _⟩, ⟨6, _⟩ => sep_0_6
  | ⟨0, _⟩, ⟨7, _⟩ => sep_0_7
  | ⟨0, _⟩, ⟨8, _⟩ => sep_0_8
  | ⟨0, _⟩, ⟨9, _⟩ => sep_0_9
  | ⟨0, _⟩, ⟨10, _⟩ => sep_0_10
  | ⟨0, _⟩, ⟨11, _⟩ => sep_0_11
  | ⟨0, _⟩, ⟨12, _⟩ => sep_0_12
  | ⟨0, _⟩, ⟨13, _⟩ => sep_0_13
  | ⟨0, _⟩, ⟨14, _⟩ => sep_0_14
  | ⟨0, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨0, by decide⟩ h.symm
  | ⟨1, _⟩, ⟨0, _⟩ => fun h => sep_0_1 h.symm
  | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hne
  | ⟨1, _⟩, ⟨2, _⟩ => sep_1_2
  | ⟨1, _⟩, ⟨3, _⟩ => sep_1_3
  | ⟨1, _⟩, ⟨4, _⟩ => sep_1_4
  | ⟨1, _⟩, ⟨5, _⟩ => sep_1_5
  | ⟨1, _⟩, ⟨6, _⟩ => sep_1_6
  | ⟨1, _⟩, ⟨7, _⟩ => sep_1_7
  | ⟨1, _⟩, ⟨8, _⟩ => sep_1_8
  | ⟨1, _⟩, ⟨9, _⟩ => sep_1_9
  | ⟨1, _⟩, ⟨10, _⟩ => sep_1_10
  | ⟨1, _⟩, ⟨11, _⟩ => sep_1_11
  | ⟨1, _⟩, ⟨12, _⟩ => sep_1_12
  | ⟨1, _⟩, ⟨13, _⟩ => sep_1_13
  | ⟨1, _⟩, ⟨14, _⟩ => sep_1_14
  | ⟨1, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨1, by decide⟩ h.symm
  | ⟨2, _⟩, ⟨0, _⟩ => fun h => sep_0_2 h.symm
  | ⟨2, _⟩, ⟨1, _⟩ => fun h => sep_1_2 h.symm
  | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hne
  | ⟨2, _⟩, ⟨3, _⟩ => sep_2_3
  | ⟨2, _⟩, ⟨4, _⟩ => sep_2_4
  | ⟨2, _⟩, ⟨5, _⟩ => sep_2_5
  | ⟨2, _⟩, ⟨6, _⟩ => sep_2_6
  | ⟨2, _⟩, ⟨7, _⟩ => sep_2_7
  | ⟨2, _⟩, ⟨8, _⟩ => sep_2_8
  | ⟨2, _⟩, ⟨9, _⟩ => sep_2_9
  | ⟨2, _⟩, ⟨10, _⟩ => sep_2_10
  | ⟨2, _⟩, ⟨11, _⟩ => sep_2_11
  | ⟨2, _⟩, ⟨12, _⟩ => sep_2_12
  | ⟨2, _⟩, ⟨13, _⟩ => sep_2_13
  | ⟨2, _⟩, ⟨14, _⟩ => sep_2_14
  | ⟨2, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨2, by decide⟩ h.symm
  | ⟨3, _⟩, ⟨0, _⟩ => fun h => sep_0_3 h.symm
  | ⟨3, _⟩, ⟨1, _⟩ => fun h => sep_1_3 h.symm
  | ⟨3, _⟩, ⟨2, _⟩ => fun h => sep_2_3 h.symm
  | ⟨3, _⟩, ⟨3, _⟩ => absurd rfl hne
  | ⟨3, _⟩, ⟨4, _⟩ => sep_3_4
  | ⟨3, _⟩, ⟨5, _⟩ => sep_3_5
  | ⟨3, _⟩, ⟨6, _⟩ => sep_3_6
  | ⟨3, _⟩, ⟨7, _⟩ => sep_3_7
  | ⟨3, _⟩, ⟨8, _⟩ => sep_3_8
  | ⟨3, _⟩, ⟨9, _⟩ => sep_3_9
  | ⟨3, _⟩, ⟨10, _⟩ => sep_3_10
  | ⟨3, _⟩, ⟨11, _⟩ => sep_3_11
  | ⟨3, _⟩, ⟨12, _⟩ => sep_3_12
  | ⟨3, _⟩, ⟨13, _⟩ => sep_3_13
  | ⟨3, _⟩, ⟨14, _⟩ => sep_3_14
  | ⟨3, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨3, by decide⟩ h.symm
  | ⟨4, _⟩, ⟨0, _⟩ => fun h => sep_0_4 h.symm
  | ⟨4, _⟩, ⟨1, _⟩ => fun h => sep_1_4 h.symm
  | ⟨4, _⟩, ⟨2, _⟩ => fun h => sep_2_4 h.symm
  | ⟨4, _⟩, ⟨3, _⟩ => fun h => sep_3_4 h.symm
  | ⟨4, _⟩, ⟨4, _⟩ => absurd rfl hne
  | ⟨4, _⟩, ⟨5, _⟩ => sep_4_5
  | ⟨4, _⟩, ⟨6, _⟩ => sep_4_6
  | ⟨4, _⟩, ⟨7, _⟩ => sep_4_7
  | ⟨4, _⟩, ⟨8, _⟩ => sep_4_8
  | ⟨4, _⟩, ⟨9, _⟩ => sep_4_9
  | ⟨4, _⟩, ⟨10, _⟩ => sep_4_10
  | ⟨4, _⟩, ⟨11, _⟩ => sep_4_11
  | ⟨4, _⟩, ⟨12, _⟩ => sep_4_12
  | ⟨4, _⟩, ⟨13, _⟩ => sep_4_13
  | ⟨4, _⟩, ⟨14, _⟩ => sep_4_14
  | ⟨4, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨4, by decide⟩ h.symm
  | ⟨5, _⟩, ⟨0, _⟩ => fun h => sep_0_5 h.symm
  | ⟨5, _⟩, ⟨1, _⟩ => fun h => sep_1_5 h.symm
  | ⟨5, _⟩, ⟨2, _⟩ => fun h => sep_2_5 h.symm
  | ⟨5, _⟩, ⟨3, _⟩ => fun h => sep_3_5 h.symm
  | ⟨5, _⟩, ⟨4, _⟩ => fun h => sep_4_5 h.symm
  | ⟨5, _⟩, ⟨5, _⟩ => absurd rfl hne
  | ⟨5, _⟩, ⟨6, _⟩ => sep_5_6
  | ⟨5, _⟩, ⟨7, _⟩ => sep_5_7
  | ⟨5, _⟩, ⟨8, _⟩ => sep_5_8
  | ⟨5, _⟩, ⟨9, _⟩ => sep_5_9
  | ⟨5, _⟩, ⟨10, _⟩ => sep_5_10
  | ⟨5, _⟩, ⟨11, _⟩ => sep_5_11
  | ⟨5, _⟩, ⟨12, _⟩ => sep_5_12
  | ⟨5, _⟩, ⟨13, _⟩ => sep_5_13
  | ⟨5, _⟩, ⟨14, _⟩ => sep_5_14
  | ⟨5, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨5, by decide⟩ h.symm
  | ⟨6, _⟩, ⟨0, _⟩ => fun h => sep_0_6 h.symm
  | ⟨6, _⟩, ⟨1, _⟩ => fun h => sep_1_6 h.symm
  | ⟨6, _⟩, ⟨2, _⟩ => fun h => sep_2_6 h.symm
  | ⟨6, _⟩, ⟨3, _⟩ => fun h => sep_3_6 h.symm
  | ⟨6, _⟩, ⟨4, _⟩ => fun h => sep_4_6 h.symm
  | ⟨6, _⟩, ⟨5, _⟩ => fun h => sep_5_6 h.symm
  | ⟨6, _⟩, ⟨6, _⟩ => absurd rfl hne
  | ⟨6, _⟩, ⟨7, _⟩ => sep_6_7
  | ⟨6, _⟩, ⟨8, _⟩ => sep_6_8
  | ⟨6, _⟩, ⟨9, _⟩ => sep_6_9
  | ⟨6, _⟩, ⟨10, _⟩ => sep_6_10
  | ⟨6, _⟩, ⟨11, _⟩ => sep_6_11
  | ⟨6, _⟩, ⟨12, _⟩ => sep_6_12
  | ⟨6, _⟩, ⟨13, _⟩ => sep_6_13
  | ⟨6, _⟩, ⟨14, _⟩ => sep_6_14
  | ⟨6, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨6, by decide⟩ h.symm
  | ⟨7, _⟩, ⟨0, _⟩ => fun h => sep_0_7 h.symm
  | ⟨7, _⟩, ⟨1, _⟩ => fun h => sep_1_7 h.symm
  | ⟨7, _⟩, ⟨2, _⟩ => fun h => sep_2_7 h.symm
  | ⟨7, _⟩, ⟨3, _⟩ => fun h => sep_3_7 h.symm
  | ⟨7, _⟩, ⟨4, _⟩ => fun h => sep_4_7 h.symm
  | ⟨7, _⟩, ⟨5, _⟩ => fun h => sep_5_7 h.symm
  | ⟨7, _⟩, ⟨6, _⟩ => fun h => sep_6_7 h.symm
  | ⟨7, _⟩, ⟨7, _⟩ => absurd rfl hne
  | ⟨7, _⟩, ⟨8, _⟩ => sep_7_8
  | ⟨7, _⟩, ⟨9, _⟩ => sep_7_9
  | ⟨7, _⟩, ⟨10, _⟩ => sep_7_10
  | ⟨7, _⟩, ⟨11, _⟩ => sep_7_11
  | ⟨7, _⟩, ⟨12, _⟩ => sep_7_12
  | ⟨7, _⟩, ⟨13, _⟩ => sep_7_13
  | ⟨7, _⟩, ⟨14, _⟩ => sep_7_14
  | ⟨7, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨7, by decide⟩ h.symm
  | ⟨8, _⟩, ⟨0, _⟩ => fun h => sep_0_8 h.symm
  | ⟨8, _⟩, ⟨1, _⟩ => fun h => sep_1_8 h.symm
  | ⟨8, _⟩, ⟨2, _⟩ => fun h => sep_2_8 h.symm
  | ⟨8, _⟩, ⟨3, _⟩ => fun h => sep_3_8 h.symm
  | ⟨8, _⟩, ⟨4, _⟩ => fun h => sep_4_8 h.symm
  | ⟨8, _⟩, ⟨5, _⟩ => fun h => sep_5_8 h.symm
  | ⟨8, _⟩, ⟨6, _⟩ => fun h => sep_6_8 h.symm
  | ⟨8, _⟩, ⟨7, _⟩ => fun h => sep_7_8 h.symm
  | ⟨8, _⟩, ⟨8, _⟩ => absurd rfl hne
  | ⟨8, _⟩, ⟨9, _⟩ => sep_8_9
  | ⟨8, _⟩, ⟨10, _⟩ => sep_8_10
  | ⟨8, _⟩, ⟨11, _⟩ => sep_8_11
  | ⟨8, _⟩, ⟨12, _⟩ => sep_8_12
  | ⟨8, _⟩, ⟨13, _⟩ => sep_8_13
  | ⟨8, _⟩, ⟨14, _⟩ => sep_8_14
  | ⟨8, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨8, by decide⟩ h.symm
  | ⟨9, _⟩, ⟨0, _⟩ => fun h => sep_0_9 h.symm
  | ⟨9, _⟩, ⟨1, _⟩ => fun h => sep_1_9 h.symm
  | ⟨9, _⟩, ⟨2, _⟩ => fun h => sep_2_9 h.symm
  | ⟨9, _⟩, ⟨3, _⟩ => fun h => sep_3_9 h.symm
  | ⟨9, _⟩, ⟨4, _⟩ => fun h => sep_4_9 h.symm
  | ⟨9, _⟩, ⟨5, _⟩ => fun h => sep_5_9 h.symm
  | ⟨9, _⟩, ⟨6, _⟩ => fun h => sep_6_9 h.symm
  | ⟨9, _⟩, ⟨7, _⟩ => fun h => sep_7_9 h.symm
  | ⟨9, _⟩, ⟨8, _⟩ => fun h => sep_8_9 h.symm
  | ⟨9, _⟩, ⟨9, _⟩ => absurd rfl hne
  | ⟨9, _⟩, ⟨10, _⟩ => sep_9_10
  | ⟨9, _⟩, ⟨11, _⟩ => sep_9_11
  | ⟨9, _⟩, ⟨12, _⟩ => sep_9_12
  | ⟨9, _⟩, ⟨13, _⟩ => sep_9_13
  | ⟨9, _⟩, ⟨14, _⟩ => sep_9_14
  | ⟨9, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨9, by decide⟩ h.symm
  | ⟨10, _⟩, ⟨0, _⟩ => fun h => sep_0_10 h.symm
  | ⟨10, _⟩, ⟨1, _⟩ => fun h => sep_1_10 h.symm
  | ⟨10, _⟩, ⟨2, _⟩ => fun h => sep_2_10 h.symm
  | ⟨10, _⟩, ⟨3, _⟩ => fun h => sep_3_10 h.symm
  | ⟨10, _⟩, ⟨4, _⟩ => fun h => sep_4_10 h.symm
  | ⟨10, _⟩, ⟨5, _⟩ => fun h => sep_5_10 h.symm
  | ⟨10, _⟩, ⟨6, _⟩ => fun h => sep_6_10 h.symm
  | ⟨10, _⟩, ⟨7, _⟩ => fun h => sep_7_10 h.symm
  | ⟨10, _⟩, ⟨8, _⟩ => fun h => sep_8_10 h.symm
  | ⟨10, _⟩, ⟨9, _⟩ => fun h => sep_9_10 h.symm
  | ⟨10, _⟩, ⟨10, _⟩ => absurd rfl hne
  | ⟨10, _⟩, ⟨11, _⟩ => sep_10_11
  | ⟨10, _⟩, ⟨12, _⟩ => sep_10_12
  | ⟨10, _⟩, ⟨13, _⟩ => sep_10_13
  | ⟨10, _⟩, ⟨14, _⟩ => sep_10_14
  | ⟨10, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨10, by decide⟩ h.symm
  | ⟨11, _⟩, ⟨0, _⟩ => fun h => sep_0_11 h.symm
  | ⟨11, _⟩, ⟨1, _⟩ => fun h => sep_1_11 h.symm
  | ⟨11, _⟩, ⟨2, _⟩ => fun h => sep_2_11 h.symm
  | ⟨11, _⟩, ⟨3, _⟩ => fun h => sep_3_11 h.symm
  | ⟨11, _⟩, ⟨4, _⟩ => fun h => sep_4_11 h.symm
  | ⟨11, _⟩, ⟨5, _⟩ => fun h => sep_5_11 h.symm
  | ⟨11, _⟩, ⟨6, _⟩ => fun h => sep_6_11 h.symm
  | ⟨11, _⟩, ⟨7, _⟩ => fun h => sep_7_11 h.symm
  | ⟨11, _⟩, ⟨8, _⟩ => fun h => sep_8_11 h.symm
  | ⟨11, _⟩, ⟨9, _⟩ => fun h => sep_9_11 h.symm
  | ⟨11, _⟩, ⟨10, _⟩ => fun h => sep_10_11 h.symm
  | ⟨11, _⟩, ⟨11, _⟩ => absurd rfl hne
  | ⟨11, _⟩, ⟨12, _⟩ => sep_11_12
  | ⟨11, _⟩, ⟨13, _⟩ => sep_11_13
  | ⟨11, _⟩, ⟨14, _⟩ => sep_11_14
  | ⟨11, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨11, by decide⟩ h.symm
  | ⟨12, _⟩, ⟨0, _⟩ => fun h => sep_0_12 h.symm
  | ⟨12, _⟩, ⟨1, _⟩ => fun h => sep_1_12 h.symm
  | ⟨12, _⟩, ⟨2, _⟩ => fun h => sep_2_12 h.symm
  | ⟨12, _⟩, ⟨3, _⟩ => fun h => sep_3_12 h.symm
  | ⟨12, _⟩, ⟨4, _⟩ => fun h => sep_4_12 h.symm
  | ⟨12, _⟩, ⟨5, _⟩ => fun h => sep_5_12 h.symm
  | ⟨12, _⟩, ⟨6, _⟩ => fun h => sep_6_12 h.symm
  | ⟨12, _⟩, ⟨7, _⟩ => fun h => sep_7_12 h.symm
  | ⟨12, _⟩, ⟨8, _⟩ => fun h => sep_8_12 h.symm
  | ⟨12, _⟩, ⟨9, _⟩ => fun h => sep_9_12 h.symm
  | ⟨12, _⟩, ⟨10, _⟩ => fun h => sep_10_12 h.symm
  | ⟨12, _⟩, ⟨11, _⟩ => fun h => sep_11_12 h.symm
  | ⟨12, _⟩, ⟨12, _⟩ => absurd rfl hne
  | ⟨12, _⟩, ⟨13, _⟩ => sep_12_13
  | ⟨12, _⟩, ⟨14, _⟩ => sep_12_14
  | ⟨12, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨12, by decide⟩ h.symm
  | ⟨13, _⟩, ⟨0, _⟩ => fun h => sep_0_13 h.symm
  | ⟨13, _⟩, ⟨1, _⟩ => fun h => sep_1_13 h.symm
  | ⟨13, _⟩, ⟨2, _⟩ => fun h => sep_2_13 h.symm
  | ⟨13, _⟩, ⟨3, _⟩ => fun h => sep_3_13 h.symm
  | ⟨13, _⟩, ⟨4, _⟩ => fun h => sep_4_13 h.symm
  | ⟨13, _⟩, ⟨5, _⟩ => fun h => sep_5_13 h.symm
  | ⟨13, _⟩, ⟨6, _⟩ => fun h => sep_6_13 h.symm
  | ⟨13, _⟩, ⟨7, _⟩ => fun h => sep_7_13 h.symm
  | ⟨13, _⟩, ⟨8, _⟩ => fun h => sep_8_13 h.symm
  | ⟨13, _⟩, ⟨9, _⟩ => fun h => sep_9_13 h.symm
  | ⟨13, _⟩, ⟨10, _⟩ => fun h => sep_10_13 h.symm
  | ⟨13, _⟩, ⟨11, _⟩ => fun h => sep_11_13 h.symm
  | ⟨13, _⟩, ⟨12, _⟩ => fun h => sep_12_13 h.symm
  | ⟨13, _⟩, ⟨13, _⟩ => absurd rfl hne
  | ⟨13, _⟩, ⟨14, _⟩ => sep_13_14
  | ⟨13, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨13, by decide⟩ h.symm
  | ⟨14, _⟩, ⟨0, _⟩ => fun h => sep_0_14 h.symm
  | ⟨14, _⟩, ⟨1, _⟩ => fun h => sep_1_14 h.symm
  | ⟨14, _⟩, ⟨2, _⟩ => fun h => sep_2_14 h.symm
  | ⟨14, _⟩, ⟨3, _⟩ => fun h => sep_3_14 h.symm
  | ⟨14, _⟩, ⟨4, _⟩ => fun h => sep_4_14 h.symm
  | ⟨14, _⟩, ⟨5, _⟩ => fun h => sep_5_14 h.symm
  | ⟨14, _⟩, ⟨6, _⟩ => fun h => sep_6_14 h.symm
  | ⟨14, _⟩, ⟨7, _⟩ => fun h => sep_7_14 h.symm
  | ⟨14, _⟩, ⟨8, _⟩ => fun h => sep_8_14 h.symm
  | ⟨14, _⟩, ⟨9, _⟩ => fun h => sep_9_14 h.symm
  | ⟨14, _⟩, ⟨10, _⟩ => fun h => sep_10_14 h.symm
  | ⟨14, _⟩, ⟨11, _⟩ => fun h => sep_11_14 h.symm
  | ⟨14, _⟩, ⟨12, _⟩ => fun h => sep_12_14 h.symm
  | ⟨14, _⟩, ⟨13, _⟩ => fun h => sep_13_14 h.symm
  | ⟨14, _⟩, ⟨14, _⟩ => absurd rfl hne
  | ⟨14, _⟩, ⟨15, _⟩ => fun h => refute_cImp_9_4 ⟨14, by decide⟩ h.symm
  | ⟨15, _⟩, ⟨0, _⟩ => fun h => refute_cImp_9_4 ⟨0, by decide⟩ h
  | ⟨15, _⟩, ⟨1, _⟩ => fun h => refute_cImp_9_4 ⟨1, by decide⟩ h
  | ⟨15, _⟩, ⟨2, _⟩ => fun h => refute_cImp_9_4 ⟨2, by decide⟩ h
  | ⟨15, _⟩, ⟨3, _⟩ => fun h => refute_cImp_9_4 ⟨3, by decide⟩ h
  | ⟨15, _⟩, ⟨4, _⟩ => fun h => refute_cImp_9_4 ⟨4, by decide⟩ h
  | ⟨15, _⟩, ⟨5, _⟩ => fun h => refute_cImp_9_4 ⟨5, by decide⟩ h
  | ⟨15, _⟩, ⟨6, _⟩ => fun h => refute_cImp_9_4 ⟨6, by decide⟩ h
  | ⟨15, _⟩, ⟨7, _⟩ => fun h => refute_cImp_9_4 ⟨7, by decide⟩ h
  | ⟨15, _⟩, ⟨8, _⟩ => fun h => refute_cImp_9_4 ⟨8, by decide⟩ h
  | ⟨15, _⟩, ⟨9, _⟩ => fun h => refute_cImp_9_4 ⟨9, by decide⟩ h
  | ⟨15, _⟩, ⟨10, _⟩ => fun h => refute_cImp_9_4 ⟨10, by decide⟩ h
  | ⟨15, _⟩, ⟨11, _⟩ => fun h => refute_cImp_9_4 ⟨11, by decide⟩ h
  | ⟨15, _⟩, ⟨12, _⟩ => fun h => refute_cImp_9_4 ⟨12, by decide⟩ h
  | ⟨15, _⟩, ⟨13, _⟩ => fun h => refute_cImp_9_4 ⟨13, by decide⟩ h
  | ⟨15, _⟩, ⟨14, _⟩ => fun h => refute_cImp_9_4 ⟨14, by decide⟩ h
  | ⟨15, _⟩, ⟨15, _⟩ => absurd rfl hne
  | ⟨_+16, hh⟩, _ => absurd hh (by omega)
  | _, ⟨_+16, hh⟩ => absurd hh (by omega)

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.RND.coll_w1_w2' does not depend on any axioms
-/
#guard_msgs in
#print axioms coll_w1_w2

/--
info: 'PLLND.SemUI.RND.coll_w2_w3' does not depend on any axioms
-/
#guard_msgs in
#print axioms coll_w2_w3

/--
info: 'PLLND.SemUI.RND.coll_w3_w4' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms coll_w3_w4

/--
info: 'PLLND.SemUI.RND.rep16_pairwise_distinct' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms rep16_pairwise_distinct

end RND
end SemUI
end PLLND
