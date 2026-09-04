import wip.rnSepColl

/-!
# Hand-lemma layer for the enlarged dictionary round

Hand-authored `Deriv` lemmas discharging cells of the 16-class closure
round that the searcher misses (2026-07-26).  Two devices:

* `ofImpTop`: every certified `Interd (A ⊃ B) ⊤` cell of
  `wip/rnDict.lean` is an ORDER FACT `[A] ⊢ B` — this unlocks it;
* the inside-◯ case-analysis LEGO of `wip/rnSepColl.lean` (derive a
  ◯-formula from `◯q7`/`◯q3`-type hypotheses by `orElim` under
  `dSomehowElim`, closing refuted branches with `falsoElim`).
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND

/-- A certified `(A ⊃ B) ≡ ⊤` cell is the order fact `[A] ⊢ B`. -/
theorem ofImpTop {A B : PLLFormula} (h : Interd (A.ifThen B) truePLL) :
    Deriv [A] B :=
  Deriv.impElim (Deriv.cutHead topD h.2) (Deriv.iden (.head _))

/-- `[q3] ⊢ q8`: with `q3` at hand, `q4` holds by its right disjunct. -/
theorem d_q3_q8 : Deriv [q3] q8 :=
  Deriv.impIntro (Deriv.orIntro2 (Deriv.iden (.tail _ (.head _))))

/-- `[q6] ⊢ q8`: from `q5 = ◯q3` and `q6 = ¬q3`, collapse to `◯⊥`. -/
theorem d_q6_q8 : Deriv [q6] q8 := by
  refine Deriv.impIntro (Deriv.orIntro1 ?_)
  refine dSomehowElim (Deriv.iden (.head _)) ?_
  exact Deriv.falsoElim _
    (Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
      (Deriv.iden (.head _)))

/-- `[q9] ⊢ q13 = ◯q8`: case analysis on `q9 = q5 ∨ q6`. -/
theorem d_q9_q13 : Deriv [q9] q13 := by
  refine Deriv.orElim (Deriv.iden (.head _)) ?c5 ?c6
  · -- q5 = ◯q3: derive q8 inside the modality
    exact dSomehowElim (Deriv.iden (.head _))
      (dSomehowIntro (d_q3_q8.toHead))
  · -- q6: q8 outright, then ◯-intro
    exact dSomehowIntro (d_q6_q8.toHead)

/-- From `◯⊥` anywhere, any ◯-formula: ex falso inside the modality. -/
theorem box_of_bb {Γ : List PLLFormula} (h : Deriv Γ q2)
    (X : PLLFormula) : Deriv Γ X.somehow :=
  dSomehowElim h (Deriv.falsoElim _ (Deriv.iden (.head _)))

/-- `[q4] ⊢ q9`: `q2`-branch by ex falso inside ◯, `q3`-branch by
◯-introduction (`q5 = ◯q3`). -/
theorem d_q4_q9 : Deriv [q4] q9 := by
  refine Deriv.orElim (Deriv.iden (.head _)) ?c2 ?c3
  · exact Deriv.orIntro1 (box_of_bb (Deriv.iden (.head _)) q3)
  · exact Deriv.orIntro1 (dSomehowIntro (Deriv.iden (.head _)))

/-- `[q4] ⊢ q14 = q10 ⊃ q5`: the hypothesis `q10` is not even
needed. -/
theorem d_q4_q14 : Deriv [q4] q14 := by
  refine Deriv.impIntro ?_
  refine Deriv.orElim (Deriv.iden (.tail _ (.head _))) ?c2 ?c3
  · exact box_of_bb (Deriv.iden (.head _)) q3
  · exact dSomehowIntro (Deriv.iden (.head _))

/-! ## Per-cell certificates (wired into the generator's `overrides`) -/

theorem hand_cAnd_9_13 : Interd (q9.and q13) q9 :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _)) d_q9_q13⟩

theorem hand_cAnd_9_14 : Interd (q9.and q14) q9 :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _)) (ofImpTop cImp_9_14)⟩

theorem hand_cAnd_11_14 : Interd (q11.and q14) q9 := by
  constructor
  · -- q11 = q6 ∨ q10 with q14 = q10 ⊃ q5 at hand
    refine Deriv.orElim (Deriv.andElim1 (Deriv.iden (.head _))) ?c6 ?c10
    · exact Deriv.orIntro2 (Deriv.iden (.head _))
    · exact Deriv.orIntro1
        (Deriv.impElim
          (Deriv.andElim2 (Deriv.iden (.tail _ (.head _))))
          (Deriv.iden (.head _)))
  · exact Deriv.andIntro (ofImpTop cImp_9_11) (ofImpTop cImp_9_14)

theorem hand_cAnd_12_14 : Interd (q12.and q14) q12 :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _)) (ofImpTop cImp_12_14)⟩

theorem hand_cAnd_4_14 : Interd (q4.and q14) q4 :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _)) d_q4_q14⟩

theorem hand_cAnd_8_10 : Interd (q8.and q10) w2 := coll_w1_w2

theorem hand_cAnd_8_15 : Interd (q8.and w2) w2 :=
  ⟨Deriv.andElim2 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.andElim1 d_w2_w1) (Deriv.iden (.head _))⟩

theorem hand_cAnd_9_15 : Interd (q9.and w2) q4 :=
  ⟨Deriv.impElim (Deriv.andElim2 (Deriv.iden (.head _)))
     (Deriv.andElim1 (Deriv.iden (.head _))),
   Deriv.andIntro d_q4_q9
     (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))⟩

theorem hand_cAnd_10_15 : Interd (q10.and w2) w2 :=
  ⟨Deriv.andElim2 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.andElim2 d_w2_w1) (Deriv.iden (.head _))⟩

theorem hand_cAnd_11_15 : Interd (q11.and w2) w2 :=
  ⟨Deriv.andElim2 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.orIntro2 (Deriv.andElim2 d_w2_w1))
     (Deriv.iden (.head _))⟩

theorem hand_cAnd_13_15 : Interd (q13.and w2) w2 :=
  ⟨Deriv.andElim2 (Deriv.iden (.head _)),
   Deriv.andIntro (dSomehowIntro (Deriv.andElim1 d_w2_w1))
     (Deriv.iden (.head _))⟩

theorem hand_cOr_2_13 : Interd (q2.or q13) q13 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (box_of_bb (Deriv.iden (.head _)) q8)
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_2_15 : Interd (q2.or w2) w2 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.impIntro (Deriv.orIntro1 (Deriv.iden (.tail _ (.head _)))))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_3_14 : Interd (q3.or q14) q14 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.impIntro (dSomehowIntro (Deriv.iden (.tail _ (.head _)))))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_4_15 : Interd (q4.or w2) w2 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_5_14 : Interd (q5.or q14) q14 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_6_13 : Interd (q6.or q13) q13 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (dSomehowIntro d_q6_q8.toHead)
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_3_15 : Interd (q3.or w2) w2 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.impIntro (Deriv.orIntro2 (Deriv.iden (.tail _ (.head _)))))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_6_14 : Interd (q6.or q14) q14 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.impIntro
       (box_of_bb
         (Deriv.impElim (Deriv.iden (.head _))
           (Deriv.iden (.tail _ (.head _)))) q3))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_7_13 : Interd (q7.or q13) q13 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.orElim (Deriv.iden (.head _))
       (dSomehowIntro d_q3_q8.toHead)
       (dSomehowIntro d_q6_q8.toHead))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_8_13 : Interd (q8.or q13) q13 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (dSomehowIntro (Deriv.iden (.head _)))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_8_15 : Interd (q8.or w2) q8 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.iden (.head _))
     (Deriv.andElim1 d_w2_w1.toHead),
   Deriv.orIntro1 (Deriv.iden (.head _))⟩

theorem hand_cOr_9_14 : Interd (q9.or q14) q14 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (ofImpTop cImp_9_14).toHead
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

/-- `q5 ⊢ q10 = q6 ⊃ q2` in any context carrying `q5`: from `◯q3` and
`q6 = ¬q3`, collapse to `◯⊥`. -/
theorem d_q5_q10 {Γ : List PLLFormula} (h : Deriv Γ q5) : Deriv Γ q10 :=
  Deriv.impIntro
    (dSomehowElim (h.rename fun _ hχ => .tail _ hχ)
      (Deriv.falsoElim _
        (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
          (Deriv.iden (.head _)))))

theorem hand_cImp_10_8 : Interd (q10.ifThen q8) q8 := by
  constructor
  · -- q8 = q5 ⊃ q4: q5 gives q10, so the hypothesis fires
    refine Deriv.impIntro ?_
    have d10 : Deriv [q5, q10.ifThen q8] q10 :=
      d_q5_q10 (Deriv.iden (.head _))
    exact Deriv.impElim
      (Deriv.impElim (Deriv.iden (.tail _ (.head _))) d10)
      (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem hand_cImp_5_15 : Interd (q5.ifThen w2) q8 := by
  constructor
  · -- from q5: the hypothesis gives w2, then q9 = orIntro1 q5, then q4
    refine Deriv.impIntro ?_
    exact Deriv.impElim
      (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.iden (.head _)))
      (Deriv.orIntro1 (Deriv.iden (.head _)))
  · -- from q8: on q5 and q9, apply q8 to q5
    refine Deriv.impIntro (Deriv.impIntro ?_)
    exact Deriv.impElim
      (Deriv.iden (.tail _ (.tail _ (.head _))))
      (Deriv.iden (.tail _ (.head _)))

theorem hand_cImp_9_8 : Interd (q9.ifThen q8) q8 := by
  constructor
  · refine Deriv.impIntro ?_
    exact Deriv.impElim
      (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.orIntro1 (Deriv.iden (.head _))))
      (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem hand_cImp_7_15 : Interd (q7.ifThen w2) q10 := by
  constructor
  · -- q10 = q6 ⊃ q2: from q6, get q4 via the hypothesis at q7 = orIntro2 q6,
    -- q9 = orIntro2 q6; the q3-branch of q4 is refuted by q6
    refine Deriv.impIntro ?_
    have hq4 : Deriv [q6, q7.ifThen w2] q4 :=
      Deriv.impElim
        (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
          (Deriv.orIntro2 (Deriv.iden (.head _))))
        (Deriv.orIntro2 (Deriv.iden (.head _)))
    exact Deriv.orElim hq4 (Deriv.iden (.head _))
      (Deriv.falsoElim _
        (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
          (Deriv.iden (.head _))))
  · -- from q10: on q7 and q9, all branches reach q4
    refine Deriv.impIntro (Deriv.impIntro ?_)
    refine Deriv.orElim (Deriv.iden (.head _)) ?c5 ?c6
    · -- q5-branch of q9: case q7 under it
      refine Deriv.orElim (Deriv.iden (.tail _ (.tail _ (.head _)))) ?c3 ?c6'
      · exact Deriv.orIntro2 (Deriv.iden (.head _))
      · exact Deriv.orIntro1
          (Deriv.impElim
            (Deriv.iden (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
            (Deriv.iden (.head _)))
    · exact Deriv.orIntro1
        (Deriv.impElim
          (Deriv.iden (.tail _ (.tail _ (.tail _ (.head _)))))
          (Deriv.iden (.head _)))

/-- Push a fresh hypothesis (weakening). -/
theorem _root_.PLLND.SemUI.Deriv.wk1 {Γ : List PLLFormula}
    {φ ψ : PLLFormula} (h : Deriv Γ ψ) : Deriv (φ :: Γ) ψ :=
  h.rename fun _ hχ => .tail _ hχ

/-- `q12 = ◯q7 ⊢ q13 = ◯q8` in any context: the inside-◯ case split. -/
theorem d_q12_to_q13 {Γ : List PLLFormula} (h : Deriv Γ q12) :
    Deriv Γ q13 :=
  dSomehowElim h
    (Deriv.orElim (Deriv.iden (.head _))
      (dSomehowIntro d_q3_q8.toHead)
      (dSomehowIntro d_q6_q8.toHead))

/-- `q12 ⊢ q14 = q10 ⊃ q5` in any context. -/
theorem d_q12_to_q14 {Γ : List PLLFormula} (h : Deriv Γ q12) :
    Deriv Γ q14 := by
  refine Deriv.impIntro ?_
  refine dSomehowElim h.wk1 ?_
  refine Deriv.orElim (Deriv.iden (.head _)) ?c3 ?c6
  · exact dSomehowIntro (Deriv.iden (.head _))
  · exact box_of_bb
      (Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
        (Deriv.iden (.head _))) q3

/-- `q4 ⊢ q12 = ◯q7` in any context over `[q4]`. -/
theorem d_q4_q12 : Deriv [q4] q12 := by
  refine Deriv.orElim (Deriv.iden (.head _)) ?c2 ?c3
  · exact box_of_bb (Deriv.iden (.head _)) q7
  · exact dSomehowIntro (Deriv.orIntro1 (Deriv.iden (.head _)))

theorem hand_cAnd_10_14 : Interd (q10.and q14) q5 :=
  ⟨Deriv.impElim (Deriv.andElim2 (Deriv.iden (.head _)))
     (Deriv.andElim1 (Deriv.iden (.head _))),
   Deriv.andIntro (d_q5_q10 (Deriv.iden (.head _)))
     (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))⟩

theorem hand_cAnd_12_13 : Interd (q12.and q13) q12 :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _))
     (d_q12_to_q13 (Deriv.iden (.head _)))⟩

theorem hand_cAnd_12_15 : Interd (q12.and w2) q4 :=
  ⟨Deriv.impElim
     (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) d_w2_w3)
     (Deriv.andElim1 (Deriv.iden (.head _))),
   Deriv.andIntro d_q4_q12
     (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))⟩

theorem hand_cAnd_14_15 : Interd (q14.and w2) q4 := by
  constructor
  · have h15 : Deriv [q14.and w2] w2 :=
      Deriv.andElim2 (Deriv.iden (.head _))
    have h10 : Deriv [q14.and w2] q10 :=
      Deriv.andElim2 (Deriv.cutHead h15 d_w2_w1)
    have h5 : Deriv [q14.and w2] q5 :=
      Deriv.impElim (Deriv.andElim1 (Deriv.iden (.head _))) h10
    exact Deriv.impElim h15 (Deriv.orIntro1 h5)
  · exact Deriv.andIntro d_q4_q14
      (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))

theorem hand_cImp_10_15 : Interd (q10.ifThen w2) q8 := by
  constructor
  · refine Deriv.impIntro ?_
    have h15 : Deriv [q5, q10.ifThen w2] w2 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (d_q5_q10 (Deriv.iden (.head _)))
    exact Deriv.impElim h15 (Deriv.orIntro1 (Deriv.iden (.head _)))
  · refine Deriv.impIntro (Deriv.impIntro ?_)
    refine Deriv.orElim (Deriv.iden (.head _)) ?c5 ?c6
    · exact Deriv.impElim
        (Deriv.iden (.tail _ (.tail _ (.tail _ (.head _)))))
        (Deriv.iden (.head _))
    · exact Deriv.orIntro1
        (Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
          (Deriv.iden (.head _)))

theorem hand_cImp_10_9 : Interd (q10.ifThen q9) q14 := by
  constructor
  · refine Deriv.impIntro ?_
    have h9 : Deriv [q10, q10.ifThen q9] q9 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.iden (.head _))
    refine Deriv.orElim h9 ?c5 ?c6
    · exact Deriv.iden (.head _)
    · exact box_of_bb
        (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
          (Deriv.iden (.head _))) q3
  · exact Deriv.impIntro
      (Deriv.orIntro1
        (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
          (Deriv.iden (.head _))))

theorem hand_cImp_11_12 : Interd (q11.ifThen q12) q14 := by
  constructor
  · refine Deriv.impIntro ?_
    have h12 : Deriv [q10, q11.ifThen q12] q12 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.orIntro2 (Deriv.iden (.head _)))
    refine dSomehowElim h12 ?_
    refine Deriv.orElim (Deriv.iden (.head _)) ?a3 ?a6
    case a3 => exact dSomehowIntro (Deriv.iden (.head _))
    case a6 =>
      exact box_of_bb
        (Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
          (Deriv.iden (.head _))) q3
  · refine Deriv.impIntro ?_
    refine Deriv.orElim (Deriv.iden (.head _)) ?b6 ?b10
    case b6 => exact dSomehowIntro (Deriv.orIntro2 (Deriv.iden (.head _)))
    case b10 =>
      refine dSomehowElim
        (Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
          (Deriv.iden (.head _))) ?_
      exact dSomehowIntro (Deriv.orIntro1 (Deriv.iden (.head _)))

theorem hand_cImp_11_14 : Interd (q11.ifThen q14) q14 := by
  constructor
  · refine Deriv.impIntro ?_
    have h14 : Deriv [q10, q11.ifThen q14] q14 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.orIntro2 (Deriv.iden (.head _)))
    exact Deriv.impElim h14 (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem hand_cImp_12_4 : Interd (q12.ifThen q4) w2 := coll_w2_w3.symm

theorem hand_cImp_13_8 : Interd (q13.ifThen q8) q8 := by
  constructor
  · refine Deriv.impIntro ?_
    have h13 : Deriv [q5, q13.ifThen q8] q13 :=
      dSomehowElim (Deriv.iden (.head _))
        (dSomehowIntro d_q3_q8.toHead)
    have h8 : Deriv [q5, q13.ifThen q8] q8 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) h13
    exact Deriv.impElim h8 (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem hand_cOr_11_15 : Interd (q11.or w2) q11 := by
  constructor
  · have h : Deriv [w2] q11 := Deriv.orIntro2 (Deriv.andElim2 d_w2_w1)
    exact Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _))
      h.toHead
  · exact Deriv.orIntro1 (Deriv.iden (.head _))

theorem hand_cOr_12_13 : Interd (q12.or q13) q13 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (d_q12_to_q13 (Deriv.iden (.head _)))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_12_14 : Interd (q12.or q14) q14 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (d_q12_to_q14 (Deriv.iden (.head _)))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_13_15 : Interd (q13.or w2) q13 := by
  constructor
  · have h : Deriv [w2] q13 := dSomehowIntro (Deriv.andElim1 d_w2_w1)
    exact Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _))
      h.toHead
  · exact Deriv.orIntro1 (Deriv.iden (.head _))

theorem hand_cOr_2_14 : Interd (q2.or q14) q14 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.impIntro
       (box_of_bb (Deriv.iden (.tail _ (.head _))) q3))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_3_13 : Interd (q3.or q13) q13 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (dSomehowIntro d_q3_q8.toHead)
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_4_14 : Interd (q4.or q14) q14 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     d_q4_q14.toHead
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cOr_7_14 : Interd (q7.or q14) q14 := by
  constructor
  · refine Deriv.orElim (Deriv.iden (.head _)) ?c7 ?c14
    · refine Deriv.impIntro ?_
      refine Deriv.orElim (Deriv.iden (.tail _ (.head _))) ?c3 ?c6
      · exact dSomehowIntro (Deriv.iden (.head _))
      · exact box_of_bb
          (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
            (Deriv.iden (.head _))) q3
    · exact Deriv.iden (.head _)
  · exact Deriv.orIntro2 (Deriv.iden (.head _))

/-- `q9 ⊢ q12 = ◯q7` in any context. -/
theorem d_q9_to_q12 {Γ : List PLLFormula} (h : Deriv Γ q9) :
    Deriv Γ q12 := by
  refine Deriv.orElim h ?c5 ?c6
  · exact dSomehowElim (Deriv.iden (.head _))
      (dSomehowIntro (Deriv.orIntro1 (Deriv.iden (.head _))))
  · exact dSomehowIntro (Deriv.orIntro2 (Deriv.iden (.head _)))

theorem hand_cImp_10_14 : Interd (q10.ifThen q14) q14 := by
  constructor
  · refine Deriv.impIntro ?_
    have h14 : Deriv [q10, q10.ifThen q14] q14 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.iden (.head _))
    exact Deriv.impElim h14 (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem hand_cImp_11_8 : Interd (q11.ifThen q8) q8 := by
  constructor
  · refine Deriv.impIntro ?_
    have h11 : Deriv [q5, q11.ifThen q8] q11 :=
      Deriv.orIntro2 (d_q5_q10 (Deriv.iden (.head _)))
    have h8 : Deriv [q5, q11.ifThen q8] q8 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) h11
    exact Deriv.impElim h8 (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem hand_cImp_12_15 : Interd (q12.ifThen w2) w2 := by
  constructor
  · refine Deriv.impIntro ?_
    have h15 : Deriv [q9, q12.ifThen w2] w2 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (d_q9_to_q12 (Deriv.iden (.head _)))
    exact Deriv.impElim h15 (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem hand_cImp_14_5 : Interd (q14.ifThen q5) q10 := by
  constructor
  · refine Deriv.impIntro ?_
    have h14 : Deriv [q6, q14.ifThen q5] q14 := by
      refine Deriv.impIntro ?_
      exact box_of_bb
        (Deriv.impElim (Deriv.iden (.head _))
          (Deriv.iden (.tail _ (.head _)))) q3
    have h5 : Deriv [q6, q14.ifThen q5] q5 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) h14
    refine dSomehowElim h5 ?_
    exact Deriv.falsoElim _
      (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.iden (.head _)))
  · exact Deriv.impIntro
      (Deriv.impElim (Deriv.iden (.head _))
        (Deriv.iden (.tail _ (.head _))))

theorem hand_cImp_8_15 : Interd (q8.ifThen w2) q10 := by
  constructor
  · refine Deriv.impIntro ?_
    have h15 : Deriv [q6, q8.ifThen w2] w2 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) d_q6_q8.toHead
    have hq4 : Deriv [q6, q8.ifThen w2] q4 :=
      Deriv.impElim h15 (Deriv.orIntro2 (Deriv.iden (.head _)))
    refine Deriv.orElim hq4 ?c2 ?c3
    · exact Deriv.iden (.head _)
    · exact Deriv.falsoElim _
        (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
          (Deriv.iden (.head _)))
  · refine Deriv.impIntro (Deriv.impIntro ?_)
    refine Deriv.orElim (Deriv.iden (.head _)) ?c5 ?c6
    · exact Deriv.impElim
        (Deriv.iden (.tail _ (.tail _ (.head _))))
        (Deriv.iden (.head _))
    · exact Deriv.orIntro1
        (Deriv.impElim
          (Deriv.iden (.tail _ (.tail _ (.tail _ (.head _)))))
          (Deriv.iden (.head _)))

theorem hand_cImp_9_15 : Interd (q9.ifThen w2) w2 := by
  constructor
  · refine Deriv.impIntro ?_
    have h15 : Deriv [q9, q9.ifThen w2] w2 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.iden (.head _))
    exact Deriv.impElim h15 (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem hand_cImp_8_10 : Interd (q8.ifThen q10) q10 := by
  constructor
  · refine Deriv.impIntro ?_
    have h8 : Deriv [q6, q8.ifThen q10] q8 := d_q6_q8.toHead
    have h10 : Deriv [q6, q8.ifThen q10] q10 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) h8
    exact Deriv.impElim h10 (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem hand_cImp_14_15 : Interd (q14.ifThen w2) w2 := by
  constructor
  · refine Deriv.impIntro ?_
    have h14 : Deriv [q9, q14.ifThen w2] q14 :=
      Deriv.cutHead (Deriv.iden (.head _)) (ofImpTop cImp_9_14)
    have h15 : Deriv [q9, q14.ifThen w2] w2 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) h14
    exact Deriv.impElim h15 (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem hand_cImp_14_8 : Interd (q14.ifThen q8) q8 := by
  constructor
  · refine Deriv.impIntro ?_
    have h14 : Deriv [q5, q14.ifThen q8] q14 :=
      Deriv.impIntro (Deriv.iden (.tail _ (.head _)))
    have h8 : Deriv [q5, q14.ifThen q8] q8 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) h14
    exact Deriv.impElim h8 (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

/-- `q9 ⊢ q11 = q6 ∨ q10` in any context. -/
theorem d_q9_to_q11 {Γ : List PLLFormula} (h : Deriv Γ q9) :
    Deriv Γ q11 := by
  refine Deriv.orElim h ?c5 ?c6
  · exact Deriv.orIntro2 (d_q5_q10 (Deriv.iden (.head _)))
  · exact Deriv.orIntro1 (Deriv.iden (.head _))

theorem hand_cBox_14 : Interd q14.somehow q14 := by
  constructor
  · refine Deriv.impIntro ?_
    refine dSomehowElim (Deriv.iden (.tail _ (.head _))) ?_
    exact Deriv.impElim (Deriv.iden (.head _))
      (Deriv.iden (.tail _ (.head _)))
  · exact dSomehowIntro (Deriv.iden (.head _))

theorem hand_cImp_11_15 : Interd (q11.ifThen w2) w2 := by
  constructor
  · refine Deriv.impIntro ?_
    have h15 : Deriv [q9, q11.ifThen w2] w2 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (d_q9_to_q11 (Deriv.iden (.head _)))
    exact Deriv.impElim h15 (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem hand_cImp_13_15 : Interd (q13.ifThen w2) w2 := by
  constructor
  · refine Deriv.impIntro ?_
    have h13 : Deriv [q9, q13.ifThen w2] q13 :=
      Deriv.cutHead (Deriv.iden (.head _)) d_q9_q13
    have h15 : Deriv [q9, q13.ifThen w2] w2 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) h13
    exact Deriv.impElim h15 (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

/-- `q5 = ◯q3 ⊢ q12 = ◯q7` in any context (◯-monotone injection). -/
theorem d_q5_to_q12 {Γ : List PLLFormula} (h : Deriv Γ q5) :
    Deriv Γ q12 :=
  dSomehowElim h (dSomehowIntro (Deriv.orIntro1 (Deriv.iden (.head _))))

theorem hand_cOr_9_13 : Interd (q9.or q13) q13 :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     d_q9_q13.toHead
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem hand_cImp_12_8 : Interd (q12.ifThen q8) q8 := by
  constructor
  · refine Deriv.impIntro ?_
    have h12 : Deriv [q5, q12.ifThen q8] q12 :=
      d_q5_to_q12 (Deriv.iden (.head _))
    have h8 : Deriv [q5, q12.ifThen q8] q8 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) h12
    exact Deriv.impElim h8 (Deriv.iden (.head _))
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem hand_cImp_10_12 : Interd (q10.ifThen q12) q14 := by
  constructor
  · refine Deriv.impIntro ?_
    have h12 : Deriv [q10, q10.ifThen q12] q12 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.iden (.head _))
    refine dSomehowElim h12 ?_
    refine Deriv.orElim (Deriv.iden (.head _)) ?a3 ?a6
    case a3 => exact dSomehowIntro (Deriv.iden (.head _))
    case a6 =>
      exact box_of_bb
        (Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
          (Deriv.iden (.head _))) q3
  · refine Deriv.impIntro ?_
    exact d_q5_to_q12
      (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.iden (.head _)))

theorem hand_cImp_11_9 : Interd (q11.ifThen q9) q14 := by
  constructor
  · refine Deriv.impIntro ?_
    have h9 : Deriv [q10, q11.ifThen q9] q9 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.orIntro2 (Deriv.iden (.head _)))
    refine Deriv.orElim h9 ?a5 ?a6
    case a5 => exact Deriv.iden (.head _)
    case a6 =>
      exact box_of_bb
        (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
          (Deriv.iden (.head _))) q3
  · refine Deriv.impIntro ?_
    refine Deriv.orElim (Deriv.iden (.head _)) ?b6 ?b10
    case b6 => exact Deriv.orIntro2 (Deriv.iden (.head _))
    case b10 =>
      exact Deriv.orIntro1
        (Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
          (Deriv.iden (.head _)))

theorem hand_cImp_11_4 : Interd (q11.ifThen q4) q4 := by
  constructor
  · -- derive q10 internally from the q6-arm of the hypothesis, then apply
    have h6_4 : Deriv [q11.ifThen q4] (q6.ifThen q4) :=
      Deriv.impIntro
        (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
          (Deriv.orIntro1 (Deriv.iden (.head _))))
    have d10 : Deriv [q11.ifThen q4] q10 := by
      refine Deriv.impIntro ?_
      have hq4 : Deriv [q6, q11.ifThen q4] q4 :=
        Deriv.impElim h6_4.wk1 (Deriv.iden (.head _))
      refine Deriv.orElim hq4 ?x2 ?x3
      case x2 => exact Deriv.iden (.head _)
      case x3 =>
        exact Deriv.falsoElim _
          (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
            (Deriv.iden (.head _)))
    exact Deriv.impElim
      (Deriv.impIntro
        (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
          (Deriv.orIntro2 (Deriv.iden (.head _)))))
      d10
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

end RND
end SemUI
end PLLND
