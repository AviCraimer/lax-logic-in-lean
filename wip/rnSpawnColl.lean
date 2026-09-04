import wip.rnDict2Hand

/-!
# The spawned-class collapses — exact in-family classification

Hand-authored certificates (2026-07-26) deciding the 8 pairs the
spawned-class pairwise scan (`wip/xsep_*.txt`) left open: ALL are
collapses, each another instance of the searcher-gap LEGO.  With
these, the spawned classes of the 16-class closure round classify
EXACTLY within their families:

* ∧-family: 6 classes (all pairwise distinct);
* ∨-family: 9 classes (13 witnesses, 4 merges:
  q8∨q10 ≡ q8∨q11, q10∨q13 ≡ q11∨q13, q10∨q14 ≡ q11∨q14,
  q6∨q15 ≡ q7∨q15);
* ⊃-family: 8 classes (12 witnesses, 4 merges:
  q8⊃q4 ≡ q8⊃q5, q8⊃q7 ≡ q8⊃q9, q10⊃q4 ≡ q11⊃q7,
  q13⊃q12 ≡ q8⊃q12);
* ◯-column: ◯q11 and ◯q15 (distinct from the 16; cross-family
  status open).

Cross-family pairs are not yet classified; the certified global
lower bound from the ∨-family clique is 16 + 9 = 25 classes.
-/

open PLLFormula

namespace PLLND
namespace SemUI
namespace RND

/-- `q8∨q10 ≡ q8∨q11`: the `q6`-arm of `q11` already yields `q8`. -/
theorem spcoll_or_8_10_11 : Interd (q8.or q10) (q8.or q11) := by
  constructor
  · refine Deriv.orElim (Deriv.iden (.head _)) ?h1 ?h2
    case h1 => exact Deriv.orIntro1 (Deriv.iden (.head _))
    case h2 => exact Deriv.orIntro2 (Deriv.orIntro2 (Deriv.iden (.head _)))
  · refine Deriv.orElim (Deriv.iden (.head _)) ?h1 ?h2
    case h1 => exact Deriv.orIntro1 (Deriv.iden (.head _))
    case h2 =>
      refine Deriv.orElim (Deriv.iden (.head _)) ?h3 ?h4
      case h3 => exact Deriv.orIntro1 d_q6_q8.toHead
      case h4 => exact Deriv.orIntro2 (Deriv.iden (.head _))

/-- `q10∨q13 ≡ q11∨q13`: the `q6`-arm yields `q13 = ◯q8`. -/
theorem spcoll_or_10_13_11_13 : Interd (q10.or q13) (q11.or q13) := by
  constructor
  · refine Deriv.orElim (Deriv.iden (.head _)) ?h1 ?h2
    case h1 => exact Deriv.orIntro1 (Deriv.orIntro2 (Deriv.iden (.head _)))
    case h2 => exact Deriv.orIntro2 (Deriv.iden (.head _))
  · refine Deriv.orElim (Deriv.iden (.head _)) ?h1 ?h2
    case h1 =>
      refine Deriv.orElim (Deriv.iden (.head _)) ?h3 ?h4
      case h3 => exact Deriv.orIntro2 (dSomehowIntro d_q6_q8.toHead)
      case h4 => exact Deriv.orIntro1 (Deriv.iden (.head _))
    case h2 => exact Deriv.orIntro2 (Deriv.iden (.head _))

/-- `q10∨q14 ≡ q11∨q14`: the `q6`-arm yields `q14` (collapse to ◯⊥
under the pushed `q10`). -/
theorem spcoll_or_10_14_11_14 : Interd (q10.or q14) (q11.or q14) := by
  constructor
  · refine Deriv.orElim (Deriv.iden (.head _)) ?h1 ?h2
    case h1 => exact Deriv.orIntro1 (Deriv.orIntro2 (Deriv.iden (.head _)))
    case h2 => exact Deriv.orIntro2 (Deriv.iden (.head _))
  · refine Deriv.orElim (Deriv.iden (.head _)) ?h1 ?h2
    case h1 =>
      refine Deriv.orElim (Deriv.iden (.head _)) ?h3 ?h4
      case h3 =>
        refine Deriv.orIntro2 (Deriv.impIntro ?_)
        exact box_of_bb
          (Deriv.impElim (Deriv.iden (.head _))
            (Deriv.iden (.tail _ (.head _)))) q3
      case h4 => exact Deriv.orIntro1 (Deriv.iden (.head _))
    case h2 => exact Deriv.orIntro2 (Deriv.iden (.head _))

/-- `q6∨q15 ≡ q7∨q15`: the `q3`-arm of `q7` yields `q15` (`q3`
refutes the `q9`-antecedent's conclusion demand via `q4`'s right
disjunct). -/
theorem spcoll_or_6_15_7_15 : Interd (q6.or w2) (q7.or w2) := by
  constructor
  · refine Deriv.orElim (Deriv.iden (.head _)) ?h1 ?h2
    case h1 => exact Deriv.orIntro1 (Deriv.orIntro2 (Deriv.iden (.head _)))
    case h2 => exact Deriv.orIntro2 (Deriv.iden (.head _))
  · refine Deriv.orElim (Deriv.iden (.head _)) ?h1 ?h2
    case h1 =>
      refine Deriv.orElim (Deriv.iden (.head _)) ?h3 ?h4
      case h3 =>
        exact Deriv.orIntro2
          (Deriv.impIntro (Deriv.orIntro2 (Deriv.iden (.tail _ (.head _)))))
      case h4 => exact Deriv.orIntro1 (Deriv.iden (.head _))
    case h2 => exact Deriv.orIntro2 (Deriv.iden (.head _))

/-- `q8⊃q4 ≡ q8⊃q5`: under the hypothesis `q8 = q5⊃q4`, `q4` and `q5`
interderive (`q4 ⊢ q5` is the certified cell `cImp_4_5`; `q5 ⊢ q4` is
`q8` itself). -/
theorem spcoll_imp_8_4_5 : Interd (q8.ifThen q4) (q8.ifThen q5) := by
  constructor
  · refine Deriv.impIntro ?_
    have h4 : Deriv [q8, q8.ifThen q4] q4 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))
    exact Deriv.cutHead h4 (ofImpTop cImp_4_5)
  · refine Deriv.impIntro ?_
    have h5 : Deriv [q8, q8.ifThen q5] q5 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))
    exact Deriv.impElim (Deriv.iden (.head _)) h5

/-- `q8⊃q7 ≡ q8⊃q9`: `q7 ⊢ q9` outright (cell `cImp_7_9`); back, under
`q8`, the `q5`-arm of `q9` reaches `q4`, whose `q2`-arm refutes `q3`
(giving `q6`) and whose `q3`-arm is `q7`'s left disjunct. -/
theorem spcoll_imp_8_7_9 : Interd (q8.ifThen q7) (q8.ifThen q9) := by
  constructor
  · refine Deriv.impIntro ?_
    have h7 : Deriv [q8, q8.ifThen q7] q7 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))
    exact Deriv.cutHead h7 (ofImpTop cImp_7_9)
  · refine Deriv.impIntro ?_
    have h9 : Deriv [q8, q8.ifThen q9] q9 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))
    refine Deriv.orElim h9 ?c5 ?c6
    case c6 => exact Deriv.orIntro2 (Deriv.iden (.head _))
    case c5 =>
      have h4 : Deriv [q5, q8, q8.ifThen q9] q4 :=
        Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))
      refine Deriv.orElim h4 ?c2 ?c3
      case c2 =>
        refine Deriv.orIntro2 (Deriv.impIntro ?_)
        exact Deriv.impElim (Deriv.iden (.head _))
          (Deriv.iden (.tail _ (.head _)))
      case c3 => exact Deriv.orIntro1 (Deriv.iden (.head _))

/-- `q10⊃q4 ≡ q11⊃q7` (a CROSS-SHAPE collapse): forward, the
`q10`-arm of `q11` reaches `q4`, whose `q2`-arm refutes `q3` (giving
`q6`); back, the `q6`-arm of `q7` fires `q10`. -/
theorem spcoll_imp_10_4_11_7 : Interd (q10.ifThen q4) (q11.ifThen q7) := by
  constructor
  · refine Deriv.impIntro ?_
    refine Deriv.orElim (Deriv.iden (.head _)) ?c6 ?c10
    case c6 => exact Deriv.orIntro2 (Deriv.iden (.head _))
    case c10 =>
      have h4 : Deriv [q10, q11, q10.ifThen q4] q4 :=
        Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
          (Deriv.iden (.head _))
      refine Deriv.orElim h4 ?c2 ?c3
      case c2 =>
        refine Deriv.orIntro2 (Deriv.impIntro ?_)
        exact Deriv.impElim (Deriv.iden (.head _))
          (Deriv.iden (.tail _ (.head _)))
      case c3 => exact Deriv.orIntro1 (Deriv.iden (.head _))
  · refine Deriv.impIntro ?_
    have h7 : Deriv [q10, q11.ifThen q7] q7 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.orIntro2 (Deriv.iden (.head _)))
    refine Deriv.orElim h7 ?c3 ?c6
    case c3 => exact Deriv.orIntro2 (Deriv.iden (.head _))
    case c6 =>
      exact Deriv.orIntro1
        (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
          (Deriv.iden (.head _)))

/-- `q13⊃q12 ≡ q8⊃q12`: `q13 = ◯q8`, and a ◯-goal lets the hypothesis
fire inside the modality. -/
theorem spcoll_imp_13_12_8_12 :
    Interd (q13.ifThen q12) (q8.ifThen q12) := by
  constructor
  · refine Deriv.impIntro ?_
    exact Deriv.impElim (Deriv.iden (.tail _ (.head _)))
      (dSomehowIntro (Deriv.iden (.head _)))
  · refine Deriv.impIntro ?_
    refine dSomehowElim (Deriv.iden (.head _)) ?_
    exact Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
      (Deriv.iden (.head _))

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.RND.spcoll_imp_10_4_11_7' does not depend on any axioms
-/
#guard_msgs in
#print axioms spcoll_imp_10_4_11_7

/--
info: 'PLLND.SemUI.RND.spcoll_or_6_15_7_15' does not depend on any axioms
-/
#guard_msgs in
#print axioms spcoll_or_6_15_7_15

end RND
end SemUI
end PLLND
