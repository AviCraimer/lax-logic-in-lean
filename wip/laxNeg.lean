import wip.rnClassify

/-!
# The lax negation `¬_◯ A := A ⊃ ◯⊥`

Prompted by Matthew's observation (2026-08-03) that `A ⊃ ◯⊥` behaves
as a new negation.  It is the negation of the ◯-localised algebra: `◯`
is a nucleus, the ◯-fixed classes form a Heyting algebra with the same
`∧` and `⊃` but with falsum `◯⊥`, and `¬_◯` is its pseudo-complement.

Two clarifications first (both PROVED here):

* `¬◯⊥ ⊃ ◯⊥  ≡  ¬¬◯⊥` — the instance at `A = ◯⊥` of the IPC law
  `(¬A ⊃ A) ↔ ¬¬A`.  So the equivalence Matthew first expected DOES
  hold for this formula.
* The refuted cell in the dictionary is its neighbour
  `(¬¬◯⊥ ⊃ ◯⊥) ⊬ ¬¬◯⊥` (`q10 ⊬ q6`) — an instance of the RN fact
  `rn 6 ⊬ rn 4` (`¬¬p ⊃ p ⊬ ¬¬p`), obtained HERE as an instance of
  the mechanised classification: no countermodel, just `decide`
  through `rn_classification` and `rnSub_order`.

Then the basic laws of `¬_◯` (all standard nucleus facts, all proved):
ordinary negation implies it; `A ⊢ ¬_◯¬_◯A`; triple = single;
de Morgan for `∨`; **`¬_◯ A ≡ ¬_◯ ◯A`** (the negation only sees the
◯-class — it is blind to the modality); `¬_◯⊤ ≡ ◯⊥`; and lax DNE
fails (`¬_◯¬_◯⊥ ⊬ ⊥`), so the localised algebra is not Boolean.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-- The lax negation: pseudo-complement into `◯⊥` (`q2`). -/
def lneg (A : PLLFormula) : PLLFormula := A.ifThen q2

/-- **`¬◯⊥ ⊃ ◯⊥ ≡ ¬¬◯⊥`** (`q3 ⊃ q2 ≡ q6`): the IPC equivalence
`(¬A ⊃ A) ↔ ¬¬A` at `A = ◯⊥`. -/
theorem imp_q3_q2_interd_q6 : Interd (q3.ifThen q2) q6 := by
  constructor
  · -- [q3 ⊃ q2] ⊢ q3 ⊃ ⊥
    refine Deriv.impIntro ?_
    have h2 : Deriv [q3, q3.ifThen q2] q2 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))
    exact Deriv.impElim (Deriv.iden (.head _)) h2
  · -- [¬¬◯⊥] ⊢ q3 ⊃ q2, by explosion
    refine Deriv.impIntro ?_
    have h0 : Deriv [q3, q6] q0 :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))
    exact Deriv.falsoElim _ h0

/-- `q10 ≡ rnSub 6`: an instance of the classification at `¬¬p ⊃ p`
(its code is `even 2`, computed by `decide`). -/
theorem q10_rn6 : Interd q10 (rnSub 6) := by
  have h := rn_classification
    (A := ((((PLLFormula.prop pv).ifThen .falsePLL).ifThen .falsePLL)).ifThen
      (.prop pv)) (by decide) (by decide)
  have e1 : embed (((((PLLFormula.prop pv).ifThen .falsePLL).ifThen
      .falsePLL)).ifThen (.prop pv)) = q10 := by decide
  have e2 : cls (((((PLLFormula.prop pv).ifThen .falsePLL).ifThen
      .falsePLL)).ifThen (.prop pv)) = .even 2 := by decide
  rw [e1, e2] at h
  exact h

/-- `q6 ≡ rnSub 4`: the classification at `¬¬p` (code `even 1`). -/
theorem q6_rn4 : Interd q6 (rnSub 4) := by
  have h := rn_classification
    (A := (((PLLFormula.prop pv).ifThen .falsePLL).ifThen .falsePLL))
    (by decide) (by decide)
  have e1 : embed ((((PLLFormula.prop pv).ifThen .falsePLL).ifThen
      .falsePLL)) = q6 := by decide
  have e2 : cls ((((PLLFormula.prop pv).ifThen .falsePLL).ifThen
      .falsePLL)) = .even 1 := by decide
  rw [e1, e2] at h
  exact h

/-- **The refuted neighbour**: `(¬¬◯⊥ ⊃ ◯⊥) ⊬ ¬¬◯⊥` (`q10 ⊬ q6`),
with no countermodel — transferred through the classification to the
decidable rung order, where `rungLe 6 4 = false` by `decide`. -/
theorem q10_not_q6 : ¬ Deriv [q10] q6 := by
  intro d
  have hr : Deriv [rnSub 6] (rnSub 4) :=
    Deriv.cutHead (Deriv.cutHead q10_rn6.2 d) q6_rn4.1
  have h := (rnSub_order 6 4).mp hr
  exact absurd h (by decide)

/-! ## The basic laws of `¬_◯` -/

/-- Ordinary negation implies lax negation: `¬A ⊢ ¬_◯A`. -/
theorem lneg_of_neg (A : PLLFormula) :
    Deriv [A.ifThen .falsePLL] (lneg A) := by
  refine Deriv.impIntro ?_
  refine Deriv.falsoElim _ ?_
  exact Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))

/-- `A ⊢ ¬_◯¬_◯A`. -/
theorem lneg_intro (A : PLLFormula) : Deriv [A] (lneg (lneg A)) := by
  refine Deriv.impIntro ?_
  exact Deriv.impElim (Deriv.iden (.head _)) (Deriv.iden (.tail _ (.head _)))

/-- Triple lax negation collapses: `¬_◯¬_◯¬_◯A ≡ ¬_◯A`. -/
theorem lneg_triple (A : PLLFormula) :
    Interd (lneg (lneg (lneg A))) (lneg A) := by
  constructor
  · refine Deriv.impIntro ?_
    exact Deriv.impElim (Deriv.iden (.tail _ (.head _)))
      (Deriv.cutHead (Deriv.iden (.head _)) (lneg_intro A))
  · exact lneg_intro (lneg A)

/-- De Morgan: `¬_◯(A ∨ B) ≡ ¬_◯A ∧ ¬_◯B`. -/
theorem lneg_or (A B : PLLFormula) :
    Interd (lneg (A.or B)) ((lneg A).and (lneg B)) := by
  constructor
  · refine Deriv.andIntro ?_ ?_
    · refine Deriv.impIntro ?_
      exact Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.orIntro1 (Deriv.iden (.head _)))
    · refine Deriv.impIntro ?_
      exact Deriv.impElim (Deriv.iden (.tail _ (.head _)))
        (Deriv.orIntro2 (Deriv.iden (.head _)))
  · refine Deriv.impIntro ?_
    refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
    · exact Deriv.impElim
        (Deriv.andElim1 (Deriv.iden (.tail _ (.tail _ (.head _)))))
        (Deriv.iden (.head _))
    · exact Deriv.impElim
        (Deriv.andElim2 (Deriv.iden (.tail _ (.tail _ (.head _)))))
        (Deriv.iden (.head _))

/-- **`¬_◯ ◯A ≡ ¬_◯ A`**: the lax negation only sees the ◯-class.
Left to right by the unit `A ⊢ ◯A`; right to left by ◯-elimination
(bind), since the target `◯⊥` is itself boxed. -/
theorem lneg_box (A : PLLFormula) : Interd (lneg A.somehow) (lneg A) := by
  constructor
  · refine Deriv.impIntro ?_
    exact Deriv.impElim (Deriv.iden (.tail _ (.head _)))
      (dSomehowIntro (Deriv.iden (.head _)))
  · refine Deriv.impIntro ?_
    refine dSomehowElim (Deriv.iden (.head _)) ?_
    exact Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
      (Deriv.iden (.head _))

/-- `¬_◯⊤ ≡ ◯⊥`: the false of the ◯-localised algebra. -/
theorem lneg_top : Interd (lneg q1) q2 := by
  constructor
  · exact Deriv.impElim (Deriv.iden (.head _)) dTop
  · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

/-- **Lax double-negation elimination fails**: `¬_◯¬_◯⊥ ⊬ ⊥` (indeed
`¬_◯¬_◯⊥ ≡ ◯⊥`), so the ◯-localised algebra is not Boolean.  Reduced
to the pinned `◯⊥ ⊬ ⊥`. -/
theorem lneg_dne_fails :
    ¬ Deriv [lneg (lneg PLLFormula.falsePLL)] PLLFormula.falsePLL := by
  intro d
  refine oBot_not_bot ?_
  refine Deriv.cutHead ?_ d
  exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

/-! ## Axiom audits — sorry-free throughout -/

/-- info: 'PLLND.RNEmbed.imp_q3_q2_interd_q6' does not depend on any axioms -/
#guard_msgs in
#print axioms imp_q3_q2_interd_q6

/-- info: 'PLLND.RNEmbed.q10_not_q6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms q10_not_q6

/-- info: 'PLLND.RNEmbed.lneg_box' does not depend on any axioms -/
#guard_msgs in
#print axioms lneg_box

/-- info: 'PLLND.RNEmbed.lneg_dne_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lneg_dne_fails

end RNEmbed
end PLLND
