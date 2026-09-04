import wip.rnEmbed
import wip.rnDict
import LaxLogic.PLLCountermodelEmit

/-!
# Distribution is NOT free on the ladder image

`rnSub_derivU_iff_deriv` says PCLL proves no `rnSub i ⊢ rnSub j` that
PLL does not.  That is a statement about a *rung premise and a rung
conclusion*, and it does not extend to formulas built from rungs.  This
file exhibits the gap: an instance of the distribution axiom

    ◯(A ∨ B) ⊃ (◯A ∨ ◯B)

at rung arguments `A = rnSub 4`, `B = rnSub 3` which is derivable in
PCLL (it is an axiom instance) and **not** derivable in PLL.

## The countermodel

`wip/rnSep.lean` already contains it, as the certificate for
`sep_9_12 : ¬ Interd q9 q12`.  It has FIVE worlds, which is why the
searcher's default battery — all well-formed frames up to four worlds —
reports `?` here however long it is run: the refutation is out of its
range, and the positive stage cannot find a proof because there is
none.

The instance reduces to `q12 ⊢ q9` through the identifications
certified in `wip/ladderfast_out.txt`, but nothing below depends on
that reduction: the model is checked against the literal formula.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-- The five-world countermodel, from `rnSep.sep_9_12`.  World `3` is
fallible; `Rₘ` links `0 ⇝ 1` and `2 ⇝ 3`. -/
def Msep : FinCM :=
  ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)],
      [(0, 1), (2, 3)], [3], []⟩

/-- `◯(A ∨ B) ⊃ (◯A ∨ ◯B)`, the distribution axiom instance. -/
def distrAx (A B : PLLFormula) : PLLFormula :=
  (A.or B).somehow.ifThen ((A.somehow).or (B.somehow))

/-! ## The result -/

/-- **Distribution at rungs 4 and 3 is not PLL-derivable.**

Spelled out, the underivable formula is

    ◯( ((◯⊥ ∨ ¬◯⊥) ⊃ ◯⊥) ∨ (◯⊥ ∨ ¬◯⊥) )
      ⊃ ( ◯((◯⊥ ∨ ¬◯⊥) ⊃ ◯⊥) ∨ ◯(◯⊥ ∨ ¬◯⊥) )

and it is an instance of the PCLL axiom, so PCLL ⊋ PLL already on
formulas built from two rungs. -/
theorem distr_4_3_not_derivable :
    ¬ Deriv [] (distrAx (rnSub 4) (rnSub 3)) :=
  FinCM.not_provable_of_check (M := Msep) (w := 0) (by decide)

/-- The same in its reduced form: `q12 ⊬ q9`, the cell that
`wip/rnDict.lean` records as OPEN (`cImp_12_9`, sorried, "candidates
[1, 11, 13] neither proved nor refuted (exhaustive ≤4-world
battery)").  It is settled here, negatively. -/
theorem q12_not_derives_q9 : ¬ Deriv [q12] q9 :=
  FinCM.not_provable_of_check (M := Msep) (w := 0) (by decide)

/-- The converse direction does hold, so `q9 < q12` strictly. -/
theorem q9_derives_q12 : Deriv [q9] q12 := by
  refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
  · -- q5 = ◯¬◯⊥: open it, inject ¬◯⊥ as the left disjunct of q7, re-box
    exact dSomehowElim (Deriv.iden (.head _))
      (dSomehowIntro (Deriv.orIntro1 (Deriv.iden (.head _))))
  · -- q6 = ¬¬◯⊥: it is the right disjunct of q7 already
    exact dSomehowIntro (Deriv.orIntro2 (Deriv.iden (.head _)))

/-! ## Axiom audits -/

/-- info: 'PLLND.RNEmbed.distr_4_3_not_derivable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms distr_4_3_not_derivable

/-- info: 'PLLND.RNEmbed.q12_not_derives_q9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms q12_not_derives_q9

end RNEmbed
end PLLND
