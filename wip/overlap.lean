import wip.embedNeg
import wip.fiveWorld
import wip.rncCert

/-!
# Other embeddings of RN({p}): dense seeds fail, and width ≥ 3

Two results about the family of maps `h_φ : p ↦ φ` from the
Rieger–Nishimura lattice into RN(◯,{}), following the questions:
where can embeddings other than `h = h_{◯⊥}` live, and how wide is
RN(◯,{})?

## 1.  Dense seeds fail at rung 2

Call `φ` **dense** when `⊢ ¬¬φ` (equivalently `¬φ ⊣⊢ ⊥`).  For dense
`φ` the map `h_φ` collapses rung 2 onto rung 0:

    h_φ(¬p) = ¬φ ⊣⊢ ⊥ = h_φ(⊥),   though   ¬p ⊬⊢ ⊥ in RN({p}).

So a dense `φ` cannot seed an embedding of the ladder
(`no_embeds1_of_dense`).

Density propagates upward, and `◯⊥ ∨ ¬◯⊥` is dense (the instance
`¬¬(A ∨ ¬A)` of an IPC theorem).  So everything above the guard is
dense — and ALL SIX known off-image classes lie above the guard
(`guard_q5/q8/q9/q12/q13/q14`; three were in `wip/secondgen.lean`,
three are new here).  Hence none of the known off-image classes seeds
an embedding of RN({p}) (`no_embeds1_q5` … `no_embeds1_q14`).

Contrapositive, for the hunt: a fresh embedding needs a NON-dense
seed, and non-dense forces `φ` off the guard cone — the region where
every known off-image class does NOT live.

## 2.  RN(◯,{}) has width at least 3

The ladder has width exactly 2.  The full variable-free fragment is
strictly wider:

    {q8, q9, q10}  =  { ◯¬◯⊥ ⊃ (◯⊥ ∨ ¬◯⊥),  ◯¬◯⊥ ∨ ¬¬◯⊥,  ¬¬◯⊥ ⊃ ◯⊥ }

is a three-element antichain (`antichain_q8_q9_q10`): six directional
non-derivabilities, each by a checked finite countermodel.  Four come
from the PCLL refutations of `wip/rncCert.lean` (a PCLL refutation is a
fortiori a PLL one, since PLL ⊆ PCLL: `nle_of_rnc`); two are the
five-world certificates of `wip/fiveWorld.lean`.  Note the mix: `q10`
is rung 6 of the ladder, `q8` and `q9` are off the image — the extra
width comes from the complement sitting BESIDE the ladder, not above
or below it.  Whether the width is bounded is OPEN.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## Density -/

/-- `¬X`, locally. -/
private def neg (X : PLLFormula) : PLLFormula := X.ifThen falsePLL

/-- The guard is dense: `⊢ ¬¬(◯⊥ ∨ ¬◯⊥)` — the IPC theorem `¬¬(A ∨ ¬A)`
at `A = ◯⊥`. -/
theorem dense_guard : Deriv [] (neg (neg guard)) := by
  refine Deriv.impIntro ?_
  -- [¬guard] ⊢ ⊥
  have dnotA : Deriv [neg guard] (neg oBot) := by
    refine Deriv.impIntro ?_
    -- [◯⊥, ¬guard] ⊢ ⊥
    exact Deriv.impElim (Deriv.iden (.tail _ (.head _)))
      (Deriv.orIntro1 (Deriv.iden (.head _)))
  exact Deriv.impElim (Deriv.iden (.head _)) (Deriv.orIntro2 dnotA)

/-- Density propagates up the order. -/
theorem dense_of_above_guard {φ : PLLFormula} (h : Deriv [guard] φ) :
    Deriv [] (neg (neg φ)) := by
  refine Deriv.impIntro ?_
  -- [¬φ] ⊢ ⊥
  have hng : Deriv [neg φ] (neg guard) := by
    refine Deriv.impIntro ?_
    -- [guard, ¬φ] ⊢ ⊥
    exact Deriv.impElim (Deriv.iden (.tail _ (.head _))) (wk1 _ h)
  exact Deriv.impElim (wkHead _ dense_guard) hng

/-! ## Dense seeds cannot embed the ladder -/

/-- Atoms confined to `p`. -/
def varsP : PLLFormula → Bool
  | .prop a => a == "p"
  | .falsePLL => true
  | .and X Y => varsP X && varsP Y
  | .or X Y => varsP X && varsP Y
  | .ifThen X Y => varsP X && varsP Y
  | .somehow X => varsP X

/-- `h_φ` embeds the free ONE-generated Heyting algebra: distinct
one-variable pure Heyting formulas stay non-interderivable under
`p ↦ φ`.  (As in `EmbedsOver`, the conclusion is PLL-interderivability,
weaker than the IPC-equivalence true injectivity concludes, so refuting
this refutes injectivity a fortiori.)  `h = h_{◯⊥}` has this property
on the rungs — that is `rn_pairwise_pll`. -/
def Embeds1 (φ : PLLFormula) : Prop :=
  ∀ X Y : PLLFormula, boxFree X = true → boxFree Y = true →
    varsP X = true → varsP Y = true →
    Interd (substP "p" φ X) (substP "p" φ Y) → Interd X Y

/-- `¬p ⊬⊢ ⊥`: one infallible world with `p` false. -/
theorem notP_not_bot : ¬ Interd (neg (prop "p")) falsePLL := fun h =>
  FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0)
    (by decide) h.1

/-- **Dense seeds fail**: if `⊢ ¬¬φ` then `h_φ` collapses `¬p` onto
`⊥`, so it does not embed the ladder. -/
theorem no_embeds1_of_dense {φ : PLLFormula}
    (hd : Deriv [] (neg (neg φ))) : ¬ Embeds1 φ := by
  intro hEmb
  refine notP_not_bot
    (hEmb (neg (prop "p")) falsePLL (by decide) (by decide) (by decide)
      (by decide) ?_)
  -- Interd (¬φ) ⊥ — the substitution computes to ¬φ and ⊥
  show Interd ((substP "p" φ (prop "p")).ifThen falsePLL) falsePLL
  have e : substP "p" φ (prop "p") = φ := by simp [substP]
  rw [e]
  exact ⟨Deriv.impElim (wkHead _ hd) (Deriv.iden (.head _)),
         Deriv.falsoElim _ (Deriv.iden (.head _))⟩

/-! ## The remaining three guard facts (q5, q9, q12 are in secondgen) -/

theorem guard_q8 : Deriv [guard] q8 :=
  guard_derives
    (Deriv.impIntro (Deriv.orIntro1 (Deriv.iden (.tail _ (.head _)))))
    (Deriv.impIntro (Deriv.orIntro2 (Deriv.iden (.tail _ (.head _)))))

theorem guard_q13 : Deriv [guard] q13 :=
  guard_derives (boxBot_below_box _)
    (dSomehowIntro
      (Deriv.impIntro (Deriv.orIntro2 (Deriv.iden (.tail _ (.head _))))))

theorem guard_q14 : Deriv [guard] q14 :=
  guard_derives
    (Deriv.impIntro (wkHead _ (boxBot_below_box _)))
    (Deriv.impIntro (wkHead _ (dSomehowIntro (Deriv.iden (.head _)))))

/-! ## No known off-image class seeds an embedding -/

theorem no_embeds1_q5  : ¬ Embeds1 q5 :=
  no_embeds1_of_dense (dense_of_above_guard guard_q5)
theorem no_embeds1_q8  : ¬ Embeds1 q8 :=
  no_embeds1_of_dense (dense_of_above_guard guard_q8)
theorem no_embeds1_q9  : ¬ Embeds1 q9 :=
  no_embeds1_of_dense (dense_of_above_guard guard_q9)
theorem no_embeds1_q12 : ¬ Embeds1 q12 :=
  no_embeds1_of_dense (dense_of_above_guard guard_q12)
theorem no_embeds1_q13 : ¬ Embeds1 q13 :=
  no_embeds1_of_dense (dense_of_above_guard guard_q13)
theorem no_embeds1_q14 : ¬ Embeds1 q14 :=
  no_embeds1_of_dense (dense_of_above_guard guard_q14)

/-! ## Width ≥ 3 -/

/-- A PCLL refutation is a fortiori a PLL refutation. -/
theorem nle_of_rnc {A B : PLLFormula} (h : ¬ ConfluentU.DerivU [A] B) :
    ¬ Deriv [A] B := fun ⟨p⟩ => h (ConfluentU.DerivU.of_nd p)

theorem nle_8_9  : ¬ Deriv [q8] q9  := nle_of_rnc RNC.rnc_ref_8_9
theorem nle_8_10 : ¬ Deriv [q8] q10 := nle_of_rnc RNC.rnc_ref_8_10
theorem nle_9_10 : ¬ Deriv [q9] q10 := nle_of_rnc RNC.rnc_ref_9_10
theorem nle_10_9 : ¬ Deriv [q10] q9 := nle_of_rnc RNC.rnc_ref_10_9

/-- **RN(◯,{}) has width at least 3**: `{q8, q9, q10}` is an antichain.
`q10` is rung 6 of the ladder; `q8` and `q9` are off the image. -/
theorem antichain_q8_q9_q10 :
    (¬ Deriv [q8] q9) ∧ (¬ Deriv [q9] q8) ∧
    (¬ Deriv [q8] q10) ∧ (¬ Deriv [q10] q8) ∧
    (¬ Deriv [q9] q10) ∧ (¬ Deriv [q10] q9) :=
  ⟨nle_8_9, five_q9_nle_q8, nle_8_10, five_q10_nle_q8, nle_9_10, nle_10_9⟩

end RNEmbed
end PLLND
