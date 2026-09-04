import wip.boxTop
import wip.ladderdistr

/-!
# `cBox_11` settled: `◯q11` is a NEW class

The dictionary's open cell `cBox_11` offered three candidates for
`◯q11`: `⊤`, `q11`, `q13`.  All three are now refuted, so `◯q11` is a
class the 15-element dictionary does not contain — the certified
17th class of RN(◯,{}) (after `w15 = q8 ∧ q10`), and the first found
by applying `◯`.

* `⊤` — refuted by proof theory (`boxTop.cBox11_not_top`): `⊢ ◯A`
  forces `⊢ A` by empty-context inversion, and rung 7 is no theorem.

* `q11` — refuted here (`ref_boxq11_q11`) by a five-world
  countermodel that is NOT mutually confluent, which is why the
  confluent battery missed it: root `0`, a `¬◯⊥`-endpoint `1`, and a
  chain `2 < 3 < 4` with `4` fallible, `Rₘ : 0⇝1, 3⇝4`.  At the root
  `q6` fails through world 1 and `q10` fails through world 2, so
  `q11` fails; but every world `Rₘ`-reaches a `q11`-world, so `◯q11`
  holds.  With the unit `q11 ⊢ ◯q11` this makes the step STRICT:
  rung 7 sits strictly below its own box.

* `q13` — refuted both ways by five-world countermodels
  (`ref_boxq11_q13`, `ref_q13_boxq11`).

Placement (all certified below): `q9 < ◯q11` and `q12 < ◯q11`
strictly, `◯q11` incomparable with `q14`.  In particular the ◯-chain
over the odd rungs

    q5 = ◯rn3  <  q12 = ◯rn5  <  ◯rn7 = ◯q11

is strictly increasing for three terms, all off the guard-cone's
escape routes, and `boxTop.chain_never_top` says no later term can
collapse to `⊤`.

**Correction recorded.**  `wip/five.lean`'s battery keeps only
mutually confluent models (inherited from the PCLL probe), so its
"no five-world countermodel" verdicts covered the confluent part
only.  The `q11` refutation below is the first cell settled by
leaving that restriction.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-- The boxed rung 7. -/
def bq11 : PLLFormula := q11.somehow

/-- The unit half: `q11 ⊢ ◯q11`. -/
theorem d_q11_bq11 : Deriv [q11] bq11 :=
  dSomehowIntro (Deriv.iden (.head _))

/-- **`◯q11 ⊬ q11`** — the five-world NON-confluent countermodel.
Worlds: `0` root; `1` a `¬◯⊥`-endpoint; `2 < 3 < 4` with `4` fallible;
`Rₘ : 0⇝1, 3⇝4` (plus reflexive closure). -/
theorem ref_boxq11_q11 : ¬ Deriv [bq11] q11 :=
  FinCM.not_provable_of_check
    (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (2, 3), (2, 4), (3, 4)],
           [(0, 1), (3, 4)], [4], []⟩)
    (w := 0) (by decide)

/-- `◯q11 ⊬ q13`. -/
theorem ref_boxq11_q13 : ¬ Deriv [bq11] q13 :=
  FinCM.not_provable_of_check
    (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4),
               (2, 3), (4, 3)], [(1, 2), (4, 3)], [3], []⟩)
    (w := 0) (by decide)

/-- `q13 ⊬ ◯q11`. -/
theorem ref_q13_boxq11 : ¬ Deriv [q13] bq11 :=
  FinCM.not_provable_of_check
    (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)],
           [(2, 3)], [3], []⟩)
    (w := 0) (by decide)

/-- `◯q11 ⊬ q12`. -/
theorem ref_boxq11_q12 : ¬ Deriv [bq11] q12 :=
  FinCM.not_provable_of_check
    (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2)], [(1, 2)], [2], []⟩)
    (w := 0) (by decide)

/-- `◯q11 ⊬ q9`. -/
theorem ref_boxq11_q9 : ¬ Deriv [bq11] q9 :=
  FinCM.not_provable_of_check
    (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2)], [(1, 2)], [2], []⟩)
    (w := 0) (by decide)

/-- `◯q11 ⊬ q14`. -/
theorem ref_boxq11_q14 : ¬ Deriv [bq11] q14 :=
  FinCM.not_provable_of_check
    (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2)], [(1, 2)], [2], []⟩)
    (w := 0) (by decide)

/-- `q14 ⊬ ◯q11`. -/
theorem ref_q14_boxq11 : ¬ Deriv [q14] bq11 :=
  FinCM.not_provable_of_check
    (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)],
           [(2, 3)], [3], []⟩)
    (w := 0) (by decide)

/-- `q12 ⊢ ◯q11` (searcher-found, 24 nodes). -/
theorem d_q12_bq11 : Deriv [q12] bq11 :=
  ofG4 (.laxL (.head _) (.laxR (.orL (.head _) (.orR2 (.impR (.laxR (.impLImp (.head _) (.impR (.impLImp (.tail _ (.tail _ (.head _))) (.impLLaxLax (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))) (.botL (.head _)))) (.botL (.head _)))))) (.orR1 (.impR (.impLLaxLax (.head _) (.tail _ (.tail _ (.tail _ (.head _)))) (.impLImp (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))) (.botL (.head _))))))))

/-- `q9 ⊢ ◯q11` (searcher-found, 20 nodes). -/
theorem d_q9_bq11 : Deriv [q9] bq11 :=
  ofG4 (.laxR (.orL (.head _) (.orR2 (.impR (.laxL (.tail _ (.head _)) (.laxR (.impLImp (.tail _ (.head _)) (.impR (.impLLaxLax (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _))))))) (.orR1 (.impR (.impLImp (.tail _ (.head _)) (.impR (.impLLaxLax (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))))

/-- **`cBox_11` settled**: `◯q11` is none of its three candidates —
not `⊤`, not `q11` (strictly above it), not `q13`. -/
theorem cBox11_settled :
    (¬ Interd bq11 q1) ∧
    (Deriv [q11] bq11 ∧ ¬ Deriv [bq11] q11) ∧
    (¬ Deriv [bq11] q13 ∧ ¬ Deriv [q13] bq11) :=
  ⟨cBox11_not_top, ⟨d_q11_bq11, ref_boxq11_q11⟩,
   ⟨ref_boxq11_q13, ref_q13_boxq11⟩⟩

/-- Bonus from the same non-confluent battery: `q12 ⊬ q11`, closing one
of the two remaining open cells of the dictionary order.  Only
`q14 ⊢ q13` now remains. -/
theorem ref_q12_q11 : ¬ Deriv [q12] q11 :=
  FinCM.not_provable_of_check
    (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)],
           [(0, 4), (2, 3)], [3], []⟩)
    (w := 0) (by decide)

/-- **The ◯-chain is strictly increasing for three terms**:
`q5 < q12 < ◯q11`, with `q5 = ◯rn3`, `q12 = ◯rn5`, `◯q11 = ◯rn7`. -/
theorem chain_three_strict :
    (Deriv [q5] q12 ∧ ¬ Deriv [q12] q5) ∧
    (Deriv [q12] bq11 ∧ ¬ Deriv [bq11] q12) :=
  ⟨⟨dSomehowElim (Deriv.iden (.head _))
      (dSomehowIntro (Deriv.orIntro1 (Deriv.iden (.head _)))),
    -- were q12 ⊢ q5, then q12 ⊢ q5 ∨ q6 = q9, against ladderdistr
    fun h => q12_not_derives_q9
      (Deriv.cutHead h (Deriv.orIntro1 (Deriv.iden (.head _))))⟩,
   ⟨d_q12_bq11, ref_boxq11_q12⟩⟩

end RNEmbed
end PLLND
