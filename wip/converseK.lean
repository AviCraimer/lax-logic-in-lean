import LaxLogic.PLLCountermodelEmit

/-!
# The converse of K fails in PLL — two pinned countermodels

PLL is a normal modal logic: `◯(A ⊃ B) ⊢ ◯A ⊃ ◯B` (K) is derivable.
The **converse** is not:

> `◯A ⊃ ◯B ⊬ ◯(A ⊃ B)`.

Matthew asked for this on 2026-08-07, having produced the intuitionistic
countermodel by hand (two worlds `0 < 1`, `A` true only at `1`) and asked
whether it lifts to a constraint model.  It does, in two ways, and both
are checked here by `FinCM.not_provable_of_check` — the certificate
theorem of `LaxLogic/PLLCountermodelEmit.lean`, so these are kernel-level
refutations, not `#eval` evidence.

`FinCM` fields: `⟨worlds, Rᵢ-edges, Rₘ-edges, fallible worlds, valuation⟩`,
both relations closed reflexively and transitively by the checker.

* `Minf` — three worlds `0 ≤ 1 ≤ 2`, `Rₘ = {(1,2)}`, **no** fallible
  worlds, `A` true at `1, 2` and `B` true at `2`.
* `Mfal` — the same frame with world `2` **fallible** instead: it then
  forces `A`, `B` and `⊥` for free.  This is the shape that makes the
  model an instance of the F&M `PLL_C` character (their Lemma 5.3), and
  it is why fallible worlds are not a technicality.

In both, world `0` forces `◯A ⊃ ◯B` (hereditarily: `◯A` first becomes
true at `1`, and there `◯B` is true too) while `A ⊃ B` fails at `1`, so
`0 ⊮ ◯(A ⊃ B)` — the `∀∃` clause has nowhere to send world `0`.

Note also that `Minf` is **linear** (`Rᵢ` is a chain).  So linearity does
*not* force the converse of K — the point Matthew made against my
conjecture the same day.
-/

open PLLFormula PLLND

namespace ConverseK

def A : PLLFormula := prop "A"
def B : PLLFormula := prop "B"

/-- The converse-K sequent: `◯A ⊃ ◯B ⊢ ◯(A ⊃ B)`. -/
def Γck : List PLLFormula := [(A.somehow).ifThen (B.somehow)]
def Cck : PLLFormula := (A.ifThen B).somehow

/-- Infallible, linear, three worlds. -/
def Minf : FinCM := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [], [(1,"A"),(2,"A"),(2,"B")]⟩

/-- The same frame with world 2 fallible. -/
def Mfal : FinCM := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [2], [(1,"A")]⟩

theorem converseK_fails_infallible : ¬ Nonempty (LaxND Γck Cck) :=
  FinCM.not_provable_of_check (M := Minf) (w := 0) (by decide)

theorem converseK_fails_fallible : ¬ Nonempty (LaxND Γck Cck) :=
  FinCM.not_provable_of_check (M := Mfal) (w := 0) (by decide)

-- K itself is NOT refuted by either model (the checker finds no countermodel).
-- Both must be `false`; a `true` here would contradict `PLLNDCore`'s `ndK`.
/-- info: false -/
#guard_msgs in #eval FinCM.checkB Minf 0 [Cck] ((A.somehow).ifThen (B.somehow))
/-- info: false -/
#guard_msgs in #eval FinCM.checkB Mfal 0 [Cck] ((A.somehow).ifThen (B.somehow))

/-- info: 'ConverseK.converseK_fails_infallible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms converseK_fails_infallible

/-- info: 'ConverseK.converseK_fails_fallible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms converseK_fails_fallible

end ConverseK
