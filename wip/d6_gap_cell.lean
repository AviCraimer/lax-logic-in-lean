import LaxLogic.PLLSearch

/-!
# The last v2quant cell decided: D₆ ⊬ ◯(◯q⊃q)

The single undecided cell of the cross-route experiment (PROGRESS.md §35,
wip/v2quant_out3.txt): with

    D₆ := ◯¬◯⊥ ⊃ (◯⊥ ∨ ¬◯⊥)      (dictionary class crank≤6),

is `D₆ ⊢ ◯(◯q⊃q)` derivable in plain LaxND?  Verdict: **UNDERIVABLE**,
countermodel-certified below in two shapes, both 3-chains `0 ≤ 1 ≤ 2`
with the rigid first constraint step `Rₘ = {(1,2)}` and `q` true at `{2}`:

* `M6` — fallible top (this is `Search.defaultFrames` item 6 decorated
  with `q@{2}`: the battery refuted this cell all along);
* `M3` — fallible-free (the chain3F shape: fallibility is not needed).

Why they work (hand check, matching `FinCM.forceB`):

* `◯(◯q⊃q)` fails at 0: world 0's only `Rₘ`-successor is 0 itself, and
  `◯q⊃q` fails at 0 because the extension 1 forces `◯q` (its every
  extension `Rₘ`-reaches 2, where q holds) but not `q`.
* `D₆` holds at 0:
  - in `M3` (no fallible worlds) `◯⊥` is false everywhere, so `¬◯⊥` and
    with it the consequent `◯⊥ ∨ ¬◯⊥` hold everywhere — every
    fallible-free model forces D₆ at every world;
  - in `M6`, at worlds 1 and 2 the consequent holds via `◯⊥`
    (respectively fallibility), and at 0 the antecedent `◯¬◯⊥` fails:
    0's only `Rₘ`-successor is 0, and `¬◯⊥` fails at 0 via extension 1,
    which forces `◯⊥` through the fallible top.

Consequence for the experiment: D₆ does NOT enter the gap-row ∀-join at
r=6; the rank-bounded `∀p.◯(◯p⊃p)` stays at its stabilised value ◯⊥
(all 15 dictionary classes now certificate-decided on the ∀-side, ranks
0–9).
-/

open PLLFormula
namespace PLLND
namespace D6Cell

def bb : PLLFormula := falsePLL.somehow                 -- ◯⊥
def nbb : PLLFormula := bb.ifThen falsePLL              -- ¬◯⊥
def D6 : PLLFormula := (nbb.somehow).ifThen (bb.or nbb) -- ◯¬◯⊥ ⊃ (◯⊥ ∨ ¬◯⊥)

def oq : PLLFormula := .prop "q"
def phiQ : PLLFormula := (oq.somehow.ifThen oq).somehow -- ◯(◯q⊃q)
def op : PLLFormula := .prop "p"
def phiP : PLLFormula := (op.somehow.ifThen op).somehow -- ◯(◯p⊃p)

/-- Fallible-top countermodel: `defaultFrames` item 6 with q@{2}. -/
def M6 : FinCM := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [2], [(2,"q")]⟩
/-- Fallible-free countermodel: the chain3F shape with q@{2}. -/
def M3 : FinCM := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [], [(2,"q")]⟩
/-- The same two models over the harness atom `p`. -/
def M6p : FinCM := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [2], [(2,"p")]⟩
def M3p : FinCM := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [], [(2,"p")]⟩

/-- **The verdict**: `◯¬◯⊥ ⊃ (◯⊥ ∨ ¬◯⊥) ⊬ ◯(◯q⊃q)` in plain LaxND. -/
theorem D6_gap_underivable : ¬ Nonempty (LaxND [D6] phiQ) :=
  FinCM.not_provable_of_check (M := M6) (w := 0) (by decide)

/-- The same, by the fallible-free countermodel. -/
theorem D6_gap_underivable_ffree : ¬ Nonempty (LaxND [D6] phiQ) :=
  FinCM.not_provable_of_check (M := M3) (w := 0) (by decide)

/-- The harness cell (3,8) ∀-side as literally scanned (atom `p`). -/
theorem D6_gap_underivable_p : ¬ Nonempty (LaxND [D6] phiP) :=
  FinCM.not_provable_of_check (M := M6p) (w := 0) (by decide)

/-- And its fallible-free twin. -/
theorem D6_gap_underivable_p_ffree : ¬ Nonempty (LaxND [D6] phiP) :=
  FinCM.not_provable_of_check (M := M3p) (w := 0) (by decide)

#print axioms D6_gap_underivable
#print axioms D6_gap_underivable_ffree
#print axioms D6_gap_underivable_p
#print axioms D6_gap_underivable_p_ffree

/-! ## Bonus: one of the gap row's three ∃-side skips closes too

`◯(◯p⊃p) ⊢ (◯¬◯⊥) ∨ ¬¬◯⊥` (the crank≤5 ∃-side skip) is refuted by
`defaultFrames` item 8 — the 4-world fork `0 ≤ 1`, `0 ≤ 2 ≤ 3`,
`Rₘ = {(2,3)}`, fallible `{3}` — decorated `p@{2,3}`, at world 0.
The other two ∃-side skips, `◯(◯p⊃p) ⊢ D₆` and `◯(◯p⊃p) ⊢ ◯D₆`,
stay OPEN: no battery frame refutes them (sweep: none), and they are
the calls whose bounded positive search grinds. -/

def nnbb : PLLFormula := nbb.ifThen falsePLL            -- ¬¬◯⊥
def dOr : PLLFormula := (nbb.somehow).or nnbb           -- (◯¬◯⊥) ∨ ¬¬◯⊥

def Mfork : FinCM := ⟨4, [(0,1),(0,2),(2,3),(0,3)], [(2,3)], [3],
                      [(2,"p"),(3,"p")]⟩

/-- The crank≤5 ∃-side skip of the gap row: REFUTED. -/
theorem gap_row_exists_dOr_underivable : ¬ Nonempty (LaxND [phiP] dOr) :=
  FinCM.not_provable_of_check (M := Mfork) (w := 0) (by decide)

#print axioms gap_row_exists_dOr_underivable

end D6Cell
end PLLND
