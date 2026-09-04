import wip.boxedS1b
import LaxLogic.PLLSearchPin

/-!
# The boxed floor branch at the goal the descent actually reaches

§99 records that §97 closed the boxed branch at `C = ◯B`, which is *not* a jump
goal, so it was off the recursion's path.  This file closes it at `C = ◯A` — the
actual boxed jump goal of the space — and the proof is a composition of two things
the session already has.

## The route

At `C = ◯r` the target table has three disjuncts.  Two are **refuted**
(`wip/sealprobe13.lean`), so the goal clause `◯(E@0(Γ) ⇢ A@1(Γ,r))` is the only
candidate.  And:

* with `prop s` in hand, `[snd, s] ⊢ ⋁ itpAoth …` is **PROVED in 36 nodes**;
* **without** it, `[snd] ⊢ ⋁ itpAoth …` is **REFUTED**.

So `prop s` is exactly the missing ingredient — and `prop s` is derivable from the
ambient and the boxed component alone, which is §98's discovery specialised here:
`BoxedS1b.s_of_amb_box`.

Semantically the route is: `snd = A@1(s::Γ,◯r)` yields, under `◯`, the implication
`E@0(s::Γ) ⇢ A@1(s::Γ,r)`; its antecedent contains the atom `s`, which the grown
ambient supplies; so `A@1(s::Γ,r)` — which is `r` — follows at the `⊳`-successor,
and that is the target's goal clause.

## Note on the search

`[amb, box, snd, s] ⊢ target` is *not* found by the searcher even at 200 000 nodes,
while `[snd, s] ⊢ target` is found in 36.  Adding derivable hypotheses widens the
search without changing derivability — which is why the proof here is assembled
from two small pieces rather than looked for whole.
-/

open PLLFormula PLLND

namespace PLLND
namespace BoxedOnPath

abbrev S1 : Finset PLLFormula := BoxedS1b.S1
abbrev G1 : List PLLFormula := BoxedS1b.G1
abbrev amb : PLLFormula := BoxedS1b.amb
abbrev box : PLLFormula := BoxedS1b.box

/-- The source's second component at the boxed **jump** goal `◯r`. -/
def snd : PLLFormula := itpA "p" S1 4 1 (prop "s" :: G1) ((prop "r").somehow)

/-- The target table at the boxed jump goal. -/
def goal : PLLFormula := orAll (itpAoth "p" S1 3 1 G1 ((prop "r").somehow))

/-- The on-path boxed floor branch, given `s`, pinned by `#pinsrc` (36 nodes). -/
theorem boxed_onpath_given_s :
    G4c [prop "s", snd] goal :=
  (((.orR1 (.orL (.tail _ (.head _)) (.laxL (.head _) (.laxR (.impR (.orR1 (.impLAnd (.tail _ (.head _)) (.impLProp (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.init (.head _)) (.botL (.head _)))))))))) (.orL (.head _) (.laxL (.head _) (.impLAnd (.head _) (.impLProp (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.laxL (.head _) (.laxR (.impR (.orR1 (.impLAnd (.tail _ (.head _)) (.impLProp (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.init (.head _)) (.botL (.head _)))))))))) (.botL (.head _))))))) (.botL (.head _)))))) :
    G4cTm [prop "s", snd] goal).toG4c


/-- **The boxed floor branch at the on-path goal `◯A`, closed.**  Composes
`BoxedS1b.s_of_amb_box` (which is §98's `grownAmb_of_box` plus an atom projection)
with the pinned derivation above. -/
theorem boxed_onpath : G4c [amb, box, snd] goal := by
  refine G4c.cut (A := prop "s") ?_ ?_
  · exact wksub (fun ψ h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact .head _
      · rcases List.mem_singleton.mp h with rfl
        exact .tail _ (.head _)) BoxedS1b.s_of_amb_box
  · exact wksub (fun ψ h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact .head _
      · rcases List.mem_singleton.mp h with rfl
        exact .tail _ (.tail _ (.tail _ (.head _)))) boxed_onpath_given_s

end BoxedOnPath
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.BoxedOnPath.boxed_onpath' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxedOnPath.boxed_onpath
