import wip.envDesc

/-!
# The boxed floor branch, closed by hand where the searcher could not

`wip/sealprobe12.lean` leaves every boxed-goal cell `~` even at `findBudget`
2 000 000.  That is not evidence of underivability (PROGRESS §96), and a hand
computation on the smallest configuration says the branch should close — by a
route the searcher is badly placed to find, because it needs a *specific*
conjunct projected out of a weight-490 conjunction and then fired.

The configuration (as in `wip/sealRefute.lean`, γ-head an ordinary atom):

    S = {◯r ⊃ s, ◯r, r, s, z},   Γ = [◯r ⊃ s],   A = r,   B = s,   C = ◯s

## The route

The ambient `E@2(Γ)` is a conjunction, and one of its conjuncts is exactly

    ◯( E@1(Γ) ⇢ A@1(Γ,◯r) )  ⇢  E@2(s::Γ)

whose antecedent is the branch's **own** boxed component.  Fire it, and the
grown existential table `E@2(s::Γ)` follows; its atom conjuncts include `s`,
because `s` is now *in* the context.  From `s` the target's goal clause
`◯( E@0(Γ) ⇢ A@1(Γ,s) )` follows by `laxR`, `impR` and injecting `s` as the goal
clause of the atom `s` inside `A@1(Γ,s)`.

So the branch closes using **only the ambient and the boxed component** — the
second component is not needed at all, and no descent, ascent or case analysis
appears.  What made this invisible is that the decisive step is a projection out
of the ambient: the ambient's γ-conjunct has the branch's own hypothesis as its
antecedent.
-/

open PLLFormula

namespace PLLND
namespace BoxedS1b

open GoalDesc

def gam (a b : String) : PLLFormula := ((prop a).somehow).ifThen (prop b)

def S1 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s", prop "z" }

def G1 : List PLLFormula := [gam "r" "s"]

/-- The ambient at budget `2`. -/
def amb : PLLFormula := itpE "p" S1 4 2 G1

/-- The source's boxed first component. -/
def box : PLLFormula :=
  ((itpE "p" S1 3 1 G1).ifThen (itpA "p" S1 3 1 G1 (prop "r").somehow)).somehow

/-- The grown existential table the ambient's γ-conjunct yields. -/
def grownE : PLLFormula := itpE "p" S1 3 2 (prop "s" :: G1)

/-- Project a conjunct out of a derivable `andAll`. -/
theorem projAll {Δ l : List PLLFormula} {φ : PLLFormula}
    (d : G4c Δ (andAll l)) (h : φ ∈ l) : G4c Δ φ :=
  G4c.cut d (G4c.andAll_elim h (G4c.identity_mem (.head _)))

/-- The ambient's γ-conjunct: its antecedent is the branch's own boxed
component. -/
theorem amb_gamma_conjunct :
    (box.ifThen grownE) ∈ itpEcls "p" S1 3 2 G1 := by decide

/-- The grown table's atom conjunct for `s`. -/
theorem grownE_has_s : (prop "s") ∈ itpEcls "p" S1 2 2 (prop "s" :: G1) := by
  decide

/-- **`s` follows from the ambient and the boxed component.** -/
theorem s_of_amb_box : G4c [amb, box] (prop "s") := by
  have hamb : G4c [amb, box] (andAll (itpEcls "p" S1 3 2 G1)) :=
    G4c.identity_mem (.head _)
  have hfire : G4c [amb, box] grownE :=
    fire (projAll hamb amb_gamma_conjunct) (G4c.identity_mem (.tail _ (.head _)))
  have hgrown : G4c [amb, box] (andAll (itpEcls "p" S1 2 2 (prop "s" :: G1))) :=
    hfire
  exact projAll hgrown grownE_has_s

/-- The target's goal clause for the boxed goal `◯s`. -/
def goalClauseBox : PLLFormula :=
  ((itpE "p" S1 3 0 G1).ifThen (itpA "p" S1 3 1 G1 (prop "s"))).somehow

theorem goalClauseBox_mem :
    goalClauseBox ∈ itpAoth "p" S1 3 1 G1 ((prop "s").somehow) := by decide

/-- `s` is the goal clause of the atom `s` inside `A@1(Γ,s)`. -/
theorem s_mem_inner :
    (prop "s") ∈ itpAoth "p" S1 2 1 G1 (prop "s") := by decide

/-- **The boxed floor branch, closed at this configuration** — using only the
ambient and the boxed component. -/
theorem boxed_branch_b :
    G4c [amb, box] (orAll (itpAoth "p" S1 3 1 G1 ((prop "s").somehow))) := by
  refine G4c.orAll_intro goalClauseBox_mem ?_
  refine G4c.laxR (G4c.impR ?_)
  rw [itpA_succ]
  refine G4c.orAll_intro (φ := prop "s") ?_ ?_
  · simp only [itpAfull]
    exact s_mem_inner
  · exact wksub (fun ψ h => .tail _ h) s_of_amb_box

end BoxedS1b
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.BoxedS1b.s_of_amb_box' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxedS1b.s_of_amb_box

/--
info: 'PLLND.BoxedS1b.boxed_branch_b' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxedS1b.boxed_branch_b
