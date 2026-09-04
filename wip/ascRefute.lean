import wip.cascadeBox
import LaxLogic.PLLSearchCmd
import LaxLogic.PLLSearchNoFall

/-!
# `AmbGuardAscent` is FALSE — the interface refuted, kernel-checked

`wip/cascadeBox.lean` reduces the `◯`-involving low-budget descent to four
interface propositions.  This file refutes the first of them.

`AmbGuardAscent p S` asserts the one-step *ascent* of the existential
quantifier table at a freshly grown context, financed by the ambient table
at the ungrown context:

    Δ ⊢ E@(c+1)(Γ)   ⟹   E@c(X::Γ), Δ ⊢ E@(c+1)(X::Γ)      (X ∈ S, X ∉ Γ)

It was abstracted out of the three paired-implication growth arms, where the
box-free clone had financed the same step from the room-funded existential
half of its mutual pair.  It is **false at the budget floor**: with

    S = {◯p ⊃ r, r, ◯r ⊃ s, s},  Γ = [◯p ⊃ r],  X = ◯r ⊃ s,  c = 1,

the instance fails in the two-world infallible model `0 ⊑ 1`, `0 ⊳ 1` with
`r`, `s` true exactly at world `1` — the Kripke form of the countermodel the
algebraic battery first exhibited (3-chain, nucleus `j(0) = 0`, `j(x) = 2`,
valuation `r = s = 1`).  The failure is stable in the fuel (identical at
fuels 3, 4, 5) and confined to the floor (no failure at budget ≥ 2), which is
the signature of the low-budget wall itself.

**Consequence.**  The three growth arms of `oth_descent` that consume this
interface need a different treatment; the ascent cannot be assumed at the
grown context in the form stated.  What survives untouched: `oth_descent` and
`cascade_box` as *conditional* theorems, and the other three interfaces
(`GammaPairFloorA`, `GammaPairFloorBox`, `JumpPairFloor`), which the battery
supports.  `cascade_box_unconditional` is now known to rest on a false
hypothesis and must not be quoted as evidence for the kernel.
-/

open PLLFormula

namespace PLLND
namespace AscRefute

/-- The refuting space: the chained configuration of the battery. -/
def Sr : Finset PLLFormula :=
  {((prop "p").somehow).ifThen (prop "r"), prop "r",
   ((prop "r").somehow).ifThen (prop "s"), prop "s"}

/-- The context. -/
def Gr : List PLLFormula := [((prop "p").somehow).ifThen (prop "r")]

/-- The fresh space piece. -/
def Xr : PLLFormula := ((prop "r").somehow).ifThen (prop "s")

/-- The ambient existential table at the ungrown context. -/
def ambr : PLLFormula := itpE "p" Sr 4 2 Gr

/-- The existential table at the grown context, budget `1`. -/
def lowr : PLLFormula := itpE "p" Sr 3 1 (Xr :: Gr)

/-- The existential table at the grown context, budget `2` — the ascent's
target. -/
def hir : PLLFormula := itpE "p" Sr 3 2 (Xr :: Gr)

/-- The refuting model: two worlds `0 ⊑ 1` with `0 ⊳ 1`, no fallible world,
`r` and `s` forced exactly at world `1`. -/
def Mr : FinCM := ⟨2, [(0, 1)], [(0, 1)], [], [(1, "r"), (1, "s")]⟩

/-- The ascent instance fails in `Mr` at world `0`. -/
theorem check_fails : FinCM.checkB Mr 0 [lowr, ambr] hir = true := by decide

/-- The ascent instance is underivable. -/
theorem not_derivable : ¬ G4c [lowr, ambr] hir := fun h =>
  FinCM.not_provable_of_check check_fails (G4c.equiv_nd.mp h)

/-- **`AmbGuardAscent` is false.**  Instantiate at `fl = 3`, `c = 1`, the
configuration above, with the ambient itself as the deriving context. -/
theorem not_ambGuardAscent : ¬ AmbGuardAscent "p" Sr := by
  intro h
  exact not_derivable
    (h 3 1 Gr Xr [ambr] (by decide) (by decide) (by decide)
      (G4c.identity_mem (List.mem_cons_self ..)))

/-! ## 2. The room-free descent itself is false

The build's target statement drops the room hypothesis
`defect S Γ * (|jumpGoals S| + 2) ≤ c` that the tower's kernel carries,
keeping only `1 ≤ c`.  That is too strong: the descent fails at budget `1`
whenever the goal's antecedent is a `⊃◯`-clause, because the antecedent
introduces a budget-gated conjunct at the grown context which the ambient at
the ungrown context cannot finance — the same mechanism as §1, now reaching
the descent itself.

The tower's kernel `cascade_low_pos_box` is **not** touched: with
`1 ≤ defect S Γ` its room hypothesis forces `2 ≤ defect · (|jumpGoals| + 2) ≤ c`,
so its budget-`1` instances are vacuous.  What is refuted is the room-free
reformulation. -/

/-- The space of the second refutation: piece-closed, with a goal whose
antecedent is the `⊃◯`-clause `◯r ⊃ s`. -/
def Sk : Finset PLLFormula :=
  {((prop "p").somehow).ifThen (prop "r"), (prop "p").somehow, prop "p",
   prop "r", (((prop "r").somehow).ifThen (prop "s")).ifThen (prop "t"),
   ((prop "r").somehow).ifThen (prop "s"), (prop "r").somehow, prop "s",
   prop "t"}

def Gk : List PLLFormula := [((prop "p").somehow).ifThen (prop "r")]

def gk : PLLFormula := (((prop "r").somehow).ifThen (prop "s")).ifThen (prop "t")

def ambk : PLLFormula := itpE "p" Sk 4 2 Gk
def srck : PLLFormula := itpA "p" Sk 4 2 Gk gk
def tgtk : PLLFormula := itpA "p" Sk 4 1 Gk gk

/-- The refuting model: two worlds `0 ⊑ 1`, `0 ⊳ 1`, infallible, with
`r`, `s`, `t` forced exactly at world `1`. -/
def Mk : FinCM := ⟨2, [(0, 1)], [(0, 1)], [], [(1, "r"), (1, "s"), (1, "t")]⟩

theorem check_fails_k : FinCM.checkB Mk 0 [srck, ambk] tgtk = true := by decide

/-- **The descent fails at budget 1 on this instance.** -/
theorem not_derivable_k : ¬ G4c [srck, ambk] tgtk := fun h =>
  FinCM.not_provable_of_check check_fails_k (G4c.equiv_nd.mp h)

/-- The room-free descent, as a proposition: the universally quantified
form of `cascade_box`'s conclusion, with `1 ≤ c` as the only budget
hypothesis. -/
def RoomFreeDescent (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (fuel c : Nat) (Γ : List PLLFormula) (g : PLLFormula)
    (Δ : List PLLFormula),
    1 ≤ c → G4c Δ (itpE p S fuel (c + 1) Γ) →
    G4c Δ (itpA p S fuel (c + 1) Γ g) →
    G4c Δ (itpA p S fuel c Γ g)

/-- **The room-free descent is false.**  Hence no proof of the four
interface propositions of `wip/cascadeBox.lean` can exist: `cascade_box`
derives exactly this conclusion from them, at an instance whose
piece-closure side conditions `Sk` satisfies. -/
theorem not_roomFreeDescent : ¬ RoomFreeDescent "p" Sk := by
  intro h
  exact not_derivable_k
    (h 4 1 Gk gk [srck, ambk] (Nat.le_refl _)
      (G4c.identity_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (G4c.identity_mem (List.mem_cons_self ..)))

/-! ## 3. Scope of the two refutations

A countermodel to a `G4c` sequent refutes **PLL**, and refutes PCLL only
if it is mutually confluent — a distinction worth recording rather than
leaving implicit, since a model that merely *happens* to be confluent
carries strictly more than a PLL-only one.  Both models here were built
by hand for the PLL statements (`G4c` is the calculus for plain PLL,
`equiv_nd`), and both turn out to be mutually confluent and infallible.

So neither refutation is PLL-only: `AmbGuardAscent` and the room-free
descent are false over the mutually confluent infallible models too, and
the failure survives adding the distribution scheme and `¬◯⊥`.  The
budget wall is not an artefact of fallible worlds or of the missing
distribution axiom. -/

theorem Mr_confluent : RNC.confB Mr = true := by decide
theorem Mr_infallible : NoFall.infB Mr = true := by decide
theorem Mk_confluent : RNC.confB Mk = true := by decide
theorem Mk_infallible : NoFall.infB Mk = true := by decide

end AscRefute
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.AscRefute.not_ambGuardAscent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.AscRefute.not_ambGuardAscent

/-- info: 'PLLND.AscRefute.not_roomFreeDescent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.AscRefute.not_roomFreeDescent
