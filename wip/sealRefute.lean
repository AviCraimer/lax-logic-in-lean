import wip.envDesc
import LaxLogic.PLLSearchCmd
import LaxLogic.PLLSearchNoFall

/-!
# No uniform route closes the boxed γ-branch at the floor

`wip/envDesc.lean` closes the boxed γ first component at every target budget
`≥ 2`, leaving one branch at target budget `1`.  There the target table offers
exactly three kinds of disjunct, and the branch's third hypothesis
`A@1(B::Γ, C)` is already the second conjunct of two of them, so the branch
closes iff one of

    (a)  A@0(Γ, A)                      -- the plain γ-disjunct's first component
    (b)  ◯( E@0(Γ) ⇢ A@0(Γ, ◯A) )       -- the boxed one
    (c)  the goal clause of `C`

is derivable from

    E@2(Γ) ,   ◯( E@1(Γ) ⇢ A@1(Γ, ◯A) ) ,   A@1(B::Γ, C).

This file refutes **(a) and (b), and the strengthening of (b) to `◯⊥`**, at one
configuration, kernel-checked.  Since (c) is `⊢ z` and fails in any model where
`z` is false, no single one of the three routes is available in general:

> **the branch cannot be closed by a uniform route; it requires a case
> analysis over the target's disjuncts.**

That is why the mechanisms surveyed in `wip/absorb_base.lean`'s residue
analysis all failed — each of them is a *uniform* route.  It also explains why
no countermodel to the branch obligation itself has been found: in each of the
three refuting models a *different* route succeeds.

## The configuration

    S = {◯r ⊃ s, ◯r, r, s, p, z}       (piece-closed)
    Γ = [◯r ⊃ s],   A = r,   B = s,   C = z

The γ-head is `r`, an ordinary atom — **not** the eliminated variable `p`.
That matters: with a `p`-headed γ-clause the plain component `A@0(Γ,p)` is
starved (`= ⊥`) and the boxed one collapses to `◯⊥`, which is derivable on the
chain families of `wip/budgetfit.lean`.  With an ordinary head neither happens:
here `A@0(Γ,r) = r ∨ ⊥`, which is satisfiable but not derivable.

All three refuting models are **infallible and mutually confluent**, so the
refutations hold over PCLL, PILL and PICLL as well as plain PLL.
-/

open PLLFormula

namespace PLLND
namespace SealRefute

/-- `◯a ⊃ b`. -/
def gam (a b : String) : PLLFormula := ((prop a).somehow).ifThen (prop b)

/-- The piece-closed space, with an ordinary-atom γ-head. -/
def Sq : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s", prop "p", prop "z" }

def Gq : List PLLFormula := [gam "r" "s"]

/-! ### The three hypotheses of the branch -/

/-- The ambient, at budget `2`. -/
def ambq : PLLFormula := itpE "p" Sq 6 2 Gq

/-- The source's boxed first component, at budget `1`. -/
def boxq : PLLFormula :=
  ((itpE "p" Sq 5 1 Gq).ifThen (itpA "p" Sq 5 1 Gq (prop "r").somehow)).somehow

/-- The source's second component, at the grown context — what the defect tier
supplies. -/
def sndq : PLLFormula := itpA "p" Sq 5 1 (prop "s" :: Gq) (prop "z")

def hypsq : List PLLFormula := [ambq, boxq, sndq]

/-! ### Route (a): the plain γ-disjunct's first component -/

/-- Two worlds `0 ⊑ 1`, `0 ⊳ 1`, infallible, with `r` forced at `1` only and
`s`, `z` everywhere. -/
def Ma : FinCM :=
  ⟨2, [(0, 1)], [(0, 1)], [],
   [(1, "r"), (0, "s"), (1, "s"), (0, "z"), (1, "z")]⟩

theorem check_a : FinCM.checkB Ma 0 hypsq (itpA "p" Sq 5 0 Gq (prop "r")) = true := by
  decide

/-- **Route (a) is refuted.**  The plain component `A@0(Γ,r) = r ∨ ⊥` is not
derivable from the branch's hypotheses: `r` fails at the root. -/
theorem not_route_a : ¬ G4c hypsq (itpA "p" Sq 5 0 Gq (prop "r")) := fun h =>
  FinCM.not_provable_of_check check_a (G4c.equiv_nd.mp h)

theorem Ma_infallible : NoFall.infB Ma = true := by decide
theorem Ma_confluent : RNC.confB Ma = true := by decide

/-! ### Routes (b) and (b'): the boxed component, and `◯⊥` -/

/-- One reflexive world, infallible, everything forced. -/
def Mb : FinCM := ⟨1, [], [], [], [(0, "r"), (0, "s"), (0, "z")]⟩

theorem check_b : FinCM.checkB Mb 0 hypsq falsePLL.somehow = true := by decide

/-- **The `◯⊥` strengthening of route (b) is refuted.**  So the collapse that
closes the chain families of `wip/budgetfit.lean` — where the γ-head is the
eliminated variable — is unavailable here. -/
theorem not_route_bot : ¬ G4c hypsq falsePLL.somehow := fun h =>
  FinCM.not_provable_of_check check_b (G4c.equiv_nd.mp h)

theorem check_b' :
    FinCM.checkB Mb 0 hypsq
      (((itpE "p" Sq 5 0 Gq).ifThen
        (itpA "p" Sq 5 0 Gq (prop "r").somehow)).somehow) = true := by
  decide

/-- **Route (b) is refuted.**  The matching target component itself is not
derivable from the branch's hypotheses. -/
theorem not_route_b :
    ¬ G4c hypsq (((itpE "p" Sq 5 0 Gq).ifThen
      (itpA "p" Sq 5 0 Gq (prop "r").somehow)).somehow) := fun h =>
  FinCM.not_provable_of_check check_b' (G4c.equiv_nd.mp h)

theorem Mb_infallible : NoFall.infB Mb = true := by decide
theorem Mb_confluent : RNC.confB Mb = true := by decide

/-! ### The consequence

Each of the three routes is a `Prop` about *all* configurations; each is now
refuted at one.  Stated as the non-existence of a uniform route: -/

/-- Route (a) as a uniform claim: the plain component is always available. -/
def UniformRouteA (p : String) : Prop :=
  ∀ (S : Finset PLLFormula) (F fl : Nat) (Γ : List PLLFormula)
    (A B C : PLLFormula),
    G4c [itpE p S (fl + 1) 2 Γ,
         ((itpE p S F 1 Γ).ifThen (itpA p S F 1 Γ A.somehow)).somehow,
         itpA p S F 1 (B :: Γ) C]
      (itpA p S fl 0 Γ A)

/-- Route (b) as a uniform claim: the boxed component is always available. -/
def UniformRouteB (p : String) : Prop :=
  ∀ (S : Finset PLLFormula) (F fl : Nat) (Γ : List PLLFormula)
    (A B C : PLLFormula),
    G4c [itpE p S (fl + 1) 2 Γ,
         ((itpE p S F 1 Γ).ifThen (itpA p S F 1 Γ A.somehow)).somehow,
         itpA p S F 1 (B :: Γ) C]
      (((itpE p S fl 0 Γ).ifThen (itpA p S fl 0 Γ A.somehow)).somehow)

theorem not_uniformRouteA : ¬ UniformRouteA "p" := fun h =>
  not_route_a (h Sq 5 5 Gq (prop "r") (prop "s") (prop "z"))

theorem not_uniformRouteB : ¬ UniformRouteB "p" := fun h =>
  not_route_b (h Sq 5 5 Gq (prop "r") (prop "s") (prop "z"))

end SealRefute
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.SealRefute.not_uniformRouteA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.SealRefute.not_uniformRouteA

/-- info: 'PLLND.SealRefute.not_uniformRouteB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.SealRefute.not_uniformRouteB

/-- info: 'PLLND.SealRefute.not_route_bot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.SealRefute.not_route_bot
