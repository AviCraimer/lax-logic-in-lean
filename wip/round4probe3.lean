import wip.ascRefute

/-!
# ROUND 4, Task 1(c) — the DISCRIMINATING screen for `Round4.BoxDesc`

`wip/round4Comp.lean` states the round's single obligation ROOM-FREE:

    BoxDesc :  E@(ft, b+1)(Γ)  ⟶  A@(fs, b+1)(Γ, ◯D)  ⟶  A@(ft, b)(Γ, ◯D)

The room was dropped because `seal2Free.gammaHead_budget_free` proves the
atomic instance with the target budget universally quantified.  There is one
obvious place where room-freeness could break at a **compound** body: open the
target's box and the obligation inside it looks like

    E@(ft, b+1)(Γ) ,  A@(fs−1, b+1)(Γ, D)  ⟹  A@(ft−1, b)(Γ, D)

— the ROOM-FREE descent at goal `D`, and `AscRefute.not_roomFreeDescent`
refutes exactly that at `D = gk = (◯r ⊃ s) ⊃ t` over `Sk`, in `Mk`, at budget
`1`.  If the `◯` in front of `gk` changed nothing, the same model would refute
`BoxDesc` at that instance and the round-4 architecture would have to carry
the room the three sites actually supply.

**It does not.**  Adding `◯gk` to `Sk` and asking the *same* model at the
*same* budget and fuels:

| instance | goal | `Mk` refutes? |
|---|---|---|
| `not_roomFreeDescent`'s own | `gk` | **YES** (`unboxed_refuted`) |
| the `◯`-goal form | `◯gk` | **NO** (`boxed_survives`) |
| the `◯`-goal form, other model | `◯gk` | **NO** (`boxed_survives_Mr`) |

So at the one configuration in the repository's inventory that is known to
break the room-free descent, the `◯` in front of the goal is load-bearing —
which is exactly PROGRESS §59(c)'s claim, now screened rather than asserted.

`checkB` is used directly: the models are fixed, so each verdict is a kernel
computation, not a search.
-/

open PLLFormula

namespace PLLND
namespace Round4Probe3

open PLLND.AscRefute

/-- `Sk` with the boxed goal body added.  `gk ∈ Sk` already, so `Skb` is still
`◯`-subformula-closed, and `Gk ⊆ Skb`. -/
def Skb : Finset PLLFormula := insert gk.somehow Sk

theorem skb_some_closed : gk ∈ Skb := by decide +kernel

theorem skb_cover : ∀ X ∈ Gk, X ∈ Skb := by decide +kernel

/-- The `◯`-goal descent at the refuting configuration: ambient and source at
budget `2`, target at budget `1` — the budget at which `not_roomFreeDescent`
certifies failure for the UNBOXED goal. -/
def ambB : PLLFormula := itpE "p" Skb 4 2 Gk
def srcB : PLLFormula := itpA "p" Skb 4 2 Gk gk.somehow
def tgtB : PLLFormula := itpA "p" Skb 4 1 Gk gk.somehow

/-- The unboxed control: `not_roomFreeDescent`'s own instance, re-run over
`Skb`. -/
def srcU : PLLFormula := itpA "p" Skb 4 2 Gk gk
def tgtU : PLLFormula := itpA "p" Skb 4 1 Gk gk

/-- **The control fires.**  `Mk` still refutes the room-free descent at the
unboxed goal over the enlarged space — the screen is live. -/
theorem unboxed_refuted :
    FinCM.checkB Mk 0 [srcU, ambB] tgtU = true := by decide +kernel

/-- **The `◯`-goal form survives the same screen.**  Same model, same world,
same budgets, same fuels, same context — only the `◯` added. -/
theorem boxed_survives :
    FinCM.checkB Mk 0 [srcB, ambB] tgtB = false := by decide +kernel

/-- …and survives the inventory's other model as well. -/
theorem boxed_survives_Mr :
    FinCM.checkB Mr 0 [srcB, ambB] tgtB = false := by decide +kernel

/-- **The contrast, in one statement.**  At one and the same instance the
unboxed descent is refuted and the `◯`-goal descent is not. -/
theorem box_is_load_bearing :
    FinCM.checkB Mk 0 [srcU, ambB] tgtU = true ∧
    FinCM.checkB Mk 0 [srcB, ambB] tgtB = false :=
  ⟨unboxed_refuted, boxed_survives⟩

/-- The unboxed instance is genuinely underivable (the control is not just a
model artefact). -/
theorem not_derivable_unboxed : ¬ G4c [srcU, ambB] tgtU := fun h =>
  FinCM.not_provable_of_check unboxed_refuted (G4c.equiv_nd.mp h)

end Round4Probe3
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Round4Probe3.box_is_load_bearing' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round4Probe3.box_is_load_bearing

/--
info: 'PLLND.Round4Probe3.not_derivable_unboxed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round4Probe3.not_derivable_unboxed
