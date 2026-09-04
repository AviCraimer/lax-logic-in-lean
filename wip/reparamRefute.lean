import absorb_base
import wip.ascRefute

/-!
# The room-free re-parameterisation of the kernel is FALSE

PROGRESS §58.  Round 2 of the assault on `cascade_low_pos_box`
(`wip/absorb_base.lean`) re-parameterised that holdout: the old `hbox`
disjunction over an ARBITRARY space is replaced by piece-closure
(`hand`/`hor`/`himp`/`hsome`) and coverage (`g ∈ S`, `Γ ⊆ S`), which is what
the ◯-band apparatus of PROGRESS §57 needs.

The tempting further step is to make the holdout **verbatim**
`PLLND.cascade_box` (`wip/cascadeBox.lean`:1532), i.e. to drop the room
hypotheses `1 ≤ defect S Γ` and `defect S Γ · (|jumpGoals S| + 2) ≤ c`
and keep only `1 ≤ c`.  **That statement is false.**

`wip/ascRefute.lean` already refutes the room-free descent
(`AscRefute.not_roomFreeDescent`, axioms `[propext, Quot.sound]`), but it
states it in a *bare* form, with no closure or coverage side conditions at
all — leaving open whether closure and coverage might have excluded the
counterexample.  This file settles that: they do not.

§1 checks by `decide` that `AscRefute.Sk` satisfies every closure and
coverage side condition the re-parameterised kernel carries.  §2 states the
kernel in `wip/absorb_base.lean`'s own idiom (inner head fuel `fh`, the two
premises, `fh ≤ fuel`) with closure and coverage but *without* the room, and
refutes it.  §3 exhibits the room quantities at the counterexample, showing
exactly which hypothesis does the excluding.

**Consequence for the route.**  `cascade_box` derives the room-free
conclusion from its four open interfaces at a space satisfying its side
conditions; the conclusion is false there; so the four interfaces
(`AmbGuardAscent`, `GammaPairFloorA`, `GammaPairFloorBox`, `JumpPairFloor`)
are **jointly unsatisfiable** at `Sk`.  One of them is already known false
outright (`AscRefute.not_ambGuardAscent`).  Hence no repair of
`oth_descent`'s ascent sites — however clever — can yield the room-free
descent: the room hypothesis has to enter the ◯-band build, and the §57
apparatus has to be re-run carrying it.
-/

open PLLFormula

namespace PLLND
namespace ReparamRefute

open AscRefute

/-! ## §1  `Sk` is piece-closed and covers the counterexample's `Γ` and `g` -/

/-- `∧`-closure of `Sk` (vacuous: `Sk` has no conjunction). -/
theorem sk_and : ∀ {A B : PLLFormula}, A.and B ∈ Sk → A ∈ Sk ∧ B ∈ Sk := by
  intro A B h
  simp only [Sk, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h | h | h | h | h <;> cases h

/-- `∨`-closure of `Sk` (vacuous: `Sk` has no disjunction). -/
theorem sk_or : ∀ {A B : PLLFormula}, A.or B ∈ Sk → A ∈ Sk ∧ B ∈ Sk := by
  intro A B h
  simp only [Sk, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h | h | h | h | h <;> cases h

/-- `⊃`-closure of `Sk`: both pieces of every implication of `Sk` are in `Sk`. -/
theorem sk_imp : ∀ {A B : PLLFormula}, A.ifThen B ∈ Sk → A ∈ Sk ∧ B ∈ Sk := by
  intro A B h
  simp only [Sk, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h | h | h | h | h <;> cases h <;>
    refine ⟨?_, ?_⟩ <;> simp [Sk]

/-- `◯`-closure of `Sk`: the body of every box of `Sk` is in `Sk`. -/
theorem sk_some : ∀ {A : PLLFormula}, A.somehow ∈ Sk → A ∈ Sk := by
  intro A h
  simp only [Sk, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h | h | h | h | h <;> cases h <;> simp [Sk]

/-- The counterexample's context is inside `Sk`. -/
theorem sk_cover : ∀ X ∈ Gk, X ∈ Sk := by decide +kernel

/-- The counterexample's goal is inside `Sk`. -/
theorem sk_goal : gk ∈ Sk := by decide +kernel

/-! ## §2  The room-free re-parameterised kernel, refuted

`ReparamKernelRoomFree p S` is `wip/absorb_base.lean`'s `cascade_low_pos_box`
as the first draft of the re-parameterisation stated it: closure and coverage
in, room out.  The closure hypotheses are *arguments* of the proposition, so
that the refutation below is a refutation of the whole implication, not of a
weaker bare form. -/

/-- The room-free re-parameterisation of the kernel, in `absorb_base`'s
idiom. -/
def ReparamKernelRoomFree (p : String) (S : Finset PLLFormula) : Prop :=
  (∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S) →
  (∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S) →
  (∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S) →
  (∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S) →
  ∀ (fh : Nat) (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula)
    (Δ : List PLLFormula),
    g ∈ S → (∀ X ∈ Γ, X ∈ S) → 1 ≤ c →
    G4c Δ (itpE p S fuel (c + 1) Γ) →
    G4c Δ (itpA p S fh (c + 1) Γ g) →
    fh ≤ fuel →
    G4c Δ (itpA p S fuel c Γ g)

/-- **The room-free re-parameterisation is FALSE**, at a space satisfying
every one of its closure and coverage hypotheses. -/
theorem not_reparamKernelRoomFree : ¬ ReparamKernelRoomFree "p" Sk := by
  intro h
  exact not_derivable_k
    (h sk_and sk_or sk_imp sk_some 4 Gk 4 1 gk [srck, ambk]
      sk_goal sk_cover (Nat.le_refl _)
      (G4c.identity_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (G4c.identity_mem (List.mem_cons_self ..))
      (Nat.le_refl _))

/-! ## §3  What the room does exclude

`defect Sk Gk = 8`: the context has absorbed one of the nine space formulas.
So the kernel's own room hypothesis
`defect S Γ · (|jumpGoals S| + 2) ≤ c` demands `8 · (|jumpGoals Sk| + 2) ≤ 1`
at the counterexample, which is false however small `|jumpGoals Sk|` is.
The counterexample is therefore outside the kernel's band, and the
room-carrying statement is untouched by it. -/

theorem defect_Sk_Gk : defect Sk Gk = 8 := by decide +kernel

theorem room_fails :
    ¬ (defect Sk Gk * ((jumpGoals Sk).card + 2) ≤ 1) := by
  rw [defect_Sk_Gk]
  omega

/-! ## §4  The kernel never runs at the budget floor

The room hypotheses do more than exclude one counterexample: together they
force `|jumpGoals S| + 2 ≤ c`, hence `2 ≤ c`.  So the holdout's own band
never contains the budget floor `c = 1` — which is exactly where
`AmbGuardAscent` is refuted (`AscRefute.not_ambGuardAscent` is an instance
at `c = 1`, and `wip/ascRefute.lean` records that no failure was found at
budget `≥ 2`), and exactly where `cascadeBox`'s three pair-floor interfaces
`GammaPairFloorA` / `GammaPairFloorBox` / `JumpPairFloor` are *stated*
(target budget `1`, source components at `2`).

Reading: those three interfaces are not obligations of the kernel's own
band at all.  They arise only from a budget-descending recursion that
does not pay a ledger — which is what `oth_descent` runs.  A ◯-band build
that carries the defect-tower ledger the way `cascade_main` does keeps
every recursive call inside `defect · (J+2) ≤ c`, and therefore never
reaches them. -/

/-- **The kernel's band starts at `|jumpGoals S| + 2`.** -/
theorem room_ge_jump (S : Finset PLLFormula) (Γ : List PLLFormula) (c : Nat)
    (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ c) :
    (jumpGoals S).card + 2 ≤ c := by
  have h : 1 * ((jumpGoals S).card + 2) ≤
      defect S Γ * ((jumpGoals S).card + 2) :=
    Nat.mul_le_mul_right _ hd1
  omega

/-- **The kernel never runs at the budget floor**: its room hypotheses
force `2 ≤ c`. -/
theorem room_two (S : Finset PLLFormula) (Γ : List PLLFormula) (c : Nat)
    (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ c) : 2 ≤ c := by
  have := room_ge_jump S Γ c hd1 hroom
  omega

/-! ## §5  Every known countermodel to the ◯-band descent sits at `c ≤ 1`

The three machine-checked refutations of the ◯-band descent in this repo
are all at budget `≤ 1`:

* `AscRefute.not_ambGuardAscent` — the guard ascent, at `c = 1`;
* `AscRefute.not_roomFreeDescent` — the descent itself, at `c = 1`;
* `wip/floorRefute.lean` — the descent to budget `0`, at `c = 0`.

The corollary below says the kernel's room excludes every one of them, so
**the room-carrying holdout is not refuted by anything now known**, and the
`§56` room-satisfying sweep (all 22 certified failures at `c = 0`, below the
guard) is consistent with that: the band is `c ≥ |jumpGoals S| + 2`. -/

/-- **The room excludes every budget `≤ 1`.**  Contrapositive of
`room_two`: no instance of the kernel sits where the known countermodels
live. -/
theorem band_excludes_c_le_one (S : Finset PLLFormula) (Γ : List PLLFormula)
    (c : Nat) (hd1 : 1 ≤ defect S Γ) (hc : c ≤ 1) :
    ¬ (defect S Γ * ((jumpGoals S).card + 2) ≤ c) := by
  intro hroom
  have := room_two S Γ c hd1 hroom
  omega

end ReparamRefute
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.ReparamRefute.not_reparamKernelRoomFree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ReparamRefute.not_reparamKernelRoomFree

/-- info: 'PLLND.ReparamRefute.room_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ReparamRefute.room_fails

/-- info: 'PLLND.ReparamRefute.room_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.ReparamRefute.room_two

/--
info: 'PLLND.ReparamRefute.band_excludes_c_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.ReparamRefute.band_excludes_c_le_one
