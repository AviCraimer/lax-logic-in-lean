import round7core
import round6force

/-!
# ROUND 8 — the goal-row absorption, certified interfaces

PROGRESS §66(h) names the round-8 residue: `Round7.CompProd`'s goal-row
case at compound unboxed bodies — absorb the source table's goal row

    Gsrc = ◯( E@(f, b−1)(Γ) ⊃ A@(f, b)(Γ, D) )

into the target table `A@(f+1, c)(Γ, ◯D)` at `1 ≤ c ≤ b` from the ambient
`E@(f+1, b+1)(Γ)` alone.  This file states the absorption as a `Prop`
(`GoalRowAbsorb`) and certifies the reduction that makes the round-8
screens load-bearing:

* `goalRowAbsorb_of_boxDesc` — the absorption follows from the room-free
  `Round4.BoxDesc`: the goal row IS a disjunct of the source table at
  budget `b`, so introduce it and iterate the descent with the ambient
  re-lowered at every step, exactly as `Round7.compProd_of_boxDesc`.
  Consequently — the direction that matters — **any countermodel to
  `GoalRowAbsorb` at admissible parameters refutes `BoxDesc` itself**
  (`not_boxDesc_of_not_goalRowAbsorb`).  The round-8 replay passes W1/W2
  and the `g8-*` strata screen exactly `GoalRowAbsorb`'s sequent shape, so
  their verdicts are verdicts about the room-free route as a whole.

The slots: inside `CompProd`'s walk the fired value is lifted to the
reference fuel `ft = f + 1`, so its rows sit at inner fuel `f`; the goal
row's guard sits one budget below its value (`itpAgoal` at a `◯`-goal).
`b − 1` is truncated subtraction, exact because `1 ≤ b`.
-/

open PLLFormula

namespace PLLND
namespace Round8

open PLLND.Round4

/-- **The goal-row absorption** (the §66(h) residue, stated as the round-8
screen sequent): from the ambient and the source table's goal row, the
target table at every budget in the band `1 ≤ c ≤ b`.  Room-free. -/
def GoalRowAbsorb (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (f b c : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula),
    D.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) → 1 ≤ c → c ≤ b → 1 ≤ b →
    G4c Δ (itpE p S (f + 1) (b + 1) Γ) →
    G4c Δ (((itpE p S f (b - 1) Γ).ifThen (itpA p S f b Γ D)).somehow) →
    G4c Δ (itpA p S (f + 1) c Γ D.somehow)

/-- **The absorption follows from the room-free descent.**  The goal row is
a disjunct of the source table at budget `b` (its `itpAgoal` entry), so the
table follows by disjunct introduction, and the band is walked by iterating
`BoxDesc` with the ambient re-lowered at every step.  No room anywhere. -/
theorem goalRowAbsorb_of_boxDesc (p : String) (S : Finset PLLFormula)
    (hBD : BoxDesc p S) : GoalRowAbsorb p S := by
  intro f b c Γ Δ D hgS hΓS hc hcb hb hamb hrow
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  -- the goal row is a disjunct of the source table at budget b' + 1
  have htbl : G4c Δ (itpA p S (f + 1) (b' + 1) Γ D.somehow) := by
    rw [itpA_succ]
    refine G4c.orAll_intro (φ := ((itpE p S f b' Γ).ifThen
      (itpA p S f (b' + 1) Γ D)).somehow) ?_ ?_
    · simp only [itpAfull, itpAoth, itpAgoal]
      refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
      exact .head _
    · have : b' + 1 - 1 = b' := by omega
      rw [this] at hrow
      exact hrow
  -- walk the band down: b' + 1 = c + k → table at c
  have hdesc : ∀ (k β : Nat), β = c + k → β ≤ b' + 1 →
      G4c Δ (itpA p S (f + 1) β Γ D.somehow) →
      G4c Δ (itpA p S (f + 1) c Γ D.somehow) := by
    intro k
    induction k with
    | zero =>
        intro β h1 _ hv
        rw [h1] at hv
        exact hv
    | succ n ih =>
        intro β h1 h2 hv
        refine ih (c + n) rfl (by omega) ?_
        refine hBD (f + 1) (f + 1) (c + n) Γ Δ D hgS hΓS (Nat.le_refl _)
          (by omega) ?_ ?_
        · exact GoalDesc.ambE p S (Nat.le_refl _) (by omega) rfl hamb
        · have : β = (c + n) + 1 := by omega
          rw [this] at hv
          exact hv
  exact hdesc (b' + 1 - c) (b' + 1) (by omega) (Nat.le_refl _) htbl

/-- **The upgrade direction**: a refutation of the absorption at admissible
parameters refutes the room-free descent.  This is what makes the round-8
replay passes W1/W2 (and the `g8-*` strata) two-sided instruments for the
whole route. -/
theorem not_boxDesc_of_not_goalRowAbsorb (p : String) (S : Finset PLLFormula)
    (h : ¬ GoalRowAbsorb p S) : ¬ BoxDesc p S :=
  fun hBD => h (goalRowAbsorb_of_boxDesc p S hBD)

/-! ## Delimited positives -/

/-- **The top of the band is free, at ANY body**: at `c = b` the goal row
IS a disjunct of the target table — disjunct introduction, no descent, no
room, no body analysis. -/
theorem goalRowAbsorb_top (p : String) (S : Finset PLLFormula)
    (f b : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula) (hb : 1 ≤ b)
    (hrow : G4c Δ (((itpE p S f (b - 1) Γ).ifThen
      (itpA p S f b Γ D)).somehow)) :
    G4c Δ (itpA p S (f + 1) b Γ D.somehow) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [itpA_succ]
  refine G4c.orAll_intro (φ := ((itpE p S f b' Γ).ifThen
    (itpA p S f (b' + 1) Γ D)).somehow) ?_ ?_
  · simp only [itpAfull, itpAoth, itpAgoal]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (.head _))))
  · have : b' + 1 - 1 = b' := by omega
    rw [this] at hrow
    exact hrow

/-- **The absorption at ATOMIC bodies, PROVED, room-free**: commit the
target to its own goal clause; open the goal row, fire it with the lowered
ambient, and convert the fired value by the ambient-carrying atom forcing
(`Round6Force.itpA_atom_forces_amb`, no `∨`-freeness) — the forced atom is
the entire inner value table.  The `c < b` band needs `2 ≤ b` (automatic)
and the forcing's matched slots come from the ambient by downward
monotonicity.  At fuel `f = 0` the goal row is `◯(⊤ ⊃ ⊥)` and the
committed clause closes by explosion under the box. -/
theorem goalRowAbsorb_atom (p : String) (S : Finset PLLFormula)
    {q : String} (hq : q ≠ p)
    (f b c : Nat) (Γ Δ : List PLLFormula)
    (hΓS : ∀ X ∈ Γ, X ∈ S) (hc : 1 ≤ c) (hcb : c ≤ b) (hb : 1 ≤ b)
    (hamb : G4c Δ (itpE p S (f + 1) (b + 1) Γ))
    (hrow : G4c Δ (((itpE p S f (b - 1) Γ).ifThen
      (itpA p S f b Γ (prop q))).somehow)) :
    G4c Δ (itpA p S (f + 1) c Γ (prop q).somehow) := by
  rcases Nat.eq_or_lt_of_le hcb with rfl | hlt
  · exact goalRowAbsorb_top p S f c Γ Δ (prop q) hb hrow
  -- c < b, so b ≥ 2: commit the target's own goal clause
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, b = e + 2 := ⟨b - 2, by omega⟩
  rw [itpA_succ]
  refine G4c.orAll_intro (φ := ((itpE p S f c' Γ).ifThen
    (itpA p S f (c' + 1) Γ (prop q))).somehow) ?_ ?_
  · simp only [itpAfull, itpAoth, itpAgoal]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (.head _))))
  refine G4c.cut hrow (G4c.laxL (.head _) ?_)
  -- context: H :: ◯H :: Δ with H the opened goal row
  cases f with
  | zero =>
      -- H = ⊤ ⊃ ⊥: explosion under the box
      simp only [itpE, itpA] at *
      refine G4c.cut (Round6.fire (G4c.identity_mem (.head _))
        (G4c.truePLL_intro _)) (G4c.botL (.head _))
  | succ f' =>
      -- fire the goal row with the lowered ambient, force the atom
      have hambW : G4c ((itpE p S (f' + 1) (e + 2 - 1) Γ).ifThen
          (itpA p S (f' + 1) (e + 2) Γ (prop q)) ::
          ((itpE p S (f' + 1) (e + 2 - 1) Γ).ifThen
            (itpA p S (f' + 1) (e + 2) Γ (prop q))).somehow :: Δ)
          (itpE p S (f' + 1) (e + 2) Γ) :=
        GoalDesc.ambE p S (Nat.le_succ _) (by omega) rfl
          (Round6.weaken_sub (fun ψ h => .tail _ (.tail _ h)) hamb)
      have hV : G4c ((itpE p S (f' + 1) (e + 2 - 1) Γ).ifThen
          (itpA p S (f' + 1) (e + 2) Γ (prop q)) ::
          ((itpE p S (f' + 1) (e + 2 - 1) Γ).ifThen
            (itpA p S (f' + 1) (e + 2) Γ (prop q))).somehow :: Δ)
          (itpA p S (f' + 1) (e + 2) Γ (prop q)) := by
        refine Round6.fire (G4c.identity_mem (.head _)) ?_
        exact Round6.consume₁ hambW
          ((itp_budget_mono_le p S (b := e + 2 - 1) (b' := e + 2)
            (by omega) (f' + 1)).1 Γ)
      have hqd : G4c ((itpE p S (f' + 1) (e + 2 - 1) Γ).ifThen
          (itpA p S (f' + 1) (e + 2) Γ (prop q)) ::
          ((itpE p S (f' + 1) (e + 2 - 1) Γ).ifThen
            (itpA p S (f' + 1) (e + 2) Γ (prop q))).somehow :: Δ)
          (prop q) :=
        Round6Force.itpA_atom_forces_amb p S hq (f' + 1) e Γ _
          hΓS hambW hV
      refine G4c.laxR (G4c.impR ?_)
      -- the inner table's goal disjunct is the atom itself
      rw [itpA_succ]
      refine G4c.orAll_intro (φ := prop q) ?_ (hqd.weaken _)
      simp only [itpAfull, itpAoth, itpAgoal]
      refine List.mem_append.mpr (Or.inl ?_)
      rw [if_neg hq]
      exact .head _

end Round8
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Round8.goalRowAbsorb_of_boxDesc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round8.goalRowAbsorb_of_boxDesc

/--
info: 'PLLND.Round8.not_boxDesc_of_not_goalRowAbsorb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round8.not_boxDesc_of_not_goalRowAbsorb

/--
info: 'PLLND.Round8.goalRowAbsorb_top' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round8.goalRowAbsorb_top

/--
info: 'PLLND.Round8.goalRowAbsorb_atom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round8.goalRowAbsorb_atom

/-! **The statement carries no financing.**  Pinned as a type check: the
only arithmetic in `GoalRowAbsorb` is the band `1 ≤ c ≤ b`, `1 ≤ b` — no
`defect`, no `jumpGoals`, no room. -/

/--
info: PLLND.Round8.GoalRowAbsorb (p : String) (S : Finset PLLFormula) : Prop
-/
#guard_msgs in
#check PLLND.Round8.GoalRowAbsorb
