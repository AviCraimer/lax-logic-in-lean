import wip.ascRefute
import wip.goalDesc

/-!
# The low-band descent with the budget left OPEN

Every earlier statement of this lemma fixed a budget law in advance and
then defended it:

| statement | budget hypothesis | status |
|---|---|---|
| `cascade_low_pos_box` (`wip/absorb_base.lean`) | `defect S Γ * (\|jumpGoals S\| + 2) ≤ c` | open (the tower's only `sorry`) |
| `RoomFreeDescent` (`wip/cascadeBox.lean`'s target) | `1 ≤ c` | **REFUTED** (`wip/ascRefute.lean`) |
| "the corrected target" | `2 ≤ c` | a guess, untested above the probed spaces |

This file takes the third option off the table by not making a guess at
all.  The budget requirement is a **parameter** `need : Need`; the
theorem to be proved is `Descends p need`; and every branch of the proof
that consumes budget deposits a *law* that `need` must satisfy.  What
`need` is gets settled at the end, by solving the accumulated laws — not
at the start, by intuition.

This is the method the repo already uses for timing constraints
(`LaxLogic/PLLConstraints.lean`, after Mendler's *proofs-as-delays*): a
proof of an abstract specification collects its side conditions instead
of discharging them against guessed numbers, and the constraint algebra
is `(ℕ, 0, +, max)` — `+1` where the recursion crosses a budget gate,
`max` where it branches.  The same algebra is the expected shape of
`need` here, because `itpE`/`itpA` read `b` at exactly two clause
branches and decrement it by one when they do.

## What is already known about the unknown

`refutation_lower_bound` below is the first *extracted* fact: a
machine-checked **lower bound on `need` itself**, read off the
countermodel of `wip/ascRefute.lean` §2.  It says nothing about how the
proof goes; it constrains what any successful proof's budget law can be.
Together with the measured minima of `wip/budgetfit.lean` it brackets
the function from both sides.
-/

open PLLFormula

namespace PLLND
namespace Descent2

/-! ## 1. The parameter and the target -/

/-- A **room requirement**: how much budget a configuration needs.  Left
abstract on purpose. -/
abbrev Need := Finset PLLFormula → List PLLFormula → PLLFormula → Nat

/-- The low-band descent, relative to a room requirement.

This is `cascade_low_pos_box`'s conclusion with the product law replaced
by `need S Γ g ≤ c`, and with the case split on `hbox` dropped: the
box-free/closed/covered case is already settled by
`cascade_low_pos_boxfree`, so a `need` that works uniformly subsumes it,
and a `need` that must distinguish the cases can do so itself. -/
def Descends (p : String) (need : Need) : Prop :=
  ∀ (S : Finset PLLFormula) (fuel fh c : Nat) (Γ : List PLLFormula)
    (g : PLLFormula) (Δ : List PLLFormula),
    need S Γ g ≤ c →
    fh ≤ fuel →
    G4c Δ (itpE p S fuel (c + 1) Γ) →
    G4c Δ (itpA p S fh (c + 1) Γ g) →
    G4c Δ (itpA p S fuel c Γ g)

/-! ## 2. Extracted constraints: what the data already forces

The refutation of §2 of `wip/ascRefute.lean` is an instance of `Descends`
at `c = 1`, `fuel = fh = 4`, with both hypotheses in the context.  So any
`need` for which `Descends` holds must ask for **more than 1** there.
This is the sense in which the budget is being measured rather than
assumed: the countermodel is data, and the theorem turns it into a
constraint on the unknown function. -/

open AscRefute

/-- **A machine-checked lower bound on the unknown budget law.**  Every
room requirement that supports the descent asks for at least `2` at the
refuting configuration — so the room-free law `1 ≤ c` is excluded, and
any candidate `need` must be checked against this before it is adopted. -/
theorem refutation_lower_bound (need : Need)
    (h : Descends "p" need) : 2 ≤ need Sk Gk gk := by
  by_contra hlt
  refine not_derivable_k ?_
  have h1 : need Sk Gk gk ≤ 1 := by omega
  exact h Sk 4 4 1 Gk gk [srck, ambk] h1 (Nat.le_refl _)
    (G4c.identity_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (G4c.identity_mem (List.mem_cons_self ..))

/-- The same statement in the contrapositive form the build will use: a
candidate room law that is `≤ 1` at the refuting configuration cannot
support the descent, whatever else it does. -/
theorem candidate_excluded (need : Need)
    (hle : need Sk Gk gk ≤ 1) : ¬ Descends "p" need := fun h => by
  have := refutation_lower_bound need h
  omega

/-- The constant law `need = 0` is excluded — the trivial sanity check
that the extraction machinery is pointing at something real. -/
theorem const_zero_excluded :
    ¬ Descends "p" (fun _ _ _ => 0) := candidate_excluded _ (by omega)

/-- The room-free law `need = 1` is excluded: this *is*
`not_roomFreeDescent`, restated as a fact about budget laws rather than
about a bespoke `Prop`. -/
theorem const_one_excluded :
    ¬ Descends "p" (fun _ _ _ => 1) := candidate_excluded _ (by omega)

/-! ## 3. The first branch, and the first extracted law

The rebuild's top level is the truncation-pairing wrapper `desc_of_oth`
(`wip/cascadeBox.lean`), which reduces the full-table descent to the
**others-descent** — the same statement with the truncation disjunct
stripped from both sides (`itpAoth`).  That wrapper never touched the
four refuted interfaces, so it is reused verbatim.

Discharging this branch against an abstract `need` deposits exactly one
demand: `desc_of_oth` needs `1 ≤ c`, so it needs

    NeedFloor1 need  :=  ∀ S Γ g, 1 ≤ need S Γ g.

That is the first law, and it is *read off the proof*, not assumed in
advance.  Note it is strictly weaker than what the data already forces
(`refutation_lower_bound`: `2 ≤ need Sk Gk gk`) — which is the shape the
extraction should have.  Each branch states its own demand; the budget
law is the supremum of them and of the measured lower bounds, computed
at the end rather than guessed at the start. -/

/-- The others-descent, relative to a room requirement: what the whole
rebuild now reduces to. -/
def OthDescends (p : String) (need : Need) : Prop :=
  ∀ (S : Finset PLLFormula) (F fl c : Nat) (Γ : List PLLFormula)
    (g : PLLFormula) (Δ : List PLLFormula),
    need S Γ g ≤ c → F ≤ fl →
    G4c Δ (itpE p S (fl + 1) (c + 1) Γ) →
    G4c Δ (orAll (itpAoth p S F (c + 1) Γ g)) →
    G4c Δ (orAll (itpAoth p S fl c Γ g))

/-- **The first extracted law**: the truncation-pairing branch needs a
budget floor of one. -/
def NeedFloor1 (need : Need) : Prop := ∀ S Γ g, 1 ≤ need S Γ g

/-- **The rebuild's top level, PROVED.**  The full descent follows from
the others-descent, for *any* room requirement satisfying the one law
this branch demands.  Nothing here is specific to `2 ≤ c`: the budget
enters only through `NeedFloor1`, so tightening or loosening the law
later costs no rework above this line. -/
theorem descends_of_othDescends (p : String) (need : Need)
    (hfloor : NeedFloor1 need) (h : OthDescends p need) :
    Descends p need := by
  intro S fuel fh c Γ g Δ hneed hfh hamb hhead
  have hc : 1 ≤ c := le_trans (hfloor S Γ g) hneed
  cases fh with
  | zero => exact desc_zero p S hhead
  | succ F =>
      cases fuel with
      | zero => exact absurd hfh (by omega)
      | succ fl =>
          have hF : F ≤ fl := by omega
          exact desc_of_oth p S hF hc
            (fun Δ' hamb' hoth' => h S F fl c Γ g Δ' hneed hF hamb' hoth')
            hamb hhead

/-! ## 4. Screening candidate budget laws

A candidate `need` can now be tested against the accumulated refutation
data *by the kernel*, before any effort is spent proving `Descends` for
it.  `candidate_excluded` is the screen; the theorems below run it.

The screen is one-sided — surviving it is necessary, not sufficient —
but it is the difference between adopting a budget law because it looks
right and adopting one because nothing known refutes it. -/

/-- The two clause shapes at which `itpE`/`itpA` read the budget. -/
def isGated : PLLFormula → Bool
  | .ifThen (.ifThen _ _) _ => true
  | .ifThen (.somehow _) _ => true
  | _ => false

/-- How many budget-gated pieces a space has. -/
def gateCount (S : Finset PLLFormula) : Nat :=
  (S.filter (fun F => isGated F = true)).card

/-- Candidate A: the constant law suggested by the probed boundary. -/
def needConst2 : Need := fun _ _ _ => 2

/-- Candidate B: the gate-count law — budget proportional to the number
of places the recursion can cross a gate, which is the delay-algebra
reading (`+1` per gate crossed, `max` over branches, so the total is
bounded by the number of gates). -/
def needGate : Need := fun S _ _ => gateCount S

/-- `jumpGoals` of `wip/absorb_base.lean`, inlined (that file is not a
lake library target). -/
def jumpGoalsOf (S : Finset PLLFormula) : Finset PLLFormula :=
  S.biUnion (fun F => match F with
    | .ifThen (.ifThen A B) _ => {A.ifThen B}
    | .ifThen (.somehow A) _ => {A, A.somehow}
    | _ => ∅)

/-- Candidate C: the law the tower currently assumes. -/
def needProduct : Need := fun S Γ _ =>
  defect S Γ * ((jumpGoalsOf S).card + 2)

/-- **Candidate A survives the screen.**  `2 ≤ 2`, exactly — the
refutation pins the constant from below with nothing to spare, so any
further refutation at this configuration would kill it. -/
theorem needConst2_survives : ¬ (needConst2 Sk Gk gk ≤ 1) := by decide

/-- **Candidate B survives the screen**, with room to spare. -/
theorem needGate_survives : ¬ (needGate Sk Gk gk ≤ 1) := by decide

/-! ### The proof's demand screens what the data could not

`NeedFloor1` is the first law the *proof* deposited (§3).  Running the
candidates against it separates them where the countermodel data could
not: both survive the refutation screen, but only one satisfies the law.
This is the extraction earning its keep — a demand that no amount of
probing would have produced, because it comes from the argument rather
than from the instances. -/

/-- Candidate A satisfies the first law. -/
theorem needConst2_floor1 : NeedFloor1 needConst2 :=
  fun _ _ _ => Nat.le_succ 1

/-- **Candidate B is eliminated by the first law.**  On a space with no
budget-gated pieces `needGate` asks for nothing, but the
truncation-pairing branch needs a floor of one whatever the space looks
like.  So `needGate` cannot be the budget law, and no effort need be
spent trying to prove `Descends` for it. -/
theorem needGate_not_floor1 : ¬ NeedFloor1 needGate := by
  intro h
  have h0 := h ∅ [] (prop "a")
  simp [needGate, gateCount] at h0

/-- **Candidate C fails the first law too.**  On a *saturated* context
(`S ⊆ Γ`, so `defect S Γ = 0`) the product asks for nothing.  That band is
separately settled by `cascade_zero` in `wip/absorb_base.lean` — every
space-guarded clause is dead there — so the failure is not fatal to the
tower; but it does mean `needProduct` cannot be fed to
`descends_of_othDescends` as it stands. -/
theorem needProduct_not_floor1 : ¬ NeedFloor1 needProduct := by
  intro h
  have h0 := h ∅ [] (prop "a")
  simp [needProduct, defect] at h0

/-! ## 5. The ledger law: what the caller actually funds

The two screens above are necessary conditions coming from *below*
(refutations) and from the *proof* (`NeedFloor1`).  There is a third
constraint, from **above**: the room requirement must be something the
caller can pay.

The caller is the tower's stabilisation entry
(`cascade_entry`/`itp_stab_aux` in `wip/absorb_base.lean`), which runs
under `kcap S < c + 2` where

    kcap S = (2·|S| + 4)·(|S| + 2).

`kcap_room` (reproved here, since `wip/absorb_base.lean` is not a lake
library target) turns that entry condition into the ledger

    |jumpGoals S| + 1 + defect S Γ · (|jumpGoals S| + 2)  ≤  c,

*at every context* `Γ`.  So the ledger is the pointwise maximum the caller
funds, and any `need` below it is affordable.  Unlike `needProduct` it has
a floor of one built in, so it is the strongest candidate that can be fed
to `descends_of_othDescends` unmodified. -/

/-- Candidate D: **the ledger law** — exactly what `kcap_room` funds. -/
def needKcap : Need := fun S Γ _ =>
  (jumpGoalsOf S).card + 1 + defect S Γ * ((jumpGoalsOf S).card + 2)

/-- The jump-goal count is at most twice the size of the space. -/
theorem jumpGoalsOf_card_le (S : Finset PLLFormula) :
    (jumpGoalsOf S).card ≤ 2 * S.card := by
  refine le_trans (Finset.card_biUnion_le) ?_
  rw [two_mul]
  refine le_trans (Finset.sum_le_sum (g := fun _ => 2) ?_) ?_
  · intro F _
    match F with
    | .ifThen (.ifThen A B) _ => simp
    | .ifThen (.somehow A) _ => exact Finset.card_insert_le _ _
    | .prop _ => simp
    | .falsePLL => simp
    | .and _ _ => simp
    | .or _ _ => simp
    | .somehow _ => simp
    | .ifThen (.prop _) _ => simp
    | .ifThen .falsePLL _ => simp
    | .ifThen (.and _ _) _ => simp
    | .ifThen (.or _ _) _ => simp
  · simp only [Finset.sum_const, smul_eq_mul]
    omega

/-- The jump-state threshold of the tower. -/
def kcapOf (S : Finset PLLFormula) : Nat := (2 * S.card + 4) * (S.card + 2)

/-- **The ledger is funded** (`kcap_room` of `wip/absorb_base.lean`): the
tower's entry condition pays the ledger at every context. -/
theorem needKcap_funded {S : Finset PLLFormula} {c : Nat}
    (hb : kcapOf S < c + 2) (Γ : List PLLFormula) (g : PLLFormula) :
    needKcap S Γ g ≤ c := by
  have hJ : (jumpGoalsOf S).card ≤ 2 * S.card := jumpGoalsOf_card_le S
  have hd : defect S Γ ≤ S.card :=
    Finset.card_le_card (Finset.sdiff_subset)
  have h1 : defect S Γ * ((jumpGoalsOf S).card + 2) ≤
      S.card * (2 * S.card + 2) :=
    Nat.mul_le_mul hd (by omega)
  have h2 : (2 * S.card + 4) * (S.card + 2) =
      S.card * (2 * S.card + 2) + (6 * S.card + 8) := by
    ring
  simp only [kcapOf] at hb
  simp only [needKcap]
  omega

/-- **The ledger law satisfies the first extracted law**, unlike the gate
count and the bare product: the `+1` is unconditional. -/
theorem needKcap_floor1 : NeedFloor1 needKcap := by
  intro S Γ g
  simp only [needKcap]
  omega

/-- The ledger law survives the refutation screen at the `wip/ascRefute.lean`
configuration, with room to spare. -/
theorem needKcap_survives : ¬ (needKcap Sk Gk gk ≤ 1) := by decide

/-! ### The reduction that would close the tower's `sorry`

`cascade_low_pos_box` is `wip/absorb_base.lean`'s single `sorry`, and the
only source of `sorryAx` in `uniform_interpolation_PLL`.  Stated as a
`Prop` here (it is `private` there, and that file is not importable), it is
the descent under the tower's own room hypothesis. -/

/-- The tower's holdout, as a proposition: the descent at every
ledger-funded configuration. -/
def LedgerDescent (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (fuel fh c : Nat) (Γ : List PLLFormula) (g : PLLFormula)
    (Δ : List PLLFormula),
    kcapOf S < c + 2 → fh ≤ fuel →
    G4c Δ (itpE p S fuel (c + 1) Γ) →
    G4c Δ (itpA p S fh (c + 1) Γ g) →
    G4c Δ (itpA p S fuel c Γ g)

/-- **Proving the parametric descent with the ledger law closes the
tower's holdout.**  Machine-checked reduction: `Descends p needKcap` gives
the descent at every configuration the tower's entry condition funds, which
is every configuration `cascade_low_pos_box` is ever applied at. -/
theorem ledgerDescent_of_descends (p : String) (S : Finset PLLFormula)
    (h : Descends p needKcap) : LedgerDescent p S :=
  fun fuel fh c Γ g Δ hb hfh hamb hhead =>
    h S fuel fh c Γ g Δ (needKcap_funded hb Γ g) hfh hamb hhead

/-- The same reduction routed through the others-descent: the whole
remaining content of the rebuild, in one statement. -/
theorem ledgerDescent_of_othDescends (p : String) (S : Finset PLLFormula)
    (h : OthDescends p needKcap) : LedgerDescent p S :=
  ledgerDescent_of_descends p S
    (descends_of_othDescends p needKcap needKcap_floor1 h)

/-! ## 6. The floor law, refined by goal shape

§3's first extracted law was `NeedFloor1 need := ∀ S Γ g, 1 ≤ need S Γ g`,
read off `desc_of_oth`.  It is stronger than it needs to be.  `desc_of_oth`
uses `1 ≤ c` in exactly one place — the **truncation** disjunct, which
`itpAfull` appends only for a `◯`-shaped goal.  Splitting the wrapper by
goal shape (`GoalDesc.desc_of_oth_nonbox`) therefore weakens the law to a
floor on boxed goals alone.

This matters because the measurement (`wip/ascprobe.lean`, PROGRESS §84)
says the requirement genuinely **varies with the shape of the goal**: `0` at
atom goals (the descent is proved there by search even at budget `0`), `1`
at boxed goals (certified failure at `0` and only at `0`), `2` in general.
A law of that shape is inexpressible under `NeedFloor1` and admissible
under the refinement. -/

/-- The first law, refined: a budget floor of one **at boxed goals**, which
is all the truncation-pairing wrapper actually needs. -/
def NeedBoxFloor1 (need : Need) : Prop :=
  ∀ (S : Finset PLLFormula) (Γ : List PLLFormula) (D : PLLFormula),
    1 ≤ need S Γ D.somehow

/-- **The rebuild's top level, with the floor law refined.**  Same reduction
as `descends_of_othDescends`, but the budget floor is now demanded only where
the truncation disjunct exists. -/
theorem descends_of_othDescends_shape (p : String) (need : Need)
    (hfloor : NeedBoxFloor1 need) (h : OthDescends p need) :
    Descends p need := by
  intro S fuel fh c Γ g Δ hneed hfh hamb hhead
  cases fh with
  | zero => exact desc_zero p S hhead
  | succ F =>
      cases fuel with
      | zero => exact absurd hfh (by omega)
      | succ fl =>
          have hF : F ≤ fl := by omega
          by_cases hbox : ∃ D : PLLFormula, g = D.somehow
          · obtain ⟨D, rfl⟩ := hbox
            have hc : 1 ≤ c := le_trans (hfloor S Γ D) hneed
            exact desc_of_oth p S hF hc
              (fun _ hamb' hoth' => h S F fl c Γ _ _ hneed hF hamb' hoth')
              hamb hhead
          · exact GoalDesc.desc_of_oth_nonbox p S
              (fun D hD => hbox ⟨D, hD⟩)
              (fun _ hamb' hoth' => h S F fl c Γ g _ hneed hF hamb' hoth')
              hamb hhead

/-- Candidate E: **the goal-shape law** — the one the measurement points to.
`0` at atoms and `⊥`, `1` at boxed goals, `2` elsewhere. -/
def needShape : Need := fun _ _ g =>
  match g with
  | .prop _ => 0
  | .falsePLL => 0
  | .somehow _ => 1
  | _ => 2

/-- **The goal-shape law satisfies the refined floor**, exactly. -/
theorem needShape_boxFloor1 : NeedBoxFloor1 needShape :=
  fun _ _ _ => Nat.le_refl 1

/-- It does *not* satisfy the unrefined floor: at an atom goal it asks for
nothing.  So the refinement of §6 is not cosmetic — it is what admits this
candidate at all. -/
theorem needShape_not_floor1 : ¬ NeedFloor1 needShape := by
  intro h
  have h0 := h ∅ [] (prop "a")
  simp only [needShape] at h0
  omega

/-- The goal-shape law survives the `wip/ascRefute.lean` screen: the refuting
goal `(◯r ⊃ s) ⊃ t` is an implication, so the law asks for `2` there — and
`2` is exactly the certified lower bound. -/
theorem needShape_survives : ¬ (needShape Sk Gk gk ≤ 1) := by decide

end Descent2
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.Descent2.refutation_lower_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Descent2.refutation_lower_bound

/-- info: 'PLLND.Descent2.const_one_excluded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Descent2.const_one_excluded

/--
info: 'PLLND.Descent2.descends_of_othDescends' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Descent2.descends_of_othDescends

/--
info: 'PLLND.Descent2.needGate_not_floor1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Descent2.needGate_not_floor1

/--
info: 'PLLND.Descent2.needKcap_funded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Descent2.needKcap_funded

/--
info: 'PLLND.Descent2.needKcap_floor1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Descent2.needKcap_floor1

/--
info: 'PLLND.Descent2.needProduct_not_floor1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Descent2.needProduct_not_floor1

/--
info: 'PLLND.Descent2.ledgerDescent_of_othDescends' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Descent2.ledgerDescent_of_othDescends

/--
info: 'PLLND.Descent2.descends_of_othDescends_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Descent2.descends_of_othDescends_shape

/-- info: 'PLLND.Descent2.needShape_boxFloor1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Descent2.needShape_boxFloor1
