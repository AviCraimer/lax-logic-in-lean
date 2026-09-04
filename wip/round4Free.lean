import wip.boxSndTight

/-!
# ROUND 4, Task 2 — the traversal's target, DECOUPLED from the traversal

PROGRESS §59 records the round-4 calibration warning: `boxSnd_tight` consumes
both premises at fuel `f+1` and delivers `tgtClause p S f c Γ q`, whose *value*
slot sits at fuel `f+1`; so `seal2Free.gammaHead_budget_free` lands the target
value at fuel `f+2` — **one level above** the consumer, whose three sealed
sites hold the source at `F` and want the target at `fl` with only `F ≤ fl`.
§59 offered two ways out: tighten `fh ≤ fuel` to `fh < fuel` at the call sites,
or re-run the traversal one level down.

Neither is needed.  The +1 is an artefact of how `tgtClause` is *written*, not
of what the traversal *proves*.

    tgtClause p S f c Γ q  =  ◯( E@(f, c)(Γ)  ⇢  A@(f+1, c+1)(Γ, q) )

Both parameters of the target are pinned to the recursion's own fuel `f`, and
`boxSnd_tight`'s recursive calls need `tgtClause_fuel_lift` at every step
purely to re-pin them.  But the target is produced in exactly one place — the
goal-clause case of `boxGoal_remap_free` — and there

* the **guard** slot is never used: the source's guard is discharged against
  the *grown ambient* (`ambE`), and the target's own guard is weakened away;
* the **value** slot is `prop q`, injected into the target table's own goal
  clause; `itpA_atom_forces` supplies `prop q` at **every** fuel and **every**
  budget (that is what §91 proved it for).

So the four target parameters — guard fuel, guard budget, value fuel, value
budget — are all free, subject only to `f ≤ (guard fuel)`, `c ≤ (guard
budget)` (downward existential monotonicity, `ambE`) and `1 ≤ (value fuel)`
(the value table must be unfoldable for the atom to be one of its disjuncts).

`tgtClause_relax` states that, and `boxDesc_atom` composes it with
`boxSnd_tight` into `Round4.BoxDesc` **at an atomic body**, with the sites'
own fuel calibration `fs ≤ ft` and no room, no ledger, no defect bound.

## What is still open

The body.  `boxDesc_atom` is `Round4.BoxDesc` restricted to `D = prop q` with
`q ≠ p` over a `∨`-free, `◯`-subformula-closed space.  Generalising `D` is the
mathematical step PROGRESS §59's amendment identifies, and it is *not*
addressed here: `itpA_atom_forces` is what makes the value slot free, and it
has no analogue at a compound body.
-/

open PLLFormula

namespace PLLND
namespace Round4Free

open GoalDesc AtomForce EnvDesc BoxSnd BoxSndTight

/-! ## 1. The target, with all four parameters free -/

/-- The boxed goal clause of an arbitrary target table: guard at `(fg, cg)`,
value at `(fv+1, cv)`, independent of each other and of the traversal. -/
abbrev freeClause (p : String) (S : Finset PLLFormula) (fg cg fv cv : Nat)
    (Γ : List PLLFormula) (q : String) : PLLFormula :=
  ((itpE p S fg cg Γ).ifThen (itpA p S (fv + 1) cv Γ (prop q))).somehow

/-- **The traversal's target relaxes to any guard above it and any value slot
at all.**  `f ≤ fg` and `c ≤ cg` are downward existential monotonicity; the
value parameters `fv`, `cv` are unconstrained. -/
theorem tgtClause_relax (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    {f c fg cg fv cv : Nat} {Γ Δ : List PLLFormula}
    (hΓS : ∀ Y ∈ Γ, Y ∈ S) (hf : f ≤ fg) (hc : c ≤ cg)
    (h : G4c Δ (tgtClause p S f c Γ q)) :
    G4c Δ (freeClause p S fg cg fv cv Γ q) := by
  refine box_remap_free h ?_ ?_
  · exact ambE p S hf hc rfl (G4c.identity_mem (.head _))
  · have hatom : G4c (itpA p S (f + 1) (c + 1) Γ (prop q) ::
        itpE p S fg cg Γ :: Δ) (prop q) :=
      consume₁ (G4c.identity_mem (.head _))
        (itpA_atom_forces p S hOr hq (f + 1) (c + 1) Γ hΓS)
    rw [itpA_succ]
    refine G4c.orAll_intro (φ := prop q) ?_ hatom
    simp only [itpAfull, itpAoth, itpAgoal]
    refine List.mem_append.mpr (Or.inl ?_)
    rw [if_neg hq]
    exact .head _

/-! ## 2. The target table's own goal clause, at any fuel -/

/-- The `◯`-goal disjunct of `itpA p S (fu+1) (c+1) Γ (◯q)`, at **any** fuel
`fu` (`seal2Free.goalDisjunct_mem` is this at `fu = f+1`). -/
theorem goalDisj_mem (p : String) (S : Finset PLLFormula) (fu c : Nat)
    (Γ : List PLLFormula) (q : String) :
    ((itpE p S fu c Γ).ifThen
        (itpA p S fu (c + 1) Γ (prop q))).somehow
      ∈ itpAfull p S fu (c + 1) Γ ((prop q).somehow) := by
  simp only [itpAfull, itpAoth, itpAgoal]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (.head _))))

/-! ## 3. `BoxDesc` at an atomic body, at the sites' own fuels -/

/-- **The `◯`-goal descent at an atomic body, budget-free and fuel-calibrated
to the consumer.**  `fs ≤ ft` is the sites' own `hF : F ≤ fl`; `2 ≤ ft` is
needed because the target's value table must be unfoldable (`ft = 1` leaves
the target's goal clause with a `⊥` value); `1 ≤ b` is needed because at
`b = 0` the target table is literally `⊥`.  There is **no room, no ledger and
no defect bound**. -/
theorem boxDesc_atom (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (fs ft b : Nat) (Γ Δ : List PLLFormula)
    (hΓS : ∀ Y ∈ Γ, Y ∈ S) (hfs : fs ≤ ft) (hb : 1 ≤ b) (hft : 2 ≤ ft)
    (hamb : G4c Δ (itpE p S ft (b + 1) Γ))
    (hsrc : G4c Δ (itpA p S fs (b + 1) Γ ((prop q).somehow))) :
    G4c Δ (itpA p S ft b Γ ((prop q).somehow)) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  obtain ⟨ft', rfl⟩ : ∃ ft', ft = ft' + 2 := ⟨ft - 2, by omega⟩
  cases fs with
  | zero =>
      simp only [itpA] at hsrc
      exact G4c.cut hsrc (G4c.botL (.head _))
  | succ f =>
      -- the ambient, lowered to the source's own fuel
      have hambL : G4c Δ (itpE p S (f + 1) (b' + 2) Γ) :=
        ambE p S (by omega) (Nat.le_refl _) rfl hamb
      -- the traversal: target guard budget `b'`, target guard fuel `f`
      have hclause : G4c Δ (tgtClause p S f b' Γ q) :=
        boxSnd_tight p S hOr hq hsome (defect S Γ) f b' b' Γ Γ Δ
          (Nat.le_refl _) hΓS hambL hsrc
      -- relax the target to the fuels the consumer's table actually uses
      have hfree : G4c Δ (freeClause p S (ft' + 1) b' ft' (b' + 1) Γ q) :=
        tgtClause_relax p S hOr hq hΓS (by omega) (Nat.le_refl _) hclause
      rw [itpA_succ]
      exact G4c.orAll_intro (goalDisj_mem p S (ft' + 1) b' Γ q) hfree

/-! ## 4. The `ft ≤ 1` corner

`boxDesc_atom` asks `2 ≤ ft`.  The sites supply `ft = fl` (site 2) and
`ft = fl + 1` (sites 1 and 3), so only site 2 can present `ft ≤ 1`, and only
in two configurations, both of which are trivial:

* `ft = 0`: then `fs = 0` and the source is `⊥`;
* `ft = 1`: then `fs ∈ {0, 1}`; at `fs = 0` the source is `⊥`, and at
  `fs = 1` the source and the target are the **same formula** — at fuel `1`
  every recursive occurrence sits at fuel `0`, where `itpE` is `⊤` and `itpA`
  is `⊥` regardless of budget, so the whole table is budget-blind above `0`.

`itpA_one_budget_blind` below is that last fact. -/

/-- At fuel `1` and positive budget the universal table does not read the
budget: every recursive occurrence is at fuel `0`, where `itpE = ⊤` and
`itpA = ⊥`. -/
theorem itpA_one_budget_blind (p : String) (S : Finset PLLFormula)
    (b b' : Nat) (Γ : List PLLFormula) (C : PLLFormula) :
    itpA p S 1 (b + 1) Γ C = itpA p S 1 (b' + 1) Γ C := by
  rfl

/-- **`BoxDesc` at an atomic body, with the `ft ≤ 1` corner absorbed.**  The
only fuel hypothesis is the sites' own `fs ≤ ft`. -/
theorem boxDesc_atom_all (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (fs ft b : Nat) (Γ Δ : List PLLFormula)
    (hΓS : ∀ Y ∈ Γ, Y ∈ S) (hfs : fs ≤ ft) (hb : 1 ≤ b)
    (hamb : G4c Δ (itpE p S ft (b + 1) Γ))
    (hsrc : G4c Δ (itpA p S fs (b + 1) Γ ((prop q).somehow))) :
    G4c Δ (itpA p S ft b Γ ((prop q).somehow)) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  match ft, hfs with
  | 0, hfs =>
      have : fs = 0 := Nat.le_zero.mp hfs
      subst this
      simp only [itpA] at hsrc
      exact G4c.cut hsrc (G4c.botL (.head _))
  | 1, hfs =>
      match fs, hfs with
      | 0, _ =>
          simp only [itpA] at hsrc
          exact G4c.cut hsrc (G4c.botL (.head _))
      | 1, _ =>
          rw [itpA_one_budget_blind p S b' (b' + 1) Γ ((prop q).somehow)]
          exact hsrc
  | (ft' + 2), hfs =>
      exact boxDesc_atom p S hOr hq hsome fs (ft' + 2) (b' + 1) Γ Δ hΓS hfs
        (by omega) (by omega) hamb hsrc

end Round4Free
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Round4Free.tgtClause_relax' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round4Free.tgtClause_relax

/--
info: 'PLLND.Round4Free.boxDesc_atom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round4Free.boxDesc_atom

/--
info: 'PLLND.Round4Free.boxDesc_atom_all' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round4Free.boxDesc_atom_all

/-! **The statement carries no financing.**  Pinned as a type check. -/

/--
info: PLLND.Round4Free.boxDesc_atom_all (p : String) (S : Finset PLLFormula) (hOr : ∀ (A B : PLLFormula), A.or B ∉ S)
  {q : String} (hq : q ≠ p) (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S) (fs ft b : ℕ) (Γ Δ : List PLLFormula)
  (hΓS : ∀ Y ∈ Γ, Y ∈ S) (hfs : fs ≤ ft) (hb : 1 ≤ b) (hamb : PLLND.G4c Δ (PLLND.itpE p S ft (b + 1) Γ))
  (hsrc : PLLND.G4c Δ (PLLND.itpA p S fs (b + 1) Γ (prop q).somehow)) :
  PLLND.G4c Δ (PLLND.itpA p S ft b Γ (prop q).somehow)
-/
#guard_msgs in
#check PLLND.Round4Free.boxDesc_atom_all
