import LaxLogic.PLLG4UITrunc

/-!
# Starvation at the budget floor — first bricks of the `cascade_low_pos_box` campaign

Terminology, in standard language (translating the tower's internal
vocabulary): the *universal quantifier table* `itpA p S fuel b Γ C` is the
disjunction (`orAll`) of its clause lists; a state *(Γ, C, b)* is **starved**
when that clause list is empty, so the table is literally `⊥` (`orAll [] =
⊥`).  The budget-gated clause families — the goal clause of a `◯`-shaped
goal, the truncation disjunct, and the two `⊃`-family environment clauses —
all vanish at budget `b = 0`.

The countermodel battery of the July 8–12 session (`wip/refute4.lean`)
located the *unique* false point of the bare low-band descent at exactly
(`◯`-shaped goal, `b = 0`).  This file proves the syntactic half of that
boundary as theorems:

* `itpAgoal_obGoal_floor`, `itpAfull_obGoal_floor` — at the floor a
  `◯`-goal's table is its environment table alone (goal clause and
  truncation both gated off);
* `itpA_obGoal_floor` — the floor normal form of the table;
* `itpA_starve_floor` — **starvation collapse**: empty environment table
  at the floor gives `itpA = ⊥` *literally*.

These are the base facts of the starvation-collapse classification that
the kernel's own failure analysis names as step one of the unattempted
proof plan (`(defect, budget)`-lexicographic landing map over starved
states); the campaign continues from here.
-/

open PLLFormula

namespace PLLND

/-- At budget `0` a `◯`-shaped goal contributes no goal clause. -/
theorem itpAgoal_obGoal_floor (p : String) (S : Finset PLLFormula) (f : Nat)
    (Γ : List PLLFormula) (D : PLLFormula) :
    itpAgoal p S f 0 Γ (D.somehow) = [] := rfl

/-- At budget `0` the truncation disjunct is gated off, so the full table
of a `◯`-goal is its environment table. -/
theorem itpAfull_obGoal_floor (p : String) (S : Finset PLLFormula) (f : Nat)
    (Γ : List PLLFormula) (D : PLLFormula) :
    itpAfull p S f 0 Γ (D.somehow) = itpAenv p S f 0 Γ (D.somehow) := by
  show (itpAoth p S f 0 Γ (D.somehow) ++
      (if (itpAoth p S f 0 Γ (D.somehow)).isEmpty then [] else [])) =
    itpAenv p S f 0 Γ (D.somehow)
  rw [ite_self, List.append_nil]
  show itpAgoal p S f 0 Γ (D.somehow) ++ itpAenv p S f 0 Γ (D.somehow) =
    itpAenv p S f 0 Γ (D.somehow)
  rw [itpAgoal_obGoal_floor, List.nil_append]

/-- The floor normal form: at budget `0` the universal table of a `◯`-goal
is the disjunction of its environment clauses alone. -/
theorem itpA_obGoal_floor (p : String) (S : Finset PLLFormula) (f : Nat)
    (Γ : List PLLFormula) (D : PLLFormula) :
    itpA p S (f + 1) 0 Γ (D.somehow) =
      orAll (itpAenv p S f 0 Γ (D.somehow)) := by
  rw [itpA_succ, itpAfull_obGoal_floor]

/-- **Starvation collapse at the floor**: an empty environment table makes
the universal quantifier table of a `◯`-goal at budget `0` literally `⊥`.
This pins, as a theorem, the exact boundary at which the low-band descent
fails — the countermodel battery's unique false point. -/
theorem itpA_starve_floor (p : String) (S : Finset PLLFormula) (f : Nat)
    (Γ : List PLLFormula) (D : PLLFormula)
    (h : itpAenv p S f 0 Γ (D.somehow) = []) :
    itpA p S (f + 1) 0 Γ (D.somehow) = falsePLL := by
  rw [itpA_obGoal_floor, h]
  rfl

end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.itpA_starve_floor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.itpA_starve_floor

/-! ## The starved-seal engine, and starvation beyond the floor -/

namespace PLLND

/-- Cons-weakening at `G4c`. -/
private theorem wk {Γ : List PLLFormula} {C : PLLFormula} (ψ : PLLFormula)
    (d : G4c Γ C) : G4c (ψ :: Γ) C := by
  obtain ⟨n, h⟩ := d; exact ⟨n, h.weaken ψ⟩

/-- **A starved seal closes.**  A boxed guarded implication whose value
slot is `⊥`, together with a derivable guard, yields *any* `◯`-conclusion:
open the box, fire the guard, explode.  This is the engine that dispatches
every sealed branch whose inner partner is starved. -/
theorem box_absurd {Δ : List PLLFormula} {X : PLLFormula} (W : PLLFormula)
    (dBox : G4c Δ ((X.ifThen falsePLL).somehow)) (dX : G4c Δ X) :
    G4c Δ W.somehow := by
  refine G4c.cut dBox (G4c.laxL (.head _) ?_)
  refine G4c.cut (wk _ (wk _ dX)) ?_
  exact G4c.cut (G4c.mp X falsePLL _) (G4c.botL (.head _))

/-- The eliminated atom's goal clause is empty at **every** budget. -/
theorem itpAgoal_elimAtom (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) : itpAgoal p S f b Γ (prop p) = [] := by
  simp [itpAgoal]

/-- **Eliminated-atom starvation, all budgets**: with an empty environment
table the universal quantifier at the eliminated atom collapses to `⊥` at
any budget, not only the floor. -/
theorem itpA_starve_elimAtom (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) (h : itpAenv p S f b Γ (prop p) = []) :
    itpA p S (f + 1) b Γ (prop p) = falsePLL := by
  rw [itpA_succ]
  show orAll (itpAgoal p S f b Γ (prop p) ++ itpAenv p S f b Γ (prop p)) =
    falsePLL
  rw [itpAgoal_elimAtom, h]
  rfl

end PLLND

/-! ## T2: the starvation dispatch, table-keyed -/

namespace PLLND

/-- Extend a singleton-context derivation by an arbitrary tail. -/
private theorem wkctx {Δ : List PLLFormula} {A C : PLLFormula}
    (d : G4c [A] C) : G4c (A :: Δ) C := by
  induction Δ with
  | nil => exact d
  | cons ψ Δ ih =>
      obtain ⟨n, h⟩ := ih
      exact ⟨n, (h.weaken ψ).perm (List.Perm.swap A ψ Δ)⟩

/-- **A starved γ-seal dispatches**: a source disjunct
`◯(E@x ⇢ A@x(Γ, gs))` whose value slot is starved (`A@x(Γ, gs) = ⊥`),
under an ambient existential table at any budget `y ≥ x`, yields *any*
`◯`-conclusion — fire the guard by downward budget monotonicity and
explode.  With `itpA_starve_floor` / `itpA_starve_elimAtom` this closes
every sealed branch of the low-band descent whose source partner is
starved. -/
theorem gamma_seal_starved (p : String) (S : Finset PLLFormula)
    (f x y : Nat) (Γ : List PLLFormula) (gs : PLLFormula)
    {Δ : List PLLFormula} (W : PLLFormula) (hxy : x ≤ y)
    (hstarve : itpA p S f x Γ gs = falsePLL)
    (hamb : G4c Δ (itpE p S f y Γ))
    (dBox : G4c Δ (((itpE p S f x Γ).ifThen (itpA p S f x Γ gs)).somehow)) :
    G4c Δ W.somehow := by
  rw [hstarve] at dBox
  exact box_absurd W dBox
    (G4c.cut hamb (wkctx ((itp_budget_mono_le p S hxy f).1 Γ)))

end PLLND

/-- info: 'PLLND.gamma_seal_starved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.gamma_seal_starved

/-! ## The free-directions box remap -/

namespace PLLND

/-- General subset weakening for `G4c` (through the set calculus, as
`absorb_base`'s private `weaken_sub`). -/
theorem wksub {Γ Γ' : List PLLFormula} {C : PLLFormula}
    (h : ∀ ψ ∈ Γ, ψ ∈ Γ') (d : G4c Γ C) : G4c Γ' C := by
  rw [G4c.iff_set] at d ⊢
  refine d.weaken_subset ?_
  intro y hy
  rw [List.mem_toFinset] at hy ⊢
  exact h y hy

/-- **The free-directions box remap**: from a boxed guarded implication, a
guard conversion, and a value conversion — both as derivations in the
extended context — the remapped box follows.  One plumbing shape for the
`◯χ` box-growth branches and the clause-γ seal step: the conversions are
instantiated with downward existential monotonicity (guard) and the
recursive descent (value). -/
theorem box_remap_free {Δ : List PLLFormula} {E E' A A' : PLLFormula}
    (dBox : G4c Δ ((E.ifThen A).somehow))
    (dE : G4c (E' :: Δ) E)
    (dA : G4c (A :: E' :: Δ) A') :
    G4c Δ ((E'.ifThen A').somehow) := by
  refine G4c.cut dBox (G4c.laxL (.head _) ?_)
  refine G4c.laxR (G4c.impR ?_)
  have dE' : G4c (E' :: (E.ifThen A) :: (E.ifThen A).somehow :: Δ) E :=
    wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto) dE
  have dmp : G4c (E :: E' :: (E.ifThen A) :: (E.ifThen A).somehow :: Δ) A :=
    wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto)
      (G4c.mp E A (E' :: (E.ifThen A).somehow :: Δ))
  refine G4c.cut (G4c.cut dE' dmp) ?_
  exact wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto) dA

end PLLND

/-- info: 'PLLND.box_remap_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.box_remap_free

/-! ## Public box opening -/

namespace PLLND

/-- Open a derivable boxed guarded implication against a `◯`-goal: fire the
guard and continue with the value in context (`absorb_base`'s private
`box_fire`, replicated public). -/
theorem box_open {Δ : List PLLFormula} {X Y W : PLLFormula}
    (dBox : G4c Δ ((X.ifThen Y).somehow)) (dX : G4c Δ X)
    (k : G4c (Y :: Δ) W.somehow) : G4c Δ W.somehow := by
  refine G4c.cut dBox (G4c.laxL (.head _) ?_)
  have dX' : G4c ((X.ifThen Y) :: (X.ifThen Y).somehow :: Δ) X :=
    wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto) dX
  refine G4c.cut (G4c.cut dX' (G4c.mp X Y ((X.ifThen Y).somehow :: Δ))) ?_
  exact wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto) k

end PLLND

/-- info: 'PLLND.box_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.box_open
