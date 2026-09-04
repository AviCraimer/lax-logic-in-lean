import LaxLogic.PLLG4UITrunc

/-!
# The ◯-involving low-budget descent: the others-descent build

The kernel `cascade_low_pos_box` (wip/absorb_base.lean) asks, for a
piece-closed space `S` with goal and context inside `S`:

    from  Δ ⊢ itpE p S fuel (c+1) Γ   (the ambient existential table)
    and   Δ ⊢ itpA p S fh (c+1) Γ g   (the universal table, head fuel)
    infer Δ ⊢ itpA p S fuel c Γ g     (one budget down).

This file builds that descent by the organisation fixed in PROGRESS
§§71–77: a lexicographic induction on (defect `S Γ` strong, budget
strong, fuel structural) whose inner statement is the **others-descent**

    [E-ambient@(c+1), orAll (itpAoth @(c+1))] ⊢ orAll (itpAoth @c)

— both disjunct tables stripped of their truncation disjunct — with the
full-table descent recovered by a two-branch wrapper (`desc_of_oth`):
the source truncation disjunct commits the *target* truncation, opens
the source box against it (`box_open`), and the residual obligation is
again the others-descent; every undecorated source disjunct maps
through the others-descent directly.

Branch mechanisms inside the others-descent (the §71/§77 table):

* goal decomposition, present-antecedent goals — head-fuel descent
  (the fuel induction, through the wrapper);
* growth disjuncts (`∧`, atom-`⊃`, `⊃∧`, `⊃∨`, jump/γ second
  components) — the defect strong induction, ambient re-supplied from
  the matching conjunct of the ambient table;
* `◯χ`-environment disjuncts of a `◯`-goal — the ambient's own bare
  box `◯ itpE (χ::Γ)` is opened against the committed target box, and
  the boxed pair remaps by `box_remap_free` with the defect induction
  at the `χ`-grown context;
* goal-γ (`◯`-goal clause) — same-budget remap, value slot by the
  head-fuel descent at the unboxed goal;
* clause-γ and jump-family first components — the budget strong
  induction one budget down (`c ≥ 2`);
* at target budget `1` the gated first components sit at budget `0`,
  where the descent statement is false at `◯`-goals (the battery's
  false point): those branch instances, together with the one-step
  guard ascent at a fresh space piece (the fresh-antecedent equality
  law, battery-exact but unproven), are the OPEN interfaces stated as
  `Prop`s below; the assembly consumes them as hypotheses, so every
  theorem in this file is sorry-free except the clearly-marked stubs
  in the final section.

Sequent-level glue is replicated from `wip/absorb_base.lean`'s private
helpers and `wip/starve.lean`'s public versions (wip files are outside
the module path, so they cannot be imported).
-/

open PLLFormula

namespace PLLND

/-! ### Sequent-level glue (replicated) -/

/-- General subset weakening for `G4c` (through the set calculus). -/
private theorem wksub {Γ Γ' : List PLLFormula} {C : PLLFormula}
    (h : ∀ ψ ∈ Γ, ψ ∈ Γ') (d : G4c Γ C) : G4c Γ' C := by
  rw [G4c.iff_set] at d ⊢
  refine d.weaken_subset ?_
  intro y hy
  rw [List.mem_toFinset] at hy ⊢
  exact h y hy

/-- Consume a one-hypothesis lemma under a deriving context. -/
private theorem consume₁ {Δ : List PLLFormula} {X Z : PLLFormula}
    (dX : G4c Δ X) (L : G4c [X] Z) : G4c Δ Z :=
  G4c.cut dX (wksub (by
    intro ψ hψ
    rcases List.mem_singleton.mp hψ with rfl
    exact .head _) L)

/-- Consume a two-hypothesis lemma under a deriving context. -/
private theorem consume₂ {Δ : List PLLFormula} {X Y Z : PLLFormula}
    (dX : G4c Δ X) (dY : G4c Δ Y) (L : G4c [X, Y] Z) : G4c Δ Z :=
  G4c.cut dX (G4c.cut (dY.weaken X) (wksub (by
    intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact .tail _ (.head _)
    · rcases List.mem_singleton.mp hψ with rfl
      exact .head _) L))

/-- Fire a derivable implication with a derivable antecedent. -/
private theorem fire {Δ : List PLLFormula} {X Y : PLLFormula}
    (dImp : G4c Δ (X.ifThen Y)) (dX : G4c Δ X) : G4c Δ Y :=
  consume₂ dX dImp (G4c.mp X Y [])

/-- Project a conjunct out of a derivable bundle. -/
private theorem projE {Δ l : List PLLFormula} {φ : PLLFormula}
    (dE : G4c Δ (andAll l)) (hmem : φ ∈ l) : G4c Δ φ :=
  G4c.cut dE (G4c.andAll_elim hmem (G4c.identity_mem (.head _)))

/-- Open a derivable boxed guarded implication against a `◯`-goal:
fire the guard and continue with the value in context (`wip/starve.lean`'s
public `box_open`, replicated). -/
private theorem box_open {Δ : List PLLFormula} {X Y W : PLLFormula}
    (dBox : G4c Δ ((X.ifThen Y).somehow)) (dX : G4c Δ X)
    (k : G4c (Y :: Δ) W.somehow) : G4c Δ W.somehow := by
  refine G4c.cut dBox (G4c.laxL (.head _) ?_)
  have dX' : G4c ((X.ifThen Y) :: (X.ifThen Y).somehow :: Δ) X :=
    wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto) dX
  refine G4c.cut (G4c.cut dX' (G4c.mp X Y ((X.ifThen Y).somehow :: Δ))) ?_
  exact wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto) k

/-- Open a derivable bare box against a `◯`-goal, keeping the body. -/
private theorem box_elim {Δ : List PLLFormula} {X W : PLLFormula}
    (dBox : G4c Δ X.somehow) (k : G4c (X :: Δ) W.somehow) :
    G4c Δ W.somehow := by
  refine G4c.cut dBox (G4c.laxL (.head _) ?_)
  exact wksub (by intro ψ h; simp only [List.mem_cons] at h ⊢; tauto) k

/-- The free-directions box remap (`wip/starve.lean`'s public version,
replicated): from a boxed guarded implication, a guard conversion, and
a value conversion — both as derivations in the extended context — the
remapped box follows. -/
private theorem box_remap_free {Δ : List PLLFormula} {E E' A A' : PLLFormula}
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

/-- A boxed guarded implication whose value slot is `⊥`, with a
derivable guard, yields any `◯`-conclusion (`wip/starve.lean`'s public
`box_absurd`, replicated): open the box, fire the guard, explode. -/
private theorem box_absurd {Δ : List PLLFormula} {X : PLLFormula}
    (W : PLLFormula) (dBox : G4c Δ ((X.ifThen falsePLL).somehow))
    (dX : G4c Δ X) : G4c Δ W.somehow :=
  box_open dBox dX (G4c.botL (.head _))

/-! ### Monotonicity plumbing (replicated) -/

/-- Multi-step fuel monotonicity (`itp_fuel_mono` composed). -/
private theorem itp_fuel_mono_le (p : String) (S : Finset PLLFormula)
    {f f' : Nat} (h : f ≤ f') :
    (∀ b Γ, G4c [itpE p S f' b Γ] (itpE p S f b Γ)) ∧
    (∀ b Γ C, G4c [itpA p S f b Γ C] (itpA p S f' b Γ C)) := by
  induction h with
  | refl => exact ⟨fun b Γ => G4c.iden (.head _), fun b Γ C => G4c.iden (.head _)⟩
  | @step m _ ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · intro b Γ
        exact consume₁ (consume₁ (G4c.identity_mem (.head _))
          ((itp_fuel_mono p S m).1 b Γ)) (ihE b Γ)
      · intro b Γ C
        exact consume₁ (consume₁ (G4c.identity_mem (.head _)) (ihA b Γ C))
          ((itp_fuel_mono p S m).2 b Γ C)

/-- Lower a derivable existential table in fuel and budget (both free
directions on the `E`-side). -/
private theorem amb_down {p : String} {S : Finset PLLFormula}
    {f f' b b' : Nat} {Γ Δ : List PLLFormula}
    (d : G4c Δ (itpE p S f b Γ)) (hf : f' ≤ f) (hb : b' ≤ b) :
    G4c Δ (itpE p S f' b' Γ) :=
  consume₁ (consume₁ d ((itp_fuel_mono_le p S hf).1 _ _))
    ((itp_budget_mono_le p S hb f').1 Γ)

/-- Lift a derivable universal value in fuel and budget (both free
directions on the `A`-side). -/
private theorem val_lift {p : String} {S : Finset PLLFormula}
    {f f' b b' : Nat} {Γ Δ : List PLLFormula} {C : PLLFormula}
    (d : G4c Δ (itpA p S f b Γ C)) (hf : f ≤ f') (hb : b ≤ b') :
    G4c Δ (itpA p S f' b' Γ C) :=
  consume₁ (consume₁ d ((itp_fuel_mono_le p S hf).2 b Γ C))
    ((itp_budget_mono_le p S hb f').2 Γ C)

/-- Shift a derivable existential table onto a set-equal cons context. -/
private theorem amb_congr {p : String} {S : Finset PLLFormula} {f b : Nat}
    {Γ Δ : List PLLFormula} {X : PLLFormula}
    (d : G4c Δ (itpE p S f b Γ)) (hX : X ∈ Γ) :
    G4c Δ (itpE p S f b (X :: Γ)) :=
  consume₁ d ((itp_congr p S f).1 b Γ (X :: Γ) (by
    rw [List.toFinset_cons]
    exact (Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hX)).symm))

/-- Free fuel lift of a boxed guarded pair: the guard converts
downward, the value upward — both fuel monotonicities. -/
private theorem box_fuel_lift {p : String} {S : Finset PLLFormula}
    {f f' b : Nat} {Γ : List PLLFormula} {gs : PLLFormula}
    (h : f ≤ f') {Δ : List PLLFormula}
    (dBox : G4c Δ (((itpE p S f b Γ).ifThen (itpA p S f b Γ gs)).somehow)) :
    G4c Δ (((itpE p S f' b Γ).ifThen (itpA p S f' b Γ gs)).somehow) :=
  box_remap_free dBox
    (consume₁ (G4c.identity_mem (.head _)) ((itp_fuel_mono_le p S h).1 _ _))
    (consume₁ (G4c.identity_mem (.head _)) ((itp_fuel_mono_le p S h).2 _ _ _))

/-- Free fuel lift of a guarded implication pair (the jump-conjunct
shape): guard downward, value upward. -/
private theorem imp_fuel_lift {p : String} {S : Finset PLLFormula}
    {f f' b : Nat} {Γ : List PLLFormula} {gs : PLLFormula}
    (h : f ≤ f') {Δ : List PLLFormula}
    (d : G4c Δ ((itpE p S f b Γ).ifThen (itpA p S f b Γ gs))) :
    G4c Δ ((itpE p S f' b Γ).ifThen (itpA p S f' b Γ gs)) :=
  consume₁ d (imp_mono ((itp_fuel_mono_le p S h).1 _ _)
    ((itp_fuel_mono_le p S h).2 _ _ _))

/-! ### Table facts -/

/-- Undecorated disjuncts always sit in the full table. -/
private theorem mem_itpAfull_of_oth {p : String} {S : Finset PLLFormula}
    {f b : Nat} {Γ : List PLLFormula} {C ψ : PLLFormula}
    (h : ψ ∈ itpAoth p S f b Γ C) : ψ ∈ itpAfull p S f b Γ C := by
  cases C <;> simp only [itpAfull] <;>
    first
      | exact h
      | exact List.mem_append.mpr (Or.inl h)

/-- At positive budget a `◯`-goal's undecorated table is nonempty: the
goal clause is present. -/
private theorem itpAoth_obGoal_isEmpty (p : String) (S : Finset PLLFormula)
    (f b : Nat) (Γ : List PLLFormula) (D : PLLFormula) :
    (itpAoth p S f (b + 1) Γ (D.somehow)).isEmpty = false := rfl

/-- Strict defect drop from a fresh space piece landing anywhere in a
grown context. -/
private theorem defect_lt_of_mem {S : Finset PLLFormula}
    {Γ Γ' : List PLLFormula} {x : PLLFormula}
    (hsub : Γ.toFinset ⊆ Γ'.toFinset) (hxS : x ∈ S) (hxΓ : x ∉ Γ)
    (hxΓ' : x ∈ Γ') : defect S Γ' < defect S Γ := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    exact ⟨hy.1, fun h => hy.2 (hsub h)⟩
  · intro hsub2
    have h2 := hsub2 (Finset.mem_sdiff.mpr
      ⟨hxS, fun h => hxΓ (List.mem_toFinset.mp h)⟩)
    rw [Finset.mem_sdiff] at h2
    exact h2.2 (List.mem_toFinset.mpr hxΓ')

/-! ### The head-fuel floor of the descent -/

/-- At head fuel `0` the descent is vacuous: the source table is `⊥`. -/
theorem desc_zero (p : String) (S : Finset PLLFormula)
    {fuel c : Nat} {Γ Δ : List PLLFormula} {g : PLLFormula}
    (hhead : G4c Δ (itpA p S 0 (c + 1) Γ g)) :
    G4c Δ (itpA p S fuel c Γ g) := by
  simp only [itpA] at hhead
  exact G4c.cut hhead (G4c.botL (.head _))

/-! ### The two-branch wrapper (§77)

The full-table descent from the others-descent.  Truncations pair
across the descent: the source truncation disjunct commits the
*target* truncation `◯(itpE@(c−1) ⇢ ⋁ others@c)` — a `◯`-goal — and
opens the source box against it, the guard fired from the ambient by
downward monotonicity; the residual obligation inside is exactly the
others-descent, which also absorbs every undecorated source disjunct
directly.  No truncation strip is ever performed (§77's correction:
the strip's conclusion is not `◯`-shaped, so `laxL` could never open
the source box for it). -/

/-- The full-table descent at head fuel `F + 1`, target fuel `fl + 1`,
budgets `c + 1 → c`, from the others-descent at inner fuels `(F, fl)`
(supplied context-polymorphically). -/
theorem desc_of_oth (p : String) (S : Finset PLLFormula)
    {F fl c : Nat} {Γ : List PLLFormula} {g : PLLFormula}
    (hF : F ≤ fl) (hc : 1 ≤ c)
    (hoth : ∀ (Δ' : List PLLFormula),
      G4c Δ' (itpE p S (fl + 1) (c + 1) Γ) →
      G4c Δ' (orAll (itpAoth p S F (c + 1) Γ g)) →
      G4c Δ' (orAll (itpAoth p S fl c Γ g)))
    {Δ : List PLLFormula}
    (hamb : G4c Δ (itpE p S (fl + 1) (c + 1) Γ))
    (hhead : G4c Δ (itpA p S (F + 1) (c + 1) Γ g)) :
    G4c Δ (itpA p S (fl + 1) c Γ g) := by
  obtain ⟨c'', rfl⟩ : ∃ c'', c = c'' + 1 := ⟨c - 1, by omega⟩
  rw [itpA_succ] at hhead ⊢
  refine G4c.cut hhead (G4c.orAll_elim ?_)
  intro φ hφ
  cases g with
  | somehow D =>
      simp only [itpAfull] at hφ ⊢
      rcases List.mem_append.mp hφ with hφ | hφ
      · -- undecorated source disjunct: through the others-descent,
        -- then inject the target others-table into the full table
        refine consume₁ (hoth (φ :: Δ) (hamb.weaken φ)
          (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))) ?_
        exact orAll_map (fun ψ h => ⟨ψ, List.mem_append.mpr (Or.inl h),
          G4c.iden (.head _)⟩)
      · -- the truncation disjunct: commit the target truncation, open
        -- the source box inside it, finish by the others-descent
        by_cases h1 : (itpAoth p S F (c'' + 2) Γ (D.somehow)).isEmpty = true
        · rw [if_pos h1] at hφ; cases hφ
        · rw [if_neg h1] at hφ
          rcases List.mem_singleton.mp hφ with rfl
          refine G4c.orAll_intro
            (φ := ((itpE p S fl c'' Γ).ifThen
              (orAll (itpAoth p S fl (c'' + 1) Γ (D.somehow)))).somehow)
            (List.mem_append.mpr (Or.inr ?_)) ?_
          · rw [if_neg (by
              rw [itpAoth_obGoal_isEmpty]; exact Bool.false_ne_true)]
            exact .head _
          · refine box_open (W := (itpE p S fl c'' Γ).ifThen
                (orAll (itpAoth p S fl (c'' + 1) Γ (D.somehow))))
              (G4c.identity_mem (.head _))
              (amb_down (hamb.weaken _) (by omega) (by omega)) ?_
            refine G4c.laxR (G4c.impR ?_)
            refine hoth _ ?_ (G4c.identity_mem (.tail _ (.head _)))
            exact ((hamb.weaken _).weaken _).weaken _
  | prop q =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))
  | falsePLL =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))
  | and C₁ C₂ =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))
  | or C₁ C₂ =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))
  | ifThen C₁ C₂ =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))

/-! ### The open interfaces

Three branch shapes of the others-descent are not closed by the
mechanisms proved in this file.  Each is stated here as a `Prop`; the
assembly consumes them as hypotheses, so the assembly itself is
sorry-free.  Stub instantiations (clearly marked OPEN) close the file.

* `AmbGuardAscent` — the one-step existential ascent at a fresh space
  piece, *relative to the ambient at the base context*:

      itpE@(c+1)(Γ), itpE@c(X::Γ)  ⊢  itpE@(c+1)(X::Γ).

  This is the fresh-antecedent equality law of PROGRESS §66 (exact on
  every instance of the countermodel battery, unproven).  The bare
  ascent `itpE@c ⊢ itpE@(c+1)` is countermodel-refuted at `c = 1`, so
  the ambient conjunct is essential.  Consumed by the fresh-antecedent
  goal branch, the `∨`-growth pair, and the fresh jump-family pair.

* `GammaPairFloorA` / `GammaPairFloorBox` — the two gated γ-pair
  branches at target budget `1` (source components at budget `1`,
  target components at the floor `0`), where the budget-tier recursion
  would need the descent at target budget `0` — false at `◯`-goals
  (the battery's unique false point).  This is exactly the §73 stuck
  shape; the instances are battery-true (§76: zero failures including
  the growth-live band).

* `JumpPairFloor` — the same floor for the gated jump-family pair
  (`(A⊃B)⊃D ∈ Γ ∩ S` with `B⊃D ∈ Γ`).

Each floor interface receives the grown-context descent at strictly
smaller defect (the defect-tier induction hypothesis) — the resource
§73's candidate mechanism (i) (*commute the growth disjuncts of the
target first*) would consume. -/

/-- OPEN interface: the ambient-relative one-step guard ascent at a
fresh space piece (the fresh-antecedent equality law, §66/§73(ii)). -/
def AmbGuardAscent (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (fl c : Nat) (Γ : List PLLFormula) (X : PLLFormula)
    (Δ : List PLLFormula),
    X ∈ S → X ∉ Γ → (∀ Y ∈ Γ, Y ∈ S) →
    G4c Δ (itpE p S (fl + 1) (c + 1) Γ) →
    G4c (itpE p S fl c (X :: Γ) :: Δ) (itpE p S fl (c + 1) (X :: Γ))

/-- OPEN interface: the plain gated γ-pair branch at the budget floor
(target budget `1`; the pair's first component is the bare universal
value at the γ-head's unboxed goal). -/
def GammaPairFloorA (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (F fl : Nat) (Γ : List PLLFormula) (A B g : PLLFormula)
    (Δ : List PLLFormula),
    F + 1 ≤ fl →
    A.somehow.ifThen B ∈ Γ → A.somehow.ifThen B ∈ S →
    B ∈ S → B ∉ Γ → g ∈ S → (∀ X ∈ Γ, X ∈ S) →
    (∀ (Γ' : List PLLFormula) (g' : PLLFormula) (Δ' : List PLLFormula),
      defect S Γ' < defect S Γ → g' ∈ S → (∀ X ∈ Γ', X ∈ S) →
      G4c Δ' (itpE p S fl 2 Γ') →
      G4c Δ' (itpA p S (F + 1) 2 Γ' g') →
      G4c Δ' (itpA p S fl 1 Γ' g')) →
    G4c Δ (itpE p S (fl + 1) 2 Γ) →
    G4c Δ (itpA p S (F + 1) 1 Γ A) →
    G4c Δ (itpA p S (F + 1) 2 (B :: Γ) g) →
    G4c Δ (orAll (itpAoth p S fl 1 Γ g))

/-- OPEN interface: the boxed gated γ-pair branch at the budget floor
(the §73 stuck shape: target budget `1`, clause-γ head `◯A`, the
target's boxed component sits at budget `0`). -/
def GammaPairFloorBox (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (F fl : Nat) (Γ : List PLLFormula) (A B g : PLLFormula)
    (Δ : List PLLFormula),
    F + 1 ≤ fl →
    A.somehow.ifThen B ∈ Γ → A.somehow.ifThen B ∈ S →
    B ∈ S → B ∉ Γ → g ∈ S → (∀ X ∈ Γ, X ∈ S) →
    (∀ (Γ' : List PLLFormula) (g' : PLLFormula) (Δ' : List PLLFormula),
      defect S Γ' < defect S Γ → g' ∈ S → (∀ X ∈ Γ', X ∈ S) →
      G4c Δ' (itpE p S fl 2 Γ') →
      G4c Δ' (itpA p S (F + 1) 2 Γ' g') →
      G4c Δ' (itpA p S fl 1 Γ' g')) →
    G4c Δ (itpE p S (fl + 1) 2 Γ) →
    G4c Δ (((itpE p S (F + 1) 1 Γ).ifThen
      (itpA p S (F + 1) 1 Γ A.somehow)).somehow) →
    G4c Δ (itpA p S (F + 1) 2 (B :: Γ) g) →
    G4c Δ (orAll (itpAoth p S fl 1 Γ g))

/-- OPEN interface: the gated jump-family pair branch at the budget
floor (target budget `1`, `(A⊃B)⊃D ∈ Γ ∩ S`, `B⊃D ∈ Γ`). -/
def JumpPairFloor (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (F fl : Nat) (Γ : List PLLFormula) (A B D g : PLLFormula)
    (Δ : List PLLFormula),
    F + 1 ≤ fl →
    (A.ifThen B).ifThen D ∈ Γ → (A.ifThen B).ifThen D ∈ S →
    B.ifThen D ∈ Γ → D ∈ S → D ∉ Γ → g ∈ S → (∀ X ∈ Γ, X ∈ S) →
    (∀ (Γ' : List PLLFormula) (g' : PLLFormula) (Δ' : List PLLFormula),
      defect S Γ' < defect S Γ → g' ∈ S → (∀ X ∈ Γ', X ∈ S) →
      G4c Δ' (itpE p S fl 2 Γ') →
      G4c Δ' (itpA p S (F + 1) 2 Γ' g') →
      G4c Δ' (itpA p S fl 1 Γ' g')) →
    G4c Δ (itpE p S (fl + 1) 2 Γ) →
    G4c Δ ((itpE p S (F + 1) 1 Γ).ifThen
      (itpA p S (F + 1) 1 Γ (A.ifThen B))) →
    G4c Δ (itpA p S (F + 1) 2 (D :: Γ) g) →
    G4c Δ (orAll (itpAoth p S fl 1 Γ g))

/-! ### The others-descent (§77): the assembled lexicographic induction

Statement: for a piece-closed space `S`, goal and context inside `S`,

    Δ ⊢ itpE p S (fl+1) (c+1) Γ    (the ambient existential table)
    Δ ⊢ ⋁ itpAoth p S F (c+1) Γ g  (the undecorated source table)
    ────────────────────────────────
    Δ ⊢ ⋁ itpAoth p S fl c Γ g     (the undecorated target table)

for `1 ≤ c` and `F ≤ fl`, by strong induction on the defect, strong
induction on the budget, and structural induction on the source inner
fuel `F`.  At fuel `0` every source component is literally `⊥` or `⊤`
and each branch closes outright (`⊥`-conjunct explosion, guard-fire
into `⊥`, or `box_absurd` against a committed `◯`-target).  At fuel
`F + 1` each branch closes by its §71/§77 mechanism; the three open
interfaces are consumed exactly at the fresh-guard and floor sites. -/
theorem oth_descent (p : String) (S : Finset PLLFormula)
    (hand : ∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S)
    (hor : ∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (hasc : AmbGuardAscent p S)
    (hgfA : GammaPairFloorA p S)
    (hgfB : GammaPairFloorBox p S)
    (hjf : JumpPairFloor p S) :
    ∀ (d c : Nat), 1 ≤ c → ∀ (F : Nat)
    (Γ : List PLLFormula) (fl : Nat) (g : PLLFormula)
    (Δ : List PLLFormula),
    defect S Γ ≤ d → g ∈ S → (∀ X ∈ Γ, X ∈ S) → F ≤ fl →
    G4c Δ (itpE p S (fl + 1) (c + 1) Γ) →
    G4c Δ (orAll (itpAoth p S F (c + 1) Γ g)) →
    G4c Δ (orAll (itpAoth p S fl c Γ g)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
  intro hc F
  induction F with
  | zero =>
      intro Γ fl g Δ hd hgS hΓS hF hamb hsrc
      obtain ⟨c'', rfl⟩ : ∃ c'', c = c'' + 1 := ⟨c - 1, by omega⟩
      refine G4c.cut hsrc (G4c.orAll_elim ?_)
      intro φ hφ
      simp only [itpAoth] at hφ
      rcases List.mem_append.mp hφ with hφ | hφ
      · -- goal-directed disjuncts at inner fuel 0
        cases g with
        | prop q =>
            simp only [itpAgoal] at hφ
            split at hφ
            next => cases hφ
            next hq =>
              rcases List.mem_singleton.mp hφ with rfl
              refine G4c.orAll_intro (φ := prop q) ?_ (G4c.init (.head _))
              simp only [itpAoth, itpAgoal]
              refine List.mem_append.mpr (Or.inl ?_)
              rw [if_neg hq]
              exact .head _
        | falsePLL => simp only [itpAgoal] at hφ; cases hφ
        | and C₁ C₂ =>
            simp only [itpAgoal] at hφ
            rcases List.mem_singleton.mp hφ with rfl
            exact G4c.andL (List.Perm.refl _) (G4c.botL (.head _))
        | or C₁ C₂ =>
            simp only [itpAgoal] at hφ
            rcases List.mem_cons.mp hφ with rfl | hφ'
            · exact G4c.botL (.head _)
            · rcases List.mem_singleton.mp hφ' with rfl
              exact G4c.botL (.head _)
        | ifThen C₁ C₂ =>
            simp only [itpAgoal] at hφ
            split at hφ
            next hpres =>
              rcases List.mem_singleton.mp hφ with rfl
              exact G4c.cut (fire (G4c.identity_mem (.head _))
                (G4c.truePLL_intro _)) (G4c.botL (.head _))
            next hpres =>
              rcases List.mem_singleton.mp hφ with rfl
              exact G4c.cut (fire (G4c.identity_mem (.head _))
                (G4c.truePLL_intro _)) (G4c.botL (.head _))
        | somehow D =>
            simp only [itpAgoal] at hφ
            rcases List.mem_singleton.mp hφ with rfl
            refine G4c.orAll_intro
              (φ := ((itpE p S fl c'' Γ).ifThen
                (itpA p S fl (c'' + 1) Γ D)).somehow) ?_ ?_
            · simp only [itpAoth, itpAgoal]
              exact List.mem_append.mpr (Or.inl (.head _))
            · exact box_absurd _ (G4c.identity_mem (.head _))
                (G4c.truePLL_intro _)
      · -- context-directed disjuncts at inner fuel 0
        obtain ⟨F', hF'Γ, hin⟩ := List.mem_flatMap.mp hφ
        cases F' with
        | prop q =>
            simp only at hin
            split at hin
            next hq =>
              rcases List.mem_singleton.mp hin with rfl
              refine G4c.orAll_intro (φ := truePLL) ?_ (G4c.truePLL_intro _)
              simp only [itpAoth]
              refine List.mem_append.mpr (Or.inr ?_)
              simp only [itpAenv]
              refine List.mem_flatMap.mpr ⟨prop q, hF'Γ, ?_⟩
              simp only
              rw [if_pos hq]
              exact .head _
            next => cases hin
        | falsePLL => cases hin
        | and A B =>
            simp only at hin
            split at hin
            next => cases hin
            next h1 =>
              split at hin
              next h2 =>
                rcases List.mem_singleton.mp hin with rfl
                exact G4c.botL (.head _)
              next => cases hin
        | or A B =>
            simp only at hin
            split at hin
            next => cases hin
            next h1 =>
              split at hin
              next h2 =>
                rcases List.mem_singleton.mp hin with rfl
                refine G4c.andL (List.Perm.refl _) ?_
                exact G4c.cut (fire (G4c.identity_mem (.head _))
                  (G4c.truePLL_intro _)) (G4c.botL (.head _))
              next => cases hin
        | somehow χ =>
            cases g with
            | somehow D =>
                simp only at hin
                split at hin
                next => cases hin
                next hcond =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4c.orAll_intro
                    (φ := ((itpE p S fl (c'' + 1) (χ :: Γ)).ifThen
                      (itpA p S fl (c'' + 1) (χ :: Γ) (D.somehow))).somehow)
                    ?_ ?_
                  · simp only [itpAoth]
                    refine List.mem_append.mpr (Or.inr ?_)
                    simp only [itpAenv]
                    refine List.mem_flatMap.mpr ⟨χ.somehow, hF'Γ, ?_⟩
                    simp only
                    rw [if_neg hcond]
                    exact .head _
                  · exact box_absurd _ (G4c.identity_mem (.head _))
                      (G4c.truePLL_intro _)
            | prop _ => cases hin
            | falsePLL => cases hin
            | and _ _ => cases hin
            | or _ _ => cases hin
            | ifThen _ _ => cases hin
        | ifThen A' B =>
            cases A' with
            | prop q =>
                simp only at hin
                split at hin
                next => cases hin
                next hBΓ =>
                  split at hin
                  next hBS =>
                    split at hin
                    next hq =>
                      rcases List.mem_singleton.mp hin with rfl
                      exact G4c.botL (.head _)
                    next hq =>
                      split at hin
                      next => cases hin
                      next hqp =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine G4c.andL (List.Perm.refl _) ?_
                        exact G4c.botL (.tail _ (.head _))
                  next => cases hin
            | falsePLL => cases hin
            | and A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_singleton.mp hin with rfl
                    exact G4c.botL (.head _)
                  next => cases hin
            | or A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_singleton.mp hin with rfl
                    exact G4c.botL (.head _)
                  next => cases hin
            | ifThen A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next hDΓ =>
                  split at hin
                  next hDS =>
                    split at hin
                    next hBD =>
                      split at hin
                      next hABS =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine G4c.andL (List.Perm.refl _) ?_
                        exact G4c.botL (.tail _ (.head _))
                      next => cases hin
                    next hBD =>
                      split at hin
                      next hBDS =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine G4c.andL (List.Perm.refl _) ?_
                        exact G4c.botL (.tail _ (.head _))
                      next => cases hin
                  next => cases hin
            | somehow A₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next hBΓ =>
                  split at hin
                  next hBS =>
                    rcases List.mem_append.mp hin with hin | hin
                    · split at hin
                      next hγS =>
                        rcases List.mem_cons.mp hin with rfl | hin'
                        · exact G4c.andL (List.Perm.refl _)
                            (G4c.botL (.head _))
                        · rcases List.mem_singleton.mp hin' with rfl
                          refine G4c.andL (List.Perm.refl _) ?_
                          exact G4c.botL (.tail _ (.head _))
                      next => cases hin
                    · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                      cases X with
                      | somehow x =>
                          simp only at heq
                          split at heq
                          next => cases heq
                          next hxc =>
                            injection heq with heq'
                            subst heq'
                            refine G4c.andL (List.Perm.refl _) ?_
                            exact G4c.botL (.tail _ (.head _))
                      | prop _ => cases heq
                      | falsePLL => cases heq
                      | and _ _ => cases heq
                      | or _ _ => cases heq
                      | ifThen _ _ => cases heq
                  next => cases hin
  | succ F ihF =>
      intro Γ fl g Δ hd hgS hΓS hF hamb hsrc
      obtain ⟨c'', rfl⟩ : ∃ c'', c = c'' + 1 := ⟨c - 1, by omega⟩
      obtain ⟨fl', rfl⟩ : ∃ fl', fl = fl' + 1 := ⟨fl - 1, by omega⟩
      have hSor : ∀ {X : PLLFormula}, X ∈ Γ ∨ X ∈ S → X ∈ S :=
        fun h => h.elim (fun h' => hΓS _ h') id
      have hScons : ∀ {X : PLLFormula}, X ∈ S → ∀ Y ∈ X :: Γ, Y ∈ S := by
        intro X hX Y hY
        rcases List.mem_cons.mp hY with rfl | hY
        · exact hX
        · exact hΓS _ hY
      -- the head-fuel descent (the fuel induction through the wrapper)
      have hdesc : ∀ (Γ' : List PLLFormula) (g' : PLLFormula)
          (Δ' : List PLLFormula), defect S Γ' ≤ d → g' ∈ S →
          (∀ X ∈ Γ', X ∈ S) →
          G4c Δ' (itpE p S (fl' + 1) (c'' + 2) Γ') →
          G4c Δ' (itpA p S (F + 1) (c'' + 2) Γ' g') →
          G4c Δ' (itpA p S (fl' + 1) (c'' + 1) Γ' g') :=
        fun Γ' g' Δ' hd' hg' hΓ' ha hh =>
          desc_of_oth p S (by omega) (by omega)
            (fun Δ'' a b => ihF Γ' fl' g' Δ'' hd' hg' hΓ' (by omega) a b)
            ha hh
      -- the grown-context descent (the defect tier)
      have hgrown : ∀ (Γ' : List PLLFormula) (g' : PLLFormula)
          (Δ' : List PLLFormula), defect S Γ' < defect S Γ → g' ∈ S →
          (∀ X ∈ Γ', X ∈ S) →
          G4c Δ' (itpE p S (fl' + 1) (c'' + 2) Γ') →
          G4c Δ' (itpA p S (F + 1) (c'' + 2) Γ' g') →
          G4c Δ' (itpA p S (fl' + 1) (c'' + 1) Γ' g') :=
        fun Γ' g' Δ' hlt hg' hΓ' ha hh =>
          desc_of_oth p S (by omega) (by omega)
            (fun Δ'' a b => ihd (defect S Γ') (by omega) (c'' + 1)
              (by omega) F Γ' fl' g' Δ'' (Nat.le_refl _) hg' hΓ'
              (by omega) a b) ha hh
      -- the budget-tier descent (the gated first components, `c'' ≥ 1`)
      have hdescB : ∀ (c₃ : Nat), c'' = c₃ + 1 → ∀ (g' : PLLFormula)
          (Δ' : List PLLFormula), g' ∈ S →
          G4c Δ' (itpE p S (fl' + 1) (c'' + 1) Γ) →
          G4c Δ' (itpA p S (F + 1) (c'' + 1) Γ g') →
          G4c Δ' (itpA p S (fl' + 1) c'' Γ g') := by
        rintro c₃ rfl g' Δ' hg' ha hh
        exact desc_of_oth p S (by omega) (by omega)
          (fun Δ'' a b => ihc (c₃ + 1) (by omega) (by omega) F Γ fl' g'
            Δ'' hd hg' hΓS (by omega) a b) ha hh
      refine G4c.cut hsrc (G4c.orAll_elim ?_)
      intro φ hφ
      simp only [itpAoth] at hφ
      rcases List.mem_append.mp hφ with hφ | hφ
      · -- goal-directed disjuncts
        cases g with
        | prop q =>
            simp only [itpAgoal] at hφ
            split at hφ
            next => cases hφ
            next hq =>
              rcases List.mem_singleton.mp hφ with rfl
              refine G4c.orAll_intro (φ := prop q) ?_ (G4c.init (.head _))
              simp only [itpAoth, itpAgoal]
              refine List.mem_append.mpr (Or.inl ?_)
              rw [if_neg hq]
              exact .head _
        | falsePLL => simp only [itpAgoal] at hφ; cases hφ
        | and C₁ C₂ =>
            simp only [itpAgoal] at hφ
            rcases List.mem_singleton.mp hφ with rfl
            refine G4c.andL (List.Perm.refl _) ?_
            refine G4c.orAll_intro
              (φ := (itpA p S (fl' + 1) (c'' + 1) Γ C₁).and
                (itpA p S (fl' + 1) (c'' + 1) Γ C₂)) ?_ (G4c.andR ?_ ?_)
            · simp only [itpAoth, itpAgoal]
              exact List.mem_append.mpr (Or.inl (.head _))
            · exact hdesc Γ C₁ _ hd (hand hgS).1 hΓS
                (wksub (fun ψ h => .tail _ (.tail _ h))
                  (amb_down hamb (by omega) (Nat.le_refl _)))
                (G4c.identity_mem (.head _))
            · exact hdesc Γ C₂ _ hd (hand hgS).2 hΓS
                (wksub (fun ψ h => .tail _ (.tail _ h))
                  (amb_down hamb (by omega) (Nat.le_refl _)))
                (G4c.identity_mem (.tail _ (.head _)))
        | or C₁ C₂ =>
            simp only [itpAgoal] at hφ
            rcases List.mem_cons.mp hφ with rfl | hφ'
            · refine G4c.orAll_intro
                (φ := itpA p S (fl' + 1) (c'' + 1) Γ C₁) ?_ ?_
              · simp only [itpAoth, itpAgoal]
                exact List.mem_append.mpr (Or.inl (.head _))
              · exact hdesc Γ C₁ _ hd (hor hgS).1 hΓS
                  ((amb_down hamb (by omega) (Nat.le_refl _)).weaken _)
                  (G4c.identity_mem (.head _))
            · rcases List.mem_singleton.mp hφ' with rfl
              refine G4c.orAll_intro
                (φ := itpA p S (fl' + 1) (c'' + 1) Γ C₂) ?_ ?_
              · simp only [itpAoth, itpAgoal]
                exact List.mem_append.mpr (Or.inl (.tail _ (.head _)))
              · exact hdesc Γ C₂ _ hd (hor hgS).2 hΓS
                  ((amb_down hamb (by omega) (Nat.le_refl _)).weaken _)
                  (G4c.identity_mem (.head _))
        | ifThen C₁ C₂ =>
            simp only [itpAgoal] at hφ
            split at hφ
            next hpres =>
              -- present antecedent: head-fuel descent at the set-equal
              -- grown context, guard from the ambient by congruence
              rcases List.mem_singleton.mp hφ with rfl
              have hdef : defect S (C₁ :: Γ) = defect S Γ :=
                defect_cons_eq hpres
              refine G4c.orAll_intro
                (φ := (itpE p S (fl' + 1) c'' (C₁ :: Γ)).ifThen
                  (itpA p S (fl' + 1) (c'' + 1) (C₁ :: Γ) C₂)) ?_
                (G4c.impR ?_)
              · simp only [itpAoth, itpAgoal]
                refine List.mem_append.mpr (Or.inl ?_)
                rw [if_pos hpres]
                exact .head _
              · have haC : G4c (itpE p S (fl' + 1) c'' (C₁ :: Γ) ::
                    ((itpE p S (F + 1) (c'' + 1) (C₁ :: Γ)).ifThen
                      (itpA p S (F + 1) (c'' + 2) (C₁ :: Γ) C₂)) :: Δ)
                    (itpE p S (fl' + 1) (c'' + 2) (C₁ :: Γ)) :=
                  amb_congr (wksub (fun ψ h => .tail _ (.tail _ h))
                    (amb_down (f' := fl' + 1) hamb (by omega)
                      (Nat.le_refl _))) hpres
                refine hdesc (C₁ :: Γ) C₂ _ (by rw [hdef]; exact hd)
                  (himp hgS).2 (hScons (hΓS _ hpres)) haC
                  (fire (G4c.identity_mem (.tail _ (.head _)))
                    (amb_down (f' := F + 1) (b' := c'' + 1) haC (by omega)
                      (by omega)))
            next hpres =>
              -- fresh antecedent: the guard ascent at the fresh piece
              -- (OPEN interface), then the defect tier
              rcases List.mem_singleton.mp hφ with rfl
              have hC₁S : C₁ ∈ S := (himp hgS).1
              have hlt : defect S (C₁ :: Γ) < defect S Γ :=
                defect_cons_lt hC₁S hpres
              refine G4c.orAll_intro
                (φ := (itpE p S (fl' + 1) (c'' + 1) (C₁ :: Γ)).ifThen
                  (itpA p S (fl' + 1) (c'' + 1) (C₁ :: Γ) C₂)) ?_
                (G4c.impR ?_)
              · simp only [itpAoth, itpAgoal]
                refine List.mem_append.mpr (Or.inl ?_)
                rw [if_neg hpres]
                exact .head _
              · have hE2 := hasc (fl' + 1) (c'' + 1) Γ C₁
                  (((itpE p S (F + 1) (c'' + 2) (C₁ :: Γ)).ifThen
                    (itpA p S (F + 1) (c'' + 2) (C₁ :: Γ) C₂)) :: Δ)
                  hC₁S hpres hΓS (hamb.weaken _)
                refine hgrown (C₁ :: Γ) C₂ _ hlt (himp hgS).2 (hScons hC₁S)
                  hE2 (fire (G4c.identity_mem (.tail _ (.head _)))
                    (amb_down (f' := F + 1) hE2 (by omega) (Nat.le_refl _)))
        | somehow D =>
            -- the goal clause of a ◯-goal: same-budget remap, value by
            -- the head-fuel descent at the unboxed goal
            simp only [itpAgoal] at hφ
            rcases List.mem_singleton.mp hφ with rfl
            refine G4c.orAll_intro
              (φ := ((itpE p S (fl' + 1) c'' Γ).ifThen
                (itpA p S (fl' + 1) (c'' + 1) Γ D)).somehow) ?_ ?_
            · simp only [itpAoth, itpAgoal]
              exact List.mem_append.mpr (Or.inl (.head _))
            · refine box_remap_free (G4c.identity_mem (.head _)) ?_ ?_
              · exact amb_down (wksub (fun ψ h => .tail _ (.tail _ h)) hamb)
                  (by omega) (by omega)
              · refine hdesc Γ D _ hd (hsome hgS) hΓS ?_
                  (G4c.identity_mem (.head _))
                exact amb_down (wksub (fun ψ h =>
                  .tail _ (.tail _ (.tail _ h))) hamb) (by omega)
                  (Nat.le_refl _)
      · -- context-directed disjuncts
        obtain ⟨F', hF'Γ, hin⟩ := List.mem_flatMap.mp hφ
        cases F' with
        | prop q =>
            simp only at hin
            split at hin
            next hq =>
              rcases List.mem_singleton.mp hin with rfl
              refine G4c.orAll_intro (φ := truePLL) ?_ (G4c.truePLL_intro _)
              simp only [itpAoth]
              refine List.mem_append.mpr (Or.inr ?_)
              simp only [itpAenv]
              refine List.mem_flatMap.mpr ⟨prop q, hF'Γ, ?_⟩
              simp only
              rw [if_pos hq]
              exact .head _
            next => cases hin
        | falsePLL => cases hin
        | and A B =>
            simp only at hin
            split at hin
            next => cases hin
            next h1 =>
              split at hin
              next h2 =>
                rcases List.mem_singleton.mp hin with rfl
                have hlt : defect S (A :: B :: Γ) < defect S Γ := by
                  by_cases hA : A ∈ Γ
                  · have hB : B ∉ Γ := fun hB => h1 ⟨hA, hB⟩
                    exact defect_lt_of_mem (Γ' := A :: B :: Γ)
                      (by intro y hy; simp only [List.toFinset_cons,
                        Finset.mem_insert]; exact Or.inr (Or.inr hy))
                      (h2.2.resolve_left hB) hB (.tail _ (.head _))
                  · exact defect_lt_of_mem (Γ' := A :: B :: Γ)
                      (by intro y hy; simp only [List.toFinset_cons,
                        Finset.mem_insert]; exact Or.inr (Or.inr hy))
                      (h2.1.resolve_left hA) hA (.head _)
                refine G4c.orAll_intro
                  (φ := itpA p S (fl' + 1) (c'' + 1) (A :: B :: Γ) g) ?_ ?_
                · simp only [itpAoth]
                  refine List.mem_append.mpr (Or.inr ?_)
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨A.and B, hF'Γ, ?_⟩
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                · refine hgrown (A :: B :: Γ) g _ hlt hgS (by
                      intro Y hY
                      rcases List.mem_cons.mp hY with rfl | hY
                      · exact hSor h2.1
                      · rcases List.mem_cons.mp hY with rfl | hY
                        · exact hSor h2.2
                        · exact hΓS _ hY) ?_
                    (G4c.identity_mem (.head _))
                  refine projE (l := itpEcls p S (fl' + 1) (c'' + 2) Γ)
                    (hamb.weaken _) ?_
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr
                    (List.mem_flatMap.mpr ⟨A.and B, hF'Γ, ?_⟩))
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
              next => cases hin
        | or A B =>
            simp only at hin
            split at hin
            next => cases hin
            next h1 =>
              split at hin
              next h2 =>
                rcases List.mem_singleton.mp hin with rfl
                have hA : A ∉ Γ := fun h => h1 (Or.inl h)
                have hB : B ∉ Γ := fun h => h1 (Or.inr h)
                refine G4c.orAll_intro
                  (φ := ((itpE p S (fl' + 1) (c'' + 1) (A :: Γ)).ifThen
                      (itpA p S (fl' + 1) (c'' + 1) (A :: Γ) g)).and
                    ((itpE p S (fl' + 1) (c'' + 1) (B :: Γ)).ifThen
                      (itpA p S (fl' + 1) (c'' + 1) (B :: Γ) g))) ?_ ?_
                · simp only [itpAoth]
                  refine List.mem_append.mpr (Or.inr ?_)
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨A.or B, hF'Γ, ?_⟩
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                · refine G4c.andL (List.Perm.refl _) (G4c.andR ?_ ?_)
                  · refine G4c.impR ?_
                    have hE2 := hasc (fl' + 1) (c'' + 1) Γ A
                      (((itpE p S (F + 1) (c'' + 2) (A :: Γ)).ifThen
                          (itpA p S (F + 1) (c'' + 2) (A :: Γ) g)) ::
                        ((itpE p S (F + 1) (c'' + 2) (B :: Γ)).ifThen
                          (itpA p S (F + 1) (c'' + 2) (B :: Γ) g)) :: Δ)
                      h2.1 hA hΓS
                      (wksub (fun ψ h => .tail _ (.tail _ h)) hamb)
                    refine hgrown (A :: Γ) g _ (defect_cons_lt h2.1 hA) hgS
                      (hScons h2.1) hE2
                      (fire (G4c.identity_mem (.tail _ (.head _)))
                        (amb_down (f' := F + 1) hE2 (by omega) (Nat.le_refl _)))
                  · refine G4c.impR ?_
                    have hE2 := hasc (fl' + 1) (c'' + 1) Γ B
                      (((itpE p S (F + 1) (c'' + 2) (A :: Γ)).ifThen
                          (itpA p S (F + 1) (c'' + 2) (A :: Γ) g)) ::
                        ((itpE p S (F + 1) (c'' + 2) (B :: Γ)).ifThen
                          (itpA p S (F + 1) (c'' + 2) (B :: Γ) g)) :: Δ)
                      h2.2 hB hΓS
                      (wksub (fun ψ h => .tail _ (.tail _ h)) hamb)
                    refine hgrown (B :: Γ) g _ (defect_cons_lt h2.2 hB) hgS
                      (hScons h2.2) hE2
                      (fire (G4c.identity_mem (.tail _ (.tail _ (.head _))))
                        (amb_down (f' := F + 1) hE2 (by omega) (Nat.le_refl _)))
              next => cases hin
        | somehow χ =>
            cases g with
            | somehow D =>
                simp only at hin
                split at hin
                next => cases hin
                next hcond =>
                  rcases List.mem_singleton.mp hin with rfl
                  have hχΓ : χ ∉ Γ := fun h => hcond (Or.inl h)
                  have hχS : χ ∈ S := by
                    by_contra h
                    exact hcond (Or.inr h)
                  refine G4c.orAll_intro
                    (φ := ((itpE p S (fl' + 1) (c'' + 1) (χ :: Γ)).ifThen
                      (itpA p S (fl' + 1) (c'' + 1) (χ :: Γ)
                        (D.somehow))).somehow) ?_ ?_
                  · simp only [itpAoth]
                    refine List.mem_append.mpr (Or.inr ?_)
                    simp only [itpAenv]
                    refine List.mem_flatMap.mpr ⟨χ.somehow, hF'Γ, ?_⟩
                    simp only
                    rw [if_neg hcond]
                    exact .head _
                  · -- open the ambient's bare ◯χ-conjunct against the
                    -- committed target box, then remap the source box
                    refine box_elim
                      (X := itpE p S (fl' + 1) (c'' + 2) (χ :: Γ)) ?_ ?_
                    · refine projE (l := itpEcls p S (fl' + 1) (c'' + 2) Γ)
                        (hamb.weaken _) ?_
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr ⟨χ.somehow, hF'Γ, ?_⟩))
                      simp only
                      rw [if_neg hcond]
                      exact .head _
                    · refine box_remap_free
                        (G4c.identity_mem (.tail _ (.head _))) ?_ ?_
                      · exact amb_down (G4c.identity_mem (.tail _ (.head _)))
                          (by omega) (Nat.le_refl _)
                      · refine hgrown (χ :: Γ) (D.somehow) _
                          (defect_cons_lt hχS hχΓ) hgS (hScons hχS) ?_
                          (G4c.identity_mem (.head _))
                        exact G4c.identity_mem
                          (.tail _ (.tail _ (.head _)))
            | prop _ => cases hin
            | falsePLL => cases hin
            | and _ _ => cases hin
            | or _ _ => cases hin
            | ifThen _ _ => cases hin
        | ifThen A' B =>
            cases A' with
            | prop q =>
                simp only at hin
                split at hin
                next => cases hin
                next hBΓ =>
                  split at hin
                  next hBS =>
                    split at hin
                    next hq =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine G4c.orAll_intro
                        (φ := itpA p S (fl' + 1) (c'' + 1) (B :: Γ) g) ?_ ?_
                      · simp only [itpAoth]
                        refine List.mem_append.mpr (Or.inr ?_)
                        simp only [itpAenv]
                        refine List.mem_flatMap.mpr
                          ⟨(prop q).ifThen B, hF'Γ, ?_⟩
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                        exact .head _
                      · refine hgrown (B :: Γ) g _
                          (defect_cons_lt hBS hBΓ) hgS (hScons hBS) ?_
                          (G4c.identity_mem (.head _))
                        refine projE
                          (l := itpEcls p S (fl' + 1) (c'' + 2) Γ)
                          (hamb.weaken _) ?_
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr
                          (List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hF'Γ, ?_⟩))
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                        exact .head _
                    next hq =>
                      split at hin
                      next => cases hin
                      next hqp =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine G4c.andL (List.Perm.refl _) ?_
                        refine G4c.orAll_intro
                          (φ := (prop q).and
                            (itpA p S (fl' + 1) (c'' + 1) (B :: Γ) g)) ?_
                          (G4c.andR (G4c.init (.head _)) ?_)
                        · simp only [itpAoth]
                          refine List.mem_append.mpr (Or.inr ?_)
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hF'Γ, ?_⟩
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                          exact .head _
                        · refine hgrown (B :: Γ) g _
                            (defect_cons_lt hBS hBΓ) hgS (hScons hBS) ?_
                            (G4c.identity_mem (.tail _ (.head _)))
                          refine fire (projE
                            (l := itpEcls p S (fl' + 1) (c'' + 2) Γ)
                            (wksub (fun ψ h => .tail _ (.tail _ h)) hamb)
                            ?_) (G4c.init (.head _))
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(prop q).ifThen B, hF'Γ, ?_⟩))
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                          exact .head _
                  next => cases hin
            | falsePLL => cases hin
            | and A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_singleton.mp hin with rfl
                    refine G4c.orAll_intro
                      (φ := itpA p S (fl' + 1) (c'' + 1)
                        (A₁.ifThen (B₁.ifThen B) :: Γ) g) ?_ ?_
                    · simp only [itpAoth]
                      refine List.mem_append.mpr (Or.inr ?_)
                      simp only [itpAenv]
                      refine List.mem_flatMap.mpr
                        ⟨(A₁.and B₁).ifThen B, hF'Γ, ?_⟩
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    · refine hgrown _ g _ (defect_cons_lt h2 h1) hgS
                        (hScons h2) ?_ (G4c.identity_mem (.head _))
                      refine projE (l := itpEcls p S (fl' + 1) (c'' + 2) Γ)
                        (hamb.weaken _) ?_
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr
                          ⟨(A₁.and B₁).ifThen B, hF'Γ, ?_⟩))
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                  next => cases hin
            | or A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_singleton.mp hin with rfl
                    have hlt : defect S (A₁.ifThen B :: B₁.ifThen B :: Γ) <
                        defect S Γ := by
                      by_cases hA : A₁.ifThen B ∈ Γ
                      · have hBn : B₁.ifThen B ∉ Γ := fun hB => h1 ⟨hA, hB⟩
                        exact defect_lt_of_mem
                          (Γ' := A₁.ifThen B :: B₁.ifThen B :: Γ)
                          (by intro y hy; simp only [List.toFinset_cons,
                            Finset.mem_insert]; exact Or.inr (Or.inr hy))
                          (h2.2.resolve_left hBn) hBn (.tail _ (.head _))
                      · exact defect_lt_of_mem
                          (Γ' := A₁.ifThen B :: B₁.ifThen B :: Γ)
                          (by intro y hy; simp only [List.toFinset_cons,
                            Finset.mem_insert]; exact Or.inr (Or.inr hy))
                          (h2.1.resolve_left hA) hA (.head _)
                    refine G4c.orAll_intro
                      (φ := itpA p S (fl' + 1) (c'' + 1)
                        (A₁.ifThen B :: B₁.ifThen B :: Γ) g) ?_ ?_
                    · simp only [itpAoth]
                      refine List.mem_append.mpr (Or.inr ?_)
                      simp only [itpAenv]
                      refine List.mem_flatMap.mpr
                        ⟨(A₁.or B₁).ifThen B, hF'Γ, ?_⟩
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    · refine hgrown _ g _ hlt hgS (by
                          intro Y hY
                          rcases List.mem_cons.mp hY with rfl | hY
                          · exact hSor h2.1
                          · rcases List.mem_cons.mp hY with rfl | hY
                            · exact hSor h2.2
                            · exact hΓS _ hY) ?_
                        (G4c.identity_mem (.head _))
                      refine projE (l := itpEcls p S (fl' + 1) (c'' + 2) Γ)
                        (hamb.weaken _) ?_
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr
                          ⟨(A₁.or B₁).ifThen B, hF'Γ, ?_⟩))
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                  next => cases hin
            | ifThen A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next hDΓ =>
                  split at hin
                  next hDS =>
                    split at hin
                    next hBD =>
                      split at hin
                      next hABS =>
                        -- the gated jump-family pair
                        rcases List.mem_singleton.mp hin with rfl
                        refine G4c.andL (List.Perm.refl _) ?_
                        cases c'' with
                        | zero =>
                            exact hjf F (fl' + 1) Γ A₁ B₁ B g _ (by omega)
                              hF'Γ (hΓS _ hF'Γ) hBD hDS hDΓ hgS hΓS hgrown
                              (wksub (fun ψ h => .tail _ (.tail _ h)) hamb)
                              (G4c.identity_mem (.head _))
                              (G4c.identity_mem (.tail _ (.head _)))
                        | succ c₃ =>
                            refine G4c.orAll_intro
                              (φ := ((itpE p S (fl' + 1) (c₃ + 1) Γ).ifThen
                                  (itpA p S (fl' + 1) (c₃ + 1) Γ
                                    (A₁.ifThen B₁))).and
                                (itpA p S (fl' + 1) (c₃ + 2) (B :: Γ) g)) ?_
                              (G4c.andR ?_ ?_)
                            · simp only [itpAoth]
                              refine List.mem_append.mpr (Or.inr ?_)
                              simp only [itpAenv]
                              refine List.mem_flatMap.mpr
                                ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩
                              simp only
                              rw [if_neg hDΓ, if_pos hDS, if_pos hBD,
                                if_pos hABS]
                              exact .head _
                            · -- first component: the budget tier
                              refine G4c.impR ?_
                              refine hdescB c₃ rfl (A₁.ifThen B₁) _
                                (himp hABS).1 ?_ ?_
                              · exact amb_down (wksub (fun ψ h =>
                                  .tail _ (.tail _ (.tail _ h))) hamb)
                                  (by omega) (by omega)
                              · exact fire
                                  (G4c.identity_mem (.tail _ (.head _)))
                                  (amb_down (f' := F + 1) (b' := c₃ + 2)
                                    (wksub (fun ψ h =>
                                      .tail _ (.tail _ (.tail _ h))) hamb)
                                    (by omega) (by omega))
                            · -- second component: growth; the grown ambient
                              -- is unlocked by firing the ambient's jump
                              -- conjunct with the fuel-lifted component
                              refine hgrown (B :: Γ) g _
                                (defect_cons_lt hDS hDΓ) hgS (hScons hDS)
                                ?_ (G4c.identity_mem (.tail _ (.head _)))
                              refine fire (projE
                                (l := itpEcls p S (fl' + 1) (c₃ + 3) Γ)
                                (wksub (fun ψ h => .tail _ (.tail _ h))
                                  hamb) ?_)
                                (imp_fuel_lift (by omega)
                                  (G4c.identity_mem (.head _)))
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩))
                              simp only
                              rw [if_neg hDΓ, if_pos hDS, if_pos hBD,
                                if_pos hABS]
                              exact .head _
                      next => cases hin
                    next hBD =>
                      split at hin
                      next hBDS =>
                        -- the fresh jump-family pair
                        rcases List.mem_singleton.mp hin with rfl
                        refine G4c.andL (List.Perm.refl _) ?_
                        refine G4c.orAll_intro
                          (φ := ((itpE p S (fl' + 1) (c'' + 1)
                              (B₁.ifThen B :: Γ)).ifThen
                              (itpA p S (fl' + 1) (c'' + 1)
                                (B₁.ifThen B :: Γ) (A₁.ifThen B₁))).and
                            (itpA p S (fl' + 1) (c'' + 1) (B :: Γ) g)) ?_
                          (G4c.andR ?_ ?_)
                        · simp only [itpAoth]
                          refine List.mem_append.mpr (Or.inr ?_)
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩
                          simp only
                          rw [if_neg hDΓ, if_pos hDS, if_neg hBD,
                            if_pos hBDS]
                          exact .head _
                        · -- first component: fresh-guard ascent (OPEN
                          -- interface) + defect tier
                          refine G4c.impR ?_
                          have hE2 := hasc (fl' + 1) (c'' + 1) Γ
                            (B₁.ifThen B)
                            (((itpE p S (F + 1) (c'' + 2)
                                (B₁.ifThen B :: Γ)).ifThen
                              (itpA p S (F + 1) (c'' + 2)
                                (B₁.ifThen B :: Γ) (A₁.ifThen B₁))) ::
                              (itpA p S (F + 1) (c'' + 2) (B :: Γ) g) :: Δ)
                            hBDS hBD hΓS
                            (wksub (fun ψ h => .tail _ (.tail _ h)) hamb)
                          refine hgrown (B₁.ifThen B :: Γ) (A₁.ifThen B₁) _
                            (defect_cons_lt hBDS hBD)
                            (himp (hΓS _ hF'Γ)).1 (hScons hBDS) hE2
                            (fire (G4c.identity_mem (.tail _ (.head _)))
                              (amb_down (f' := F + 1) hE2 (by omega) (Nat.le_refl _)))
                        · -- second component: growth; unlock by the
                          -- fuel-lifted first component
                          refine hgrown (B :: Γ) g _
                            (defect_cons_lt hDS hDΓ) hgS (hScons hDS) ?_
                            (G4c.identity_mem (.tail _ (.head _)))
                          refine fire (projE
                            (l := itpEcls p S (fl' + 1) (c'' + 2) Γ)
                            (wksub (fun ψ h => .tail _ (.tail _ h)) hamb)
                            ?_) (imp_fuel_lift (by omega)
                              (G4c.identity_mem (.head _)))
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hF'Γ, ?_⟩))
                          simp only
                          rw [if_neg hDΓ, if_pos hDS, if_neg hBD,
                            if_pos hBDS]
                          exact .head _
                      next => cases hin
                  next => cases hin
            | somehow A₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next hBΓ =>
                  split at hin
                  next hBS =>
                    rcases List.mem_append.mp hin with hin | hin
                    · -- the gated γ-pair disjuncts
                      split at hin
                      next hγS =>
                        rcases List.mem_cons.mp hin with rfl | hin'
                        · -- the plain pair
                          refine G4c.andL (List.Perm.refl _) ?_
                          cases c'' with
                          | zero =>
                              exact hgfA F (fl' + 1) Γ A₁ B g _ (by omega)
                                hF'Γ hγS hBS hBΓ hgS hΓS hgrown
                                (wksub (fun ψ h => .tail _ (.tail _ h))
                                  hamb)
                                (G4c.identity_mem (.head _))
                                (G4c.identity_mem (.tail _ (.head _)))
                          | succ c₃ =>
                              refine G4c.orAll_intro
                                (φ := (itpA p S (fl' + 1) (c₃ + 1) Γ
                                    A₁).and
                                  (itpA p S (fl' + 1) (c₃ + 2) (B :: Γ) g))
                                ?_ (G4c.andR ?_ ?_)
                              · simp only [itpAoth]
                                refine List.mem_append.mpr (Or.inr ?_)
                                simp only [itpAenv]
                                refine List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩
                                simp only
                                rw [if_neg hBΓ, if_pos hBS]
                                refine List.mem_append.mpr (Or.inl ?_)
                                rw [if_pos hγS]
                                exact .head _
                              · -- first component: the budget tier
                                refine hdescB c₃ rfl A₁ _
                                  (hsome (himp hγS).1) ?_
                                  (G4c.identity_mem (.head _))
                                exact amb_down (wksub (fun ψ h =>
                                  .tail _ (.tail _ h)) hamb) (by omega)
                                  (by omega)
                              · -- second component: growth; unlock by the
                                -- fuel-lifted plain component
                                refine hgrown (B :: Γ) g _
                                  (defect_cons_lt hBS hBΓ) hgS
                                  (hScons hBS) ?_
                                  (G4c.identity_mem (.tail _ (.head _)))
                                refine fire
                                  (X := itpA p S (fl' + 1) (c₃ + 2) Γ A₁)
                                  (projE
                                  (l := itpEcls p S (fl' + 1) (c₃ + 3) Γ)
                                  (wksub (fun ψ h => .tail _ (.tail _ h))
                                    hamb) ?_) ?_
                                · simp only [itpEcls]
                                  refine List.mem_append.mpr (Or.inr
                                    (List.mem_flatMap.mpr
                                      ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩))
                                  simp only
                                  rw [if_neg hBΓ, if_pos hBS]
                                  refine List.mem_append.mpr (Or.inl ?_)
                                  rw [if_pos hγS]
                                  exact .head _
                                · exact consume₁
                                    (G4c.identity_mem (.head _))
                                    ((itp_fuel_mono_le p S
                                      (by omega)).2 _ _ _)
                        · -- the boxed pair
                          rcases List.mem_singleton.mp hin' with rfl
                          refine G4c.andL (List.Perm.refl _) ?_
                          cases c'' with
                          | zero =>
                              exact hgfB F (fl' + 1) Γ A₁ B g _ (by omega)
                                hF'Γ hγS hBS hBΓ hgS hΓS hgrown
                                (wksub (fun ψ h => .tail _ (.tail _ h))
                                  hamb)
                                (G4c.identity_mem (.head _))
                                (G4c.identity_mem (.tail _ (.head _)))
                          | succ c₃ =>
                              refine G4c.orAll_intro
                                (φ := (((itpE p S (fl' + 1) (c₃ + 1)
                                      Γ).ifThen
                                    (itpA p S (fl' + 1) (c₃ + 1) Γ
                                      A₁.somehow)).somehow).and
                                  (itpA p S (fl' + 1) (c₃ + 2) (B :: Γ) g))
                                ?_ (G4c.andR ?_ ?_)
                              · simp only [itpAoth]
                                refine List.mem_append.mpr (Or.inr ?_)
                                simp only [itpAenv]
                                refine List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩
                                simp only
                                rw [if_neg hBΓ, if_pos hBS]
                                refine List.mem_append.mpr (Or.inl ?_)
                                rw [if_pos hγS]
                                exact .tail _ (.head _)
                              · -- first component: free-directions remap,
                                -- the value by the budget tier
                                refine box_remap_free
                                  (G4c.identity_mem (.head _)) ?_ ?_
                                · exact amb_down (wksub (fun ψ h =>
                                    .tail _ (.tail _ (.tail _ h))) hamb)
                                    (by omega) (by omega)
                                · refine hdescB c₃ rfl A₁.somehow _
                                    (himp hγS).1 ?_
                                    (G4c.identity_mem (.head _))
                                  exact amb_down (wksub (fun ψ h => .tail _
                                    (.tail _ (.tail _ (.tail _ h)))) hamb)
                                    (by omega) (by omega)
                              · -- second component: growth; unlock by the
                                -- fuel-lifted boxed component
                                refine hgrown (B :: Γ) g _
                                  (defect_cons_lt hBS hBΓ) hgS
                                  (hScons hBS) ?_
                                  (G4c.identity_mem (.tail _ (.head _)))
                                refine fire (projE
                                  (l := itpEcls p S (fl' + 1) (c₃ + 3) Γ)
                                  (wksub (fun ψ h => .tail _ (.tail _ h))
                                    hamb) ?_)
                                  (box_fuel_lift (by omega)
                                    (G4c.identity_mem (.head _)))
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩))
                                simp only
                                rw [if_neg hBΓ, if_pos hBS]
                                refine List.mem_append.mpr (Or.inl ?_)
                                rw [if_pos hγS]
                                exact .tail _ (.head _)
                      next => cases hin
                    · -- the ◯x-driven boxed pairs (filterMap part)
                      obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                      cases X with
                      | somehow x =>
                          simp only at heq
                          split at heq
                          next => cases heq
                          next hxc =>
                            injection heq with heq'
                            subst heq'
                            have hxΓ : x ∉ Γ := fun h => hxc (Or.inl h)
                            have hxS : x ∈ S := by
                              by_contra h
                              exact hxc (Or.inr h)
                            refine G4c.andL (List.Perm.refl _) ?_
                            refine G4c.orAll_intro
                              (φ := ((((itpE p S (fl' + 1) (c'' + 1)
                                    (x :: Γ)).ifThen
                                  (itpA p S (fl' + 1) (c'' + 1) (x :: Γ)
                                    A₁.somehow)).somehow)).and
                                (itpA p S (fl' + 1) (c'' + 1) (B :: Γ) g))
                              ?_ (G4c.andR ?_ ?_)
                            · simp only [itpAoth]
                              refine List.mem_append.mpr (Or.inr ?_)
                              simp only [itpAenv]
                              refine List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩
                              simp only
                              rw [if_neg hBΓ, if_pos hBS]
                              refine List.mem_append.mpr (Or.inr ?_)
                              refine List.mem_filterMap.mpr
                                ⟨x.somehow, hXΓ, ?_⟩
                              simp only
                              rw [if_neg hxc]
                            · -- first component: open the ambient's bare
                              -- ◯x-conjunct, remap by the defect tier
                              refine box_elim (X := itpE p S (fl' + 1)
                                  (c'' + 2) (x :: Γ)) ?_ ?_
                              · refine projE (l := itpEcls p S (fl' + 1)
                                    (c'' + 2) Γ) (wksub (fun ψ h =>
                                    .tail _ (.tail _ h)) hamb) ?_
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨x.somehow, hXΓ, ?_⟩))
                                simp only
                                rw [if_neg hxc]
                                exact .head _
                              · refine box_remap_free
                                  (G4c.identity_mem (.tail _ (.head _)))
                                  ?_ ?_
                                · exact amb_down
                                    (G4c.identity_mem (.tail _ (.head _)))
                                    (by omega) (Nat.le_refl _)
                                · refine hgrown (x :: Γ) A₁.somehow _
                                    (defect_cons_lt hxS hxΓ)
                                    (himp (hΓS _ hF'Γ)).1 (hScons hxS) ?_
                                    (G4c.identity_mem (.head _))
                                  exact G4c.identity_mem
                                    (.tail _ (.tail _ (.head _)))
                            · -- second component: growth; unlock by the
                              -- fuel-lifted boxed component
                              refine hgrown (B :: Γ) g _
                                (defect_cons_lt hBS hBΓ) hgS (hScons hBS)
                                ?_ (G4c.identity_mem (.tail _ (.head _)))
                              refine fire (projE (l := itpEcls p S
                                  (fl' + 1) (c'' + 2) Γ)
                                (wksub (fun ψ h => .tail _ (.tail _ h))
                                  hamb) ?_)
                                (box_fuel_lift (by omega)
                                  (G4c.identity_mem (.head _)))
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hF'Γ, ?_⟩))
                              simp only
                              rw [if_neg hBΓ, if_pos hBS]
                              refine List.mem_append.mpr (Or.inr ?_)
                              refine List.mem_filterMap.mpr
                                ⟨x.somehow, hXΓ, ?_⟩
                              simp only
                              rw [if_neg hxc]
                      | prop _ => cases heq
                      | falsePLL => cases heq
                      | and _ _ => cases heq
                      | or _ _ => cases heq
                      | ifThen _ _ => cases heq
                  next => cases hin

/-! ### The full-table kernel entry

The shape `cascade_low_pos_box` (wip/absorb_base.lean:2259) needs, for
a piece-closed space with goal and context inside it — modulo the
three open interfaces, which are its entire remaining content. -/

/-- The ◯-involving pair descent, one budget down, for a piece-closed
space with goal and context inside `S` — conditional on the three open
interfaces.  Sorry-free; the induction is `oth_descent`'s. -/
theorem cascade_box (p : String) (S : Finset PLLFormula)
    (hand : ∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S)
    (hor : ∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (hasc : AmbGuardAscent p S)
    (hgfA : GammaPairFloorA p S)
    (hgfB : GammaPairFloorBox p S)
    (hjf : JumpPairFloor p S)
    (fh : Nat) (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula)
    (Δ : List PLLFormula)
    (hgS : g ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S) (hc : 1 ≤ c)
    (hamb : G4c Δ (itpE p S fuel (c + 1) Γ))
    (hhead : G4c Δ (itpA p S fh (c + 1) Γ g))
    (hfh : fh ≤ fuel) :
    G4c Δ (itpA p S fuel c Γ g) := by
  cases fh with
  | zero => exact desc_zero p S hhead
  | succ F =>
      obtain ⟨fl, rfl⟩ : ∃ fl, fuel = fl + 1 := ⟨fuel - 1, by omega⟩
      exact desc_of_oth p S (by omega) hc
        (fun Δ' a b => oth_descent p S hand hor himp hsome hasc hgfA
          hgfB hjf (defect S Γ) c hc F Γ fl g Δ' (Nat.le_refl _) hgS hΓS
          (by omega) a b)
        hamb hhead

end PLLND

/-! ### Axiom audit (the sorry-free spine) -/

/-- info: 'PLLND.oth_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.oth_descent

/-- info: 'PLLND.cascade_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.cascade_box

/-! ## The open branches — stubs

**STOP (2026-08-04, PROGRESS §58).  The four interfaces below are
JOINTLY UNSATISFIABLE, and the residue programme built on them is off
the critical path.**  `cascade_box`'s conclusion is the *room-free*
descent, and that is refuted:
`PLLND.AscRefute.not_roomFreeDescent` (`wip/ascRefute.lean`) kills it at
`Sk = {◯p⊃r, ◯p, p, r, (◯r⊃s)⊃t, ◯r⊃s, ◯r, s, t}`, `Γ = [◯p⊃r]`,
`g = (◯r⊃s)⊃t`, `fuel = 4`, `c = 1`; and `wip/reparamRefute.lean` checks
by `decide` that `Sk` satisfies *every* side condition `cascade_box`
carries (`hand`, `hor`, `himp`, `hsome`, `g ∈ S`, `Γ ⊆ S`, `1 ≤ c`).  So
`cascade_box` applies there, its conclusion is false there, and the four
hypotheses cannot all hold.  `ambGuardAscent_open` is separately refuted
(`AscRefute.not_ambGuardAscent`).

Consequently: **do not** grind the "six goal shapes × three floor
interfaces" residue of PROGRESS §57.  It is a residue of a refuted
statement.  What the tower's kernel `cascade_low_pos_box`
(`wip/absorb_base.lean`) actually asks for carries the defect-tower room
`defect S Γ · (|jumpGoals S| + 2) ≤ c` with `1 ≤ defect S Γ`, which
forces `|jumpGoals S| + 2 ≤ c`, hence `2 ≤ c`
(`ReparamRefute.room_ge_jump`, `ReparamRefute.room_two`) — the kernel's
band never contains the budget floor `c = 1` where `AmbGuardAscent` fails
and where all three pair-floor interfaces are stated.  The viable ◯-band
route is a **ledger-carrying** build: `cascade_main`'s pigeonhole over
jump goals, extended to the ◯-clauses, so that every recursive call stays
inside the room.  `wip/floorRefute.lean` reached the same conclusion from
the other side (the budget tier has no base case at all).

What survives unconditionally and is reusable by such a build: everything
above this section, plus `wip/boxSndTight.lean`'s `boxSnd_tight`,
`boxGoal_remap_free`, `floorBox_of_grownAmb`, `floorAny_atom` and the
three `*_boxedAtom` instances — those are proved theorems about the
tables, not about the refuted descent.

Historical status of each interface, as recorded before the refutation:

* `ambGuardAscent_open` — the fresh-antecedent equality law
  (§66/§73(ii)): exact on every instance of the countermodel battery,
  never proved syntactically.  Candidate route: a fourth component of
  the lexicographic induction (the one-step existential ascent at
  strictly smaller defect, gated arms by the budget tier) — its own
  floor lands in the same §73 shape as the pair floors below.

* `gammaPairFloorA_open` / `gammaPairFloorBox_open` — the §73 stuck
  shape: target budget `1`, gated γ-pair, head possibly distinct from
  the goal, growth-live context.  Battery-true including the
  growth-live band (§76: zero failures at configs A/B).  Candidate
  route (§73(i)): commute the growth disjuncts of the target first —
  the interface's defect-tier slot supplies exactly that resource; at
  growth-dead states the source components starve
  (`itpA_starve_floor`) and the branch dispatches by explosion or
  `box_absurd`, so only growth-live states carry content.

* `jumpPairFloor_open` — the jump-family instance of the same floor
  (the alternative is to re-run `cascade_main_bf`'s pigeonhole with
  seen-sets, which cannot cross the boxed branches of this build).
-/

namespace PLLND

/-- **OPEN** (stub): the fresh-antecedent equality law.  Battery-exact
(§66), unproven. -/
theorem ambGuardAscent_open (p : String) (S : Finset PLLFormula) :
    AmbGuardAscent p S := sorry

/-- **OPEN** (stub): the plain gated γ-pair at the budget floor (§73). -/
theorem gammaPairFloorA_open (p : String) (S : Finset PLLFormula) :
    GammaPairFloorA p S := sorry

/-- **OPEN** (stub): the boxed gated γ-pair at the budget floor — THE
§73 stuck shape. -/
theorem gammaPairFloorBox_open (p : String) (S : Finset PLLFormula) :
    GammaPairFloorBox p S := sorry

/-- **OPEN** (stub): the gated jump-family pair at the budget floor. -/
theorem jumpPairFloor_open (p : String) (S : Finset PLLFormula) :
    JumpPairFloor p S := sorry

/-- The unconditional kernel — sorry-tainted exactly through the four
stubs above; every step of the descent itself is machine-checked. -/
theorem cascade_box_unconditional (p : String) (S : Finset PLLFormula)
    (hand : ∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S)
    (hor : ∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (fh : Nat) (Γ : List PLLFormula) (fuel c : Nat) (g : PLLFormula)
    (Δ : List PLLFormula)
    (hgS : g ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S) (hc : 1 ≤ c)
    (hamb : G4c Δ (itpE p S fuel (c + 1) Γ))
    (hhead : G4c Δ (itpA p S fh (c + 1) Γ g))
    (hfh : fh ≤ fuel) :
    G4c Δ (itpA p S fuel c Γ g) :=
  cascade_box p S hand hor himp hsome
    (ambGuardAscent_open p S) (gammaPairFloorA_open p S)
    (gammaPairFloorBox_open p S) (jumpPairFloor_open p S)
    fh Γ fuel c g Δ hgS hΓS hc hamb hhead hfh

end PLLND

/-! ### Axiom audit (the stubs' taint, confined) -/

/-- info: 'PLLND.cascade_box_unconditional' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.cascade_box_unconditional
