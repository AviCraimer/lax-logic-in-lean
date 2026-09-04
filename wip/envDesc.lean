import wip.goalDesc

/-!
# The gated environment clauses of the descent, above the floor

`wip/goalDesc.lean` removes the goal side of the descent from the problem: a
budget-gated *goal* clause demotes only its existential component, which the
ambient supplies free, so no goal branch ever reaches budget `0`.  The
low-budget difficulty is therefore entirely in the **environment** clauses,
and only in the two budget-gated ones (`itpAenv` rows 7a and 8a of the clause
table): the jump clause `(A⊃B)⊃D ∈ Γ ∩ S` with `B⊃D ∈ Γ`, and the γ-clause
`◯A ⊃ B ∈ Γ ∩ S`.

Each of those contributes disjuncts of the form (first component) ∧ (second
component), where the second component sits at the **grown** context `D::Γ`
or `B::Γ` and the same budget — so the defect tier supplies it — and the
first component sits at the **same** context one budget **lower**.  There are
three first components in all:

| clause | first component of the target at budget `b = c+1` |
|---|---|
| jump | `E@c(Γ) ⇢ A@c(Γ, A⊃B)` |
| γ, plain | `A@c(Γ, A)` |
| γ, boxed | `◯( E@c(Γ) ⇢ A@c(Γ, ◯A) )` |

This file proves **all three** close, at every target budget `b ≥ 2`, from the
descent at the corresponding *jump goal* one budget down.  The key point is
the same one that settled the goal side, and it is worth stating plainly:

> the ambient is at budget `b + 1 = c + 2`, i.e. **two** above the component's
> budget `c`, so downward existential monotonicity alone supplies the guard
> `E@(c+1)(Γ)` needed to fire the source.  No existential *ascent* is
> involved, and the refuted `AmbGuardAscent` is not consumed here at all.

What is consumed is the descent at a jump goal at target budget `c`, and that
needs `c ≥ 1` — i.e. the *target* budget `b = c + 1 ≥ 2`.  So:

* at target budget `b ≥ 2` the three gated environment first components close
  (this file);
* at target budget `b = 1` they need the descent at budget `0`, which is
  proved by search at unboxed atom goals, open at `⊃`-shaped jump goals, and
  **certified false** at boxed goals (`wip/ascprobe.lean`,
  `wip/jumpprobe.lean`).

That last line is the whole residue of the descent, and it is now one
branch at one budget: the **boxed γ first component at target budget 1**.
-/

open PLLFormula

namespace PLLND
namespace EnvDesc

open GoalDesc

/-! ## 1. The γ-clause's plain first component

The target component is `A@c(Γ, A)` and the source's is `A@(c+1)(Γ, A)` at the
same context.  So this is the descent at the unboxed jump goal `A`, applied
directly — no plumbing at all.  Recorded for completeness of the table. -/

theorem gamma_plain_of_desc (p : String) (S : Finset PLLFormula)
    {F fl c : Nat} {Γ Δ : List PLLFormula} {A : PLLFormula}
    (hdesc : ∀ (Δ' : List PLLFormula),
      G4c Δ' (itpE p S (fl + 1) (c + 1) Γ) →
      G4c Δ' (itpA p S F (c + 1) Γ A) →
      G4c Δ' (itpA p S fl c Γ A))
    (hamb : G4c Δ (itpE p S (fl + 1) (c + 2) Γ))
    (hsrc : G4c Δ (itpA p S F (c + 1) Γ A)) :
    G4c Δ (itpA p S fl c Γ A) :=
  hdesc Δ (ambE p S (Nat.le_refl _) (Nat.le_succ _) rfl hamb) hsrc

/-! ## 2. The jump clause's first component

    source   E@(c+1)(Γ)  ⇢  A@(c+1)(Γ, A⊃B)
    target   E@c(Γ)      ⇢  A@c(Γ, A⊃B)

Introduce the target's guard, fire the source with `E@(c+1)(Γ)` taken from the
ambient at budget `c+2` by downward monotonicity, then descend at the jump
goal `A⊃B`. -/

theorem jump_of_desc (p : String) (S : Finset PLLFormula)
    {F fl c : Nat} {Γ Δ : List PLLFormula} {A B : PLLFormula}
    (hF : F ≤ fl + 1)
    (hdesc : ∀ (Δ' : List PLLFormula),
      G4c Δ' (itpE p S (fl + 1) (c + 1) Γ) →
      G4c Δ' (itpA p S F (c + 1) Γ (A.ifThen B)) →
      G4c Δ' (itpA p S fl c Γ (A.ifThen B)))
    (hamb : G4c Δ (itpE p S (fl + 1) (c + 2) Γ))
    (hsrc : G4c Δ ((itpE p S F (c + 1) Γ).ifThen
      (itpA p S F (c + 1) Γ (A.ifThen B)))) :
    G4c Δ ((itpE p S fl c Γ).ifThen (itpA p S fl c Γ (A.ifThen B))) := by
  refine G4c.impR ?_
  refine hdesc _ (ambE p S (Nat.le_refl _) (Nat.le_succ _) rfl (hamb.weaken _))
    (fire (hsrc.weaken _)
      (ambE p S hF (Nat.le_succ _) rfl (hamb.weaken _)))

/-! ## 3. The γ-clause's boxed first component — the seal, above the floor

    source   ◯( E@(c+1)(Γ)  ⇢  A@(c+1)(Γ, ◯A) )
    target   ◯( E@c(Γ)      ⇢  A@c(Γ, ◯A) )

`box_remap_free` (`wip/starve.lean`) reduces this to two conversions inside
the box: the **guard** `E@c(Γ) ⊢ E@(c+1)(Γ)`, and the **value**
`A@(c+1)(Γ,◯A) ⊢ A@c(Γ,◯A)`.

The guard conversion looks like an ascent — and the bare ascent
`E@c ⊢ E@(c+1)` is refuted at low budget — but it is not needed: the ambient
sits at budget `c + 2`, so `E@(c+1)(Γ)` follows from it by downward
monotonicity, and `box_remap_free` allows the conversion to use the whole
extended context.  The value conversion is the descent at the boxed jump goal
`◯A`, at target budget `c`.

So the sealed branch that `wip/absorb_base.lean`'s residue analysis lists as
unreachable is reachable at every target budget `≥ 2`.  Only `c = 0` — target
budget `1` — is left, and there the value conversion is the certified-false
descent to budget `0` at a boxed goal. -/

theorem gamma_boxed_of_desc (p : String) (S : Finset PLLFormula)
    {F fl c : Nat} {Γ Δ : List PLLFormula} {A : PLLFormula}
    (hF : F ≤ fl + 1)
    (hdesc : ∀ (Δ' : List PLLFormula),
      G4c Δ' (itpE p S (fl + 1) (c + 1) Γ) →
      G4c Δ' (itpA p S F (c + 1) Γ A.somehow) →
      G4c Δ' (itpA p S fl c Γ A.somehow))
    (hamb : G4c Δ (itpE p S (fl + 1) (c + 2) Γ))
    (hbox : G4c Δ (((itpE p S F (c + 1) Γ).ifThen
      (itpA p S F (c + 1) Γ A.somehow)).somehow)) :
    G4c Δ (((itpE p S fl c Γ).ifThen
      (itpA p S fl c Γ A.somehow)).somehow) := by
  refine box_remap_free hbox ?_ ?_
  · exact ambE p S hF (Nat.le_succ _) rfl (hamb.weaken _)
  · exact hdesc _
      (ambE p S (Nat.le_refl _) (Nat.le_succ _) rfl
        ((hamb.weaken _).weaken _))
      (G4c.identity_mem (.head _))

/-! ## 4. The three together

`GatedEnvFirst` bundles the three gated environment first components at one
budget step.  The theorem says: the descent at jump goals at target budget `c`
gives all three at target budget `c + 1`.  Composed with `wip/goalDesc.lean`
(the goal side) and `desc_of_oth` (the truncation), the only thing left in the
descent above target budget `1` is the *ungrown* half of the environment
clauses — which is the defect tier, not the budget. -/

/-- The descent restricted to jump goals at one budget step, in the
context-polymorphic form the branches consume. -/
def JumpStep (p : String) (S : Finset PLLFormula) (F fl c : Nat)
    (Γ : List PLLFormula) : Prop :=
  ∀ (g : PLLFormula) (Δ' : List PLLFormula),
    G4c Δ' (itpE p S (fl + 1) (c + 1) Γ) →
    G4c Δ' (itpA p S F (c + 1) Γ g) →
    G4c Δ' (itpA p S fl c Γ g)

/-- **All three gated environment first components, at one blow.** -/
theorem gated_env_first (p : String) (S : Finset PLLFormula)
    {F fl c : Nat} {Γ Δ : List PLLFormula} (hF : F ≤ fl + 1)
    (hjs : JumpStep p S F fl c Γ)
    (hamb : G4c Δ (itpE p S (fl + 1) (c + 2) Γ)) :
    (∀ A : PLLFormula, G4c Δ (itpA p S F (c + 1) Γ A) →
        G4c Δ (itpA p S fl c Γ A))
    ∧ (∀ A B : PLLFormula,
        G4c Δ ((itpE p S F (c + 1) Γ).ifThen
          (itpA p S F (c + 1) Γ (A.ifThen B))) →
        G4c Δ ((itpE p S fl c Γ).ifThen
          (itpA p S fl c Γ (A.ifThen B))))
    ∧ (∀ A : PLLFormula,
        G4c Δ (((itpE p S F (c + 1) Γ).ifThen
          (itpA p S F (c + 1) Γ A.somehow)).somehow) →
        G4c Δ (((itpE p S fl c Γ).ifThen
          (itpA p S fl c Γ A.somehow)).somehow)) :=
  ⟨fun A hsrc => gamma_plain_of_desc p S (hjs A) hamb hsrc,
   fun A B hsrc => jump_of_desc p S hF (hjs (A.ifThen B)) hamb hsrc,
   fun A hbox => gamma_boxed_of_desc p S hF (hjs A.somehow) hamb hbox⟩

/-! ## 5. The floor case: a starved boxed target reduces to `◯⊥`

At target budget `1` the boxed component sits at budget `0`, where a
`◯`-goal's table is its environment table alone (`itpA_obGoal_floor`) and can
be **starved** — literally `⊥` (`itpA_starve_floor`).  When it is, the target
component is `◯( E@0(Γ) ⇢ ⊥ )`, and any derivation of `◯⊥` gives it: `⊥`
implies `E@0(Γ) ⇢ ⊥` outright, and `laxL` carries that under the box.

So at the floor the branch does not need the (refuted) descent to budget `0`
at all — it needs `◯⊥`.  That is a much weaker demand, and on the probed
configuration it is met: `wip/sealprobe2.lean` reports

    A@1(Γ,◯p)  ⊢  ◯⊥      PROVED

for `Γ = [◯p ⊃ r]`, together with `A@0(Γ,◯p) = ⊥`, `A@0(Γ,p) = ⊥` and
`E@0(Γ) = ⊤` — the three starvation facts the route uses.  Whether
`A@b(Γ,◯D) ⊢ ◯⊥` holds generally is the open question; it held there because
the recursion bottomed out in starved states, which is exactly the
propagation argument `wip/starve.lean` was begun for. -/

/-- **A starved boxed target is met by `◯⊥`.**  No descent, and no ascent. -/
theorem boxed_target_of_starved (p : String) (S : Finset PLLFormula)
    {fl c : Nat} {Γ Δ : List PLLFormula} {A : PLLFormula}
    (hstarve : itpA p S fl c Γ A.somehow = falsePLL)
    (hbot : G4c Δ falsePLL.somehow) :
    G4c Δ (((itpE p S fl c Γ).ifThen
      (itpA p S fl c Γ A.somehow)).somehow) := by
  rw [hstarve]
  refine G4c.cut hbot (G4c.laxL (.head _) ?_)
  exact G4c.botL (.head _)

/-- The same, with the starvation hypothesis in the form
`wip/starve.lean` supplies it: an empty environment table at the floor. -/
theorem boxed_target_of_env_nil (p : String) (S : Finset PLLFormula)
    {f : Nat} {Γ Δ : List PLLFormula} {A : PLLFormula}
    (henv : itpAenv p S f 0 Γ A.somehow = [])
    (hbot : G4c Δ falsePLL.somehow) :
    G4c Δ (((itpE p S (f + 1) 0 Γ).ifThen
      (itpA p S (f + 1) 0 Γ A.somehow)).somehow) :=
  boxed_target_of_starved p S (itpA_starve_floor p S f Γ A henv) hbot

/-! ## 6. The case analysis, formalised

`wip/sealRefute.lean` shows the boxed γ-branch at target budget `1` has no
uniform route: each of the three target disjuncts it could aim at is
individually underivable from the branch's hypotheses.  So the branch needs a
case analysis — and there is one available for free that the earlier survey did
not use, because it looked at the source's *first* component and at the target's
disjuncts rather than at the source's *second*.

The second hypothesis is **itself a disjunction**:

    A@1(B::Γ, C)  =  orAll (itpAfull p S F 1 (B::Γ) C)

so `orAll_elim` on it is a case analysis with one case per disjunct of the
grown-context table.  The two refuting models of §87 are consistent with this
reading: in each, which route succeeds is determined by which disjunct of the
second component holds.

The lemma below is that reduction, and it is agnostic about the routes: it says
the branch follows from *any* assignment of a derivation to each disjunct.  It
is stated for the whole branch obligation (not just the boxed disjunct), because
once the case analysis is in place the branch may reach any target disjunct it
likes, differently in different cases — which is exactly what §87 says it must
do. -/

/-- **The branch obligation, reduced to one case per disjunct of the second
component.**  No route is fixed: each case may reach a different target
disjunct. -/
theorem branch_of_cases (p : String) (S : Finset PLLFormula)
    {F fl : Nat} {Γ Δ : List PLLFormula} {B C : PLLFormula}
    (hcase : ∀ ψ ∈ itpAfull p S F 1 (B :: Γ) C,
      G4c (ψ :: Δ) (orAll (itpAoth p S fl 1 Γ C)))
    (hsnd : G4c Δ (itpA p S (F + 1) 1 (B :: Γ) C)) :
    G4c Δ (orAll (itpAoth p S fl 1 Γ C)) := by
  rw [itpA_succ] at hsnd
  exact G4c.cut hsnd (G4c.orAll_elim hcase)

/-- The same for a non-boxed goal, where the grown-context table has no
truncation disjunct so the cases are exactly `itpAoth`'s. -/
theorem branch_of_cases_nonbox (p : String) (S : Finset PLLFormula)
    {F fl : Nat} {Γ Δ : List PLLFormula} {B C : PLLFormula}
    (hC : ∀ D : PLLFormula, C ≠ D.somehow)
    (hcase : ∀ ψ ∈ itpAoth p S F 1 (B :: Γ) C,
      G4c (ψ :: Δ) (orAll (itpAoth p S fl 1 Γ C)))
    (hsnd : G4c Δ (itpA p S (F + 1) 1 (B :: Γ) C)) :
    G4c Δ (orAll (itpAoth p S fl 1 Γ C)) := by
  refine branch_of_cases p S ?_ hsnd
  intro ψ hψ
  cases C with
  | somehow D => exact absurd rfl (hC D)
  | prop q => simp only [itpAfull] at hψ; exact hcase ψ hψ
  | falsePLL => simp only [itpAfull] at hψ; exact hcase ψ hψ
  | and C₁ C₂ => simp only [itpAfull] at hψ; exact hcase ψ hψ
  | or C₁ C₂ => simp only [itpAfull] at hψ; exact hcase ψ hψ
  | ifThen C₁ C₂ => simp only [itpAfull] at hψ; exact hcase ψ hψ

/-! ## 7. The ambient fires the boxed component — the grown ambient, for free

`wip/boxedS1b.lean` closes the boxed floor branch at one configuration by a step
that generalises, and this is it.

The ambient `E@(c+2)(Γ)` is a **conjunction**, and for a γ-clause
`◯A ⊃ B ∈ Γ ∩ S` with `B ∈ S ∖ Γ` two of its conjuncts are

    A@(c+1)(Γ,A)                        ⇢  E@(c+2)(B::Γ)
    ◯( E@(c+1)(Γ) ⇢ A@(c+1)(Γ,◯A) )     ⇢  E@(c+2)(B::Γ)

and the antecedent of the second is **exactly the branch's own boxed first
component**.  Firing it yields the existential table at the *grown* context.

That is worth stating on its own, because it is a second and stronger use of the
ambient than §4's: there the ambient supplies weaker tables by downward
monotonicity, here it supplies *implications whose antecedents the branch already
has*.  And what it yields is precisely the object `AmbGuardAscent` was introduced
to produce — the grown ambient — at the one context the γ-branch needs it, with
no ascent and nothing refuted. -/

/-- The ambient's γ-conjunct whose antecedent is the boxed component. -/
theorem amb_gamma_mem (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ : List PLLFormula} {A B : PLLFormula}
    (hmem : A.somehow.ifThen B ∈ Γ) (hS : A.somehow.ifThen B ∈ S)
    (hB : B ∉ Γ) (hBS : B ∈ S) :
    ((((itpE p S f (c + 1) Γ).ifThen
        (itpA p S f (c + 1) Γ A.somehow)).somehow).ifThen
      (itpE p S f (c + 2) (B :: Γ))) ∈ itpEcls p S f (c + 2) Γ := by
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨A.somehow.ifThen B, hmem, ?_⟩
  simp only [if_neg hB, if_pos hBS, if_pos hS]
  exact List.mem_append.mpr
    (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_self ..)))


/-- **The ambient fires the boxed component, giving the grown ambient.**  No
ascent, no descent, no case analysis. -/
theorem grownAmb_of_box (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {A B : PLLFormula}
    (hmem : A.somehow.ifThen B ∈ Γ) (hS : A.somehow.ifThen B ∈ S)
    (hB : B ∉ Γ) (hBS : B ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ))
    (hbox : G4c Δ ((((itpE p S f (c + 1) Γ).ifThen
      (itpA p S f (c + 1) Γ A.somehow)).somehow))) :
    G4c Δ (itpE p S f (c + 2) (B :: Γ)) := by
  rw [itpE_succ] at hamb
  exact fire (G4c.cut hamb
    (G4c.andAll_elim (amb_gamma_mem p S hmem hS hB hBS)
      (G4c.identity_mem (.head _)))) hbox

/-- The same for the *plain* first component, whose antecedent is the other
γ-conjunct.  Stated for symmetry: the two γ-disjuncts of the source both hand
the ambient something it can fire. -/
theorem grownAmb_of_plain (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {A B : PLLFormula}
    (hmem : A.somehow.ifThen B ∈ Γ) (hS : A.somehow.ifThen B ∈ S)
    (hB : B ∉ Γ) (hBS : B ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ))
    (hval : G4c Δ (itpA p S f (c + 1) Γ A)) :
    G4c Δ (itpE p S f (c + 2) (B :: Γ)) := by
  rw [itpE_succ] at hamb
  refine fire (G4c.cut hamb (G4c.andAll_elim ?_ (G4c.identity_mem (.head _))))
    hval
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨A.somehow.ifThen B, hmem, ?_⟩
  simp only [if_neg hB, if_pos hBS, if_pos hS]
  exact List.mem_append.mpr (Or.inl (List.mem_cons_self ..))

end EnvDesc
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.EnvDesc.gamma_boxed_of_desc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.EnvDesc.gamma_boxed_of_desc

/--
info: 'PLLND.EnvDesc.jump_of_desc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.EnvDesc.jump_of_desc

/--
info: 'PLLND.EnvDesc.gated_env_first' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.EnvDesc.gated_env_first

/--
info: 'PLLND.EnvDesc.boxed_target_of_env_nil' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.EnvDesc.boxed_target_of_env_nil

/--
info: 'PLLND.EnvDesc.branch_of_cases' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.EnvDesc.branch_of_cases

/--
info: 'PLLND.EnvDesc.branch_of_cases_nonbox' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.EnvDesc.branch_of_cases_nonbox

/--
info: 'PLLND.EnvDesc.grownAmb_of_box' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.EnvDesc.grownAmb_of_box

/--
info: 'PLLND.EnvDesc.grownAmb_of_plain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.EnvDesc.grownAmb_of_plain
