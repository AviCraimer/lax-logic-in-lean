import wip.branchdia

/-!
# `φ♣`, the PARAMETERISED fork, and `∃p.φ♣ = ¬¬◯⊥ ⊃ ◯⊥`

`wip/branchdia.lean` §12 records the `n = 5` probe hit

    C♣ :  W = {0,1,2,3,4},  0 ⊑ everything,  1 ⊑ 2,  3 and 4 maximal
          Rₘ = id ∪ {(1,2)},   F = {2},   V(p) = {1,2,3}

    φ♣ = ((p ⊃ ◯⊥) ∨ (¬p ⊃ ◯⊥)) ⊃ (¬◯⊥ ∨ (◯⊥ ∧ p))

as a candidate refutation of `BranchMixedConj`.  This file pins it and
settles `∃p.φ♣`.

## What is proved

* `Cclub_force_phiClub` — `φ♣` holds at the root of `C♣` under
  `‖p‖ = {1,2,3}`;
* `phiClub_no_branchMixedCover`, `branchMixedConj_false` — **REFUTED**:
  no join of guarded stretch bounds, `(χ,⊥)`-fork bounds and
  variable-free substitution instances covers `φ♣`.  The undefinability
  argument is the transposition `3 ↔ 4`, a frame automorphism of `C♣`;
* `postInterp_phiClub` — **PROVED**: `∃p.φ♣ = ¬¬◯⊥ ⊃ ◯⊥`, by the
  PARAMETERISED fork at `(χ, δ₁, δ₂) = (◯⊥ ∨ ¬◯⊥, ◯⊥ ∨ ¬◯⊥, ◯⊥)`;
* `paramFork_stretch_incomparable` — the guarded stretch is still
  needed: `φ★` has NO parameterised fork cover at any admissible
  triple (`not_hasForkCover_phiStar`), while `φ♣` has one and no
  guarded mixed cover;
* `paramForkMixedConj_false` — **REFUTED**, in turn: the CORRECTED
  frontier conjecture is false as well.  `φ♠` (§15), found by the
  exhaustive `n ≤ 5` sweep of `wip/pforkprobe.lean`, defeats the whole
  join of substitution, guarded stretching and the parameterised fork
  — and `semParamForkConj_false` shows even its POINTWISE form fails.

Note the value: NOT `¬¬◯⊥`.  `φ★` and `φ♦` both have interpolant
`¬¬◯⊥`; `φ♣` does not, so `¬¬◯⊥` is not a universal attractor.

## The parameterised fork

`bstretch C χ` of `wip/branchdia.lean` hard-codes the two copy
valuations as `‖χ‖` and `‖⊥‖`.  The general family keeps the frame and
frees them:

    fork C χ δ₁ δ₂ :  same frame as `bstretch C χ`
                      V(a) = ‖δ₁‖ on the inl copy, ‖δ₂‖ on the inr copy

The ONLY condition is `δ₁ ⊢ χ` and `δ₂ ⊢ χ`, and it is used exactly
once, to make `hered_V` vacuous on the cross edges: a cross edge out of
`x` exists only when `x ⊮ χ`, and then `x ⊮ δᵢ` too, so nothing has to
be transported.  (`full_F` is free: fallible worlds force everything.)
`bstretch C χ = fork C χ χ ⊥` definitionally (`fork_eq_bstretch`).

Forcing at the two copies is computed by the mutually recursive pair

    FLo p     = δ₁                   FUp p     = δ₂
    FLo ⊥     = ⊥                    FUp ⊥     = ⊥
    FLo (A∧B) = FLo A ∧ FLo B        FUp (A∧B) = FUp A ∧ FUp B
    FLo (A∨B) = FLo A ∨ FLo B        FUp (A∨B) = FUp A ∨ FUp B
    FLo (A⊃B) = (FLo A ⊃ FLo B)      FUp (A⊃B) = (FUp A ⊃ FUp B)
                ∧ (χ ∨ (FUp A ⊃ FUp B))        ∧ (χ ∨ (FLo A ⊃ FLo B))
    FLo ◯A    = ◯(FLo A) ∧ (χ ∨ ◯(FUp A))
    FUp ◯A    = ◯(FUp A) ∧ (χ ∨ ◯(FLo A))

— `BLo`/`BUp` with the atom clause freed — giving a new family of
non-substitutional lower bounds `fork_below` on `F(φ)`, one per triple
`(χ, δ₁, δ₂)`, and the master reduction `postInterp_of_fork`.

## Why `φ♣` needs the free valuations

Read off the forcing condition of `φ♣` at `w`.  Every `◯⊥`-world
forces `p ⊃ ◯⊥` outright (`◯⊥` is upward closed), so the antecedent
fires there and the consequent must hold; since `¬◯⊥` and `◯⊥` are
jointly `⊥`, that says

  (α) every `◯⊥`-world of the cone forces `p`,

so `‖p‖ ⊇ ‖◯⊥‖`.  On a world `v` with `v ⊮ ◯⊥` and `v ⊮ ¬◯⊥` the
consequent fails outright, so the antecedent must fail:

  (β) above every such `v` there is a `p`-world outside `‖◯⊥‖`
      AND a `¬p`-world outside `‖◯⊥‖`.

(α) forbids the `(χ,⊥)`-fork's second copy (its `p` is `⊥`, which is
below `◯⊥`, so (α) fails on that copy at every non-fallible
`◯⊥`-world), and (β) forbids the single upper curtain of the guarded
stretch.  With free valuations both are met at once by putting
`δ₁ = ◯⊥ ∨ ¬◯⊥` on the first copy and `δ₂ = ◯⊥` on the second, guarded
by `χ = ◯⊥ ∨ ¬◯⊥` — so the two copies are glued exactly over the GAP
region `‖◯⊥‖ᶜ ∩ ‖¬◯⊥‖ᶜ`, which is where (β) has work to do.

No sorries.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## 1.  The five-world model `C♣` -/

/-- The intuitionistic order of `C♣`: `0 ⊑ everything`, `1 ⊑ 2`, and
`3`, `4` maximal (and incomparable to `1`, `2` and to each other). -/
def Rc (x y : Fin 5) : Prop := x = 0 ∨ x = y ∨ (x = 1 ∧ y = 2)

instance (x y : Fin 5) : Decidable (Rc x y) := by unfold Rc; infer_instance

/-- The modal relation of `C♣`: the identity plus the edge `1 ⇝ 2`. -/
def Rmc (x y : Fin 5) : Prop := x = y ∨ (x = 1 ∧ y = 2)

instance (x y : Fin 5) : Decidable (Rmc x y) := by unfold Rmc; infer_instance

theorem Rc_refl : ∀ x : Fin 5, Rc x x := by decide
theorem Rc_trans : ∀ x y z : Fin 5, Rc x y → Rc y z → Rc x z := by decide
theorem Rmc_refl : ∀ x : Fin 5, Rmc x x := by decide
theorem Rmc_trans : ∀ x y z : Fin 5, Rmc x y → Rmc y z → Rmc x z := by decide
theorem Rmc_sub : ∀ x y : Fin 5, Rmc x y → Rc x y := by decide
theorem Rc_hered_F : ∀ x y : Fin 5, Rc x y → x = 2 → y = 2 := by decide
theorem Rc_hered_V : ∀ x y : Fin 5, Rc x y →
    (x = 1 ∨ x = 2 ∨ x = 3) → (y = 1 ∨ y = 2 ∨ y = 3) := by decide
theorem Rc_full_V : ∀ x : Fin 5, x = 2 → (x = 1 ∨ x = 2 ∨ x = 3) := by decide
theorem Fin5_cases : ∀ u : Fin 5, u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 := by decide

/-- **The five-world countermodel `C♣`.**  `‖p‖ = {1,2,3}` separates
the two indistinguishable maximal worlds `3`, `4`, so it is
undefinable. -/
@[reducible] def Cclub : ConstraintModel where
  W := Fin 5
  Ri := Rc
  Rm := Rmc
  F := {x | x = 2}
  V _ := {x | x = 1 ∨ x = 2 ∨ x = 3}
  refl_i := Rc_refl
  trans_i {x y z} h1 h2 := Rc_trans x y z h1 h2
  refl_m := Rmc_refl
  trans_m {x y z} h1 h2 := Rmc_trans x y z h1 h2
  sub_mi {x y} h := Rmc_sub x y h
  hered_F {x y} h hx := Rc_hered_F x y h hx
  hered_V {_ x y} h hx := Rc_hered_V x y h hx
  full_F {_ x} hx := Rc_full_V x hx

/-- `◯⊥` holds exactly at `1` and `2`. -/
theorem Cclub_oBot_iff (x : Fin 5) : Cclub.force x oBot ↔ (x = 1 ∨ x = 2) := by
  have key : ∀ y : Fin 5,
      (∀ v : Fin 5, Rc y v → ∃ u : Fin 5, Rmc v u ∧ u = 2) ↔ (y = 1 ∨ y = 2) := by
    decide
  exact key x

/-- `¬◯⊥` holds exactly at `2`, `3`, `4`. -/
theorem Cclub_nOBot_iff (x : Fin 5) :
    Cclub.force x (nt oBot) ↔ (x = 2 ∨ x = 3 ∨ x = 4) := by
  have key : ∀ y : Fin 5,
      (∀ v : Fin 5, Rc y v → (v = 1 ∨ v = 2) → v = 2) ↔ (y = 2 ∨ y = 3 ∨ y = 4) := by
    decide
  constructor
  · intro h
    exact (key x).mp (fun v hv h12 => h v hv ((Cclub_oBot_iff v).mpr h12))
  · intro h v hv hvb
    exact (key x).mpr h v hv ((Cclub_oBot_iff v).mp hvb)

/-- `¬¬◯⊥` holds exactly at `1`, `2` — so in `C♣` it COINCIDES with
`◯⊥` (the `n = 5` probe's `{1,2,3,4}` is `◯⊥ ∨ ¬◯⊥`, not `¬¬◯⊥`). -/
theorem Cclub_nnOBot_iff (x : Fin 5) :
    Cclub.force x (nt (nt oBot)) ↔ (x = 1 ∨ x = 2) := by
  have key : ∀ y : Fin 5,
      (∀ v : Fin 5, Rc y v → (v = 2 ∨ v = 3 ∨ v = 4) → v = 2) ↔ (y = 1 ∨ y = 2) := by
    decide
  constructor
  · intro h
    exact (key x).mp (fun v hv h234 => h v hv ((Cclub_nOBot_iff v).mpr h234))
  · intro h v hv hvn
    exact (key x).mpr h v hv ((Cclub_nOBot_iff v).mp hvn)

/-! ## 2.  `φ♣`, and its truth at the root -/

/-- **`φ♣ = ((p ⊃ ◯⊥) ∨ (¬p ⊃ ◯⊥)) ⊃ (¬◯⊥ ∨ (◯⊥ ∧ p))`.** -/
def phiClub : PLLFormula :=
  (((PLLFormula.prop pv).ifThen oBot).or
      ((nt (PLLFormula.prop pv)).ifThen oBot)).ifThen
    ((nt oBot).or (oBot.and (PLLFormula.prop pv)))

theorem phiClub_onlyPv : onlyPv phiClub = true := by decide

/-- The antecedent of `φ♣`. -/
abbrev clubAnte : PLLFormula :=
  ((PLLFormula.prop pv).ifThen oBot).or ((nt (PLLFormula.prop pv)).ifThen oBot)

/-- The consequent of `φ♣`. -/
abbrev clubCons : PLLFormula := (nt oBot).or (oBot.and (PLLFormula.prop pv))

/-- **`φ♣` holds at the root of `C♣`.**  At `1` and `2` the consequent's
second disjunct holds (`◯⊥ ∧ p`); at `3` and `4` the first (`¬◯⊥`); at
the root itself the antecedent fails — `3` is a `p`-world outside
`‖◯⊥‖` and `4` is a `¬p`-world outside `‖◯⊥‖`. -/
theorem Cclub_force_phiClub : Cclub.force (0 : Fin 5) phiClub := by
  intro v hv hante
  rcases Fin5_cases v with rfl | rfl | rfl | rfl | rfl
  · exfalso
    rcases hante with h1 | h2
    · -- `p ⊃ ◯⊥` fails: `3` forces `p` and not `◯⊥`
      have h3 : Cclub.force (3 : Fin 5) oBot :=
        h1 3 (by decide) (show (3 : Fin 5) = 1 ∨ (3 : Fin 5) = 2 ∨ (3 : Fin 5) = 3 by decide)
      exact absurd ((Cclub_oBot_iff 3).mp h3) (by decide)
    · -- `¬p ⊃ ◯⊥` fails: `4` forces `¬p` and not `◯⊥`
      have h4n : Cclub.force (4 : Fin 5) (nt (PLLFormula.prop pv)) := by
        intro u hu hup
        have hu4 : u = 4 := by
          rcases Fin5_cases u with rfl | rfl | rfl | rfl | rfl <;>
            first | rfl | exact absurd hu (by decide)
        subst hu4
        have hup' : (4 : Fin 5) = 1 ∨ (4 : Fin 5) = 2 ∨ (4 : Fin 5) = 3 := hup
        exact absurd hup' (by decide)
      have h4 : Cclub.force (4 : Fin 5) oBot := h2 4 (by decide) h4n
      exact absurd ((Cclub_oBot_iff 4).mp h4) (by decide)
  · exact Or.inr ⟨(Cclub_oBot_iff 1).mpr (by decide),
      show (1 : Fin 5) = 1 ∨ (1 : Fin 5) = 2 ∨ (1 : Fin 5) = 3 from by decide⟩
  · exact Cclub.force_of_fallible (show (2 : Fin 5) ∈ Cclub.F from rfl)
  · exact Or.inl ((Cclub_nOBot_iff 3).mpr (by decide))
  · exact Or.inl ((Cclub_nOBot_iff 4).mpr (by decide))

theorem Cclub_root_not_fallible : ¬ Cclub.force (0 : Fin 5) PLLFormula.falsePLL := by
  intro h
  have h' : (0 : Fin 5) = 2 := h
  exact absurd h' (by decide)

/-- `φ♣` is consistent. -/
theorem phiClub_consistent : ¬ Deriv [phiClub] PLLFormula.falsePLL := by
  rintro ⟨d⟩
  refine Cclub_root_not_fallible (soundness d Cclub 0 ?_)
  intro ψ hψ
  have e : ψ = phiClub := by
    cases hψ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact Cclub_force_phiClub

/-! ## 3.  The automorphism `3 ↔ 4`, and the failure of every instance -/

/-- The transposition of the two indistinguishable maximal worlds. -/
def swc : Fin 5 → Fin 5 := fun x => if x = 3 then 4 else if x = 4 then 3 else x

theorem swc_invol : ∀ x : Fin 5, swc (swc x) = x := by decide
theorem swc_ri : ∀ x y : Fin 5, Rc x y ↔ Rc (swc x) (swc y) := by decide
theorem swc_rm : ∀ x y : Fin 5, Rmc x y ↔ Rmc (swc x) (swc y) := by decide
theorem swc_F : ∀ x : Fin 5, x = 2 ↔ swc x = 2 := by decide
theorem swc_three : swc 3 = 4 := by decide

/-- **The automorphism argument.**  Variable-free formulas cannot tell a
world of `C♣` from its image under `3 ↔ 4`. -/
theorem Cclub_swap : ∀ {A : PLLFormula}, atomFree A = true → ∀ x : Fin 5,
    (Cclub.force x A ↔ Cclub.force (swc x) A) := by
  intro A
  induction A with
  | prop a => intro h; exact absurd h (by simp [atomFree])
  | falsePLL => intro _ x; exact swc_F x
  | and A B ihA ihB =>
      intro h x
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      exact and_congr (ihA h'.1 x) (ihB h'.2 x)
  | or A B ihA ihB =>
      intro h x
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      exact or_congr (ihA h'.1 x) (ihB h'.2 x)
  | ifThen A B ihA ihB =>
      intro h x
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      constructor
      · intro hh v hv hA
        have hv' : Cclub.Ri x (swc v) := by
          refine (swc_ri x (swc v)).mpr ?_
          rw [swc_invol v]
          exact hv
        exact (ihB h'.2 v).mpr (hh (swc v) hv' ((ihA h'.1 v).mp hA))
      · intro hh v hv hA
        exact (ihB h'.2 v).mpr (hh (swc v) ((swc_ri x v).mp hv) ((ihA h'.1 v).mp hA))
  | somehow A ih =>
      intro h x
      constructor
      · intro hh v hv
        have hv' : Cclub.Ri x (swc v) := by
          refine (swc_ri x (swc v)).mpr ?_
          rw [swc_invol v]
          exact hv
        obtain ⟨u, hu, hA⟩ := hh (swc v) hv'
        refine ⟨swc u, ?_, (ih h u).mp hA⟩
        refine (swc_rm v (swc u)).mpr ?_
        rw [swc_invol u]
        exact hu
      · intro hh v hv
        obtain ⟨u, hu, hA⟩ := hh (swc v) ((swc_ri x v).mp hv)
        refine ⟨swc u, ?_, (ih h u).mp hA⟩
        refine (swc_rm v (swc u)).mpr ?_
        rw [swc_invol u]
        exact hu

/-- Worlds `3` and `4` satisfy the same variable-free formulas. -/
theorem Cclub_swap34 {A : PLLFormula} (hA : atomFree A = true) :
    Cclub.force (3 : Fin 5) A ↔ Cclub.force (4 : Fin 5) A := by
  have h := Cclub_swap hA 3
  rwa [swc_three] at h

theorem inst_phiClub (θ : PLLFormula) :
    inst θ phiClub
      = ((θ.ifThen oBot).or ((θ.ifThen .falsePLL).ifThen oBot)).ifThen
          ((oBot.ifThen .falsePLL).or (oBot.and θ)) := by
  show (((inst θ (PLLFormula.prop pv)).ifThen (inst θ oBot)).or
      (((inst θ (PLLFormula.prop pv)).ifThen (inst θ PLLFormula.falsePLL)).ifThen
        (inst θ oBot))).ifThen
      (((inst θ oBot).ifThen (inst θ PLLFormula.falsePLL)).or
        ((inst θ oBot).and (inst θ (PLLFormula.prop pv)))) = _
  rw [inst_var_eq, inst_atomFree_eq θ (show atomFree oBot = true from rfl)]
  rfl

/-- **No variable-free instance of `φ♣` is forced at the root of `C♣`.**
The consequent fails at `0` outright (`0 ⊮ ◯⊥` and `0 ⊮ ¬◯⊥`), so it is
enough that the ANTECEDENT holds there — and it does: if `θ` reaches
world `3` it reaches `4` as well (`Cclub_swap34`), and then `¬θ` is
confined to `‖◯⊥‖`, so `¬θ ⊃ ◯⊥` holds at `0`; if it does not, `θ`
itself is confined to `‖◯⊥‖`, so `θ ⊃ ◯⊥` holds at `0`. -/
theorem Cclub_inst_fails {θ : PLLFormula} (hθ : atomFree θ = true) :
    ¬ Cclub.force (0 : Fin 5) (inst θ phiClub) := by
  classical
  rw [inst_phiClub θ]
  intro h
  have hcons : ¬ Cclub.force (0 : Fin 5)
      ((oBot.ifThen .falsePLL).or (oBot.and θ)) := by
    rintro (h1 | ⟨h2, -⟩)
    · exact absurd ((Cclub_nOBot_iff 0).mp h1) (by decide)
    · exact absurd ((Cclub_oBot_iff 0).mp h2) (by decide)
  refine hcons (h 0 (Rc_refl 0) ?_)
  by_cases h3 : Cclub.force (3 : Fin 5) θ
  · -- `¬θ ⊃ ◯⊥` holds at the root
    refine Or.inr ?_
    intro u hu hnu
    have h4 : Cclub.force (4 : Fin 5) θ := (Cclub_swap34 hθ).mp h3
    rcases Fin5_cases u with rfl | rfl | rfl | rfl | rfl
    · have hb : (3 : Fin 5) = 2 := hnu 3 (by decide) h3
      exact absurd hb (by decide)
    · exact (Cclub_oBot_iff 1).mpr (by decide)
    · exact (Cclub_oBot_iff 2).mpr (by decide)
    · have hb : (3 : Fin 5) = 2 := hnu 3 (Rc_refl 3) h3
      exact absurd hb (by decide)
    · have hb : (4 : Fin 5) = 2 := hnu 4 (Rc_refl 4) h4
      exact absurd hb (by decide)
  · -- `θ ⊃ ◯⊥` holds at the root
    refine Or.inl ?_
    intro u hu hθu
    have h4 : ¬ Cclub.force (4 : Fin 5) θ := fun hh => h3 ((Cclub_swap34 hθ).mpr hh)
    have h0 : ¬ Cclub.force (0 : Fin 5) θ := fun hh =>
      h3 (Cclub.force_hered (show Cclub.Ri 0 3 by decide) hh)
    rcases Fin5_cases u with rfl | rfl | rfl | rfl | rfl
    · exact absurd hθu h0
    · exact (Cclub_oBot_iff 1).mpr (by decide)
    · exact (Cclub_oBot_iff 2).mpr (by decide)
    · exact absurd hθu h3
    · exact absurd hθu h4

/-! ## 4.  Every guarded stretch and every `(χ,⊥)`-fork fails -/

/-- **Every guarded stretch fails, uniformly in the guard.**  At the
ground copy of world `1` the antecedent's first disjunct holds outright
(`◯⊥` is forced there, so `p ⊃ ◯⊥` is vacuous), while the consequent
fails: `1 ⊮ ¬◯⊥`, and `p` on the ground layer means "fallible". -/
theorem Cclub_gstretch_fails (χ : PLLFormula) :
    ¬ (gstretch Cclub χ).force (Sum.inl (0 : Fin 5)) phiClub := by
  intro h
  have hb1 : (gstretch Cclub χ).force (Sum.inl (1 : Fin 5)) oBot :=
    (gstretch_transfer (C := Cclub) (χ := χ) atomFree_oBot 1).1.mpr
      ((Cclub_oBot_iff 1).mpr (by decide))
  have hante : (gstretch Cclub χ).force (Sum.inl (1 : Fin 5)) clubAnte :=
    Or.inl (fun q hq _ => (gstretch Cclub χ).force_hered hq hb1)
  rcases h (Sum.inl (1 : Fin 5)) (show Rc 0 1 by decide) hante with hn | ⟨-, hp⟩
  · have hbad : (gstretch Cclub χ).force (Sum.inl (1 : Fin 5)) PLLFormula.falsePLL :=
      hn (Sum.inl (1 : Fin 5)) ((gstretch Cclub χ).refl_i _) hb1
    have hbad' : (1 : Fin 5) = 2 := hbad
    exact absurd hbad' (by decide)
  · have hp' : (1 : Fin 5) = 2 := hp
    exact absurd hp' (by decide)

/-- **Every `(χ,⊥)`-fork fails.**  If the guard misses the root, the
cross edge `inl 0 ⇝ inr 1` exists and `inr 1` refutes (there `p` is
`⊥`); if the guard covers the root it covers everything, the two copies
never see each other, `p` is `⊤` on the first copy and `inl 0` itself
refutes. -/
theorem Cclub_bstretch_fails (χ : PLLFormula) :
    ¬ (bstretch Cclub χ).force (Sum.inl (0 : Fin 5)) phiClub := by
  classical
  intro h
  by_cases h0 : Cclub.force (0 : Fin 5) χ
  · -- the guard covers the whole model
    have hall : ∀ x : Fin 5, Cclub.force x χ := fun x =>
      Cclub.force_hered (show Cclub.Ri 0 x by
        rcases Fin5_cases x with rfl | rfl | rfl | rfl | rfl <;> decide) h0
    have hante : (bstretch Cclub χ).force (Sum.inl (0 : Fin 5)) clubAnte := by
      refine Or.inr ?_
      rintro (y | y) hq hnp
      · have hpy : (bstretch Cclub χ).force (Sum.inl y) (PLLFormula.prop pv) := hall y
        have hfy : (bstretch Cclub χ).force (Sum.inl y) PLLFormula.falsePLL :=
          hnp (Sum.inl y) ((bstretch Cclub χ).refl_i _) hpy
        exact (bstretch Cclub χ).force_of_fallible hfy
      · exact absurd h0 hq.2
    rcases h (Sum.inl (0 : Fin 5)) (Rc_refl 0) hante with hn | ⟨hb, -⟩
    · have hb1 : (bstretch Cclub χ).force (Sum.inl (1 : Fin 5)) oBot :=
        (bstretch_transfer (C := Cclub) (χ := χ) atomFree_oBot 1).1.mpr
          ((Cclub_oBot_iff 1).mpr (by decide))
      have hbad : (bstretch Cclub χ).force (Sum.inl (1 : Fin 5)) PLLFormula.falsePLL :=
        hn (Sum.inl (1 : Fin 5)) (show Rc 0 1 by decide) hb1
      have hbad' : (1 : Fin 5) = 2 := hbad
      exact absurd hbad' (by decide)
    · exact absurd ((Cclub_oBot_iff 0).mp
        ((bstretch_transfer (C := Cclub) (χ := χ) atomFree_oBot 0).1.mp hb)) (by decide)
  · -- the cross edge `inl 0 ⇝ inr 1` exists
    have hb1 : (bstretch Cclub χ).force (Sum.inr (1 : Fin 5)) oBot :=
      (bstretch_transfer (C := Cclub) (χ := χ) atomFree_oBot 1).2.mpr
        ((Cclub_oBot_iff 1).mpr (by decide))
    have hante : (bstretch Cclub χ).force (Sum.inr (1 : Fin 5)) clubAnte :=
      Or.inl (fun q hq _ => (bstretch Cclub χ).force_hered hq hb1)
    rcases h (Sum.inr (1 : Fin 5)) ⟨show Rc 0 1 by decide, h0⟩ hante with hn | ⟨-, hp⟩
    · have hbad : (bstretch Cclub χ).force (Sum.inr (1 : Fin 5)) PLLFormula.falsePLL :=
        hn (Sum.inr (1 : Fin 5)) ((bstretch Cclub χ).refl_i _) hb1
      have hbad' : (1 : Fin 5) = 2 := hbad
      exact absurd hbad' (by decide)
    · have hp' : (1 : Fin 5) = 2 := hp
      exact absurd hp' (by decide)

theorem Cclub_LoG_fails (χ : PLLFormula) : ¬ Cclub.force (0 : Fin 5) (LoG χ phiClub) :=
  fun h => Cclub_gstretch_fails χ ((gstretch_tr (C := Cclub) (χ := χ) phiClub 0).1.mpr h)

theorem Cclub_BLo_fails (χ : PLLFormula) : ¬ Cclub.force (0 : Fin 5) (BLo χ phiClub) :=
  fun h => Cclub_bstretch_fails χ ((bstretch_tr (C := Cclub) (χ := χ) phiClub 0).1.mpr h)

/-- **`φ♣` has NO branch-mixed cover.** -/
theorem phiClub_no_branchMixedCover : ¬ HasBranchMixedCover phiClub :=
  not_hasBranchMixedCover_of_model Cclub 0 Cclub_force_phiClub Cclub_root_not_fallible
    (fun χ _ => Cclub_LoG_fails χ) (fun χ _ => Cclub_BLo_fails χ)
    (fun _ hθ => Cclub_inst_fails hθ)

/-- **REFUTED: `BranchMixedConj`** — the successor conjecture of
`wip/branchdia.lean` §8, as stated. -/
theorem branchMixedConj_false : ¬ BranchMixedConj :=
  fun h => phiClub_no_branchMixedCover (h phiClub phiClub_onlyPv)

/-- A fortiori `φ♣` has no guarded mixed cover. -/
theorem phiClub_no_guardedMixedCover : ¬ HasGuardedMixedCover phiClub :=
  fun h => phiClub_no_branchMixedCover (hasBranchMixedCover_of_guardedMixed h)

theorem phiClub_no_mixedCover : ¬ HasMixedCover phiClub :=
  fun h => phiClub_no_guardedMixedCover (hasGuardedMixedCover_of_mixed h)

theorem phiClub_no_cover : ¬ HasCover phiClub :=
  fun h => phiClub_no_mixedCover (hasMixedCover_of_cover h)

/-! ## 5.  The UPPER BOUND: `φ♣ ⊢ ¬¬◯⊥ ⊃ ◯⊥`

Unlike `φ★` and `φ♦`, `φ♣` does NOT entail `¬¬◯⊥`: assuming `¬◯⊥` the
consequent's FIRST disjunct fires and nothing follows.  What it does
entail is the STABILITY of `◯⊥`.  Fix `v ⊒ w` with `v ⊩ ¬¬◯⊥` and
suppose `v ⊮ ◯⊥`.  Then `v ⊮ ¬◯⊥` (else `v ⊩ ⊥`), so `v` is a GAP
world and the antecedent of `φ♣` must fail at `v`; its second disjunct
supplies `z ⊒ v` with `z ⊩ ¬p` and `z ⊮ ◯⊥`.  But every `◯⊥`-world of
the cone forces `p` by (α), so `z ⊩ ¬◯⊥` — and `v ⊩ ¬¬◯⊥` then makes
`z` fallible, hence `z ⊩ ◯⊥`.  Contradiction. -/

/-- **`ψ♣ = ¬¬◯⊥ ⊃ ◯⊥`**, the stability of `◯⊥`. -/
def psiClub : PLLFormula := (nt (nt oBot)).ifThen oBot

theorem atomFree_psiClub : atomFree psiClub = true := rfl

/-- (α) Every `◯⊥`-world of a `φ♣`-cone forces `p`. -/
theorem phiClub_alpha {C : ConstraintModel} {v : C.W} (hv : C.force v phiClub)
    {u : C.W} (hu : C.Ri v u) (hub : C.force u oBot) :
    C.force u (PLLFormula.prop pv) := by
  rcases hv u hu (Or.inl (fun z hz _ => C.force_hered hz hub)) with hn | ⟨-, hp⟩
  · exact C.force_of_fallible (hn u (C.refl_i u) hub)
  · exact hp

/-- **The upper bound, semantically.** -/
theorem force_psiClub_of_phiClub {C : ConstraintModel} (w : C.W)
    (hw : C.force w phiClub) : C.force w psiClub := by
  classical
  intro v hwv hv
  by_contra hvb
  have hvphi : C.force v phiClub := C.force_hered hwv hw
  have hvn : ¬ C.force v (nt oBot) := fun hn =>
    hvb (C.force_of_fallible (hv v (C.refl_i v) hn))
  have hante : ¬ C.force v clubAnte := by
    intro ha
    rcases hvphi v (C.refl_i v) ha with hn | ⟨hb, -⟩
    · exact hvn hn
    · exact hvb hb
  have h2 : ¬ C.force v ((nt (PLLFormula.prop pv)).ifThen oBot) :=
    fun hh => hante (Or.inr hh)
  have hz : ∃ z, C.Ri v z ∧ C.force z (nt (PLLFormula.prop pv)) ∧ ¬ C.force z oBot := by
    by_contra hc
    refine h2 (fun z hzv hznp => ?_)
    by_contra hzb
    exact hc ⟨z, hzv, hznp, hzb⟩
  obtain ⟨z, hzv, hznp, hzb⟩ := hz
  have hzn : C.force z (nt oBot) := by
    intro u hu hub
    exact hznp u hu (phiClub_alpha hvphi (C.trans_i hzv hu) hub)
  exact hzb (C.force_of_fallible (hv z hzv hzn))

/-- **`φ♣ ⊢ ¬¬◯⊥ ⊃ ◯⊥`.** -/
theorem phiClub_psi : Deriv [phiClub] psiClub :=
  deriv_of_valid (fun _ w hw => force_psiClub_of_phiClub w hw)

/-- `ψ♣` is not a theorem: it fails at the root of `M3`, where `¬¬◯⊥`
holds and `◯⊥` does not. -/
theorem psiClub_not_thm : ¬ Deriv [] psiClub := by
  rintro ⟨d⟩
  have hs := soundness d M3 (0 : Fin 3) (fun ψ hψ => by cases hψ)
  have hb : M3.force (0 : Fin 3) oBot := hs 0 (le_refl (0 : Fin 3)) M3_root_nnbox
  obtain ⟨u, hu, hf⟩ := hb 0 (le_refl (0 : Fin 3))
  have hu2 : u = 2 := hf
  subst hu2
  have hu' : Rm3 0 2 := hu
  exact absurd hu' (by decide)

/-- `ψ♣` is consistent. -/
theorem psiClub_ne_bot : ¬ Deriv [psiClub] PLLFormula.falsePLL :=
  fun h => phiClub_consistent (Deriv.cutHead phiClub_psi h)

/-! ## 6.  The PARAMETERISED fork -/

/-- The valuation of `fork C χ δ₁ δ₂`: `‖δ₁‖` on the `inl` copy, `‖δ₂‖`
on the `inr` copy. -/
def fV (C : ConstraintModel) (δ₁ δ₂ : PLLFormula) : Set (C.W ⊕ C.W) :=
  fun q => match q with
    | .inl x => C.force x δ₁
    | .inr x => C.force x δ₂

/-- **The parameterised `χ`-guarded fork of `C`**: the frame of
`bstretch C χ` with FREE copy valuations `δ₁`, `δ₂`.  The only condition
is `δᵢ ⊢ χ`, used exactly once — to make `hered_V` vacuous on the cross
edges, which exist out of `x` only when `x ⊮ χ`. -/
@[reducible] def fork (C : ConstraintModel) (χ δ₁ δ₂ : PLLFormula)
    (h₁ : ∀ x : C.W, C.force x δ₁ → C.force x χ)
    (h₂ : ∀ x : C.W, C.force x δ₂ → C.force x χ) : ConstraintModel where
  W := C.W ⊕ C.W
  Ri := bRi C χ
  Rm := stRm C
  F := stF C
  V _ := fV C δ₁ δ₂
  refl_i := by rintro (x | x) <;> exact C.refl_i x
  trans_i := by
    rintro (x | x) (y | y) (z | z) hh1 hh2
    · exact C.trans_i hh1 hh2
    · exact ⟨C.trans_i hh1 hh2.1, not_force_of_Ri hh1 hh2.2⟩
    · exact C.trans_i hh1.1 hh2.1
    · exact ⟨C.trans_i hh1.1 hh2, hh1.2⟩
    · exact ⟨C.trans_i hh1.1 hh2, hh1.2⟩
    · exact C.trans_i hh1.1 hh2.1
    · exact ⟨C.trans_i hh1 hh2.1, not_force_of_Ri hh1 hh2.2⟩
    · exact C.trans_i hh1 hh2
  refl_m := by rintro (x | x) <;> exact C.refl_m x
  trans_m := by
    rintro (x | x) (y | y) (z | z) hh1 hh2
    · exact C.trans_m hh1 hh2
    · exact hh2.elim
    · exact hh1.elim
    · exact hh1.elim
    · exact hh1.elim
    · exact hh1.elim
    · exact hh2.elim
    · exact C.trans_m hh1 hh2
  sub_mi := by
    rintro (x | x) (y | y) hh
    · exact C.sub_mi hh
    · exact hh.elim
    · exact hh.elim
    · exact C.sub_mi hh
  hered_F := by
    rintro (x | x) (y | y) hh hx
    · exact C.hered_F hh hx
    · exact C.hered_F hh.1 hx
    · exact C.hered_F hh.1 hx
    · exact C.hered_F hh hx
  hered_V := by
    rintro a (x | x) (y | y) hh hx
    · exact C.force_hered hh hx
    · exact absurd (h₁ x hx) hh.2
    · exact absurd (h₂ x hx) hh.2
    · exact C.force_hered hh hx
  full_F := by
    rintro a (x | x) hx
    · exact C.force_of_fallible hx
    · exact C.force_of_fallible hx

/-- **`bstretch C χ` IS `fork C χ χ ⊥`** — the `(χ,⊥)` member of the
parameterised family, definitionally. -/
theorem fork_eq_bstretch (C : ConstraintModel) (χ : PLLFormula) :
    fork C χ χ PLLFormula.falsePLL (fun _ h => h)
        (fun _ h => C.force_of_fallible h) = bstretch C χ := rfl

/-! ## 7.  Variable-free formulas cannot see the fork

The fork and the `(χ,⊥)`-fork have the SAME worlds, `Rᵢ`, `Rₘ` and `F`
— only `V` differs — so they agree on every variable-free formula, and
`bstretch_transfer` transfers. -/

theorem fork_force_eq {C : ConstraintModel} {χ δ₁ δ₂ : PLLFormula}
    {h₁ : ∀ x : C.W, C.force x δ₁ → C.force x χ}
    {h₂ : ∀ x : C.W, C.force x δ₂ → C.force x χ} :
    ∀ {A : PLLFormula}, atomFree A = true → ∀ q : C.W ⊕ C.W,
      ((fork C χ δ₁ δ₂ h₁ h₂).force q A ↔ (bstretch C χ).force q A) := by
  intro A
  induction A with
  | prop a => intro h; exact absurd h (by simp [atomFree])
  | falsePLL => intro _ _; exact Iff.rfl
  | and A B ihA ihB =>
      intro h q
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      exact and_congr (ihA h'.1 q) (ihB h'.2 q)
  | or A B ihA ihB =>
      intro h q
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      exact or_congr (ihA h'.1 q) (ihB h'.2 q)
  | ifThen A B ihA ihB =>
      intro h q
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      show (∀ r : C.W ⊕ C.W, bRi C χ q r →
              (fork C χ δ₁ δ₂ h₁ h₂).force r A → (fork C χ δ₁ δ₂ h₁ h₂).force r B) ↔
           (∀ r : C.W ⊕ C.W, bRi C χ q r →
              (bstretch C χ).force r A → (bstretch C χ).force r B)
      constructor
      · intro hh r hr hA
        exact (ihB h'.2 r).mp (hh r hr ((ihA h'.1 r).mpr hA))
      · intro hh r hr hA
        exact (ihB h'.2 r).mpr (hh r hr ((ihA h'.1 r).mp hA))
  | somehow A ih =>
      intro h q
      show (∀ r : C.W ⊕ C.W, bRi C χ q r →
              ∃ s, stRm C r s ∧ (fork C χ δ₁ δ₂ h₁ h₂).force s A) ↔
           (∀ r : C.W ⊕ C.W, bRi C χ q r →
              ∃ s, stRm C r s ∧ (bstretch C χ).force s A)
      constructor
      · intro hh r hr
        obtain ⟨s, hs, hfs⟩ := hh r hr
        exact ⟨s, hs, (ih h s).mp hfs⟩
      · intro hh r hr
        obtain ⟨s, hs, hfs⟩ := hh r hr
        exact ⟨s, hs, (ih h s).mpr hfs⟩

/-- **Transfer for the parameterised fork.** -/
theorem fork_transfer {C : ConstraintModel} {χ δ₁ δ₂ : PLLFormula}
    {h₁ : ∀ x : C.W, C.force x δ₁ → C.force x χ}
    {h₂ : ∀ x : C.W, C.force x δ₂ → C.force x χ}
    {A : PLLFormula} (hA : atomFree A = true) (x : C.W) :
    ((fork C χ δ₁ δ₂ h₁ h₂).force (.inl x) A ↔ C.force x A) ∧
    ((fork C χ δ₁ δ₂ h₁ h₂).force (.inr x) A ↔ C.force x A) :=
  ⟨(fork_force_eq hA _).trans (bstretch_transfer hA x).1,
   (fork_force_eq hA _).trans (bstretch_transfer hA x).2⟩

/-! ## 8.  The parameterised translations -/

/-- The pair of translations of the parameterised fork: `trB` with the
atom clause freed. -/
def trF (χ δ₁ δ₂ : PLLFormula) : PLLFormula → PLLFormula × PLLFormula
  | .prop _ => (δ₁, δ₂)
  | .falsePLL => (PLLFormula.falsePLL, PLLFormula.falsePLL)
  | .and A B =>
      ((trF χ δ₁ δ₂ A).1.and (trF χ δ₁ δ₂ B).1, (trF χ δ₁ δ₂ A).2.and (trF χ δ₁ δ₂ B).2)
  | .or A B =>
      ((trF χ δ₁ δ₂ A).1.or (trF χ δ₁ δ₂ B).1, (trF χ δ₁ δ₂ A).2.or (trF χ δ₁ δ₂ B).2)
  | .ifThen A B =>
      (((trF χ δ₁ δ₂ A).1.ifThen (trF χ δ₁ δ₂ B).1).and
          (χ.or ((trF χ δ₁ δ₂ A).2.ifThen (trF χ δ₁ δ₂ B).2)),
        ((trF χ δ₁ δ₂ A).2.ifThen (trF χ δ₁ δ₂ B).2).and
          (χ.or ((trF χ δ₁ δ₂ A).1.ifThen (trF χ δ₁ δ₂ B).1)))
  | .somehow A =>
      (((trF χ δ₁ δ₂ A).1.somehow).and (χ.or ((trF χ δ₁ δ₂ A).2.somehow)),
        ((trF χ δ₁ δ₂ A).2.somehow).and (χ.or ((trF χ δ₁ δ₂ A).1.somehow)))

/-- The FIRST-copy translation. -/
def FLo (χ δ₁ δ₂ A : PLLFormula) : PLLFormula := (trF χ δ₁ δ₂ A).1

/-- The SECOND-copy translation. -/
def FUp (χ δ₁ δ₂ A : PLLFormula) : PLLFormula := (trF χ δ₁ δ₂ A).2

theorem FLo_prop (χ δ₁ δ₂ : PLLFormula) (a : String) :
    FLo χ δ₁ δ₂ (PLLFormula.prop a) = δ₁ := rfl
theorem FUp_prop (χ δ₁ δ₂ : PLLFormula) (a : String) :
    FUp χ δ₁ δ₂ (PLLFormula.prop a) = δ₂ := rfl
theorem FLo_imp (χ δ₁ δ₂ A B : PLLFormula) :
    FLo χ δ₁ δ₂ (A.ifThen B)
      = ((FLo χ δ₁ δ₂ A).ifThen (FLo χ δ₁ δ₂ B)).and
          (χ.or ((FUp χ δ₁ δ₂ A).ifThen (FUp χ δ₁ δ₂ B))) := rfl
theorem FLo_box (χ δ₁ δ₂ A : PLLFormula) :
    FLo χ δ₁ δ₂ A.somehow
      = ((FLo χ δ₁ δ₂ A).somehow).and (χ.or ((FUp χ δ₁ δ₂ A).somehow)) := rfl

/-- **The degenerate instance: `FLo χ χ ⊥ = BLo χ`, `FUp χ χ ⊥ = BUp χ`.** -/
theorem trF_eq_trB (χ : PLLFormula) :
    ∀ A : PLLFormula, trF χ χ PLLFormula.falsePLL A = trB χ A := by
  intro A
  induction A with
  | prop a => rfl
  | falsePLL => rfl
  | and A B ihA ihB =>
      show ((trF χ χ PLLFormula.falsePLL A).1.and (trF χ χ PLLFormula.falsePLL B).1,
            (trF χ χ PLLFormula.falsePLL A).2.and (trF χ χ PLLFormula.falsePLL B).2) = _
      rw [ihA, ihB]; rfl
  | or A B ihA ihB =>
      show ((trF χ χ PLLFormula.falsePLL A).1.or (trF χ χ PLLFormula.falsePLL B).1,
            (trF χ χ PLLFormula.falsePLL A).2.or (trF χ χ PLLFormula.falsePLL B).2) = _
      rw [ihA, ihB]; rfl
  | ifThen A B ihA ihB =>
      show (((trF χ χ PLLFormula.falsePLL A).1.ifThen (trF χ χ PLLFormula.falsePLL B).1).and
              (χ.or ((trF χ χ PLLFormula.falsePLL A).2.ifThen
                (trF χ χ PLLFormula.falsePLL B).2)),
            ((trF χ χ PLLFormula.falsePLL A).2.ifThen
                (trF χ χ PLLFormula.falsePLL B).2).and
              (χ.or ((trF χ χ PLLFormula.falsePLL A).1.ifThen
                (trF χ χ PLLFormula.falsePLL B).1))) = _
      rw [ihA, ihB]; rfl
  | somehow A ihA =>
      show (((trF χ χ PLLFormula.falsePLL A).1.somehow).and
              (χ.or ((trF χ χ PLLFormula.falsePLL A).2.somehow)),
            ((trF χ χ PLLFormula.falsePLL A).2.somehow).and
              (χ.or ((trF χ χ PLLFormula.falsePLL A).1.somehow))) = _
      rw [ihA]; rfl

theorem FLo_eq_BLo (χ A : PLLFormula) : FLo χ χ PLLFormula.falsePLL A = BLo χ A := by
  show (trF χ χ PLLFormula.falsePLL A).1 = (trB χ A).1
  rw [trF_eq_trB]

/-- **Both translations are variable-free, provided the guard and the
two copy valuations are.** -/
theorem atomFree_trF {χ δ₁ δ₂ : PLLFormula} (hχ : atomFree χ = true)
    (hδ₁ : atomFree δ₁ = true) (hδ₂ : atomFree δ₂ = true) : ∀ A : PLLFormula,
    atomFree (FLo χ δ₁ δ₂ A) = true ∧ atomFree (FUp χ δ₁ δ₂ A) = true := by
  intro A
  induction A with
  | prop a => exact ⟨hδ₁, hδ₂⟩
  | falsePLL => exact ⟨rfl, rfl⟩
  | and A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show (atomFree (FLo χ δ₁ δ₂ A) && atomFree (FLo χ δ₁ δ₂ B)) = true
        rw [ihA.1, ihB.1]; rfl
      · show (atomFree (FUp χ δ₁ δ₂ A) && atomFree (FUp χ δ₁ δ₂ B)) = true
        rw [ihA.2, ihB.2]; rfl
  | or A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show (atomFree (FLo χ δ₁ δ₂ A) && atomFree (FLo χ δ₁ δ₂ B)) = true
        rw [ihA.1, ihB.1]; rfl
      · show (atomFree (FUp χ δ₁ δ₂ A) && atomFree (FUp χ δ₁ δ₂ B)) = true
        rw [ihA.2, ihB.2]; rfl
  | ifThen A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show ((atomFree (FLo χ δ₁ δ₂ A) && atomFree (FLo χ δ₁ δ₂ B)) &&
              (atomFree χ && (atomFree (FUp χ δ₁ δ₂ A) && atomFree (FUp χ δ₁ δ₂ B)))) = true
        rw [ihA.1, ihB.1, ihA.2, ihB.2, hχ]; rfl
      · show ((atomFree (FUp χ δ₁ δ₂ A) && atomFree (FUp χ δ₁ δ₂ B)) &&
              (atomFree χ && (atomFree (FLo χ δ₁ δ₂ A) && atomFree (FLo χ δ₁ δ₂ B)))) = true
        rw [ihA.1, ihB.1, ihA.2, ihB.2, hχ]; rfl
  | somehow A ihA =>
      refine ⟨?_, ?_⟩
      · show (atomFree (FLo χ δ₁ δ₂ A) && (atomFree χ && atomFree (FUp χ δ₁ δ₂ A))) = true
        rw [ihA.1, ihA.2, hχ]; rfl
      · show (atomFree (FUp χ δ₁ δ₂ A) && (atomFree χ && atomFree (FLo χ δ₁ δ₂ A))) = true
        rw [ihA.1, ihA.2, hχ]; rfl

theorem atomFree_FLo {χ δ₁ δ₂ : PLLFormula} (hχ : atomFree χ = true)
    (hδ₁ : atomFree δ₁ = true) (hδ₂ : atomFree δ₂ = true) (A : PLLFormula) :
    atomFree (FLo χ δ₁ δ₂ A) = true := (atomFree_trF hχ hδ₁ hδ₂ A).1

/-- **The parameterised translation theorem.**  Forcing at either copy
of `x` in `fork C χ δ₁ δ₂` is forcing of the corresponding translation
at `x`. -/
theorem fork_tr {C : ConstraintModel} {χ δ₁ δ₂ : PLLFormula}
    {h₁ : ∀ x : C.W, C.force x δ₁ → C.force x χ}
    {h₂ : ∀ x : C.W, C.force x δ₂ → C.force x χ} :
    ∀ (A : PLLFormula) (x : C.W),
      ((fork C χ δ₁ δ₂ h₁ h₂).force (.inl x) A ↔ C.force x (FLo χ δ₁ δ₂ A)) ∧
      ((fork C χ δ₁ δ₂ h₁ h₂).force (.inr x) A ↔ C.force x (FUp χ δ₁ δ₂ A)) := by
  classical
  intro A
  induction A with
  | prop a => exact fun _ => ⟨Iff.rfl, Iff.rfl⟩
  | falsePLL => exact fun _ => ⟨Iff.rfl, Iff.rfl⟩
  | and A B ihA ihB =>
      exact fun x => ⟨and_congr (ihA x).1 (ihB x).1, and_congr (ihA x).2 (ihB x).2⟩
  | or A B ihA ihB =>
      exact fun x => ⟨or_congr (ihA x).1 (ihB x).1, or_congr (ihA x).2 (ihB x).2⟩
  | ifThen A B ihA ihB =>
      intro x
      constructor
      · show (∀ q : C.W ⊕ C.W, bRi C χ (.inl x) q →
                (fork C χ δ₁ δ₂ h₁ h₂).force q A → (fork C χ δ₁ δ₂ h₁ h₂).force q B) ↔
             (C.force x ((FLo χ δ₁ δ₂ A).ifThen (FLo χ δ₁ δ₂ B)) ∧
              (C.force x χ ∨ C.force x ((FUp χ δ₁ δ₂ A).ifThen (FUp χ δ₁ δ₂ B))))
        constructor
        · intro hh
          refine ⟨fun y hy hA => (ihB y).1.mp (hh (.inl y) hy ((ihA y).1.mpr hA)), ?_⟩
          by_cases hx : C.force x χ
          · exact Or.inl hx
          · exact Or.inr (fun y hy hA =>
              (ihB y).2.mp (hh (.inr y) ⟨hy, hx⟩ ((ihA y).2.mpr hA)))
        · rintro ⟨hc1, hc2⟩ (y | y) hq hA
          · exact (ihB y).1.mpr (hc1 y hq ((ihA y).1.mp hA))
          · rcases hc2 with hx | hc2'
            · exact absurd hx hq.2
            · exact (ihB y).2.mpr (hc2' y hq.1 ((ihA y).2.mp hA))
      · show (∀ q : C.W ⊕ C.W, bRi C χ (.inr x) q →
                (fork C χ δ₁ δ₂ h₁ h₂).force q A → (fork C χ δ₁ δ₂ h₁ h₂).force q B) ↔
             (C.force x ((FUp χ δ₁ δ₂ A).ifThen (FUp χ δ₁ δ₂ B)) ∧
              (C.force x χ ∨ C.force x ((FLo χ δ₁ δ₂ A).ifThen (FLo χ δ₁ δ₂ B))))
        constructor
        · intro hh
          refine ⟨fun y hy hA => (ihB y).2.mp (hh (.inr y) hy ((ihA y).2.mpr hA)), ?_⟩
          by_cases hx : C.force x χ
          · exact Or.inl hx
          · exact Or.inr (fun y hy hA =>
              (ihB y).1.mp (hh (.inl y) ⟨hy, hx⟩ ((ihA y).1.mpr hA)))
        · rintro ⟨hc1, hc2⟩ (y | y) hq hA
          · rcases hc2 with hx | hc2'
            · exact absurd hx hq.2
            · exact (ihB y).1.mpr (hc2' y hq.1 ((ihA y).1.mp hA))
          · exact (ihB y).2.mpr (hc1 y hq ((ihA y).2.mp hA))
  | somehow A ih =>
      intro x
      constructor
      · show (∀ q : C.W ⊕ C.W, bRi C χ (.inl x) q →
                ∃ r, stRm C q r ∧ (fork C χ δ₁ δ₂ h₁ h₂).force r A) ↔
             (C.force x ((FLo χ δ₁ δ₂ A).somehow) ∧
              (C.force x χ ∨ C.force x ((FUp χ δ₁ δ₂ A).somehow)))
        constructor
        · intro hh
          constructor
          · intro v hv
            obtain ⟨r, hr, hfr⟩ := hh (.inl v) hv
            match r, hr, hfr with
            | .inl r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).1.mp hfr⟩
            | .inr r₁, hr, _ => exact hr.elim
          · by_cases hx : C.force x χ
            · exact Or.inl hx
            · refine Or.inr (fun v hv => ?_)
              obtain ⟨r, hr, hfr⟩ := hh (.inr v) ⟨hv, hx⟩
              match r, hr, hfr with
              | .inl r₁, hr, _ => exact hr.elim
              | .inr r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).2.mp hfr⟩
        · rintro ⟨hc1, hc2⟩ (y | y) hq
          · obtain ⟨u, hu, hfu⟩ := hc1 y hq
            exact ⟨.inl u, hu, (ih u).1.mpr hfu⟩
          · rcases hc2 with hx | hc2'
            · exact absurd hx hq.2
            · obtain ⟨u, hu, hfu⟩ := hc2' y hq.1
              exact ⟨.inr u, hu, (ih u).2.mpr hfu⟩
      · show (∀ q : C.W ⊕ C.W, bRi C χ (.inr x) q →
                ∃ r, stRm C q r ∧ (fork C χ δ₁ δ₂ h₁ h₂).force r A) ↔
             (C.force x ((FUp χ δ₁ δ₂ A).somehow) ∧
              (C.force x χ ∨ C.force x ((FLo χ δ₁ δ₂ A).somehow)))
        constructor
        · intro hh
          constructor
          · intro v hv
            obtain ⟨r, hr, hfr⟩ := hh (.inr v) hv
            match r, hr, hfr with
            | .inl r₁, hr, _ => exact hr.elim
            | .inr r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).2.mp hfr⟩
          · by_cases hx : C.force x χ
            · exact Or.inl hx
            · refine Or.inr (fun v hv => ?_)
              obtain ⟨r, hr, hfr⟩ := hh (.inl v) ⟨hv, hx⟩
              match r, hr, hfr with
              | .inl r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).1.mp hfr⟩
              | .inr r₁, hr, _ => exact hr.elim
        · rintro ⟨hc1, hc2⟩ (y | y) hq
          · rcases hc2 with hx | hc2'
            · exact absurd hx hq.2
            · obtain ⟨u, hu, hfu⟩ := hc2' y hq.1
              exact ⟨.inl u, hu, (ih u).1.mpr hfu⟩
          · obtain ⟨u, hu, hfu⟩ := hc1 y hq
            exact ⟨.inr u, hu, (ih u).2.mpr hfu⟩

/-! ## 9.  The parameterised lower bounds, and the method -/

/-- One-hypothesis soundness, in the pointwise form the fork needs
(`wip/collapse.lean`'s `force_of_deriv1`, with the model explicit). -/
theorem forceMap {A B : PLLFormula} (h : Deriv [A] B) (C : ConstraintModel) :
    ∀ x : C.W, C.force x A → C.force x B :=
  fun _ hx => force_of_deriv1 (C := C) h hx

/-- **THE PARAMETERISED FORK LOWER BOUND, first copy.**  For every
triple `(χ, δ₁, δ₂)` with `δ₁ ⊢ χ` and `δ₂ ⊢ χ`, the formula
`FLo χ δ₁ δ₂ φ` lies below every variable-free consequence of `φ`. -/
theorem fork_below {χ δ₁ δ₂ φ ψ : PLLFormula} (hd₁ : Deriv [δ₁] χ) (hd₂ : Deriv [δ₂] χ)
    (hψ : atomFree ψ = true) (h : Deriv [φ] ψ) : Deriv [FLo χ δ₁ δ₂ φ] ψ := by
  classical
  by_contra hcon
  obtain ⟨C, -, u, hu, hnu⟩ := countermodel_of_not_deriv hcon
  obtain ⟨d⟩ := h
  refine hnu ((fork_transfer (h₁ := forceMap hd₁ C)
    (h₂ := forceMap hd₂ C) hψ u).1.mp
      (soundness d (fork C χ δ₁ δ₂ (forceMap hd₁ C) (forceMap hd₂ C))
        (.inl u) ?_))
  intro ρ hρ
  have e : ρ = φ := by
    cases hρ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact (fork_tr _ u).1.mpr hu

/-- **… and the second copy.** -/
theorem fork_below_up {χ δ₁ δ₂ φ ψ : PLLFormula} (hd₁ : Deriv [δ₁] χ) (hd₂ : Deriv [δ₂] χ)
    (hψ : atomFree ψ = true) (h : Deriv [φ] ψ) : Deriv [FUp χ δ₁ δ₂ φ] ψ := by
  classical
  by_contra hcon
  obtain ⟨C, -, u, hu, hnu⟩ := countermodel_of_not_deriv hcon
  obtain ⟨d⟩ := h
  refine hnu ((fork_transfer (h₁ := forceMap hd₁ C)
    (h₂ := forceMap hd₂ C) hψ u).2.mp
      (soundness d (fork C χ δ₁ δ₂ (forceMap hd₁ C) (forceMap hd₂ C))
        (.inr u) ?_))
  intro ρ hρ
  have e : ρ = φ := by
    cases hρ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact (fork_tr _ u).2.mpr hu

/-- **`φ` has a parameterised fork cover at `(χ, δ₁, δ₂)`.** -/
def HasForkCover (χ δ₁ δ₂ φ : PLLFormula) : Prop := Deriv [φ] (FLo χ δ₁ δ₂ φ)

/-- **MASTER REDUCTION for the parameterised fork method.** -/
theorem postInterp_of_fork {χ δ₁ δ₂ φ : PLLFormula} (hχ : atomFree χ = true)
    (hδ₁ : atomFree δ₁ = true) (hδ₂ : atomFree δ₂ = true)
    (hd₁ : Deriv [δ₁] χ) (hd₂ : Deriv [δ₂] χ) (h : HasForkCover χ δ₁ δ₂ φ) :
    IsPostInterp φ (FLo χ δ₁ δ₂ φ) :=
  ⟨atomFree_FLo hχ hδ₁ hδ₂ φ, h, fun _ hψ hd => fork_below hd₁ hd₂ hψ hd⟩

/-- The semantic content of the parameterised fork bound. -/
theorem FLo_iff_fork {C : ConstraintModel} {χ δ₁ δ₂ : PLLFormula}
    {h₁ : ∀ x : C.W, C.force x δ₁ → C.force x χ}
    {h₂ : ∀ x : C.W, C.force x δ₂ → C.force x χ} (φ : PLLFormula) (w : C.W) :
    C.force w (FLo χ δ₁ δ₂ φ) ↔ (fork C χ δ₁ δ₂ h₁ h₂).force (.inl w) φ :=
  (fork_tr φ w).1.symm

/-! ## 10.  `∃p.φ♣ = ¬¬◯⊥ ⊃ ◯⊥` -/

/-- **The guard of the `φ♣`-fork**: `◯⊥ ∨ ¬◯⊥`, whose complement is
exactly the GAP region — so the two copies are glued precisely where
`φ♣`'s clause (β) has work to do. -/
def gapGuard : PLLFormula := oBot.or (nt oBot)

theorem atomFree_gapGuard : atomFree gapGuard = true := rfl

theorem gapGuard_le : Deriv [gapGuard] gapGuard := Deriv.iden (.head _)

theorem oBot_le_gapGuard : Deriv [oBot] gapGuard := Deriv.orIntro1 (Deriv.iden (.head _))

/-- **The `φ♣`-fork**: `δ₁ = ◯⊥ ∨ ¬◯⊥` on the first copy (so the first
copy has a `p`-world outside `‖◯⊥‖` wherever a `¬◯⊥`-world exists),
`δ₂ = ◯⊥` on the second (so the second copy has a `¬p`-world there),
and both are `⊇ ‖◯⊥‖`, which is clause (α). -/
@[reducible] def forkClub (C : ConstraintModel) : ConstraintModel :=
  fork C gapGuard gapGuard oBot (fun _ h => h) (fun _ h => Or.inl h)

/-- **The heart of the matter.**  If `u ⊩ ¬¬◯⊥ ⊃ ◯⊥` in `C` then `φ♣`
holds at the first copy of `u` in the `φ♣`-fork.  Three cases at a copy
`q` of `x ⊒ u`: `x ⊩ ◯⊥` gives the consequent's second disjunct (both
`δᵢ` contain `‖◯⊥‖`); `x ⊩ ¬◯⊥` gives the first; and in the GAP the
hypothesis produces a non-fallible `¬◯⊥`-world `y ⊒ x`, whose two copies
`inl y` (a `p`-world outside `‖◯⊥‖`) and `inr y` (a `¬p`-world outside
`‖◯⊥‖`) are BOTH above `q` — the cross edges out of `x` exist exactly
because `x` is in the gap — and they refute the two disjuncts of the
antecedent. -/
theorem forkClub_force_phiClub {C : ConstraintModel} {u : C.W}
    (hu : C.force u psiClub) : (forkClub C).force (.inl u) phiClub := by
  classical
  have main : ∀ (x : C.W), C.Ri u x → ∀ q : C.W ⊕ C.W,
      (q = Sum.inl x ∨ q = Sum.inr x) →
      (forkClub C).force q clubAnte → (forkClub C).force q clubCons := by
    intro x hux q hq ha
    by_cases hb : C.force x oBot
    · refine Or.inr ⟨?_, ?_⟩
      · rcases hq with rfl | rfl
        · exact (fork_transfer atomFree_oBot x).1.mpr hb
        · exact (fork_transfer atomFree_oBot x).2.mpr hb
      · rcases hq with rfl | rfl
        · exact (Or.inl hb : C.force x gapGuard)
        · exact hb
    · by_cases hn : C.force x (nt oBot)
      · refine Or.inl ?_
        rcases hq with rfl | rfl
        · exact (fork_transfer (A := nt oBot) rfl x).1.mpr hn
        · exact (fork_transfer (A := nt oBot) rfl x).2.mpr hn
      · exfalso
        have hxg : ¬ C.force x gapGuard := by
          rintro (h1 | h2)
          · exact hb h1
          · exact hn h2
        have hxnn : ¬ C.force x (nt (nt oBot)) := fun h => hb (hu x hux h)
        obtain ⟨y, hxy, hyn, hyf⟩ :
            ∃ y, C.Ri x y ∧ C.force y (nt oBot) ∧ ¬ C.force y PLLFormula.falsePLL := by
          by_contra hc
          refine hxnn (fun y hy hyn => ?_)
          by_contra hyf
          exact hc ⟨y, hy, hyn, hyf⟩
        have hyb : ¬ C.force y oBot := fun h => hyf (hyn y (C.refl_i y) h)
        have hyg : C.force y gapGuard := Or.inr hyn
        have hly : bRi C gapGuard q (Sum.inl y) := by
          rcases hq with rfl | rfl
          · exact hxy
          · exact ⟨hxy, hxg⟩
        have hry : bRi C gapGuard q (Sum.inr y) := by
          rcases hq with rfl | rfl
          · exact ⟨hxy, hxg⟩
          · exact hxy
        have hlyp : (forkClub C).force (Sum.inl y) (PLLFormula.prop pv) := hyg
        have hlyb : ¬ (forkClub C).force (Sum.inl y) oBot := fun h =>
          hyb ((fork_transfer atomFree_oBot y).1.mp h)
        have hrynp : (forkClub C).force (Sum.inr y) (nt (PLLFormula.prop pv)) := by
          rintro (z | z) hz hp
          · exact absurd hyg hz.2
          · exact hyn z hz hp
        have hryb : ¬ (forkClub C).force (Sum.inr y) oBot := fun h =>
          hyb ((fork_transfer atomFree_oBot y).2.mp h)
        rcases ha with h1 | h2
        · exact hlyb (h1 (Sum.inl y) hly hlyp)
        · exact hryb (h2 (Sum.inr y) hry hrynp)
  rintro (x | x) hq ha
  · exact main x hq (Sum.inl x) (Or.inl rfl) ha
  · exact main x hq.1 (Sum.inr x) (Or.inr rfl) ha

/-- **Minimality.**  Every variable-free consequence of `φ♣` is a
consequence of `¬¬◯⊥ ⊃ ◯⊥`. -/
theorem phiClub_minimal {χ : PLLFormula} (hχ : atomFree χ = true)
    (h : Deriv [phiClub] χ) : Deriv [psiClub] χ := by
  classical
  by_contra hcon
  obtain ⟨C, -, u, hu, hnu⟩ := countermodel_of_not_deriv hcon
  obtain ⟨d⟩ := h
  refine hnu ((fork_transfer hχ u).1.mp (soundness d (forkClub C) (.inl u) ?_))
  intro ψ hψ
  have e : ψ = phiClub := by
    cases hψ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact forkClub_force_phiClub hu

/-- **PROVED: `∃p.φ♣ = ¬¬◯⊥ ⊃ ◯⊥`.**  The formula that refutes the
branch-mixed method HAS a uniform post-interpolant over the
variable-free fragment — and it is NOT `¬¬◯⊥`. -/
theorem postInterp_phiClub : IsPostInterp phiClub psiClub :=
  ⟨atomFree_psiClub, phiClub_psi, fun _ hχ hd => phiClub_minimal hχ hd⟩

/-- `¬¬◯⊥ ⊃ ◯⊥ ⊢ FLo(◯⊥∨¬◯⊥, ◯⊥∨¬◯⊥, ◯⊥) φ♣` — `forkClub_force_phiClub`
read through the translation theorem. -/
theorem psi_to_FLo_phiClub : Deriv [psiClub] (FLo gapGuard gapGuard oBot phiClub) :=
  deriv_of_valid (fun _ u hu => (fork_tr phiClub u).1.mp (forkClub_force_phiClub hu))

/-- **`φ♣` HAS a parameterised fork cover** — while it has no
branch-mixed cover at all. -/
theorem hasForkCover_phiClub : HasForkCover gapGuard gapGuard oBot phiClub :=
  Deriv.cutHead phiClub_psi psi_to_FLo_phiClub

/-- The translation computes the interpolant. -/
theorem interd_FLo_phiClub : Interd (FLo gapGuard gapGuard oBot phiClub) psiClub :=
  ⟨fork_below gapGuard_le oBot_le_gapGuard atomFree_psiClub phiClub_psi,
   psi_to_FLo_phiClub⟩

/-- **The parameterised fork method is STRICTLY stronger than the whole
branch-mixed family**: `φ♣` has a parameterised fork cover and no
branch-mixed cover. -/
theorem paramFork_beats_branchMixed :
    ∃ φ : PLLFormula, onlyPv φ = true ∧
      HasForkCover gapGuard gapGuard oBot φ ∧ ¬ HasBranchMixedCover φ :=
  ⟨phiClub, phiClub_onlyPv, hasForkCover_phiClub, phiClub_no_branchMixedCover⟩

/-! ## 11.  The instance bound: `φ♣`'s substitution bounds are all
`⊣⊢ ◯⊥ ∨ ¬◯⊥`, STRICTLY below the interpolant -/

theorem force_truePLL' {C : ConstraintModel} (v : C.W) : C.force v truePLL :=
  fun _ _ h => h

/-- **`φ♣[p := ⊤] ⊣⊢ ◯⊥ ∨ ¬◯⊥`.** -/
theorem interd_instTop_phiClub : Interd (inst truePLL phiClub) gapGuard := by
  rw [inst_phiClub truePLL]
  constructor
  · refine deriv_of_valid (fun C v h => ?_)
    have hante : C.force v ((truePLL.ifThen oBot).or
        ((truePLL.ifThen .falsePLL).ifThen oBot)) := by
      refine Or.inr (fun u _ hu => ?_)
      exact C.force_of_fallible (hu u (C.refl_i u) (force_truePLL' u))
    rcases (h v (C.refl_i v) hante :
        C.force v (oBot.ifThen .falsePLL) ∨ C.force v (oBot.and truePLL)) with h1 | ⟨h2, -⟩
    · exact Or.inr h1
    · exact Or.inl h2
  · refine deriv_of_valid (fun C v h => ?_)
    intro w hw _
    rcases (h : C.force v oBot ∨ C.force v (nt oBot)) with h1 | h2
    · exact Or.inr ⟨C.force_hered hw h1, force_truePLL' w⟩
    · exact Or.inl (C.force_hered hw h2)

/-- **`φ♣[p := ⊥] ⊣⊢ ¬◯⊥`.** -/
theorem interd_instBot_phiClub : Interd (inst PLLFormula.falsePLL phiClub) (nt oBot) := by
  rw [inst_phiClub PLLFormula.falsePLL]
  constructor
  · refine deriv_of_valid (fun C v h => ?_)
    have hante : C.force v ((PLLFormula.falsePLL.ifThen oBot).or
        ((PLLFormula.falsePLL.ifThen .falsePLL).ifThen oBot)) :=
      Or.inl (fun u _ hu => C.force_of_fallible hu)
    rcases (h v (C.refl_i v) hante :
        C.force v (oBot.ifThen .falsePLL) ∨
          C.force v (oBot.and PLLFormula.falsePLL)) with h1 | ⟨-, h2⟩
    · exact h1
    · exact C.force_of_fallible h2
  · refine deriv_of_valid (fun C v h => ?_)
    intro w hw _
    exact Or.inl (C.force_hered hw h)

/-- `◯⊥ ∨ ¬◯⊥ ⊢ ¬¬◯⊥ ⊃ ◯⊥`: every instance bound lies below the
interpolant, as it must. -/
theorem gapGuard_to_psiClub : Deriv [gapGuard] psiClub := by
  refine deriv_of_valid (fun C v h => ?_)
  intro w hw hnn
  rcases (h : C.force v oBot ∨ C.force v (nt oBot)) with h1 | h2
  · exact C.force_hered hw h1
  · exact C.force_of_fallible (hnn w (C.refl_i w) (C.force_hered hw h2))

/-- **… and STRICTLY below**: `¬¬◯⊥ ⊃ ◯⊥ ⊬ ◯⊥ ∨ ¬◯⊥` (the root of `C♣`
forces the former and not the latter).  So no join of substitution
instances can reach `∃p.φ♣` — which is `phiClub_no_cover` again, from
above. -/
theorem psiClub_not_gapGuard : ¬ Deriv [psiClub] gapGuard := by
  rintro ⟨d⟩
  have hroot : Cclub.force (0 : Fin 5) psiClub := by
    intro v _ hv
    exact (Cclub_oBot_iff v).mpr ((Cclub_nnOBot_iff v).mp hv)
  have hs : Cclub.force (0 : Fin 5) gapGuard :=
    soundness d Cclub 0 (fun ψ hψ => by
      have e : ψ = psiClub := by
        cases hψ with
        | head => rfl
        | tail _ hh => cases hh
      subst e
      exact hroot)
  rcases (hs : Cclub.force (0 : Fin 5) oBot ∨ Cclub.force (0 : Fin 5) (nt oBot)) with h1 | h2
  · exact absurd ((Cclub_oBot_iff 0).mp h1) (by decide)
  · exact absurd ((Cclub_nOBot_iff 0).mp h2) (by decide)

/-- The interpolant of `φ♣` is not `⊤` and not `⊥`. -/
theorem postInterp_phiClub_ne_top : ¬ Deriv [] psiClub := psiClub_not_thm
theorem postInterp_phiClub_ne_bot : ¬ Deriv [psiClub] PLLFormula.falsePLL := psiClub_ne_bot

/-- **`∃p.φ♣ ≠ ¬¬◯⊥`.**  `φ♣ ⊬ ¬¬◯⊥`: the root of `C♣` forces `φ♣` and
not `¬¬◯⊥`.  So the value found at `φ★` and at `φ♦` is NOT a universal
attractor. -/
theorem phiClub_not_nnbox : ¬ Deriv [phiClub] (nt (nt oBot)) := by
  rintro ⟨d⟩
  have hs : Cclub.force (0 : Fin 5) (nt (nt oBot)) :=
    soundness d Cclub 0 (fun ψ hψ => by
      have e : ψ = phiClub := by
        cases hψ with
        | head => rfl
        | tail _ hh => cases hh
      subst e
      exact Cclub_force_phiClub)
  exact absurd ((Cclub_nnOBot_iff 0).mp hs) (by decide)

/-! ## 11′.  The guarded stretch is STILL needed: `φ★` has no
parameterised fork cover, at ANY admissible triple

Parameterising the fork does not absorb the guarded stretch.  At the
root of `M3` — which forces `¬¬◯⊥ = ∃p.φ★` (`M3_root_nnbox`) — the
`◯⊥`-guarded stretch delivers `φ★` (`hasGuardedCover_phiStar`), and no
fork does. -/

/-- **Every parameterised fork fails at `φ★` over `M3`.**  Three cases
on the copy valuations at world `1`:

* `1 ⊮ δ₁`: then `inl 1 ⊩ ¬p` — the only `p`-worlds above it are the
  fallible copies of `2`, since `inr 1 ⊩ p` would give `1 ⊩ δ₂ ⊢ χ`,
  and then the cross edge out of `inl 1` would not exist — and `inl 1`
  is not fallible, so `¬¬p` fails at `inl 0`;
* `1 ⊩ δ₁` and `0 ⊩ χ`: there are no cross edges out of `inl 0` at all,
  and every `◯⊥`-world of the `inl` copy forces `p`, so `◯⊥ ⊃ p` holds
  at `inl 0` and the first conjunct forces `◯⊥` there — which fails;
* `1 ⊩ δ₁` and `0 ⊮ χ`: from `δ₁ ⊢ χ` we get `1 ⊩ χ`, so there are no
  cross edges out of `inr 1`.  If `1 ⊩ δ₂` the previous argument
  applies (both copies of `1` force `p`); if not, `inr 1` is a
  non-fallible `¬p`-world above `inl 0`. -/
theorem M3_fork_phiStar_fails {χ δ₁ δ₂ : PLLFormula}
    (h₁ : ∀ x : M3.W, M3.force x δ₁ → M3.force x χ)
    (h₂ : ∀ x : M3.W, M3.force x δ₂ → M3.force x χ) :
    ¬ (fork M3 χ δ₁ δ₂ h₁ h₂).force (Sum.inl (0 : Fin 3)) phiStar := by
  classical
  rintro ⟨hc1, hc2⟩
  by_cases hd1 : M3.force (1 : Fin 3) δ₁
  · have h1χ : M3.force (1 : Fin 3) χ := h₁ 1 hd1
    have hinl : ∀ y : Fin 3, (fork M3 χ δ₁ δ₂ h₁ h₂).force (Sum.inl y) oBot →
        (fork M3 χ δ₁ δ₂ h₁ h₂).force (Sum.inl y) (PLLFormula.prop pv) := by
      intro y hb
      have hy : (1 : Fin 3) ≤ y := by
        rcases Fin3_all_cases y with rfl | rfl | rfl
        · exact absurd ((fork_transfer (h₁ := h₁) (h₂ := h₂) atomFree_oBot 0).1.mp hb)
            M3_not_oBot_zero
        · exact le_refl (1 : Fin 3)
        · exact (by decide : (1 : Fin 3) ≤ 2)
      exact M3.force_hered (show M3.Ri 1 y from hy) hd1
    by_cases h0χ : M3.force (0 : Fin 3) χ
    · have himp : (fork M3 χ δ₁ δ₂ h₁ h₂).force (Sum.inl (0 : Fin 3))
          (oBot.ifThen (PLLFormula.prop pv)) := by
        rintro (y | y) hq hb
        · exact hinl y hb
        · exact absurd h0χ hq.2
      have hcon := hc1 (Sum.inl (0 : Fin 3))
        ((fork M3 χ δ₁ δ₂ h₁ h₂).refl_i _) himp
      exact M3_not_oBot_zero
        ((fork_transfer (h₁ := h₁) (h₂ := h₂) atomFree_oBot 0).1.mp hcon.1)
    · by_cases hd2 : M3.force (1 : Fin 3) δ₂
      · have himp : (fork M3 χ δ₁ δ₂ h₁ h₂).force (Sum.inl (0 : Fin 3))
            (oBot.ifThen (PLLFormula.prop pv)) := by
          rintro (y | y) hq hb
          · exact hinl y hb
          · have hy : (1 : Fin 3) ≤ y := by
              rcases Fin3_all_cases y with rfl | rfl | rfl
              · exact absurd ((fork_transfer (h₁ := h₁) (h₂ := h₂) atomFree_oBot 0).2.mp hb)
                  M3_not_oBot_zero
              · exact le_refl (1 : Fin 3)
              · exact (by decide : (1 : Fin 3) ≤ 2)
            exact M3.force_hered (show M3.Ri 1 y from hy) hd2
        have hcon := hc1 (Sum.inl (0 : Fin 3))
          ((fork M3 χ δ₁ δ₂ h₁ h₂).refl_i _) himp
        exact M3_not_oBot_zero
          ((fork_transfer (h₁ := h₁) (h₂ := h₂) atomFree_oBot 0).1.mp hcon.1)
      · have hnp : (fork M3 χ δ₁ δ₂ h₁ h₂).force (Sum.inr (1 : Fin 3))
            (nt (PLLFormula.prop pv)) := by
          rintro (z | z) hz hp
          · exact absurd h1χ hz.2
          · rcases Fin3_all_cases z with rfl | rfl | rfl
            · have hz' : (1 : Fin 3) ≤ 0 := hz
              exact absurd hz' (by decide)
            · exact absurd hp hd2
            · rfl
        have hbad := hc2 (Sum.inr (1 : Fin 3))
          ⟨(by decide : M3.Ri 0 1), h0χ⟩ hnp
        have hbad' : (1 : Fin 3) = 2 := hbad
        exact absurd hbad' (by decide)
  · have hnp : (fork M3 χ δ₁ δ₂ h₁ h₂).force (Sum.inl (1 : Fin 3))
        (nt (PLLFormula.prop pv)) := by
      rintro (z | z) hz hp
      · rcases Fin3_all_cases z with rfl | rfl | rfl
        · have hz' : (1 : Fin 3) ≤ 0 := hz
          exact absurd hz' (by decide)
        · exact absurd hp hd1
        · rfl
      · rcases Fin3_all_cases z with rfl | rfl | rfl
        · have hz' : (1 : Fin 3) ≤ 0 := hz.1
          exact absurd hz' (by decide)
        · exact absurd (h₂ 1 hp) hz.2
        · rfl
    have hbad := hc2 (Sum.inl (1 : Fin 3)) (by decide : M3.Ri 0 1) hnp
    have hbad' : (1 : Fin 3) = 2 := hbad
    exact absurd hbad' (by decide)

/-- **`φ★` has NO parameterised fork cover.** -/
theorem not_hasForkCover_phiStar {χ δ₁ δ₂ : PLLFormula} (hχ : atomFree χ = true)
    (hδ₁ : atomFree δ₁ = true) (hδ₂ : atomFree δ₂ = true)
    (hd₁ : Deriv [δ₁] χ) (hd₂ : Deriv [δ₂] χ) : ¬ HasForkCover χ δ₁ δ₂ phiStar := by
  intro h
  have hI : Interd (FLo χ δ₁ δ₂ phiStar) (nt (nt oBot)) :=
    postInterp_unique (postInterp_of_fork hχ hδ₁ hδ₂ hd₁ hd₂ h) postInterp_phiStar
  obtain ⟨d⟩ := hI.2
  have hs : M3.force (0 : Fin 3) (FLo χ δ₁ δ₂ phiStar) :=
    soundness d M3 0 (fun ψ hψ => by
      have e : ψ = nt (nt oBot) := by
        cases hψ with
        | head => rfl
        | tail _ hh => cases hh
      subst e
      exact M3_root_nnbox)
  exact M3_fork_phiStar_fails (forceMap hd₁ M3) (forceMap hd₂ M3)
    ((fork_tr (C := M3) (χ := χ) (δ₁ := δ₁) (δ₂ := δ₂)
      (h₁ := forceMap hd₁ M3) (h₂ := forceMap hd₂ M3) phiStar (0 : Fin 3)).1.mpr hs)

/-- **INCOMPARABILITY SURVIVES PARAMETERISATION.**  `φ★` has a guarded
stretch cover and no parameterised fork cover; `φ♣` has a parameterised
fork cover and no guarded mixed cover.  So the corrected frontier
conjecture genuinely needs BOTH non-substitutional families. -/
theorem paramFork_stretch_incomparable :
    (HasGuardedCover oBot phiStar ∧
      ∀ χ δ₁ δ₂ : PLLFormula, atomFree χ = true → atomFree δ₁ = true →
        atomFree δ₂ = true → Deriv [δ₁] χ → Deriv [δ₂] χ →
        ¬ HasForkCover χ δ₁ δ₂ phiStar) ∧
    (HasForkCover gapGuard gapGuard oBot phiClub ∧ ¬ HasGuardedMixedCover phiClub) :=
  ⟨⟨hasGuardedCover_phiStar,
    fun _ _ _ hχ hδ₁ hδ₂ hd₁ hd₂ => not_hasForkCover_phiStar hχ hδ₁ hδ₂ hd₁ hd₂⟩,
   ⟨hasForkCover_phiClub, phiClub_no_guardedMixedCover⟩⟩

/-! ## 12.  The CORRECTED frontier conjecture: `ParamForkMixedConj`

`BranchMixedConj` is refuted (`branchMixedConj_false`).  Its correction
replaces the `(χ,⊥)`-fork coordinate by the whole parameterised family:

    ParamForkMixedConj : ∀ φ one-variable, finitely many guarded stretch
      bounds `LoG χ φ`, finitely many parameterised fork bounds
      `FLo χ δ₁ δ₂ φ` (over variable-free triples with `δᵢ ⊢ χ`) and
      finitely many variable-free substitution instances `φ[p := θ]`
      jointly exhaust `φ`.

`p` is covered by substitution, `φ★` by the guarded stretch, `φ♦` by
the `(χ,⊥)`-fork (a parameterised fork), `φ♣` by a genuinely
parameterised fork. -/

/-- A parameterised-fork COORDINATE: a guard and the two copy
valuations. -/
abbrev ForkParam : Type := PLLFormula × PLLFormula × PLLFormula

/-- The side condition on a coordinate: everything variable-free, and
`δᵢ ⊢ χ` (which is exactly what makes `fork` a constraint model). -/
def OkParam (t : ForkParam) : Prop :=
  atomFree t.1 = true ∧ atomFree t.2.1 = true ∧ atomFree t.2.2 = true ∧
    Deriv [t.2.1] t.1 ∧ Deriv [t.2.2] t.1

/-- The list of parameterised fork lower bounds of `φ` at the
coordinates in `T`. -/
def floList (T : List ForkParam) (φ : PLLFormula) : List PLLFormula :=
  T.map (fun t => FLo t.1 t.2.1 t.2.2 φ)

theorem mem_floList {T : List ForkParam} {φ ψ : PLLFormula}
    (h : ψ ∈ floList T φ) : ∃ t ∈ T, ψ = FLo t.1 t.2.1 t.2.2 φ := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
  exact ⟨t, ht, rfl⟩

/-- **`φ` has a parameterised-fork mixed cover.** -/
def HasParamForkMixedCover (φ : PLLFormula) : Prop :=
  ∃ (G : List PLLFormula) (T : List ForkParam) (S : List PLLFormula),
    (∀ χ ∈ G, atomFree χ = true) ∧ (∀ t ∈ T, OkParam t) ∧
    (∀ θ ∈ S, atomFree θ = true) ∧
    Deriv [φ] (bigOr (loList G φ ++ floList T φ ++ instList S φ))

/-- **MASTER REDUCTION for the parameterised-fork mixed method.** -/
theorem postInterp_of_paramForkMixed {φ : PLLFormula} (hφ : onlyPv φ = true)
    {G : List PLLFormula} {T : List ForkParam} {S : List PLLFormula}
    (hG : ∀ χ ∈ G, atomFree χ = true) (hT : ∀ t ∈ T, OkParam t)
    (hS : ∀ θ ∈ S, atomFree θ = true)
    (hcov : Deriv [φ] (bigOr (loList G φ ++ floList T φ ++ instList S φ))) :
    IsPostInterp φ (bigOr (loList G φ ++ floList T φ ++ instList S φ)) := by
  refine ⟨atomFree_bigOr ?_, hcov, ?_⟩
  · intro ψ hψ
    rcases List.mem_append.mp hψ with h | h
    · rcases List.mem_append.mp h with h' | h'
      · obtain ⟨χ, hχ, rfl⟩ := mem_loList h'
        exact atomFree_LoG (hG χ hχ) φ
      · obtain ⟨t, ht, rfl⟩ := mem_floList h'
        obtain ⟨ha, hb, hc, -, -⟩ := hT t ht
        exact atomFree_FLo ha hb hc φ
    · exact atomFree_instList hS hφ ψ h
  · intro ψ hψ hd
    refine Deriv.bigOrElim (Deriv.iden (.head _)) ?_
    intro ρ hρ
    rcases List.mem_append.mp hρ with h | h
    · rcases List.mem_append.mp h with h' | h'
      · obtain ⟨χ, -, rfl⟩ := mem_loList h'
        exact Deriv.toHead (gstretch_below hψ hd)
      · obtain ⟨t, ht, rfl⟩ := mem_floList h'
        obtain ⟨-, -, -, hd₁, hd₂⟩ := hT t ht
        exact Deriv.toHead (fork_below hd₁ hd₂ hψ hd)
    · obtain ⟨θ, -, rfl⟩ := mem_instList h
      exact Deriv.toHead (inst_below θ hψ hd)

/-- **REFUTED** (`paramForkMixedConj_false`, §15).  The corrected
successor of `BranchMixedConj`. -/
def ParamForkMixedConj : Prop :=
  ∀ φ : PLLFormula, onlyPv φ = true → HasParamForkMixedCover φ

/-- **The reduction of last-variable `∃p` to the corrected frontier
conjecture.** -/
theorem postUI_of_paramForkMixedConj (h : ParamForkMixedConj) :
    ∀ φ : PLLFormula, onlyPv φ = true → ∃ ψ, IsPostInterp φ ψ := by
  intro φ hφ
  obtain ⟨G, T, S, hG, hT, hS, hcov⟩ := h φ hφ
  exact ⟨_, postInterp_of_paramForkMixed hφ hG hT hS hcov⟩

/-- Every `(χ,⊥)`-fork coordinate is a parameterised coordinate. -/
theorem okParam_bstretch {χ : PLLFormula} (hχ : atomFree χ = true) :
    OkParam (χ, χ, PLLFormula.falsePLL) :=
  ⟨hχ, hχ, rfl, Deriv.iden (.head _), Deriv.falsoElim _ (Deriv.iden (.head _))⟩

/-- **The corrected conjecture is WEAKER than `BranchMixedConj`**: a
branch-mixed cover is a parameterised-fork mixed cover, at the
coordinates `(χ, χ, ⊥)`. -/
theorem hasParamForkMixedCover_of_branchMixed {φ : PLLFormula}
    (h : HasBranchMixedCover φ) : HasParamForkMixedCover φ := by
  obtain ⟨G, B, S, hG, hB, hS, hd⟩ := h
  refine ⟨G, B.map (fun χ => (χ, χ, PLLFormula.falsePLL)), S, hG, ?_, hS, ?_⟩
  · intro t ht
    obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp ht
    exact okParam_bstretch (hB χ hχ)
  · have e : floList (B.map (fun χ => (χ, χ, PLLFormula.falsePLL))) φ = bloList B φ := by
      show (B.map (fun χ => (χ, χ, PLLFormula.falsePLL))).map
          (fun t => FLo t.1 t.2.1 t.2.2 φ) = B.map (fun χ => BLo χ φ)
      rw [List.map_map]
      exact List.map_congr_left (fun χ _ => FLo_eq_BLo χ φ)
    rw [e]
    exact hd

/-- **THE REFUTATION TOOL for `ParamForkMixedConj`.**  A defeater is a
non-fallible `φ`-world at which every variable-free instance, every
guarded stretch bound and every PARAMETERISED fork bound fails. -/
theorem not_hasParamForkMixedCover_of_model {φ : PLLFormula} (C : ConstraintModel)
    (w : C.W) (hw : C.force w φ) (hwF : ¬ C.force w PLLFormula.falsePLL)
    (hLo : ∀ χ : PLLFormula, atomFree χ = true → ¬ C.force w (LoG χ φ))
    (hFo : ∀ t : ForkParam, OkParam t → ¬ C.force w (FLo t.1 t.2.1 t.2.2 φ))
    (hno : ∀ θ : PLLFormula, atomFree θ = true → ¬ C.force w (inst θ φ)) :
    ¬ HasParamForkMixedCover φ := by
  rintro ⟨G, T, S, hG, hT, hS, hd⟩
  obtain ⟨d⟩ := hd
  have hforce : C.force w (bigOr (loList G φ ++ floList T φ ++ instList S φ)) :=
    soundness d C w (fun ψ hψ => by
      have e : ψ = φ := by
        cases hψ with
        | head => rfl
        | tail _ h => cases h
      subst e; exact hw)
  rcases force_bigOr hforce with ⟨A, hA, hfA⟩ | hf
  · rcases List.mem_append.mp hA with h | h
    · rcases List.mem_append.mp h with h' | h'
      · obtain ⟨χ, hχ, rfl⟩ := mem_loList h'
        exact hLo χ (hG χ hχ) hfA
      · obtain ⟨t, ht, rfl⟩ := mem_floList h'
        exact hFo t (hT t ht) hfA
    · obtain ⟨θ, hθ, rfl⟩ := mem_instList h
      exact hno θ (hS θ hθ) hfA
  · exact hwF hf

/-- `φ♣` HAS a parameterised-fork mixed cover, though no branch-mixed
cover: the single coordinate `(◯⊥ ∨ ¬◯⊥, ◯⊥ ∨ ¬◯⊥, ◯⊥)` suffices. -/
theorem hasParamForkMixedCover_phiClub : HasParamForkMixedCover phiClub := by
  refine ⟨[], [(gapGuard, gapGuard, oBot)], [], ?_, ?_, ?_, ?_⟩
  · intro χ hχ; exact absurd hχ (by simp)
  · intro t ht
    rcases List.mem_singleton.mp ht with rfl
    exact ⟨rfl, rfl, rfl, gapGuard_le, oBot_le_gapGuard⟩
  · intro θ hθ; exact absurd hθ (by simp)
  · show Deriv [phiClub] (bigOr ([] ++ [FLo gapGuard gapGuard oBot phiClub] ++ []))
    exact Deriv.orIntro1 hasForkCover_phiClub

/-- `φ★` and `φ♦` are covered too (through the branch-mixed family). -/
theorem hasParamForkMixedCover_phiStar : HasParamForkMixedCover phiStar :=
  hasParamForkMixedCover_of_branchMixed hasBranchMixedCover_phiStar

theorem hasParamForkMixedCover_phiDia : HasParamForkMixedCover phiDia :=
  hasParamForkMixedCover_of_branchMixed hasBranchMixedCover_phiDia

/-! ## 13.  The SEMANTIC (one-model) frontier statement, and the bridge

The probe tests a POINTWISE statement, one `(model, world)` at a time:
at every world forcing `φ`, SOME member of the join is forced.  That is
strictly weaker than `HasParamForkMixedCover φ`, which needs ONE finite
list working at every world simultaneously.  Both are recorded here;
only the pointwise form is what a "no hits" probe verdict supports. -/

/-- **The pointwise form of the join.**  (`semParamForkMixed_of_cover`
shows it is implied by the cover; the converse needs a finiteness
argument — see the note below.) -/
def SemParamForkMixed (φ : PLLFormula) : Prop :=
  ∀ (C : ConstraintModel) (w : C.W), C.force w φ →
    (∃ χ, atomFree χ = true ∧ C.force w (LoG χ φ)) ∨
    (∃ t : ForkParam, OkParam t ∧ C.force w (FLo t.1 t.2.1 t.2.2 φ)) ∨
    (∃ θ, atomFree θ = true ∧ C.force w (inst θ φ)) ∨
    C.force w PLLFormula.falsePLL

/-- **A cover gives the pointwise statement.** -/
theorem semParamForkMixed_of_cover {φ : PLLFormula}
    (h : HasParamForkMixedCover φ) : SemParamForkMixed φ := by
  obtain ⟨G, T, S, hG, hT, hS, hd⟩ := h
  intro C w hw
  obtain ⟨d⟩ := hd
  have hforce : C.force w (bigOr (loList G φ ++ floList T φ ++ instList S φ)) :=
    soundness d C w (fun ψ hψ => by
      have e : ψ = φ := by
        cases hψ with
        | head => rfl
        | tail _ h => cases h
      subst e; exact hw)
  rcases force_bigOr hforce with ⟨A, hA, hfA⟩ | hf
  · rcases List.mem_append.mp hA with h | h
    · rcases List.mem_append.mp h with h' | h'
      · obtain ⟨χ, hχ, rfl⟩ := mem_loList h'
        exact Or.inl ⟨χ, hG χ hχ, hfA⟩
      · obtain ⟨t, ht, rfl⟩ := mem_floList h'
        exact Or.inr (Or.inl ⟨t, hT t ht, hfA⟩)
    · obtain ⟨θ, hθ, rfl⟩ := mem_instList h
      exact Or.inr (Or.inr (Or.inl ⟨θ, hS θ hθ, hfA⟩))
  · exact Or.inr (Or.inr (Or.inr hf))

/-- **REFUTED** (`semParamForkConj_false`, §15) — the pointwise frontier
conjecture, which is what the exhaustive probe tests. -/
def SemParamForkConj : Prop :=
  ∀ φ : PLLFormula, onlyPv φ = true → SemParamForkMixed φ

/-- **OPEN (statement only).**  The bridge the probe verdict does NOT
supply: from the pointwise statement to a single finite cover.  Its
exact shape is a compactness/finiteness step — see the note in §14. -/
def SemToSyntacticBridge : Prop :=
  ∀ φ : PLLFormula, onlyPv φ = true → SemParamForkMixed φ → HasParamForkMixedCover φ

theorem paramForkMixedConj_of_sem (hb : SemToSyntacticBridge) (hs : SemParamForkConj) :
    ParamForkMixedConj := fun φ hφ => hb φ hφ (hs φ hφ)

/-! ## 14.  Where the bridge sticks

`SemParamForkMixed φ` gives, for EACH `(C, w)` with `w ⊩ φ`, SOME
member `M(C,w)` of the join forced at `w`.  A cover needs a single
finite list.  The route:

1. by the finite model property it is enough to consider FINITE `C`
   (`countermodel_of_not_deriv` already delivers finite countermodels);
2. for a fixed `φ` the members of the join that can be forced at a
   `φ`-world are determined by the TRUTH SETS of `χ`, `δ₁`, `δ₂`, `θ`
   in `C`, and `D(C)` is finite — so, per model, finitely many members
   suffice;
3. the sticking point is UNIFORMITY ACROSS MODELS: `D(C)` is finite for
   each finite `C` but unbounded over all `C` (the `RN(◯,{})` lattice
   is infinite), so step 2 gives a list depending on `C`.  What is
   needed is a bound on the SIZE of the required triples in terms of
   `φ` — e.g. that the guards and copy valuations may always be taken
   from the finitely many variable-free formulas of `◯`-depth at most
   that of `φ` — and no such bound is currently proved.  `φ★`, `φ♦`,
   `φ♣` are all covered by a SINGLE member built from `◯⊥` and `¬◯⊥`,
   which is the evidence for such a bound; it is not a proof.

Nothing in §13–14 is claimed as proved beyond the two theorems
`semParamForkMixed_of_cover` and `paramForkMixedConj_of_sem`. -/

/-! ## 15.  REFUTED: `ParamForkMixedConj` — the defeater `φ♠`

`wip/pforkprobe.lean` sweeps `n ≤ 5` exhaustively (0 capped, 0 skipped
at the phase-B budget) and finds defeaters of the FULL join.  The
commonest, in

    C♠ :  W = {0,1,2,3,4},  0 ⊑ everything,  1 ⊑ 4,  2 ⊑ 3,
          3 and 4 maximal,  Rₘ = id ∪ {(1,4)},  F = {4},  V(p) = {1,3,4}

    φ♠ = (¬◯⊥ ⊃ (¬p ∨ p)) ⊃ (¬◯⊥ ∨ (◯⊥ ∧ p))

is pinned here.  `D(C♠) = {⊥, ◯⊥, ¬◯⊥, ◯⊥ ∨ ¬◯⊥, ⊤} =
{{4}, {1,4}, {2,3,4}, {1,2,3,4}, all}` and `‖p‖ = {1,3,4}` is not among
them: worlds `2` and `3` satisfy the same variable-free formulas
(`Cspade_agree23`), although `2 ↔ 3` is NOT a frame automorphism —
`2 ⊑ 3` and `3 ⋢ 2`.  The classification is got by `decide` from a
five-row table (`Cspade_defs`).

* every guarded stretch fails at `inl 1`, uniformly in the guard,
  because `1 ⊩ ¬¬◯⊥`: every world above `1` forcing `¬◯⊥` is the
  fallible `4`, so the antecedent holds vacuously there, while the
  consequent needs `¬◯⊥` (false at `1`) or `p` (which on the ground
  layer means "fallible", false at `1`);
* every PARAMETERISED fork fails at `inl 0`, uniformly in
  `(χ, δ₁, δ₂)`: the consequent fails outright at `inl 0`
  (`0 ⊮ ◯⊥`, `0 ⊮ ¬◯⊥`), and the antecedent holds because the only
  `¬◯⊥`-worlds of the cone are `2`, `3` (where `p` is DECIDED, both
  copy valuations being variable-free and hence blind to `2` vs `3`)
  and the fallible `4`.

The `δᵢ ⊢ χ` condition is what closes the last gap: a `p`-world on the
other copy above `inl 2` would need `3 ⊩ δ₂` with `2 ⊮ χ`, and
`3 ⊩ δ₂ ↔ 2 ⊩ δ₂ ⊢ χ` forbids it. -/

/-- The intuitionistic order of `C♠`. -/
def Rs (x y : Fin 5) : Prop := x = 0 ∨ x = y ∨ (x = 1 ∧ y = 4) ∨ (x = 2 ∧ y = 3)

instance (x y : Fin 5) : Decidable (Rs x y) := by unfold Rs; infer_instance

/-- The modal relation of `C♠`: the identity plus the edge `1 ⇝ 4`. -/
def Rms (x y : Fin 5) : Prop := x = y ∨ (x = 1 ∧ y = 4)

instance (x y : Fin 5) : Decidable (Rms x y) := by unfold Rms; infer_instance

theorem Rs_refl : ∀ x : Fin 5, Rs x x := by decide
theorem Rs_trans : ∀ x y z : Fin 5, Rs x y → Rs y z → Rs x z := by decide
theorem Rms_refl : ∀ x : Fin 5, Rms x x := by decide
theorem Rms_trans : ∀ x y z : Fin 5, Rms x y → Rms y z → Rms x z := by decide
theorem Rms_sub : ∀ x y : Fin 5, Rms x y → Rs x y := by decide
theorem Rs_hered_F : ∀ x y : Fin 5, Rs x y → x = 4 → y = 4 := by decide
theorem Rs_hered_V : ∀ x y : Fin 5, Rs x y →
    (x = 1 ∨ x = 3 ∨ x = 4) → (y = 1 ∨ y = 3 ∨ y = 4) := by decide
theorem Rs_full_V : ∀ x : Fin 5, x = 4 → (x = 1 ∨ x = 3 ∨ x = 4) := by decide

/-- **The five-world defeater model `C♠`.** -/
@[reducible] def Cspade : ConstraintModel where
  W := Fin 5
  Ri := Rs
  Rm := Rms
  F := {x | x = 4}
  V _ := {x | x = 1 ∨ x = 3 ∨ x = 4}
  refl_i := Rs_refl
  trans_i {x y z} h1 h2 := Rs_trans x y z h1 h2
  refl_m := Rms_refl
  trans_m {x y z} h1 h2 := Rms_trans x y z h1 h2
  sub_mi {x y} h := Rms_sub x y h
  hered_F {x y} h hx := Rs_hered_F x y h hx
  hered_V {_ x y} h hx := Rs_hered_V x y h hx
  full_F {_ x} hx := Rs_full_V x hx

theorem Cspade_oBot_iff (x : Fin 5) : Cspade.force x oBot ↔ (x = 1 ∨ x = 4) := by
  have key : ∀ y : Fin 5,
      (∀ v : Fin 5, Rs y v → ∃ u : Fin 5, Rms v u ∧ u = 4) ↔ (y = 1 ∨ y = 4) := by decide
  exact key x

theorem Cspade_nOBot_iff (x : Fin 5) :
    Cspade.force x (nt oBot) ↔ (x = 2 ∨ x = 3 ∨ x = 4) := by
  have key : ∀ y : Fin 5,
      (∀ v : Fin 5, Rs y v → (v = 1 ∨ v = 4) → v = 4) ↔ (y = 2 ∨ y = 3 ∨ y = 4) := by decide
  constructor
  · intro h
    exact (key x).mp (fun v hv h14 => h v hv ((Cspade_oBot_iff v).mpr h14))
  · intro h v hv hvb
    exact (key x).mpr h v hv ((Cspade_oBot_iff v).mp hvb)

/-- **`φ♠ = (¬◯⊥ ⊃ (¬p ∨ p)) ⊃ (¬◯⊥ ∨ (◯⊥ ∧ p))`.** -/
def phiSpade : PLLFormula :=
  ((nt oBot).ifThen ((nt (PLLFormula.prop pv)).or (PLLFormula.prop pv))).ifThen
    ((nt oBot).or (oBot.and (PLLFormula.prop pv)))

theorem phiSpade_onlyPv : onlyPv phiSpade = true := by decide

abbrev spadeAnte : PLLFormula :=
  (nt oBot).ifThen ((nt (PLLFormula.prop pv)).or (PLLFormula.prop pv))

abbrev spadeCons : PLLFormula := (nt oBot).or (oBot.and (PLLFormula.prop pv))

/-- **`φ♠` holds at the root of `C♠`** under `‖p‖ = {1,3,4}`.  At `1` the
consequent's second disjunct holds; at `3` the first; at `4` everything;
at `0` and at `2` the ANTECEDENT fails, because `2` is a `¬◯⊥`-world at
which `p` is undecided (`p` fails at `2` and holds at the non-fallible
`3 ⊒ 2`). -/
theorem Cspade_force_phiSpade : Cspade.force (0 : Fin 5) phiSpade := by
  have h2 : ¬ Cspade.force (2 : Fin 5) ((nt (PLLFormula.prop pv)).or (PLLFormula.prop pv)) := by
    rintro (hn | hp)
    · have hbad : (3 : Fin 5) = 4 :=
        hn 3 (by decide) (show (3 : Fin 5) = 1 ∨ (3 : Fin 5) = 3 ∨ (3 : Fin 5) = 4 by decide)
      exact absurd hbad (by decide)
    · have hp' : (2 : Fin 5) = 1 ∨ (2 : Fin 5) = 3 ∨ (2 : Fin 5) = 4 := hp
      exact absurd hp' (by decide)
  intro v hv hante
  rcases Fin5_cases v with rfl | rfl | rfl | rfl | rfl
  · exact absurd (hante 2 (by decide) ((Cspade_nOBot_iff 2).mpr (by decide))) h2
  · exact Or.inr ⟨(Cspade_oBot_iff 1).mpr (by decide),
      show (1 : Fin 5) = 1 ∨ (1 : Fin 5) = 3 ∨ (1 : Fin 5) = 4 from by decide⟩
  · exact absurd (hante 2 (Rs_refl 2) ((Cspade_nOBot_iff 2).mpr (by decide))) h2
  · exact Or.inl ((Cspade_nOBot_iff 3).mpr (by decide))
  · exact Cspade.force_of_fallible (show (4 : Fin 5) ∈ Cspade.F from rfl)

theorem Cspade_root_not_fallible : ¬ Cspade.force (0 : Fin 5) PLLFormula.falsePLL := by
  intro h
  have h' : (0 : Fin 5) = 4 := h
  exact absurd h' (by decide)

theorem phiSpade_consistent : ¬ Deriv [phiSpade] PLLFormula.falsePLL := by
  rintro ⟨d⟩
  refine Cspade_root_not_fallible (soundness d Cspade 0 ?_)
  intro ψ hψ
  have e : ψ = phiSpade := by
    cases hψ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact Cspade_force_phiSpade

/-! ### The variable-free truth sets of `C♠` -/

/-- The five variable-free truth sets of `C♠`, as a table:
`⊥ = {4}`, `◯⊥ = {1,4}`, `¬◯⊥ = {2,3,4}`, `◯⊥ ∨ ¬◯⊥ = {1,2,3,4}`,
`⊤ = all`. -/
def spTbl (i x : Fin 5) : Bool :=
  if i = 0 then x == 4
  else if i = 1 then (x == 1 || x == 4)
  else if i = 2 then (x == 2 || x == 3 || x == 4)
  else if i = 3 then !(x == 0)
  else true

theorem sp_bot : ∀ x : Fin 5, (x = 4) ↔ spTbl 0 x = true := by decide
theorem sp_and : ∀ i j : Fin 5, ∃ k : Fin 5, ∀ x : Fin 5,
    (spTbl i x = true ∧ spTbl j x = true) ↔ spTbl k x = true := by decide
theorem sp_or : ∀ i j : Fin 5, ∃ k : Fin 5, ∀ x : Fin 5,
    (spTbl i x = true ∨ spTbl j x = true) ↔ spTbl k x = true := by decide
theorem sp_imp : ∀ i j : Fin 5, ∃ k : Fin 5, ∀ x : Fin 5,
    (∀ v : Fin 5, Rs x v → spTbl i v = true → spTbl j v = true) ↔ spTbl k x = true := by
  decide
theorem sp_box : ∀ i : Fin 5, ∃ k : Fin 5, ∀ x : Fin 5,
    (∀ v : Fin 5, Rs x v → ∃ u : Fin 5, Rms v u ∧ spTbl i u = true) ↔ spTbl k x = true := by
  decide

/-- **Every variable-free truth set of `C♠` is one of the five.**  (The
`decide`-checked table is closed under `∧, ∨, ⊃, ◯` and contains
`‖⊥‖`.) -/
theorem Cspade_defs : ∀ {A : PLLFormula}, atomFree A = true →
    ∃ i : Fin 5, ∀ x : Fin 5, (Cspade.force x A ↔ spTbl i x = true) := by
  intro A
  induction A with
  | prop a => intro h; exact absurd h (by simp [atomFree])
  | falsePLL => exact fun _ => ⟨0, fun x => sp_bot x⟩
  | and A B ihA ihB =>
      intro h
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      obtain ⟨i, hi⟩ := ihA h'.1
      obtain ⟨j, hj⟩ := ihB h'.2
      obtain ⟨k, hk⟩ := sp_and i j
      exact ⟨k, fun x => (and_congr (hi x) (hj x)).trans (hk x)⟩
  | or A B ihA ihB =>
      intro h
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      obtain ⟨i, hi⟩ := ihA h'.1
      obtain ⟨j, hj⟩ := ihB h'.2
      obtain ⟨k, hk⟩ := sp_or i j
      exact ⟨k, fun x => (or_congr (hi x) (hj x)).trans (hk x)⟩
  | ifThen A B ihA ihB =>
      intro h
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      obtain ⟨i, hi⟩ := ihA h'.1
      obtain ⟨j, hj⟩ := ihB h'.2
      obtain ⟨k, hk⟩ := sp_imp i j
      refine ⟨k, fun x => Iff.trans ?_ (hk x)⟩
      constructor
      · intro hh v hv hv'
        exact (hj v).mp (hh v hv ((hi v).mpr hv'))
      · intro hh v hv hv'
        exact (hj v).mpr (hh v hv ((hi v).mp hv'))
  | somehow A ih =>
      intro h
      obtain ⟨i, hi⟩ := ih h
      obtain ⟨k, hk⟩ := sp_box i
      refine ⟨k, fun x => Iff.trans ?_ (hk x)⟩
      constructor
      · intro hh v hv
        obtain ⟨u, hu, hfu⟩ := hh v hv
        exact ⟨u, hu, (hi u).mp hfu⟩
      · intro hh v hv
        obtain ⟨u, hu, hfu⟩ := hh v hv
        exact ⟨u, hu, (hi u).mpr hfu⟩

/-- **Worlds `2` and `3` satisfy the same variable-free formulas** — not
by an automorphism (`2 ⊑ 3` and `3 ⋢ 2`) but because every row of the
table agrees at `2` and `3`. -/
theorem Cspade_agree23 {A : PLLFormula} (hA : atomFree A = true) :
    Cspade.force (2 : Fin 5) A ↔ Cspade.force (3 : Fin 5) A := by
  obtain ⟨i, hi⟩ := Cspade_defs hA
  have key : ∀ j : Fin 5, spTbl j 2 = spTbl j 3 := by decide
  rw [hi 2, hi 3, key i]

/-! ### Every instance, every guarded stretch and every parameterised
fork fails at the root of `C♠` -/

theorem inst_phiSpade (θ : PLLFormula) :
    inst θ phiSpade
      = ((oBot.ifThen .falsePLL).ifThen ((θ.ifThen .falsePLL).or θ)).ifThen
          ((oBot.ifThen .falsePLL).or (oBot.and θ)) := by
  show (((inst θ oBot).ifThen (inst θ PLLFormula.falsePLL)).ifThen
      (((inst θ (PLLFormula.prop pv)).ifThen (inst θ PLLFormula.falsePLL)).or
        (inst θ (PLLFormula.prop pv)))).ifThen
      (((inst θ oBot).ifThen (inst θ PLLFormula.falsePLL)).or
        ((inst θ oBot).and (inst θ (PLLFormula.prop pv)))) = _
  rw [inst_var_eq, inst_atomFree_eq θ (show atomFree oBot = true from rfl)]
  rfl

/-- **No variable-free instance of `φ♠` is forced at the root of `C♠`.**
The consequent fails at `0` (`0 ⊮ ◯⊥`, `0 ⊮ ¬◯⊥`), so it is enough that
the antecedent holds: the `¬◯⊥`-worlds are `2`, `3`, `4`; `4` is
fallible, and at `2`, `3` a variable-free `θ` is DECIDED — by the table,
`θ` either holds at both or at neither, and in the second case `¬θ` holds
there since the cone of `2` is `{2,3}`. -/
theorem Cspade_inst_fails {θ : PLLFormula} (hθ : atomFree θ = true) :
    ¬ Cspade.force (0 : Fin 5) (inst θ phiSpade) := by
  classical
  rw [inst_phiSpade θ]
  intro h
  have hcons : ¬ Cspade.force (0 : Fin 5)
      ((oBot.ifThen .falsePLL).or (oBot.and θ)) := by
    rintro (h1 | ⟨h2, -⟩)
    · exact absurd ((Cspade_nOBot_iff 0).mp h1) (by decide)
    · exact absurd ((Cspade_oBot_iff 0).mp h2) (by decide)
  have hdec : ∀ j y : Fin 5, (y = 2 ∨ y = 3 ∨ y = 4) →
      ((∀ v : Fin 5, Rs y v → spTbl j v = true → v = 4) ∨ spTbl j y = true) := by decide
  refine hcons (h 0 (Rs_refl 0) ?_)
  obtain ⟨i, hi⟩ := Cspade_defs hθ
  intro u hu hun
  have hu234 : u = 2 ∨ u = 3 ∨ u = 4 := (Cspade_nOBot_iff u).mp hun
  rcases hdec i u hu234 with hn | hp
  · exact Or.inl (fun v hv hvθ => hn v hv ((hi v).mp hvθ))
  · exact Or.inr ((hi u).mpr hp)

/-- **Every guarded stretch fails, uniformly in the guard**, at `inl 1`:
there `1 ⊩ ¬¬◯⊥` makes the antecedent vacuous (every `¬◯⊥`-world above
`1` is the fallible `4`), while the consequent needs `¬◯⊥` — false at
`1` — or `p`, which on the ground layer means "fallible". -/
theorem Cspade_gstretch_fails (χ : PLLFormula) :
    ¬ (gstretch Cspade χ).force (Sum.inl (0 : Fin 5)) phiSpade := by
  intro h
  have key : ∀ y : Fin 5, Rs 1 y → (y = 2 ∨ y = 3 ∨ y = 4) → y = 4 := by decide
  have hante : (gstretch Cspade χ).force (Sum.inl (1 : Fin 5)) spadeAnte := by
    rintro (y | y) hq hqn
    · have hy : y = 4 := key y hq ((Cspade_nOBot_iff y).mp
        ((gstretch_transfer (C := Cspade) (χ := χ) (A := nt oBot) rfl y).1.mp hqn))
      subst hy
      exact (gstretch Cspade χ).force_of_fallible (show (4 : Fin 5) ∈ Cspade.F from rfl)
    · have hy : y = 4 := key y hq.1 ((Cspade_nOBot_iff y).mp
        ((gstretch_transfer (C := Cspade) (χ := χ) (A := nt oBot) rfl y).2.mp hqn))
      subst hy
      exact (gstretch Cspade χ).force_of_fallible (show (4 : Fin 5) ∈ Cspade.F from rfl)
  rcases h (Sum.inl (1 : Fin 5)) (show Rs 0 1 by decide) hante with hn | ⟨-, hp⟩
  · exact absurd ((Cspade_nOBot_iff 1).mp
      ((gstretch_transfer (C := Cspade) (χ := χ) (A := nt oBot) rfl 1).1.mp hn)) (by decide)
  · have hp' : (1 : Fin 5) = 4 := hp
    exact absurd hp' (by decide)

/-- **Every parameterised fork fails, uniformly in `(χ, δ₁, δ₂)`**, at
`inl 0`.  The consequent fails there outright; the antecedent holds
because the `¬◯⊥`-worlds of `C♠` are `2`, `3` and the fallible `4`, and
at a copy of `2` or `3` the atom `p` is DECIDED: both copy valuations are
variable-free, so `Cspade_agree23` makes them blind to `2` versus `3`,
and the cross edges out of a copy of `y` exist only when `y ⊮ χ`, which
`δᵢ ⊢ χ` turns into `y ⊮ δᵢ`. -/
theorem Cspade_fork_fails {χ δ₁ δ₂ : PLLFormula}
    (hδ₁ : atomFree δ₁ = true) (hδ₂ : atomFree δ₂ = true)
    (h₁ : ∀ x : Cspade.W, Cspade.force x δ₁ → Cspade.force x χ)
    (h₂ : ∀ x : Cspade.W, Cspade.force x δ₂ → Cspade.force x χ) :
    ¬ (fork Cspade χ δ₁ δ₂ h₁ h₂).force (Sum.inl (0 : Fin 5)) phiSpade := by
  classical
  intro h
  have step : ∀ y z : Fin 5, (y = 2 ∨ y = 3) → Rs y z → (z = 2 ∨ z = 3) := by decide
  have pull : ∀ (d : PLLFormula), atomFree d = true → ∀ y z : Fin 5,
      (y = 2 ∨ y = 3) → (z = 2 ∨ z = 3) → Cspade.force z d → Cspade.force y d := by
    intro d hd y z hy hz hzd
    rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
    · exact hzd
    · exact (Cspade_agree23 hd).mpr hzd
    · exact (Cspade_agree23 hd).mp hzd
    · exact hzd
  have decided : ∀ (y : Fin 5), (y = 2 ∨ y = 3) → ∀ q : Fin 5 ⊕ Fin 5,
      (q = Sum.inl y ∨ q = Sum.inr y) →
      (fork Cspade χ δ₁ δ₂ h₁ h₂).force q
        ((nt (PLLFormula.prop pv)).or (PLLFormula.prop pv)) := by
    intro y hy q hq
    rcases hq with rfl | rfl
    · by_cases hp : Cspade.force y δ₁
      · exact Or.inr hp
      · refine Or.inl ?_
        rintro (z | z) hz hpz
        · exact absurd (pull δ₁ hδ₁ y z hy (step y z hy hz) hpz) hp
        · exact absurd (h₂ y (pull δ₂ hδ₂ y z hy (step y z hy hz.1) hpz)) hz.2
    · by_cases hp : Cspade.force y δ₂
      · exact Or.inr hp
      · refine Or.inl ?_
        rintro (z | z) hz hpz
        · exact absurd (h₁ y (pull δ₁ hδ₁ y z hy (step y z hy hz.1) hpz)) hz.2
        · exact absurd (pull δ₂ hδ₂ y z hy (step y z hy hz) hpz) hp
  have hante : (fork Cspade χ δ₁ δ₂ h₁ h₂).force (Sum.inl (0 : Fin 5)) spadeAnte := by
    rintro (y | y) hq hqn
    · have hy : y = 2 ∨ y = 3 ∨ y = 4 :=
        (Cspade_nOBot_iff y).mp ((fork_transfer (h₁ := h₁) (h₂ := h₂) (A := nt oBot) rfl y).1.mp hqn)
      rcases hy with rfl | rfl | rfl
      · exact decided 2 (by decide) _ (Or.inl rfl)
      · exact decided 3 (by decide) _ (Or.inl rfl)
      · exact (fork Cspade χ δ₁ δ₂ h₁ h₂).force_of_fallible
          (show (4 : Fin 5) ∈ Cspade.F from rfl)
    · have hy : y = 2 ∨ y = 3 ∨ y = 4 :=
        (Cspade_nOBot_iff y).mp ((fork_transfer (h₁ := h₁) (h₂ := h₂) (A := nt oBot) rfl y).2.mp hqn)
      rcases hy with rfl | rfl | rfl
      · exact decided 2 (by decide) _ (Or.inr rfl)
      · exact decided 3 (by decide) _ (Or.inr rfl)
      · exact (fork Cspade χ δ₁ δ₂ h₁ h₂).force_of_fallible
          (show (4 : Fin 5) ∈ Cspade.F from rfl)
  rcases h (Sum.inl (0 : Fin 5)) (Rs_refl 0) hante with hn | ⟨hb, -⟩
  · exact absurd ((Cspade_nOBot_iff 0).mp
      ((fork_transfer (h₁ := h₁) (h₂ := h₂) (A := nt oBot) rfl 0).1.mp hn)) (by decide)
  · exact absurd ((Cspade_oBot_iff 0).mp
      ((fork_transfer (h₁ := h₁) (h₂ := h₂) atomFree_oBot 0).1.mp hb)) (by decide)

theorem Cspade_LoG_fails (χ : PLLFormula) : ¬ Cspade.force (0 : Fin 5) (LoG χ phiSpade) :=
  fun hh => Cspade_gstretch_fails χ ((gstretch_tr (C := Cspade) (χ := χ) phiSpade 0).1.mpr hh)

theorem Cspade_FLo_fails {t : ForkParam} (ht : OkParam t) :
    ¬ Cspade.force (0 : Fin 5) (FLo t.1 t.2.1 t.2.2 phiSpade) := by
  obtain ⟨-, hδ₁, hδ₂, hd₁, hd₂⟩ := ht
  intro hh
  exact Cspade_fork_fails hδ₁ hδ₂ (forceMap hd₁ Cspade) (forceMap hd₂ Cspade)
    ((fork_tr (C := Cspade) (h₁ := forceMap hd₁ Cspade) (h₂ := forceMap hd₂ Cspade)
      phiSpade (0 : Fin 5)).1.mpr hh)

/-- **`φ♠` has NO parameterised-fork mixed cover.** -/
theorem phiSpade_no_paramForkMixedCover : ¬ HasParamForkMixedCover phiSpade :=
  not_hasParamForkMixedCover_of_model Cspade 0 Cspade_force_phiSpade
    Cspade_root_not_fallible (fun χ _ => Cspade_LoG_fails χ)
    (fun _ ht => Cspade_FLo_fails ht) (fun _ hθ => Cspade_inst_fails hθ)

/-- **REFUTED: `ParamForkMixedConj`.**  The corrected frontier
conjecture is false as well: the join of substitution, guarded
stretching and the PARAMETERISED fork still does not exhaust the
one-variable fragment. -/
theorem paramForkMixedConj_false : ¬ ParamForkMixedConj :=
  fun h => phiSpade_no_paramForkMixedCover (h phiSpade phiSpade_onlyPv)

/-- A fortiori `φ♠` defeats every earlier family. -/
theorem phiSpade_no_branchMixedCover : ¬ HasBranchMixedCover phiSpade :=
  fun hh => phiSpade_no_paramForkMixedCover (hasParamForkMixedCover_of_branchMixed hh)

theorem phiSpade_no_guardedMixedCover : ¬ HasGuardedMixedCover phiSpade :=
  fun hh => phiSpade_no_branchMixedCover (hasBranchMixedCover_of_guardedMixed hh)

theorem phiSpade_no_cover : ¬ HasCover phiSpade :=
  fun hh => phiSpade_no_guardedMixedCover (hasGuardedMixedCover_of_cover hh)

/-- Even the POINTWISE form fails: at the root of `C♠` no member of the
join is forced. -/
theorem semParamForkMixed_phiSpade_false : ¬ SemParamForkMixed phiSpade := by
  intro hh
  rcases hh Cspade 0 Cspade_force_phiSpade with
    ⟨χ, -, hf⟩ | ⟨t, ht, hf⟩ | ⟨θ, hθ, hf⟩ | hf
  · exact Cspade_LoG_fails χ hf
  · exact Cspade_FLo_fails ht hf
  · exact Cspade_inst_fails hθ hf
  · exact Cspade_root_not_fallible hf

/-- **REFUTED: `SemParamForkConj`.**  So the §14 bridge question does not
arise for THIS family: it is not merely the passage from pointwise to a
finite cover that fails, the pointwise statement itself is false. -/
theorem semParamForkConj_false : ¬ SemParamForkConj :=
  fun hh => semParamForkMixed_phiSpade_false (hh phiSpade phiSpade_onlyPv)

/-- **OPEN.**  Does `φ♠` have a uniform post-interpolant at all?  As at
`φ★`, `φ♦` and `φ♣`, the refutation is of the METHOD; nothing here
touches uniform interpolation itself. -/
def PostInterpPhiSpadeExists : Prop := ∃ ψ, IsPostInterp phiSpade ψ

/-! ## 16.  Axiom audit -/

/-- info: 'PLLND.RNEmbed.Cclub_force_phiClub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cclub_force_phiClub

/-- info: 'PLLND.RNEmbed.Cclub_swap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cclub_swap

/-- info: 'PLLND.RNEmbed.Cclub_inst_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cclub_inst_fails

/-- info: 'PLLND.RNEmbed.Cclub_gstretch_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cclub_gstretch_fails

/-- info: 'PLLND.RNEmbed.Cclub_bstretch_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cclub_bstretch_fails

/-- info: 'PLLND.RNEmbed.phiClub_no_branchMixedCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiClub_no_branchMixedCover

/-- info: 'PLLND.RNEmbed.branchMixedConj_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms branchMixedConj_false

/-- info: 'PLLND.RNEmbed.phiClub_consistent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms phiClub_consistent

/-- info: 'PLLND.RNEmbed.force_psiClub_of_phiClub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms force_psiClub_of_phiClub

/-- info: 'PLLND.RNEmbed.phiClub_psi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiClub_psi

/-- info: 'PLLND.RNEmbed.fork_force_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fork_force_eq

/-- info: 'PLLND.RNEmbed.fork_transfer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fork_transfer

/-- info: 'PLLND.RNEmbed.fork_eq_bstretch' does not depend on any axioms -/
#guard_msgs in
#print axioms fork_eq_bstretch

/-- info: 'PLLND.RNEmbed.trF_eq_trB' does not depend on any axioms -/
#guard_msgs in
#print axioms trF_eq_trB

/-- info: 'PLLND.RNEmbed.fork_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fork_tr

/-- info: 'PLLND.RNEmbed.fork_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fork_below

/-- info: 'PLLND.RNEmbed.postInterp_of_fork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_fork

/-- info: 'PLLND.RNEmbed.forkClub_force_phiClub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forkClub_force_phiClub

/-- info: 'PLLND.RNEmbed.phiClub_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiClub_minimal

/-- info: 'PLLND.RNEmbed.postInterp_phiClub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_phiClub

/-- info: 'PLLND.RNEmbed.paramFork_beats_branchMixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paramFork_beats_branchMixed

/-- info: 'PLLND.RNEmbed.interd_instTop_phiClub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interd_instTop_phiClub

/-- info: 'PLLND.RNEmbed.interd_instBot_phiClub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interd_instBot_phiClub

/-- info: 'PLLND.RNEmbed.psiClub_not_gapGuard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms psiClub_not_gapGuard

/-- info: 'PLLND.RNEmbed.phiClub_not_nnbox' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms phiClub_not_nnbox

/-- info: 'PLLND.RNEmbed.M3_fork_phiStar_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms M3_fork_phiStar_fails

/-- info: 'PLLND.RNEmbed.not_hasForkCover_phiStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_hasForkCover_phiStar

/-- info: 'PLLND.RNEmbed.paramFork_stretch_incomparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paramFork_stretch_incomparable

/-- info: 'PLLND.RNEmbed.postInterp_of_paramForkMixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_paramForkMixed

/-- info: 'PLLND.RNEmbed.postUI_of_paramForkMixedConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postUI_of_paramForkMixedConj

/-- info: 'PLLND.RNEmbed.not_hasParamForkMixedCover_of_model' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_hasParamForkMixedCover_of_model

/-- info: 'PLLND.RNEmbed.hasParamForkMixedCover_of_branchMixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasParamForkMixedCover_of_branchMixed

/-- info: 'PLLND.RNEmbed.hasParamForkMixedCover_phiClub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasParamForkMixedCover_phiClub

/-- info: 'PLLND.RNEmbed.semParamForkMixed_of_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms semParamForkMixed_of_cover

/-- info: 'PLLND.RNEmbed.Cspade_force_phiSpade' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cspade_force_phiSpade

/-- info: 'PLLND.RNEmbed.Cspade_defs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cspade_defs

/-- info: 'PLLND.RNEmbed.Cspade_agree23' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cspade_agree23

/-- info: 'PLLND.RNEmbed.Cspade_inst_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cspade_inst_fails

/-- info: 'PLLND.RNEmbed.Cspade_gstretch_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cspade_gstretch_fails

/-- info: 'PLLND.RNEmbed.Cspade_fork_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cspade_fork_fails

/-- info: 'PLLND.RNEmbed.phiSpade_consistent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms phiSpade_consistent

/-- info: 'PLLND.RNEmbed.phiSpade_no_paramForkMixedCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiSpade_no_paramForkMixedCover

/-- info: 'PLLND.RNEmbed.paramForkMixedConj_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paramForkMixedConj_false

/-- info: 'PLLND.RNEmbed.semParamForkConj_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms semParamForkConj_false

end RNEmbed
end PLLND
