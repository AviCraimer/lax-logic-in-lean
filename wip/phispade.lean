import wip.paramfork

/-!
# `∃p.φ♠ = ¬¬◯⊥ ⊃ ◯⊥`, the SERIES glueing, and the two-copy GLUE scheme

`wip/paramfork.lean` §15 pins the defeater

    φ♠ = (¬◯⊥ ⊃ (¬p ∨ p)) ⊃ (¬◯⊥ ∨ (◯⊥ ∧ p))

of `ParamForkMixedConj` and leaves `∃p.φ♠` OPEN.  This file settles it,
and in doing so isolates the ONE parametric scheme of which every
construction of the campaign — substitution, the guarded stretch, the
branching stretch, the parameterised fork — is an instance.

## What is proved

* `force_psiClub_of_phiSpade`, `phiSpade_psi` — the UPPER bound
  `φ♠ ⊢ ¬¬◯⊥ ⊃ ◯⊥`.  (The same value as `φ♣`: `ψ♣ = psiClub`.)
* `glue` — **the meta-object**: two copies of `C`, an independent cross
  condition in each direction (`Cross`: none / up-closed guard on the
  TARGET / down-closed guard on the SOURCE), layer-preserving `Rₘ`, and
  free variable-free copy valuations `d₁`, `d₂`.
* `glue_transfer` — variable-free invisibility, with NO side condition
  at all (the only fact used is `crossRel_le : crossRel ⊆ Rᵢ`).
* `trGl`/`GLo`/`GUp`, `glue_tr` — the translation, with the guard as an
  IMPLICATION for up-closed cross conditions and as a DISJUNCT for
  down-closed ones (`guardImp`), and no clause at all when there is no
  cross edge.
* `glue_below`, `postInterp_of_glue` — the lower-bound principle and the
  master reduction, under the model-independent side condition `OkGlue`.
* `GLo_off_off`, `GLo_up_off`, `GLo_dn_dn` — the three identifications:
  the scheme's members at `(off, off, θ, θ)`, `(up χ, off, ⊥, ⊤)` and
  `(dn χ, dn χ, δ₁, δ₂)` ARE substitution `inst θ`, the guarded stretch
  `LoG χ` and the parameterised fork `FLo χ δ₁ δ₂`.
* `sfork` — the NEW member the campaign was missing: `(up χ, off, δ₁, δ₂)`,
  the guarded stretch with FREE copy valuations, i.e. the two copies
  glued in SERIES over an up-closed region.
* `sforkSpade_force_phiSpade`, `phiSpade_minimal`,
  **`postInterp_phiSpade : IsPostInterp phiSpade psiClub`** — the verdict
  `∃p.φ♠ = ¬¬◯⊥ ⊃ ◯⊥`, by the series member at
  `(χ, δ₁, δ₂) = (¬◯⊥, ◯⊥, ⊤)`.
* `hasGlueMixedCover_phiSpade`, `glue_beats_paramForkMixed` — the glue
  method is STRICTLY stronger than the whole parameterised-fork mixed
  family.
* `hasGlueMixedCover_of_paramForkMixed`,
  `glue_strictly_beats_paramForkMixed` — the glue scheme SUBSUMES every
  earlier family (a guard `χ` becomes `(up χ, off, ⊥, ⊤)`, a fork
  coordinate `(χ,δ₁,δ₂)` becomes `(dn χ, dn χ, δ₁, δ₂)`, a substitution
  `θ` becomes `(off, off, θ, θ)`), and strictly, by `φ♠`.
* `series_needs_free_valuations` — inside the glue scheme it is exactly
  the FREE copy valuations of the series pattern that do the work at
  `φ♠`: every `(up χ, off, ⊥, ⊤)` and every `(dn χ, dn χ, δ₁, δ₂)`
  member still fails at the root of `C♠`.
* `interd_instTop_phiSpade`, `interd_instBot_phiSpade`,
  `interd_instOBot_phiSpade`, `interd_instNOBot_phiSpade` — the
  substitution bracket: `φ♠[p := ⊤] ⊣⊢ φ♠[p := ◯⊥] ⊣⊢ ◯⊥ ∨ ¬◯⊥` and
  `φ♠[p := ⊥] ⊣⊢ φ♠[p := ¬◯⊥] ⊣⊢ ¬◯⊥`, both STRICTLY below the
  interpolant (`psiClub_not_gapGuard`).
* `GlueMixedConj` / `GlueCompleteConj` and `GlueDiagonal` — the two rival
  endgames, stated; `SeriesSuffices` — OPEN.

## Which endgame does `φ♠` support?

`GlueCompleteConj`.  Every defeater the campaign has produced (`φ★`,
`φ♦`, `φ♣`, `φ♠`) has turned out to HAVE a uniform post-interpolant, and
each time the missing ingredient was a new *shape of gluing* — never a
new *parameter*: the guards and copy valuations used are, in all four
cases, drawn from `{⊥, ◯⊥, ¬◯⊥, ◯⊥ ∨ ¬◯⊥, ⊤}`, the variable-free
formulas of `◯`-depth ≤ 1.  `φ♠` is the sharpest instance of the
pattern: it defeats the previous method *uniformly in all its
parameters* (`Cspade_gstretch_fails`, `Cspade_fork_fails`), so no
enlargement of the parameter set could have covered it — only the new
`up`-polarity-with-free-valuations shape does.  That is evidence for the
`dict φ`-bounded form of the conjecture and against the diagonal, since
a `GlueDiagonal` witness would have to defeat a scheme that now contains
all four cross polarities.

## Why `φ♠` needs the series glueing

Read off the forcing condition of `φ♠` at `w`.  Every `◯⊥`-world forces
the antecedent vacuously (above it, every `¬◯⊥`-world is fallible), so

  (α) every `◯⊥`-world of the cone forces `p`

— the same clause as `φ♣`.  On a GAP world `v` the consequent fails
outright, so the antecedent must fail:

  (β) above every gap world there is a `¬◯⊥`-world `u` at which `p` is
      UNDECIDED: `u ⊮ p`, and some NON-FALLIBLE `z ⊒ u` has `z ⊩ p`.

(β) is what no parameterised fork reproduces.  Its two copies carry
variable-free valuations, so on a variable-free-indistinguishable
`Rᵢ`-pair (`2 ⊑ 3` in `C♠`) the atom is constant on each copy, and the
cross edges — guarded by the SOURCE refuting `χ`, with `δᵢ ⊢ χ` — cannot
put a `p`-world above a `¬p`-world of the other copy.  The series
glueing does exactly that: with the cross guard on the TARGET, `inl y ⊑
inr y` holds whenever `y ⊩ χ`, and the two copies may carry INCOMPARABLE
valuations as long as `δ₁ ⊢ δ₂` — the `p`-world `inr y` sits above the
`¬p`-world `inl y` inside the guard region.  At
`(χ, δ₁, δ₂) = (¬◯⊥, ◯⊥, ⊤)`: (α) holds because `δ₁ = ◯⊥`, and (β) holds
at `inl y` for the witness `y` of `v ⊮ ¬¬◯⊥` supplied by `ψ♣`.

No sorries.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## 1.  The UPPER bound: `φ♠ ⊢ ¬¬◯⊥ ⊃ ◯⊥` -/

/-- (α) Every `◯⊥`-world of a `φ♠`-cone forces `p`.  The antecedent of
`φ♠` holds VACUOUSLY at an `◯⊥`-world: above it, `◯⊥` still holds, so a
`¬◯⊥`-world there is fallible and forces `¬p ∨ p` outright. -/
theorem phiSpade_alpha {C : ConstraintModel} {v : C.W} (hv : C.force v phiSpade)
    {u : C.W} (hu : C.Ri v u) (hub : C.force u oBot) :
    C.force u (PLLFormula.prop pv) := by
  have hante : C.force u spadeAnte := by
    intro z hz hzn
    exact C.force_of_fallible (hzn z (C.refl_i z) (C.force_hered hz hub))
  rcases hv u hu hante with hn | ⟨-, hp⟩
  · exact C.force_of_fallible (hn u (C.refl_i u) hub)
  · exact hp

/-- **The upper bound, semantically.**  Fix `v ⊒ w` with `v ⊩ ¬¬◯⊥` and
suppose `v ⊮ ◯⊥`.  Then `v ⊮ ¬◯⊥` too, so `v` is a GAP world, the
consequent of `φ♠` fails there and the antecedent must fail: some
`y ⊒ v` forces `¬◯⊥` and refutes `¬p ∨ p`.  A world refuting a
disjunction is not fallible — but `v ⊩ ¬¬◯⊥` makes every `¬◯⊥`-world
above `v` fallible.  Contradiction. -/
theorem force_psiClub_of_phiSpade {C : ConstraintModel} (w : C.W)
    (hw : C.force w phiSpade) : C.force w psiClub := by
  classical
  intro v hwv hv
  by_contra hvb
  have hvphi : C.force v phiSpade := C.force_hered hwv hw
  have hvn : ¬ C.force v (nt oBot) := fun hn =>
    hvb (C.force_of_fallible (hv v (C.refl_i v) hn))
  have hante : ¬ C.force v spadeAnte := by
    intro ha
    rcases hvphi v (C.refl_i v) ha with hn | ⟨hb, -⟩
    · exact hvn hn
    · exact hvb hb
  obtain ⟨y, hvy, hyn, hyd⟩ : ∃ y, C.Ri v y ∧ C.force y (nt oBot) ∧
      ¬ C.force y ((nt (PLLFormula.prop pv)).or (PLLFormula.prop pv)) := by
    by_contra hc
    refine hante (fun y hvy hyn => ?_)
    by_contra hyd
    exact hc ⟨y, hvy, hyn, hyd⟩
  exact (fun h => hyd (C.force_of_fallible h)) (hv y hvy hyn)

/-- **`φ♠ ⊢ ¬¬◯⊥ ⊃ ◯⊥`.** -/
theorem phiSpade_psi : Deriv [phiSpade] psiClub :=
  deriv_of_valid (fun _ w hw => force_psiClub_of_phiSpade w hw)

/-! ## 2.  The meta-object: the two-copy GLUE

A cross condition is one of three things: no edge; an edge guarded by
the TARGET forcing an (up-closed) region `χ`; an edge guarded by the
SOURCE refuting `χ` (a down-closed condition).  These are exactly the
polarities occurring in the campaign — `gstretch`/`stretch` use the
first form in one direction only, `bstretch`/`fork` the second in both.
-/

/-- A cross-edge condition between the two copies. -/
inductive Cross where
  /-- no cross edges in this direction -/
  | off : Cross
  /-- `x ⇝ y` iff `x ⊑ y` and the TARGET `y` forces `χ` (up-closed) -/
  | up : PLLFormula → Cross
  /-- `x ⇝ y` iff `x ⊑ y` and the SOURCE `x` REFUTES `χ` (down-closed) -/
  | dn : PLLFormula → Cross

/-- The relation a cross condition denotes in `C`. -/
def crossRel (C : ConstraintModel) : Cross → C.W → C.W → Prop
  | .off, _, _ => False
  | .up χ, x, y => C.Ri x y ∧ C.force y χ
  | .dn χ, x, y => C.Ri x y ∧ ¬ C.force x χ

/-- Cross edges are `Rᵢ`-edges. -/
theorem crossRel_le {C : ConstraintModel} {c : Cross} {x y : C.W}
    (h : crossRel C c x y) : C.Ri x y := by
  cases c with
  | off => exact h.elim
  | up χ => exact h.1
  | dn χ => exact h.1

/-- Cross edges absorb `Rᵢ` on the RIGHT. -/
theorem crossRel_right {C : ConstraintModel} {c : Cross} {x y z : C.W}
    (h : crossRel C c x y) (hz : C.Ri y z) : crossRel C c x z := by
  cases c with
  | off => exact h.elim
  | up χ => exact ⟨C.trans_i h.1 hz, C.force_hered hz h.2⟩
  | dn χ => exact ⟨C.trans_i h.1 hz, h.2⟩

/-- Cross edges absorb `Rᵢ` on the LEFT. -/
theorem crossRel_left {C : ConstraintModel} {c : Cross} {x y z : C.W}
    (hx : C.Ri x y) (h : crossRel C c y z) : crossRel C c x z := by
  cases c with
  | off => exact h.elim
  | up χ => exact ⟨C.trans_i hx h.1, h.2⟩
  | dn χ => exact ⟨C.trans_i hx h.1, not_force_of_Ri hx h.2⟩

/-- The intuitionistic relation of the glue. -/
def glRi (C : ConstraintModel) (cl cr : Cross) :
    C.W ⊕ C.W → C.W ⊕ C.W → Prop
  | .inl x, .inl y => C.Ri x y
  | .inl x, .inr y => crossRel C cl x y
  | .inr x, .inl y => crossRel C cr x y
  | .inr x, .inr y => C.Ri x y

/-- **The exact heredity condition on a cross direction.**  For `off` it
is vacuous; for `dn χ` with `ds ⊢ χ` it is vacuous too (the cross edge
needs `x ⊮ χ`, and `x ⊩ ds` would give `x ⊩ χ`); for `up χ` it is the
inclusion `‖ds‖ ⊆ ‖dt‖`. -/
def CrossHered (C : ConstraintModel) (c : Cross) (ds dt : PLLFormula) : Prop :=
  ∀ x y : C.W, crossRel C c x y → C.force x ds → C.force y dt

/-- **THE GLUE.**  Two copies of `C`, cross conditions `cl` (`inl ⇝ inr`)
and `cr` (`inr ⇝ inl`), layer-preserving `Rₘ` and `F`, and the copy
valuations `‖d₁‖`, `‖d₂‖`. -/
@[reducible] def glue (C : ConstraintModel) (cl cr : Cross) (d₁ d₂ : PLLFormula)
    (hlr : CrossHered C cl d₁ d₂) (hrl : CrossHered C cr d₂ d₁) : ConstraintModel where
  W := C.W ⊕ C.W
  Ri := glRi C cl cr
  Rm := stRm C
  F := stF C
  V _ := fV C d₁ d₂
  refl_i := by rintro (x | x) <;> exact C.refl_i x
  trans_i := by
    rintro (x | x) (y | y) (z | z) h1 h2
    · exact C.trans_i h1 h2
    · exact crossRel_left h1 h2
    · exact C.trans_i (crossRel_le h1) (crossRel_le h2)
    · exact crossRel_right h1 h2
    · exact crossRel_right h1 h2
    · exact C.trans_i (crossRel_le h1) (crossRel_le h2)
    · exact crossRel_left h1 h2
    · exact C.trans_i h1 h2
  refl_m := by rintro (x | x) <;> exact C.refl_m x
  trans_m := by
    rintro (x | x) (y | y) (z | z) h1 h2
    · exact C.trans_m h1 h2
    · exact h2.elim
    · exact h1.elim
    · exact h1.elim
    · exact h1.elim
    · exact h1.elim
    · exact h2.elim
    · exact C.trans_m h1 h2
  sub_mi := by
    rintro (x | x) (y | y) h
    · exact C.sub_mi h
    · exact h.elim
    · exact h.elim
    · exact C.sub_mi h
  hered_F := by
    rintro (x | x) (y | y) h hx
    · exact C.hered_F h hx
    · exact C.hered_F (crossRel_le h) hx
    · exact C.hered_F (crossRel_le h) hx
    · exact C.hered_F h hx
  hered_V := by
    rintro a (x | x) (y | y) h hx
    · exact C.force_hered h hx
    · exact hlr x y h hx
    · exact hrl x y h hx
    · exact C.force_hered h hx
  full_F := by
    rintro a (x | x) hx
    · exact C.force_of_fallible hx
    · exact C.force_of_fallible hx

/-! ## 3.  Variable-free formulas cannot see the glue

The transfer lemma needs NO condition on the pattern: the cross edges
out of a copy of `x` land on copies of worlds `y ⊒ x`, which are already
represented on the same layer, and `Rₘ` is layer-preserving. -/

/-- **Transfer, any pattern.** -/
theorem glue_transfer {C : ConstraintModel} {cl cr : Cross} {d₁ d₂ : PLLFormula}
    {hlr : CrossHered C cl d₁ d₂} {hrl : CrossHered C cr d₂ d₁} :
    ∀ {A : PLLFormula}, atomFree A = true → ∀ x : C.W,
      ((glue C cl cr d₁ d₂ hlr hrl).force (.inl x) A ↔ C.force x A) ∧
      ((glue C cl cr d₁ d₂ hlr hrl).force (.inr x) A ↔ C.force x A) := by
  intro A
  induction A with
  | prop a => intro h; exact absurd h (by simp [atomFree])
  | falsePLL => intro _ _; exact ⟨Iff.rfl, Iff.rfl⟩
  | and A B ihA ihB =>
      intro h x
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      exact ⟨and_congr (ihA h'.1 x).1 (ihB h'.2 x).1,
             and_congr (ihA h'.1 x).2 (ihB h'.2 x).2⟩
  | or A B ihA ihB =>
      intro h x
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      exact ⟨or_congr (ihA h'.1 x).1 (ihB h'.2 x).1,
             or_congr (ihA h'.1 x).2 (ihB h'.2 x).2⟩
  | ifThen A B ihA ihB =>
      intro h x
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      constructor
      · show (∀ q : C.W ⊕ C.W, glRi C cl cr (.inl x) q →
              (glue C cl cr d₁ d₂ hlr hrl).force q A →
              (glue C cl cr d₁ d₂ hlr hrl).force q B) ↔
             (∀ v : C.W, C.Ri x v → C.force v A → C.force v B)
        constructor
        · intro hh v hv hA
          exact (ihB h'.2 v).1.mp (hh (.inl v) hv ((ihA h'.1 v).1.mpr hA))
        · rintro hh (y | y) hq hA
          · exact (ihB h'.2 y).1.mpr (hh y hq ((ihA h'.1 y).1.mp hA))
          · exact (ihB h'.2 y).2.mpr (hh y (crossRel_le hq) ((ihA h'.1 y).2.mp hA))
      · show (∀ q : C.W ⊕ C.W, glRi C cl cr (.inr x) q →
              (glue C cl cr d₁ d₂ hlr hrl).force q A →
              (glue C cl cr d₁ d₂ hlr hrl).force q B) ↔
             (∀ v : C.W, C.Ri x v → C.force v A → C.force v B)
        constructor
        · intro hh v hv hA
          exact (ihB h'.2 v).2.mp (hh (.inr v) hv ((ihA h'.1 v).2.mpr hA))
        · rintro hh (y | y) hq hA
          · exact (ihB h'.2 y).1.mpr (hh y (crossRel_le hq) ((ihA h'.1 y).1.mp hA))
          · exact (ihB h'.2 y).2.mpr (hh y hq ((ihA h'.1 y).2.mp hA))
  | somehow A ih =>
      intro h x
      constructor
      · show (∀ q : C.W ⊕ C.W, glRi C cl cr (.inl x) q →
              ∃ r, stRm C q r ∧ (glue C cl cr d₁ d₂ hlr hrl).force r A) ↔
             (∀ v : C.W, C.Ri x v → ∃ u, C.Rm v u ∧ C.force u A)
        constructor
        · intro hh v hv
          obtain ⟨r, hr, hfr⟩ := hh (.inl v) hv
          match r, hr, hfr with
          | .inl r₁, hr, hfr => exact ⟨r₁, hr, (ih h r₁).1.mp hfr⟩
          | .inr r₁, hr, _ => exact hr.elim
        · rintro hh (y | y) hq
          · obtain ⟨u, hu, hfu⟩ := hh y hq
            exact ⟨.inl u, hu, (ih h u).1.mpr hfu⟩
          · obtain ⟨u, hu, hfu⟩ := hh y (crossRel_le hq)
            exact ⟨.inr u, hu, (ih h u).2.mpr hfu⟩
      · show (∀ q : C.W ⊕ C.W, glRi C cl cr (.inr x) q →
              ∃ r, stRm C q r ∧ (glue C cl cr d₁ d₂ hlr hrl).force r A) ↔
             (∀ v : C.W, C.Ri x v → ∃ u, C.Rm v u ∧ C.force u A)
        constructor
        · intro hh v hv
          obtain ⟨r, hr, hfr⟩ := hh (.inr v) hv
          match r, hr, hfr with
          | .inl r₁, hr, _ => exact hr.elim
          | .inr r₁, hr, hfr => exact ⟨r₁, hr, (ih h r₁).2.mp hfr⟩
        · rintro hh (y | y) hq
          · obtain ⟨u, hu, hfu⟩ := hh y (crossRel_le hq)
            exact ⟨.inl u, hu, (ih h u).1.mpr hfu⟩
          · obtain ⟨u, hu, hfu⟩ := hh y hq
            exact ⟨.inr u, hu, (ih h u).2.mpr hfu⟩

/-! ## 4.  The translation: guard-as-implication, guard-as-disjunct -/

/-- The cross clause of a translation: nothing at all when there is no
cross edge; the guard as an IMPLICATION for an up-closed condition; the
guard as a DISJUNCT for a down-closed one. -/
def crossGuard : Cross → PLLFormula → PLLFormula
  | .off, _ => truePLL
  | .up χ, E => χ.ifThen E
  | .dn χ, E => χ.or E

/-- The translation node: the same-copy clause `D`, conjoined with the
cross clause for `E` — and NO conjunct when there is no cross edge. -/
def guardImp : Cross → PLLFormula → PLLFormula → PLLFormula
  | .off, D, _ => D
  | .up χ, D, E => D.and (χ.ifThen E)
  | .dn χ, D, E => D.and (χ.or E)

/-- **Quantifying over the cross edges out of `x` IS forcing the cross
clause at `x`.** -/
theorem force_cross_forall {C : ConstraintModel} (c : Cross) (E : PLLFormula)
    (x : C.W) :
    (∀ y : C.W, crossRel C c x y → C.force y E) ↔ C.force x (crossGuard c E) := by
  classical
  cases c with
  | off =>
      exact ⟨fun _ => fun _ _ h => h, fun _ y hy => hy.elim⟩
  | up χ =>
      exact ⟨fun hh y hy hg => hh y ⟨hy, hg⟩, fun hh y hy => hh y hy.1 hy.2⟩
  | dn χ =>
      constructor
      · intro hh
        by_cases hx : C.force x χ
        · exact Or.inl hx
        · exact Or.inr (hh x ⟨C.refl_i x, hx⟩)
      · rintro (hx | hE) y hy
        · exact absurd hx hy.2
        · exact C.force_hered hy.1 hE

/-- The cross clause of a `◯`-node. -/
theorem force_cross_box {C : ConstraintModel} (c : Cross) (D : PLLFormula)
    (x : C.W) :
    (∀ y : C.W, crossRel C c x y → ∃ s, C.Rm y s ∧ C.force s D) ↔
      C.force x (crossGuard c D.somehow) := by
  refine Iff.trans ?_ (force_cross_forall c D.somehow x)
  constructor
  · intro hh y hy z hz
    exact hh z (crossRel_right hy hz)
  · intro hh y hy
    exact hh y hy y (C.refl_i y)

/-- Forcing a translation node. -/
theorem force_guardImp {C : ConstraintModel} (c : Cross) (D E : PLLFormula)
    (x : C.W) :
    C.force x (guardImp c D E) ↔ (C.force x D ∧ C.force x (crossGuard c E)) := by
  cases c with
  | off => exact ⟨fun h => ⟨h, fun _ _ hb => hb⟩, fun h => h.1⟩
  | up χ => exact Iff.rfl
  | dn χ => exact Iff.rfl

/-- **The glue translations.**  `trGl cl cr d₁ d₂ A = (GLo A, GUp A)`. -/
def trGl (cl cr : Cross) (d₁ d₂ : PLLFormula) : PLLFormula → PLLFormula × PLLFormula
  | .prop _ => (d₁, d₂)
  | .falsePLL => (PLLFormula.falsePLL, PLLFormula.falsePLL)
  | .and A B =>
      ((trGl cl cr d₁ d₂ A).1.and (trGl cl cr d₁ d₂ B).1,
        (trGl cl cr d₁ d₂ A).2.and (trGl cl cr d₁ d₂ B).2)
  | .or A B =>
      ((trGl cl cr d₁ d₂ A).1.or (trGl cl cr d₁ d₂ B).1,
        (trGl cl cr d₁ d₂ A).2.or (trGl cl cr d₁ d₂ B).2)
  | .ifThen A B =>
      (guardImp cl ((trGl cl cr d₁ d₂ A).1.ifThen (trGl cl cr d₁ d₂ B).1)
          ((trGl cl cr d₁ d₂ A).2.ifThen (trGl cl cr d₁ d₂ B).2),
        guardImp cr ((trGl cl cr d₁ d₂ A).2.ifThen (trGl cl cr d₁ d₂ B).2)
          ((trGl cl cr d₁ d₂ A).1.ifThen (trGl cl cr d₁ d₂ B).1))
  | .somehow A =>
      (guardImp cl ((trGl cl cr d₁ d₂ A).1.somehow) ((trGl cl cr d₁ d₂ A).2.somehow),
        guardImp cr ((trGl cl cr d₁ d₂ A).2.somehow) ((trGl cl cr d₁ d₂ A).1.somehow))

/-- The FIRST-copy translation. -/
def GLo (cl cr : Cross) (d₁ d₂ A : PLLFormula) : PLLFormula := (trGl cl cr d₁ d₂ A).1

/-- The SECOND-copy translation. -/
def GUp (cl cr : Cross) (d₁ d₂ A : PLLFormula) : PLLFormula := (trGl cl cr d₁ d₂ A).2

/-- **The glue translation theorem.**  Forcing at either copy of `x` is
forcing of the corresponding translation at `x`. -/
theorem glue_tr {C : ConstraintModel} {cl cr : Cross} {d₁ d₂ : PLLFormula}
    {hlr : CrossHered C cl d₁ d₂} {hrl : CrossHered C cr d₂ d₁} :
    ∀ (A : PLLFormula) (x : C.W),
      ((glue C cl cr d₁ d₂ hlr hrl).force (.inl x) A ↔ C.force x (GLo cl cr d₁ d₂ A)) ∧
      ((glue C cl cr d₁ d₂ hlr hrl).force (.inr x) A ↔ C.force x (GUp cl cr d₁ d₂ A)) := by
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
      · show (∀ q : C.W ⊕ C.W, glRi C cl cr (.inl x) q →
                (glue C cl cr d₁ d₂ hlr hrl).force q A →
                (glue C cl cr d₁ d₂ hlr hrl).force q B) ↔
             C.force x (guardImp cl
               ((GLo cl cr d₁ d₂ A).ifThen (GLo cl cr d₁ d₂ B))
               ((GUp cl cr d₁ d₂ A).ifThen (GUp cl cr d₁ d₂ B)))
        rw [force_guardImp]
        constructor
        · intro hh
          refine ⟨fun y hy hA => (ihB y).1.mp (hh (.inl y) hy ((ihA y).1.mpr hA)), ?_⟩
          refine (force_cross_forall cl _ x).mp (fun y hy z hz hA => ?_)
          exact (ihB z).2.mp (hh (.inr z) (crossRel_right hy hz) ((ihA z).2.mpr hA))
        · rintro ⟨h1, h2⟩ (y | y) hq hA
          · exact (ihB y).1.mpr (h1 y hq ((ihA y).1.mp hA))
          · exact (ihB y).2.mpr
              ((force_cross_forall cl _ x).mpr h2 y hq y (C.refl_i y) ((ihA y).2.mp hA))
      · show (∀ q : C.W ⊕ C.W, glRi C cl cr (.inr x) q →
                (glue C cl cr d₁ d₂ hlr hrl).force q A →
                (glue C cl cr d₁ d₂ hlr hrl).force q B) ↔
             C.force x (guardImp cr
               ((GUp cl cr d₁ d₂ A).ifThen (GUp cl cr d₁ d₂ B))
               ((GLo cl cr d₁ d₂ A).ifThen (GLo cl cr d₁ d₂ B)))
        rw [force_guardImp]
        constructor
        · intro hh
          refine ⟨fun y hy hA => (ihB y).2.mp (hh (.inr y) hy ((ihA y).2.mpr hA)), ?_⟩
          refine (force_cross_forall cr _ x).mp (fun y hy z hz hA => ?_)
          exact (ihB z).1.mp (hh (.inl z) (crossRel_right hy hz) ((ihA z).1.mpr hA))
        · rintro ⟨h1, h2⟩ (y | y) hq hA
          · exact (ihB y).1.mpr
              ((force_cross_forall cr _ x).mpr h2 y hq y (C.refl_i y) ((ihA y).1.mp hA))
          · exact (ihB y).2.mpr (h1 y hq ((ihA y).2.mp hA))
  | somehow A ih =>
      intro x
      constructor
      · show (∀ q : C.W ⊕ C.W, glRi C cl cr (.inl x) q →
                ∃ r, stRm C q r ∧ (glue C cl cr d₁ d₂ hlr hrl).force r A) ↔
             C.force x (guardImp cl ((GLo cl cr d₁ d₂ A).somehow)
               ((GUp cl cr d₁ d₂ A).somehow))
        rw [force_guardImp]
        constructor
        · intro hh
          constructor
          · intro v hv
            obtain ⟨r, hr, hfr⟩ := hh (.inl v) hv
            match r, hr, hfr with
            | .inl r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).1.mp hfr⟩
            | .inr r₁, hr, _ => exact hr.elim
          · refine (force_cross_box cl _ x).mp (fun y hy => ?_)
            obtain ⟨r, hr, hfr⟩ := hh (.inr y) hy
            match r, hr, hfr with
            | .inl r₁, hr, _ => exact hr.elim
            | .inr r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).2.mp hfr⟩
        · rintro ⟨h1, h2⟩ (y | y) hq
          · obtain ⟨u, hu, hfu⟩ := h1 y hq
            exact ⟨.inl u, hu, (ih u).1.mpr hfu⟩
          · obtain ⟨u, hu, hfu⟩ := (force_cross_box cl _ x).mpr h2 y hq
            exact ⟨.inr u, hu, (ih u).2.mpr hfu⟩
      · show (∀ q : C.W ⊕ C.W, glRi C cl cr (.inr x) q →
                ∃ r, stRm C q r ∧ (glue C cl cr d₁ d₂ hlr hrl).force r A) ↔
             C.force x (guardImp cr ((GUp cl cr d₁ d₂ A).somehow)
               ((GLo cl cr d₁ d₂ A).somehow))
        rw [force_guardImp]
        constructor
        · intro hh
          constructor
          · intro v hv
            obtain ⟨r, hr, hfr⟩ := hh (.inr v) hv
            match r, hr, hfr with
            | .inl r₁, hr, _ => exact hr.elim
            | .inr r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).2.mp hfr⟩
          · refine (force_cross_box cr _ x).mp (fun y hy => ?_)
            obtain ⟨r, hr, hfr⟩ := hh (.inl y) hy
            match r, hr, hfr with
            | .inl r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).1.mp hfr⟩
            | .inr r₁, hr, _ => exact hr.elim
        · rintro ⟨h1, h2⟩ (y | y) hq
          · obtain ⟨u, hu, hfu⟩ := (force_cross_box cr _ x).mpr h2 y hq
            exact ⟨.inl u, hu, (ih u).1.mpr hfu⟩
          · obtain ⟨u, hu, hfu⟩ := h1 y hq
            exact ⟨.inr u, hu, (ih u).2.mpr hfu⟩

/-! ## 5.  The lower-bound principle -/

/-- Variable-freeness of a cross condition. -/
def crossAF : Cross → Bool
  | .off => true
  | .up χ => atomFree χ
  | .dn χ => atomFree χ

theorem atomFree_guardImp : ∀ {c : Cross} {D E : PLLFormula}, crossAF c = true →
    atomFree D = true → atomFree E = true → atomFree (guardImp c D E) = true
  | .off, _, _, _, hD, _ => hD
  | .up χ, D, E, hc, hD, hE => by
      have hχ : atomFree χ = true := hc
      show (atomFree D && (atomFree χ && atomFree E)) = true
      rw [hD, hχ, hE]; rfl
  | .dn χ, D, E, hc, hD, hE => by
      have hχ : atomFree χ = true := hc
      show (atomFree D && (atomFree χ && atomFree E)) = true
      rw [hD, hχ, hE]; rfl

/-- **Both glue translations are variable-free, provided the guards and
the two copy valuations are.** -/
theorem atomFree_trGl {cl cr : Cross} {d₁ d₂ : PLLFormula}
    (hcl : crossAF cl = true) (hcr : crossAF cr = true)
    (h₁ : atomFree d₁ = true) (h₂ : atomFree d₂ = true) : ∀ A : PLLFormula,
    atomFree (GLo cl cr d₁ d₂ A) = true ∧ atomFree (GUp cl cr d₁ d₂ A) = true := by
  intro A
  induction A with
  | prop a => exact ⟨h₁, h₂⟩
  | falsePLL => exact ⟨rfl, rfl⟩
  | and A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show (atomFree (GLo cl cr d₁ d₂ A) && atomFree (GLo cl cr d₁ d₂ B)) = true
        rw [ihA.1, ihB.1]; rfl
      · show (atomFree (GUp cl cr d₁ d₂ A) && atomFree (GUp cl cr d₁ d₂ B)) = true
        rw [ihA.2, ihB.2]; rfl
  | or A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show (atomFree (GLo cl cr d₁ d₂ A) && atomFree (GLo cl cr d₁ d₂ B)) = true
        rw [ihA.1, ihB.1]; rfl
      · show (atomFree (GUp cl cr d₁ d₂ A) && atomFree (GUp cl cr d₁ d₂ B)) = true
        rw [ihA.2, ihB.2]; rfl
  | ifThen A B ihA ihB =>
      refine ⟨atomFree_guardImp hcl ?_ ?_, atomFree_guardImp hcr ?_ ?_⟩
      · show (atomFree (GLo cl cr d₁ d₂ A) && atomFree (GLo cl cr d₁ d₂ B)) = true
        rw [ihA.1, ihB.1]; rfl
      · show (atomFree (GUp cl cr d₁ d₂ A) && atomFree (GUp cl cr d₁ d₂ B)) = true
        rw [ihA.2, ihB.2]; rfl
      · show (atomFree (GUp cl cr d₁ d₂ A) && atomFree (GUp cl cr d₁ d₂ B)) = true
        rw [ihA.2, ihB.2]; rfl
      · show (atomFree (GLo cl cr d₁ d₂ A) && atomFree (GLo cl cr d₁ d₂ B)) = true
        rw [ihA.1, ihB.1]; rfl
  | somehow A ihA =>
      exact ⟨atomFree_guardImp hcl ihA.1 ihA.2, atomFree_guardImp hcr ihA.2 ihA.1⟩

theorem atomFree_GLo {cl cr : Cross} {d₁ d₂ : PLLFormula}
    (hcl : crossAF cl = true) (hcr : crossAF cr = true)
    (h₁ : atomFree d₁ = true) (h₂ : atomFree d₂ = true) (A : PLLFormula) :
    atomFree (GLo cl cr d₁ d₂ A) = true := (atomFree_trGl hcl hcr h₁ h₂ A).1

/-- **The model-independent side condition on a cross direction.**  For
`up` it is the inclusion `ds ⊢ dt`; for `dn χ` it is `ds ⊢ χ`, which
makes the heredity obligation VACUOUS (the cross edge needs the source
to refute `χ`). -/
def OkCross : Cross → PLLFormula → PLLFormula → Prop
  | .off, _, _ => True
  | .up _, ds, dt => Deriv [ds] dt
  | .dn χ, ds, _ => Deriv [ds] χ

theorem crossHered_of_ok : ∀ {c : Cross} {ds dt : PLLFormula}, OkCross c ds dt →
    ∀ C : ConstraintModel, CrossHered C c ds dt
  | .off, _, _, _, _ => fun _ _ h _ => h.elim
  | .up χ, ds, dt, h, C => by
      have h' : Deriv [ds] dt := h
      exact fun x y hxy hx => C.force_hered hxy.1 (forceMap h' C x hx)
  | .dn χ, ds, dt, h, C => by
      have h' : Deriv [ds] χ := h
      exact fun x y hxy hx => absurd (forceMap h' C x hx) hxy.2

/-- **THE GLUE LOWER BOUND.**  For every pattern satisfying the side
conditions, `GLo cl cr d₁ d₂ φ` lies below every variable-free
consequence of `φ`. -/
theorem glue_below {cl cr : Cross} {d₁ d₂ φ ψ : PLLFormula}
    (hl : OkCross cl d₁ d₂) (hr : OkCross cr d₂ d₁)
    (hψ : atomFree ψ = true) (h : Deriv [φ] ψ) :
    Deriv [GLo cl cr d₁ d₂ φ] ψ := by
  classical
  by_contra hcon
  obtain ⟨C, -, u, hu, hnu⟩ := countermodel_of_not_deriv hcon
  obtain ⟨d⟩ := h
  refine hnu ((glue_transfer (hlr := crossHered_of_ok hl C)
    (hrl := crossHered_of_ok hr C) hψ u).1.mp
      (soundness d (glue C cl cr d₁ d₂ (crossHered_of_ok hl C)
        (crossHered_of_ok hr C)) (.inl u) ?_))
  intro ρ hρ
  have e : ρ = φ := by
    cases hρ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact (glue_tr _ u).1.mpr hu

/-- **`φ` has a glue cover at the pattern `(cl, cr, d₁, d₂)`.** -/
def HasGlueCover (cl cr : Cross) (d₁ d₂ φ : PLLFormula) : Prop :=
  Deriv [φ] (GLo cl cr d₁ d₂ φ)

/-- **MASTER REDUCTION for a single glue member.** -/
theorem postInterp_of_glue {cl cr : Cross} {d₁ d₂ φ : PLLFormula}
    (hcl : crossAF cl = true) (hcr : crossAF cr = true)
    (h₁ : atomFree d₁ = true) (h₂ : atomFree d₂ = true)
    (hl : OkCross cl d₁ d₂) (hr : OkCross cr d₂ d₁)
    (h : HasGlueCover cl cr d₁ d₂ φ) : IsPostInterp φ (GLo cl cr d₁ d₂ φ) :=
  ⟨atomFree_GLo hcl hcr h₁ h₂ φ, h, fun _ hψ hd => glue_below hl hr hψ hd⟩

/-! ## 6.  The three identifications

Substitution, the guarded stretch and the parameterised fork are the
glue at `(off, off)`, `(up χ, off)` and `(dn χ, dn χ)`. -/

/-- **Substitution IS the glue with no cross edges and equal copy
valuations.** -/
theorem trGl_off_off (θ : PLLFormula) : ∀ {A : PLLFormula}, onlyPv A = true →
    trGl .off .off θ θ A = (inst θ A, inst θ A)
  | .prop a, h => by
      have ha : a = pv := by simpa [onlyPv] using h
      subst ha
      show ((θ : PLLFormula), (θ : PLLFormula)) = _
      rw [inst_var_eq]
  | .falsePLL, _ => rfl
  | .and A B, h => by
      have h' : onlyPv A = true ∧ onlyPv B = true := by
        simpa [onlyPv, Bool.and_eq_true] using h
      show ((trGl .off .off θ θ A).1.and (trGl .off .off θ θ B).1,
            (trGl .off .off θ θ A).2.and (trGl .off .off θ θ B).2) = _
      rw [trGl_off_off θ h'.1, trGl_off_off θ h'.2]; rfl
  | .or A B, h => by
      have h' : onlyPv A = true ∧ onlyPv B = true := by
        simpa [onlyPv, Bool.and_eq_true] using h
      show ((trGl .off .off θ θ A).1.or (trGl .off .off θ θ B).1,
            (trGl .off .off θ θ A).2.or (trGl .off .off θ θ B).2) = _
      rw [trGl_off_off θ h'.1, trGl_off_off θ h'.2]; rfl
  | .ifThen A B, h => by
      have h' : onlyPv A = true ∧ onlyPv B = true := by
        simpa [onlyPv, Bool.and_eq_true] using h
      show ((trGl .off .off θ θ A).1.ifThen (trGl .off .off θ θ B).1,
            (trGl .off .off θ θ A).2.ifThen (trGl .off .off θ θ B).2) = _
      rw [trGl_off_off θ h'.1, trGl_off_off θ h'.2]; rfl
  | .somehow A, h => by
      show ((trGl .off .off θ θ A).1.somehow, (trGl .off .off θ θ A).2.somehow) = _
      rw [trGl_off_off θ (show onlyPv A = true by simpa [onlyPv] using h)]; rfl

theorem GLo_off_off {θ φ : PLLFormula} (hφ : onlyPv φ = true) :
    GLo .off .off θ θ φ = inst θ φ := by
  show (trGl .off .off θ θ φ).1 = _
  rw [trGl_off_off θ hφ]

/-- **The guarded stretch IS the glue at `(up χ, off, ⊥, ⊤)`.** -/
theorem trGl_up_off (χ : PLLFormula) :
    ∀ A : PLLFormula, trGl (.up χ) .off PLLFormula.falsePLL truePLL A = trG χ A := by
  intro A
  induction A with
  | prop a => rfl
  | falsePLL => rfl
  | and A B ihA ihB =>
      show ((trGl (.up χ) .off PLLFormula.falsePLL truePLL A).1.and
              (trGl (.up χ) .off PLLFormula.falsePLL truePLL B).1,
            (trGl (.up χ) .off PLLFormula.falsePLL truePLL A).2.and
              (trGl (.up χ) .off PLLFormula.falsePLL truePLL B).2) = _
      rw [ihA, ihB]; rfl
  | or A B ihA ihB =>
      show ((trGl (.up χ) .off PLLFormula.falsePLL truePLL A).1.or
              (trGl (.up χ) .off PLLFormula.falsePLL truePLL B).1,
            (trGl (.up χ) .off PLLFormula.falsePLL truePLL A).2.or
              (trGl (.up χ) .off PLLFormula.falsePLL truePLL B).2) = _
      rw [ihA, ihB]; rfl
  | ifThen A B ihA ihB =>
      show (guardImp (.up χ)
              ((trGl (.up χ) .off PLLFormula.falsePLL truePLL A).1.ifThen
                (trGl (.up χ) .off PLLFormula.falsePLL truePLL B).1)
              ((trGl (.up χ) .off PLLFormula.falsePLL truePLL A).2.ifThen
                (trGl (.up χ) .off PLLFormula.falsePLL truePLL B).2),
            guardImp .off
              ((trGl (.up χ) .off PLLFormula.falsePLL truePLL A).2.ifThen
                (trGl (.up χ) .off PLLFormula.falsePLL truePLL B).2)
              ((trGl (.up χ) .off PLLFormula.falsePLL truePLL A).1.ifThen
                (trGl (.up χ) .off PLLFormula.falsePLL truePLL B).1)) = _
      rw [ihA, ihB]; rfl
  | somehow A ihA =>
      show (guardImp (.up χ)
              ((trGl (.up χ) .off PLLFormula.falsePLL truePLL A).1.somehow)
              ((trGl (.up χ) .off PLLFormula.falsePLL truePLL A).2.somehow),
            guardImp .off
              ((trGl (.up χ) .off PLLFormula.falsePLL truePLL A).2.somehow)
              ((trGl (.up χ) .off PLLFormula.falsePLL truePLL A).1.somehow)) = _
      rw [ihA]; rfl

theorem GLo_up_off (χ A : PLLFormula) :
    GLo (.up χ) .off PLLFormula.falsePLL truePLL A = LoG χ A := by
  show (trGl (.up χ) .off PLLFormula.falsePLL truePLL A).1 = (trG χ A).1
  rw [trGl_up_off]

/-- **The parameterised fork IS the glue at `(dn χ, dn χ, δ₁, δ₂)`.** -/
theorem trGl_dn_dn (χ δ₁ δ₂ : PLLFormula) :
    ∀ A : PLLFormula, trGl (.dn χ) (.dn χ) δ₁ δ₂ A = trF χ δ₁ δ₂ A := by
  intro A
  induction A with
  | prop a => rfl
  | falsePLL => rfl
  | and A B ihA ihB =>
      show ((trGl (.dn χ) (.dn χ) δ₁ δ₂ A).1.and (trGl (.dn χ) (.dn χ) δ₁ δ₂ B).1,
            (trGl (.dn χ) (.dn χ) δ₁ δ₂ A).2.and (trGl (.dn χ) (.dn χ) δ₁ δ₂ B).2) = _
      rw [ihA, ihB]; rfl
  | or A B ihA ihB =>
      show ((trGl (.dn χ) (.dn χ) δ₁ δ₂ A).1.or (trGl (.dn χ) (.dn χ) δ₁ δ₂ B).1,
            (trGl (.dn χ) (.dn χ) δ₁ δ₂ A).2.or (trGl (.dn χ) (.dn χ) δ₁ δ₂ B).2) = _
      rw [ihA, ihB]; rfl
  | ifThen A B ihA ihB =>
      show (guardImp (.dn χ)
              ((trGl (.dn χ) (.dn χ) δ₁ δ₂ A).1.ifThen (trGl (.dn χ) (.dn χ) δ₁ δ₂ B).1)
              ((trGl (.dn χ) (.dn χ) δ₁ δ₂ A).2.ifThen (trGl (.dn χ) (.dn χ) δ₁ δ₂ B).2),
            guardImp (.dn χ)
              ((trGl (.dn χ) (.dn χ) δ₁ δ₂ A).2.ifThen (trGl (.dn χ) (.dn χ) δ₁ δ₂ B).2)
              ((trGl (.dn χ) (.dn χ) δ₁ δ₂ A).1.ifThen
                (trGl (.dn χ) (.dn χ) δ₁ δ₂ B).1)) = _
      rw [ihA, ihB]; rfl
  | somehow A ihA =>
      show (guardImp (.dn χ) ((trGl (.dn χ) (.dn χ) δ₁ δ₂ A).1.somehow)
              ((trGl (.dn χ) (.dn χ) δ₁ δ₂ A).2.somehow),
            guardImp (.dn χ) ((trGl (.dn χ) (.dn χ) δ₁ δ₂ A).2.somehow)
              ((trGl (.dn χ) (.dn χ) δ₁ δ₂ A).1.somehow)) = _
      rw [ihA]; rfl

theorem GLo_dn_dn (χ δ₁ δ₂ A : PLLFormula) :
    GLo (.dn χ) (.dn χ) δ₁ δ₂ A = FLo χ δ₁ δ₂ A := by
  show (trGl (.dn χ) (.dn χ) δ₁ δ₂ A).1 = (trF χ δ₁ δ₂ A).1
  rw [trGl_dn_dn]

/-! ## 7.  The SERIES member, and `∃p.φ♠ = ¬¬◯⊥ ⊃ ◯⊥` -/

theorem sforkHered {C : ConstraintModel} {χ δ₁ δ₂ : PLLFormula} (h : Deriv [δ₁] δ₂) :
    CrossHered C (.up χ) δ₁ δ₂ :=
  fun x y hxy hx => C.force_hered hxy.1 (forceMap h C x hx)

theorem offHered {C : ConstraintModel} {ds dt : PLLFormula} :
    CrossHered C .off ds dt := fun _ _ h _ => h.elim

/-- **The SERIES glueing** — the glue member the campaign was missing:
cross edges in ONE direction, guarded by the TARGET forcing `χ`, with
FREE copy valuations `δ₁ ⊢ δ₂`.  At `(δ₁, δ₂) = (⊥, ⊤)` it IS the
guarded stretch; the point of the free valuations is that a `p`-world of
the upper copy may sit directly above a `¬p`-world of the LOWER copy,
inside the guard region — the `Rᵢ`-edge along which `p` changes that no
parallel gluing has. -/
@[reducible] def sfork (C : ConstraintModel) (χ δ₁ δ₂ : PLLFormula)
    (h : Deriv [δ₁] δ₂) : ConstraintModel :=
  glue C (.up χ) .off δ₁ δ₂ (sforkHered h) offHered

/-- The series translation. -/
def SLo (χ δ₁ δ₂ A : PLLFormula) : PLLFormula := GLo (.up χ) .off δ₁ δ₂ A

theorem SLo_eq_LoG (χ A : PLLFormula) :
    SLo χ PLLFormula.falsePLL truePLL A = LoG χ A := GLo_up_off χ A

theorem oBot_le_top : Deriv [oBot] truePLL :=
  deriv_of_valid (fun _ v _ => force_truePLL' v)

/-- **The `φ♠`-glueing**: the series member at `(χ, δ₁, δ₂) = (¬◯⊥, ◯⊥, ⊤)`.
The lower copy carries `p` exactly on `‖◯⊥‖` — clause (α) — and the
upper copy carries `p` everywhere, glued on over the `¬◯⊥`-region, which
is where clause (β) has work to do. -/
@[reducible] def sforkSpade (C : ConstraintModel) : ConstraintModel :=
  sfork C (nt oBot) oBot truePLL oBot_le_top

/-- Transfer for the `φ♠`-glueing (the two heredity proofs pinned). -/
theorem sforkSpade_transfer {C : ConstraintModel} {A : PLLFormula}
    (hA : atomFree A = true) (x : C.W) :
    ((sforkSpade C).force (.inl x) A ↔ C.force x A) ∧
    ((sforkSpade C).force (.inr x) A ↔ C.force x A) :=
  glue_transfer (hlr := sforkHered (χ := nt oBot) oBot_le_top) (hrl := offHered) hA x

/-- The translation theorem for the `φ♠`-glueing. -/
theorem sforkSpade_tr {C : ConstraintModel} (A : PLLFormula) (x : C.W) :
    ((sforkSpade C).force (.inl x) A ↔ C.force x (SLo (nt oBot) oBot truePLL A)) ∧
    ((sforkSpade C).force (.inr x) A ↔
      C.force x (GUp (.up (nt oBot)) .off oBot truePLL A)) :=
  glue_tr (hlr := sforkHered (χ := nt oBot) oBot_le_top) (hrl := offHered) A x

/-- **THE HEART OF THE MATTER.**  If `u ⊩ ¬¬◯⊥ ⊃ ◯⊥` in `C` then `φ♠`
holds at the lower copy of `u` in the `φ♠`-glueing.

At a copy of an `◯⊥`-world the consequent's second disjunct holds (`p`
is `◯⊥` on the lower copy and `⊤` on the upper); at a copy of a
`¬◯⊥`-world the first; and the UPPER copy is reachable only over
`‖¬◯⊥‖`, so those are its only worlds.  At a lower copy of a GAP world
`x` the hypothesis produces a non-fallible `y ⊒ x` with `y ⊩ ¬◯⊥`, and
`inl y` refutes the antecedent: `inl y ⊩ ¬◯⊥`, `inl y ⊮ p` (since
`y ⊮ ◯⊥`), and `inl y ⊮ ¬p` because the cross edge `inl y ⊑ inr y`
exists (`y ⊩ ¬◯⊥` is the guard) and `inr y` is a non-fallible
`p`-world. -/
theorem sforkSpade_force_phiSpade {C : ConstraintModel} {u : C.W}
    (hu : C.force u psiClub) : (sforkSpade C).force (.inl u) phiSpade := by
  classical
  rintro (x | x) hq ha
  · by_cases hb : C.force x oBot
    · exact Or.inr ⟨(sforkSpade_transfer atomFree_oBot x).1.mpr hb, hb⟩
    · by_cases hn : C.force x (nt oBot)
      · exact Or.inl ((sforkSpade_transfer (A := nt oBot) rfl x).1.mpr hn)
      · exfalso
        have hxnn : ¬ C.force x (nt (nt oBot)) := fun h => hb (hu x hq h)
        obtain ⟨y, hxy, hyn, hyf⟩ :
            ∃ y, C.Ri x y ∧ C.force y (nt oBot) ∧ ¬ C.force y PLLFormula.falsePLL := by
          by_contra hc
          refine hxnn (fun y hy hyn => ?_)
          by_contra hyf
          exact hc ⟨y, hy, hyn, hyf⟩
        have hlyn : (sforkSpade C).force (Sum.inl y) (nt oBot) :=
          (sforkSpade_transfer (A := nt oBot) rfl y).1.mpr hyn
        rcases ha (Sum.inl y) hxy hlyn with hnp | hp
        · have hcross : crossRel C (.up (nt oBot)) y y := ⟨C.refl_i y, hyn⟩
          have hpr : (sforkSpade C).force (Sum.inr y) (PLLFormula.prop pv) :=
            force_truePLL' y
          exact hyf (hnp (Sum.inr y) hcross hpr)
        · have hyb : C.force y oBot := hp
          exact hyf (hyn y (C.refl_i y) hyb)
  · exact Or.inl ((sforkSpade_transfer (A := nt oBot) rfl x).2.mpr hq.2)

/-- **Minimality.**  Every variable-free consequence of `φ♠` is a
consequence of `¬¬◯⊥ ⊃ ◯⊥`. -/
theorem phiSpade_minimal {χ : PLLFormula} (hχ : atomFree χ = true)
    (h : Deriv [phiSpade] χ) : Deriv [psiClub] χ := by
  classical
  by_contra hcon
  obtain ⟨C, -, u, hu, hnu⟩ := countermodel_of_not_deriv hcon
  obtain ⟨d⟩ := h
  refine hnu ((sforkSpade_transfer hχ u).1.mp (soundness d (sforkSpade C) (.inl u) ?_))
  intro ψ hψ
  have e : ψ = phiSpade := by
    cases hψ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact sforkSpade_force_phiSpade hu

/-- **PROVED: `∃p.φ♠ = ¬¬◯⊥ ⊃ ◯⊥`.**  The formula that defeats the whole
parameterised-fork mixed method has a uniform post-interpolant over the
variable-free fragment — the SAME value as `φ♣`. -/
theorem postInterp_phiSpade : IsPostInterp phiSpade psiClub :=
  ⟨atomFree_psiClub, phiSpade_psi, fun _ hχ hd => phiSpade_minimal hχ hd⟩

/-- `¬¬◯⊥ ⊃ ◯⊥ ⊢ SLo(¬◯⊥, ◯⊥, ⊤) φ♠`. -/
theorem psi_to_SLo_phiSpade :
    Deriv [psiClub] (SLo (nt oBot) oBot truePLL phiSpade) :=
  deriv_of_valid (fun _ u hu =>
    (sforkSpade_tr phiSpade u).1.mp (sforkSpade_force_phiSpade hu))

/-- **`φ♠` HAS a series glue cover** — while it has no
parameterised-fork mixed cover at all. -/
theorem hasGlueCover_phiSpade :
    HasGlueCover (.up (nt oBot)) .off oBot truePLL phiSpade :=
  Deriv.cutHead phiSpade_psi psi_to_SLo_phiSpade

/-- The series translation computes the interpolant. -/
theorem interd_SLo_phiSpade :
    Interd (SLo (nt oBot) oBot truePLL phiSpade) psiClub :=
  ⟨glue_below (cl := .up (nt oBot)) (cr := .off) oBot_le_top trivial
     atomFree_psiClub phiSpade_psi,
   psi_to_SLo_phiSpade⟩

/-- **The glue method is STRICTLY stronger than the whole
parameterised-fork mixed family**: `φ♠` has a glue cover at a SERIES
pattern, and no cover by any join of substitution instances, guarded
stretch bounds and parameterised fork bounds. -/
theorem glue_beats_paramForkMixed :
    ∃ φ : PLLFormula, onlyPv φ = true ∧
      HasGlueCover (.up (nt oBot)) .off oBot truePLL φ ∧
      ¬ HasParamForkMixedCover φ :=
  ⟨phiSpade, phiSpade_onlyPv, hasGlueCover_phiSpade,
   phiSpade_no_paramForkMixedCover⟩

/-! ## 8.  The instance bracket: every substitution bound of `φ♠` is
`⊣⊢ ◯⊥ ∨ ¬◯⊥` or `⊣⊢ ¬◯⊥`, both STRICTLY below the interpolant -/

/-- **`φ♠[p := ⊤] ⊣⊢ ◯⊥ ∨ ¬◯⊥`.** -/
theorem interd_instTop_phiSpade : Interd (inst truePLL phiSpade) gapGuard := by
  rw [inst_phiSpade truePLL]
  constructor
  · refine deriv_of_valid (fun C v h => ?_)
    have hante : C.force v ((oBot.ifThen .falsePLL).ifThen
        ((truePLL.ifThen .falsePLL).or truePLL)) :=
      fun u _ _ => Or.inr (force_truePLL' u)
    rcases (h v (C.refl_i v) hante :
        C.force v (oBot.ifThen .falsePLL) ∨ C.force v (oBot.and truePLL)) with h1 | ⟨h2, -⟩
    · exact Or.inr h1
    · exact Or.inl h2
  · refine deriv_of_valid (fun C v h => ?_)
    intro w hw _
    rcases (h : C.force v oBot ∨ C.force v (nt oBot)) with h1 | h2
    · exact Or.inr ⟨C.force_hered hw h1, force_truePLL' w⟩
    · exact Or.inl (C.force_hered hw h2)

/-- **`φ♠[p := ⊥] ⊣⊢ ¬◯⊥`.** -/
theorem interd_instBot_phiSpade :
    Interd (inst PLLFormula.falsePLL phiSpade) (nt oBot) := by
  rw [inst_phiSpade PLLFormula.falsePLL]
  constructor
  · refine deriv_of_valid (fun C v h => ?_)
    have hante : C.force v ((oBot.ifThen .falsePLL).ifThen
        ((PLLFormula.falsePLL.ifThen .falsePLL).or PLLFormula.falsePLL)) :=
      fun u _ _ => Or.inl (force_truePLL' u)
    rcases (h v (C.refl_i v) hante :
        C.force v (oBot.ifThen .falsePLL) ∨
          C.force v (oBot.and PLLFormula.falsePLL)) with h1 | ⟨-, h2⟩
    · exact h1
    · exact C.force_of_fallible h2
  · refine deriv_of_valid (fun C v h => ?_)
    intro w hw _
    exact Or.inl (C.force_hered hw h)

/-- **`φ♠[p := ◯⊥] ⊣⊢ ◯⊥ ∨ ¬◯⊥`.** -/
theorem interd_instOBot_phiSpade : Interd (inst oBot phiSpade) gapGuard := by
  rw [inst_phiSpade oBot]
  constructor
  · refine deriv_of_valid (fun C v h => ?_)
    have hante : C.force v ((oBot.ifThen .falsePLL).ifThen
        ((oBot.ifThen .falsePLL).or oBot)) := fun _ _ hu => Or.inl hu
    rcases (h v (C.refl_i v) hante :
        C.force v (oBot.ifThen .falsePLL) ∨ C.force v (oBot.and oBot)) with h1 | ⟨h2, -⟩
    · exact Or.inr h1
    · exact Or.inl h2
  · refine deriv_of_valid (fun C v h => ?_)
    intro w hw _
    rcases (h : C.force v oBot ∨ C.force v (nt oBot)) with h1 | h2
    · exact Or.inr ⟨C.force_hered hw h1, C.force_hered hw h1⟩
    · exact Or.inl (C.force_hered hw h2)

/-- **`φ♠[p := ¬◯⊥] ⊣⊢ ¬◯⊥`.** -/
theorem interd_instNOBot_phiSpade : Interd (inst (nt oBot) phiSpade) (nt oBot) := by
  rw [inst_phiSpade (nt oBot)]
  constructor
  · refine deriv_of_valid (fun C v h => ?_)
    have hante : C.force v ((oBot.ifThen .falsePLL).ifThen
        (((oBot.ifThen .falsePLL).ifThen .falsePLL).or (oBot.ifThen .falsePLL))) :=
      fun _ _ hu => Or.inr hu
    rcases (h v (C.refl_i v) hante :
        C.force v (oBot.ifThen .falsePLL) ∨
          C.force v (oBot.and (oBot.ifThen .falsePLL))) with h1 | ⟨h2, h3⟩
    · exact h1
    · exact C.force_of_fallible (h3 v (C.refl_i v) h2)
  · refine deriv_of_valid (fun C v h => ?_)
    intro w hw _
    exact Or.inl (C.force_hered hw h)

/-- Every instance bound of `φ♠` lies STRICTLY below the interpolant:
`◯⊥ ∨ ¬◯⊥ ⊢ ¬¬◯⊥ ⊃ ◯⊥` and `¬◯⊥ ⊢ ¬¬◯⊥ ⊃ ◯⊥`, but
`¬¬◯⊥ ⊃ ◯⊥ ⊬ ◯⊥ ∨ ¬◯⊥` (`psiClub_not_gapGuard`). -/
theorem nOBot_to_psiClub : Deriv [nt oBot] psiClub :=
  Deriv.cutHead (Deriv.orIntro2 (Deriv.iden (.head _))) gapGuard_to_psiClub

/-- **`∃p.φ♠ ≠ ¬¬◯⊥`.**  The root of `C♠` forces `φ♠` and not `¬¬◯⊥`. -/
theorem Cspade_nnOBot_iff (x : Fin 5) :
    Cspade.force x (nt (nt oBot)) ↔ (x = 1 ∨ x = 4) := by
  have key : ∀ y : Fin 5,
      (∀ v : Fin 5, Rs y v → (v = 2 ∨ v = 3 ∨ v = 4) → v = 4) ↔ (y = 1 ∨ y = 4) := by
    decide
  constructor
  · intro h
    exact (key x).mp (fun v hv h234 => h v hv ((Cspade_nOBot_iff v).mpr h234))
  · intro h v hv hvn
    exact (key x).mpr h v hv ((Cspade_nOBot_iff v).mp hvn)

theorem phiSpade_not_nnbox : ¬ Deriv [phiSpade] (nt (nt oBot)) := by
  rintro ⟨d⟩
  have hs : Cspade.force (0 : Fin 5) (nt (nt oBot)) :=
    soundness d Cspade 0 (fun ψ hψ => by
      have e : ψ = phiSpade := by
        cases hψ with
        | head => rfl
        | tail _ hh => cases hh
      subst e
      exact Cspade_force_phiSpade)
  exact absurd ((Cspade_nnOBot_iff 0).mp hs) (by decide)

/-! ## 9.  The glue mixed method, and the two rival endgames -/

/-- A glue COORDINATE. -/
abbrev GlueParam : Type := Cross × Cross × PLLFormula × PLLFormula

/-- The side condition on a coordinate. -/
def OkGlue (t : GlueParam) : Prop :=
  crossAF t.1 = true ∧ crossAF t.2.1 = true ∧ atomFree t.2.2.1 = true ∧
    atomFree t.2.2.2 = true ∧ OkCross t.1 t.2.2.1 t.2.2.2 ∧
    OkCross t.2.1 t.2.2.2 t.2.2.1

/-- The list of glue lower bounds of `φ` at the coordinates in `T`. -/
def gloList (T : List GlueParam) (φ : PLLFormula) : List PLLFormula :=
  T.map (fun t => GLo t.1 t.2.1 t.2.2.1 t.2.2.2 φ)

theorem mem_gloList {T : List GlueParam} {φ ψ : PLLFormula}
    (h : ψ ∈ gloList T φ) : ∃ t ∈ T, ψ = GLo t.1 t.2.1 t.2.2.1 t.2.2.2 φ := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
  exact ⟨t, ht, rfl⟩

/-- **`φ` has a glue mixed cover.**  (No separate substitution
coordinate is needed: `GLo off off θ θ φ = φ[p := θ]`, `GLo_off_off`.) -/
def HasGlueMixedCover (φ : PLLFormula) : Prop :=
  ∃ T : List GlueParam, (∀ t ∈ T, OkGlue t) ∧ Deriv [φ] (bigOr (gloList T φ))

/-- **MASTER REDUCTION for the glue mixed method.** -/
theorem postInterp_of_glueMixed {φ : PLLFormula} {T : List GlueParam}
    (hT : ∀ t ∈ T, OkGlue t) (hcov : Deriv [φ] (bigOr (gloList T φ))) :
    IsPostInterp φ (bigOr (gloList T φ)) := by
  refine ⟨atomFree_bigOr ?_, hcov, ?_⟩
  · intro ψ hψ
    obtain ⟨t, ht, rfl⟩ := mem_gloList hψ
    obtain ⟨ha, hb, hc, hd, -, -⟩ := hT t ht
    exact atomFree_GLo ha hb hc hd φ
  · intro ψ hψ hd
    refine Deriv.bigOrElim (Deriv.iden (.head _)) ?_
    intro ρ hρ
    obtain ⟨t, ht, rfl⟩ := mem_gloList hρ
    obtain ⟨-, -, -, -, hl, hr⟩ := hT t ht
    exact Deriv.toHead (glue_below hl hr hψ hd)

/-- **THE REFUTATION TOOL.** -/
theorem not_hasGlueMixedCover_of_model {φ : PLLFormula} (C : ConstraintModel)
    (w : C.W) (hw : C.force w φ) (hwF : ¬ C.force w PLLFormula.falsePLL)
    (hGl : ∀ t : GlueParam, OkGlue t → ¬ C.force w (GLo t.1 t.2.1 t.2.2.1 t.2.2.2 φ)) :
    ¬ HasGlueMixedCover φ := by
  rintro ⟨T, hT, hd⟩
  obtain ⟨d⟩ := hd
  have hforce : C.force w (bigOr (gloList T φ)) :=
    soundness d C w (fun ψ hψ => by
      have e : ψ = φ := by
        cases hψ with
        | head => rfl
        | tail _ h => cases h
      subst e; exact hw)
  rcases force_bigOr hforce with ⟨A, hA, hfA⟩ | hf
  · obtain ⟨t, ht, rfl⟩ := mem_gloList hA
    exact hGl t (hT t ht) hfA
  · exact hwF hf

/-- `φ♠` has a glue mixed cover: the single SERIES coordinate
`(up ¬◯⊥, off, ◯⊥, ⊤)` suffices. -/
theorem hasGlueMixedCover_phiSpade : HasGlueMixedCover phiSpade := by
  refine ⟨[(.up (nt oBot), .off, oBot, truePLL)], ?_, ?_⟩
  · intro t ht
    rcases List.mem_singleton.mp ht with rfl
    exact ⟨rfl, rfl, rfl, rfl, oBot_le_top, trivial⟩
  · show Deriv [phiSpade] (bigOr [GLo (.up (nt oBot)) .off oBot truePLL phiSpade])
    exact Deriv.orIntro1 hasGlueCover_phiSpade

/-- Every substitution cover is a glue mixed cover. -/
theorem hasGlueMixedCover_of_cover {φ : PLLFormula} (hφ : onlyPv φ = true)
    (h : HasCover φ) : HasGlueMixedCover φ := by
  obtain ⟨S, hS, hd⟩ := h
  refine ⟨S.map (fun θ => (Cross.off, Cross.off, θ, θ)), ?_, ?_⟩
  · intro t ht
    obtain ⟨θ, hθ, rfl⟩ := List.mem_map.mp ht
    exact ⟨rfl, rfl, hS θ hθ, hS θ hθ, trivial, trivial⟩
  · have e : gloList (S.map (fun θ => (Cross.off, Cross.off, θ, θ))) φ = instList S φ := by
      show (S.map (fun θ => (Cross.off, Cross.off, θ, θ))).map
          (fun t => GLo t.1 t.2.1 t.2.2.1 t.2.2.2 φ) = S.map (fun θ => inst θ φ)
      rw [List.map_map]
      exact List.map_congr_left (fun θ _ => GLo_off_off hφ)
    rw [e]
    exact hd

/-- **ENDGAME 1 — `GlueCompleteConj`.**  Finitely many glue members, at
coordinates BOUNDED IN `φ` (the uniformity sticking point of
`paramfork` §13–14: here the bound is that the guards and copy
valuations may be taken from a list `dict φ` computed from `φ`), cover
every one-variable formula. -/
def GlueCompleteConj (dict : PLLFormula → List PLLFormula) : Prop :=
  ∀ φ : PLLFormula, onlyPv φ = true →
    ∃ T : List GlueParam, (∀ t ∈ T, OkGlue t) ∧
      (∀ t ∈ T, (∀ χ : PLLFormula, t.1 = Cross.up χ ∨ t.1 = Cross.dn χ →
          χ ∈ dict φ) ∧ t.2.2.1 ∈ dict φ ∧ t.2.2.2 ∈ dict φ) ∧
      Deriv [φ] (bigOr (gloList T φ))

/-- The unbounded form: finitely many glue members, coordinates
arbitrary. -/
def GlueMixedConj : Prop := ∀ φ : PLLFormula, onlyPv φ = true → HasGlueMixedCover φ

theorem glueMixedConj_of_complete {dict : PLLFormula → List PLLFormula}
    (h : GlueCompleteConj dict) : GlueMixedConj := by
  intro φ hφ
  obtain ⟨T, hT, -, hcov⟩ := h φ hφ
  exact ⟨T, hT, hcov⟩

/-- **The reduction of last-variable `∃p` to the glue conjecture.** -/
theorem postUI_of_glueMixedConj (h : GlueMixedConj) :
    ∀ φ : PLLFormula, onlyPv φ = true → ∃ ψ, IsPostInterp φ ψ := by
  intro φ hφ
  obtain ⟨T, hT, hcov⟩ := h φ hφ
  exact ⟨_, postInterp_of_glueMixed hT hcov⟩

/-- **ENDGAME 2 — the DIAGONAL.**  A one-variable formula defeating
every member of the glue scheme at once.  By the ladder's history
(`coverConj_false`, `mixedCoverConj_false`, `branchMixedConj_false`,
`paramForkMixedConj_false`) this is the shape a genuine
Ghilardi–Zawadowski-style failure of uniform interpolation for PLL would
take; but note that every defeater so far — `φ★`, `φ♦`, `φ♣`, `φ♠` — has
turned out to HAVE a uniform post-interpolant, so a `GlueDiagonal`
witness would still not by itself refute uniform interpolation. -/
def GlueDiagonal : Prop :=
  ∃ φ : PLLFormula, onlyPv φ = true ∧ ¬ HasGlueMixedCover φ

theorem glueMixedConj_iff_no_diagonal : GlueMixedConj ↔ ¬ GlueDiagonal := by
  constructor
  · rintro h ⟨φ, hφ, hno⟩
    exact hno (h φ hφ)
  · intro h φ hφ
    by_contra hc
    exact h ⟨φ, hφ, hc⟩

/-- **OPEN.**  Is the `dn` (parallel fork) family still needed once the
series family carries free valuations?  `φ♣` has no cover with `(⊥,⊤)`
valuations (`phiClub_no_guardedMixedCover`), but nothing here rules out
a series cover at a genuinely parameterised `(up χ, off, δ₁, δ₂)`. -/
def SeriesSuffices : Prop :=
  ∀ φ : PLLFormula, onlyPv φ = true → HasGlueMixedCover φ →
    ∃ T : List GlueParam, (∀ t ∈ T, OkGlue t) ∧
      (∀ t ∈ T, (∀ χ : PLLFormula, t.1 ≠ Cross.dn χ) ∧
        (∀ χ : PLLFormula, t.2.1 ≠ Cross.dn χ)) ∧
      Deriv [φ] (bigOr (gloList T φ))

/-! ## 9′.  The glue scheme SUBSUMES the whole parameterised-fork mixed
family, and strictly -/

theorem botLeTop : Deriv [PLLFormula.falsePLL] truePLL :=
  Deriv.falsoElim _ (Deriv.iden (.head _))

theorem gloList_append (A B : List GlueParam) (φ : PLLFormula) :
    gloList (A ++ B) φ = gloList A φ ++ gloList B φ := by
  show (A ++ B).map (fun t => GLo t.1 t.2.1 t.2.2.1 t.2.2.2 φ)
      = A.map (fun t => GLo t.1 t.2.1 t.2.2.1 t.2.2.2 φ) ++
        B.map (fun t => GLo t.1 t.2.1 t.2.2.1 t.2.2.2 φ)
  rw [List.map_append]

/-- **Every parameterised-fork mixed cover is a glue mixed cover.**  A
guarded-stretch coordinate `χ` becomes `(up χ, off, ⊥, ⊤)`, a fork
coordinate `(χ, δ₁, δ₂)` becomes `(dn χ, dn χ, δ₁, δ₂)`, and a
substitution `θ` becomes `(off, off, θ, θ)`. -/
theorem hasGlueMixedCover_of_paramForkMixed {φ : PLLFormula} (hφ : onlyPv φ = true)
    (h : HasParamForkMixedCover φ) : HasGlueMixedCover φ := by
  obtain ⟨G, T, S, hG, hT, hS, hd⟩ := h
  refine ⟨(G.map (fun χ => (Cross.up χ, Cross.off, PLLFormula.falsePLL, truePLL)) ++
      T.map (fun t => (Cross.dn t.1, Cross.dn t.1, t.2.1, t.2.2))) ++
      S.map (fun θ => (Cross.off, Cross.off, θ, θ)), ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with h1 | h1
    · rcases List.mem_append.mp h1 with h2 | h2
      · obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp h2
        exact ⟨hG χ hχ, rfl, rfl, rfl, botLeTop, trivial⟩
      · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp h2
        obtain ⟨ha, hb, hc, hd₁, hd₂⟩ := hT t' ht'
        exact ⟨ha, ha, hb, hc, hd₁, hd₂⟩
    · obtain ⟨θ, hθ, rfl⟩ := List.mem_map.mp h1
      exact ⟨rfl, rfl, hS θ hθ, hS θ hθ, trivial, trivial⟩
  · have e1 : gloList (G.map
        (fun χ => (Cross.up χ, Cross.off, PLLFormula.falsePLL, truePLL))) φ
          = loList G φ := by
      show (G.map (fun χ => (Cross.up χ, Cross.off, PLLFormula.falsePLL, truePLL))).map
          (fun t => GLo t.1 t.2.1 t.2.2.1 t.2.2.2 φ) = G.map (fun χ => LoG χ φ)
      rw [List.map_map]
      exact List.map_congr_left (fun χ _ => GLo_up_off χ φ)
    have e2 : gloList (T.map
        (fun t => (Cross.dn t.1, Cross.dn t.1, t.2.1, t.2.2))) φ = floList T φ := by
      show (T.map (fun t => (Cross.dn t.1, Cross.dn t.1, t.2.1, t.2.2))).map
          (fun t => GLo t.1 t.2.1 t.2.2.1 t.2.2.2 φ)
            = T.map (fun t => FLo t.1 t.2.1 t.2.2 φ)
      rw [List.map_map]
      exact List.map_congr_left (fun t _ => GLo_dn_dn t.1 t.2.1 t.2.2 φ)
    have e3 : gloList (S.map (fun θ => (Cross.off, Cross.off, θ, θ))) φ
        = instList S φ := by
      show (S.map (fun θ => (Cross.off, Cross.off, θ, θ))).map
          (fun t => GLo t.1 t.2.1 t.2.2.1 t.2.2.2 φ) = S.map (fun θ => inst θ φ)
      rw [List.map_map]
      exact List.map_congr_left (fun θ _ => GLo_off_off hφ)
    have e : gloList ((G.map
        (fun χ => (Cross.up χ, Cross.off, PLLFormula.falsePLL, truePLL)) ++
        T.map (fun t => (Cross.dn t.1, Cross.dn t.1, t.2.1, t.2.2))) ++
        S.map (fun θ => (Cross.off, Cross.off, θ, θ))) φ
          = loList G φ ++ floList T φ ++ instList S φ := by
      rw [gloList_append, gloList_append, e1, e2, e3]
    rw [e]
    exact hd

/-- **The glue method is STRICTLY stronger than everything before it.** -/
theorem glue_strictly_beats_paramForkMixed :
    (∀ φ : PLLFormula, onlyPv φ = true → HasParamForkMixedCover φ →
      HasGlueMixedCover φ) ∧
    (onlyPv phiSpade = true ∧ HasGlueMixedCover phiSpade ∧
      ¬ HasParamForkMixedCover phiSpade) :=
  ⟨fun _ hφ h => hasGlueMixedCover_of_paramForkMixed hφ h,
   ⟨phiSpade_onlyPv, hasGlueMixedCover_phiSpade,
    phiSpade_no_paramForkMixedCover⟩⟩

/-- Every glue member at a plain guarded-stretch coordinate
`(up χ, off, ⊥, ⊤)` fails at the root of `C♠` — uniformly in `χ`. -/
theorem Cspade_GLo_up_bot_fails (χ : PLLFormula) :
    ¬ Cspade.force (0 : Fin 5)
      (GLo (.up χ) .off PLLFormula.falsePLL truePLL phiSpade) := by
  rw [GLo_up_off]
  exact Cspade_LoG_fails χ

/-- … and every member at a FORK coordinate `(dn χ, dn χ, δ₁, δ₂)` does
too. -/
theorem Cspade_GLo_dn_dn_fails {χ δ₁ δ₂ : PLLFormula} (hχ : atomFree χ = true)
    (hδ₁ : atomFree δ₁ = true) (hδ₂ : atomFree δ₂ = true)
    (hd₁ : Deriv [δ₁] χ) (hd₂ : Deriv [δ₂] χ) :
    ¬ Cspade.force (0 : Fin 5) (GLo (.dn χ) (.dn χ) δ₁ δ₂ phiSpade) := by
  rw [GLo_dn_dn]
  exact Cspade_FLo_fails (t := (χ, δ₁, δ₂)) ⟨hχ, hδ₁, hδ₂, hd₁, hd₂⟩

/-- **The FREE copy valuations of the series pattern are exactly what
does the work.**  `φ♠` has a glue cover at `(up ¬◯⊥, off, ◯⊥, ⊤)`; it has
none at any `(up χ, off, ⊥, ⊤)` (the guarded stretch) and none at any
`(dn χ, dn χ, δ₁, δ₂)` (the parameterised fork). -/
theorem series_needs_free_valuations :
    HasGlueCover (.up (nt oBot)) .off oBot truePLL phiSpade ∧
    (∀ χ : PLLFormula, ¬ Cspade.force (0 : Fin 5)
      (GLo (.up χ) .off PLLFormula.falsePLL truePLL phiSpade)) ∧
    (∀ χ δ₁ δ₂ : PLLFormula, atomFree χ = true → atomFree δ₁ = true →
      atomFree δ₂ = true → Deriv [δ₁] χ → Deriv [δ₂] χ →
      ¬ Cspade.force (0 : Fin 5) (GLo (.dn χ) (.dn χ) δ₁ δ₂ phiSpade)) :=
  ⟨hasGlueCover_phiSpade, Cspade_GLo_up_bot_fails,
   fun _ _ _ hχ hδ₁ hδ₂ hd₁ hd₂ => Cspade_GLo_dn_dn_fails hχ hδ₁ hδ₂ hd₁ hd₂⟩

/-- The interpolant of `φ♠` is neither `⊤` nor `⊥`. -/
theorem postInterp_phiSpade_ne_top : ¬ Deriv [] psiClub := psiClub_not_thm
theorem postInterp_phiSpade_ne_bot : ¬ Deriv [psiClub] PLLFormula.falsePLL :=
  psiClub_ne_bot

/-- **`φ♠` and `φ♣` have the SAME uniform post-interpolant** `¬¬◯⊥ ⊃ ◯⊥`
— the gap-region value — while `φ★` and `φ♦` have `¬¬◯⊥`. -/
theorem postInterp_phiSpade_eq_phiClub :
    IsPostInterp phiSpade psiClub ∧ IsPostInterp phiClub psiClub :=
  ⟨postInterp_phiSpade, postInterp_phiClub⟩

/-! ## 10.  Axiom audit -/

/-- info: 'PLLND.RNEmbed.phiSpade_alpha' does not depend on any axioms -/
#guard_msgs in
#print axioms phiSpade_alpha

/-- info: 'PLLND.RNEmbed.force_psiClub_of_phiSpade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms force_psiClub_of_phiSpade

/-- info: 'PLLND.RNEmbed.phiSpade_psi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiSpade_psi

/-- info: 'PLLND.RNEmbed.crossRel_le' does not depend on any axioms -/
#guard_msgs in
#print axioms crossRel_le

/-- info: 'PLLND.RNEmbed.glue_transfer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms glue_transfer

/-- info: 'PLLND.RNEmbed.force_cross_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms force_cross_forall

/-- info: 'PLLND.RNEmbed.glue_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms glue_tr

/-- info: 'PLLND.RNEmbed.glue_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms glue_below

/-- info: 'PLLND.RNEmbed.postInterp_of_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_glue

/-- info: 'PLLND.RNEmbed.GLo_off_off' depends on axioms: [propext] -/
#guard_msgs in
#print axioms GLo_off_off

/-- info: 'PLLND.RNEmbed.GLo_up_off' does not depend on any axioms -/
#guard_msgs in
#print axioms GLo_up_off

/-- info: 'PLLND.RNEmbed.GLo_dn_dn' does not depend on any axioms -/
#guard_msgs in
#print axioms GLo_dn_dn

/-- info: 'PLLND.RNEmbed.sforkSpade_force_phiSpade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sforkSpade_force_phiSpade

/-- info: 'PLLND.RNEmbed.phiSpade_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiSpade_minimal

/-- info: 'PLLND.RNEmbed.postInterp_phiSpade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_phiSpade

/-- info: 'PLLND.RNEmbed.glue_beats_paramForkMixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms glue_beats_paramForkMixed

/-- info: 'PLLND.RNEmbed.interd_instTop_phiSpade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interd_instTop_phiSpade

/-- info: 'PLLND.RNEmbed.interd_instBot_phiSpade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interd_instBot_phiSpade

/-- info: 'PLLND.RNEmbed.phiSpade_not_nnbox' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms phiSpade_not_nnbox

/-- info: 'PLLND.RNEmbed.postInterp_of_glueMixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_glueMixed

/-- info: 'PLLND.RNEmbed.hasGlueMixedCover_phiSpade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasGlueMixedCover_phiSpade

/-- info: 'PLLND.RNEmbed.postUI_of_glueMixedConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postUI_of_glueMixedConj

/-- info: 'PLLND.RNEmbed.interd_SLo_phiSpade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interd_SLo_phiSpade

/-- info: 'PLLND.RNEmbed.hasGlueMixedCover_of_paramForkMixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hasGlueMixedCover_of_paramForkMixed

/-- info: 'PLLND.RNEmbed.glue_strictly_beats_paramForkMixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms glue_strictly_beats_paramForkMixed

/-- info: 'PLLND.RNEmbed.series_needs_free_valuations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms series_needs_free_valuations

/-- info: 'PLLND.RNEmbed.postInterp_phiSpade_eq_phiClub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_phiSpade_eq_phiClub

/-- info: 'PLLND.RNEmbed.not_hasGlueMixedCover_of_model' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_hasGlueMixedCover_of_model

end RNEmbed
end PLLND
