import wip.coverfail

/-!
# PROVED: `∃p.φ★ = ¬¬◯⊥`

`wip/coverfail.lean` refutes the substitution-cover method at

    φ★ = ((◯⊥ ⊃ p) ⊃ (◯⊥ ∧ p)) ∧ ¬¬p ,

leaving OPEN whether `φ★` has a uniform post-interpolant at all.  This
file settles it: it does, and it is `¬¬◯⊥`.

## The construction: STRETCHING a model along its `◯⊥`-region

By `postInterpPhiStarIsNNBox_iff` only MINIMALITY is left: every
variable-free `χ` with `φ★ ⊢ χ` must satisfy `¬¬◯⊥ ⊢ χ`.
Contrapositively, from a world `u` of a model `C` with `u ⊩ ¬¬◯⊥` and
`u ⊮ χ` we must manufacture a model with a `φ★`-world refuting `χ`.

`M3v_phiStar_fails` shows the cheap route — re-valuing `p` on `C`
itself — is dead.  The repair is to STRETCH `C`: put a second copy of
the `◯⊥`-region on top of the model and value `p` there.

    stretch C :  W = C.W ⊕ C.W          (`inl` = ground layer, `inr` = upper layer)
                 Rᵢ (inl x) (inl y)  ⟺  x Rᵢ y
                 Rᵢ (inl x) (inr y)  ⟺  x Rᵢ y  ∧  y ⊩ ◯⊥      ← the GUARD
                 Rᵢ (inr x) (inl y)  ⟺  ⊥
                 Rᵢ (inr x) (inr y)  ⟺  x Rᵢ y
                 Rₘ layer-preserving, `F` on both layers,
                 V(a) = whole upper layer ∪ `F`.

The guard `y ⊩ ◯⊥` is the whole point.  Without it — i.e. for the
unguarded doubling `dbl` of `wip/postui.lean` — the upper copy `(u,1)`
of the root is available, and there `◯⊥ ⊃ p` holds vacuously (`p` is
true throughout the upper layer) while `◯⊥` fails, so the first
conjunct of `φ★` is destroyed.  With the guard, the upper copy of a
world exists above `inl u` only where `◯⊥` already holds, and
`◯⊥ ⊃ p` becomes informative again.

Concretely `stretch M3` is `M4` (with the fallible top doubled
harmlessly): the `◯⊥`-floor of `M3` is split in two and `p` is valued
on the upper half — exactly the shape `coverfail.lean` found by
exhaustive search.

Two facts drive the proof.

* `stretch_transfer` — variable-free formulas cannot see the stretch,
  on either layer.  Same mechanism as `dbl_transfer`: the `⊃` and `◯`
  clauses quantify over the new layer, but the layer index instantiates
  at itself; the guard is harmless because the `◯⊥`-region is
  `Rᵢ`-upward closed.
* `stretch_force_phiStar` — if `u ⊩ ¬¬◯⊥` in `C` then `inl u ⊩ φ★` in
  `stretch C`.  The two conjuncts are, in the stretch, EXACTLY the
  hypothesis:
  - `inl y ⊩ ¬p` ⟺ `y ⊩ ¬◯⊥` (the `p`-worlds above `inl y` are the
    upper copies, which exist precisely over the `◯⊥`-worlds), so
    `¬¬p` at `inl u` ⟺ `¬¬◯⊥` at `u`;
  - if `inl y ⊩ ◯⊥ ⊃ p` then (testing at ground-layer `◯⊥`-worlds,
    where `p` means fallible) `y ⊩ ¬◯⊥`, so `y ⊩ ⊥` by the hypothesis
    and `◯⊥ ∧ p` holds; and at an upper world `inr y` the guard has
    already delivered `y ⊩ ◯⊥`, while `p` is free.

`φ★` therefore has a post-interpolant, so it is NOT a counterexample to
uniform interpolation; the campaign's `∃`-side counterexample hunt must
look elsewhere (`gzSchema.lean`).  Note the interpolant is NOT produced
by any finite disjunction of substitution instances (`phiStar_no_cover`):
`postInterp_phiStar` is a genuinely non-substitutional interpolant.

No sorries.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## 1.  The stretch of a constraint model -/

/-- The intuitionistic relation of `stretch C`.  The only non-obvious
clause is `inl x ⊑ inr y`, which is GUARDED by `y ⊩ ◯⊥`: the upper
layer is only reachable over the `◯⊥`-region. -/
def stRi (C : ConstraintModel) : C.W ⊕ C.W → C.W ⊕ C.W → Prop
  | .inl x, .inl y => C.Ri x y
  | .inl x, .inr y => C.Ri x y ∧ C.force y oBot
  | .inr _, .inl _ => False
  | .inr x, .inr y => C.Ri x y

/-- The modal relation of `stretch C`: layer-preserving. -/
def stRm (C : ConstraintModel) : C.W ⊕ C.W → C.W ⊕ C.W → Prop
  | .inl x, .inl y => C.Rm x y
  | .inl _, .inr _ => False
  | .inr _, .inl _ => False
  | .inr x, .inr y => C.Rm x y

/-- Fallible worlds of `stretch C`: both copies of a fallible world. -/
def stF (C : ConstraintModel) : Set (C.W ⊕ C.W) :=
  fun q => match q with
    | .inl x => x ∈ C.F
    | .inr x => x ∈ C.F

/-- The valuation of `stretch C`: the WHOLE upper layer, plus the
fallible worlds (as `full_F` demands). -/
def stV (C : ConstraintModel) : Set (C.W ⊕ C.W) :=
  fun q => match q with
    | .inl x => x ∈ C.F
    | .inr _ => True

/-- **The stretch of `C`**: a second copy of the model glued on above
the `◯⊥`-region, carrying the valuation of `p`. -/
@[reducible] def stretch (C : ConstraintModel) : ConstraintModel where
  W := C.W ⊕ C.W
  Ri := stRi C
  Rm := stRm C
  F := stF C
  V _ := stV C
  refl_i := by rintro (x | x) <;> exact C.refl_i x
  trans_i := by
    rintro (x | x) (y | y) (z | z) h1 h2
    · exact C.trans_i h1 h2
    · exact ⟨C.trans_i h1 h2.1, h2.2⟩
    · exact h2.elim
    · exact ⟨C.trans_i h1.1 h2, C.force_hered h2 h1.2⟩
    · exact h1.elim
    · exact h1.elim
    · exact h2.elim
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
    · exact C.hered_F h.1 hx
    · exact h.elim
    · exact C.hered_F h hx
  hered_V := by
    rintro a (x | x) (y | y) h hx
    · exact C.hered_F h hx
    · exact trivial
    · exact h.elim
    · exact trivial
  full_F := by
    rintro a (x | x) hx
    · exact hx
    · exact trivial

/-! ## 2.  Variable-free formulas cannot see the stretch -/

/-- **Transfer.**  On BOTH layers, a variable-free formula is forced at
a copy of `x` exactly when it is forced at `x`.  (The `⊃` and `◯`
clauses quantify over the extra layer, but the layer index can always
be instantiated at its own value; the guard on `inl x ⊑ inr y` is
harmless because the `◯⊥`-region is `Rᵢ`-upward closed.) -/
theorem stretch_transfer {C : ConstraintModel} :
    ∀ {A : PLLFormula}, atomFree A = true → ∀ x : C.W,
      ((stretch C).force (.inl x) A ↔ C.force x A) ∧
      ((stretch C).force (.inr x) A ↔ C.force x A) := by
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
      · show (∀ q : C.W ⊕ C.W, stRi C (.inl x) q →
              (stretch C).force q A → (stretch C).force q B) ↔
             (∀ v : C.W, C.Ri x v → C.force v A → C.force v B)
        constructor
        · intro hh v hv hA
          exact (ihB h'.2 v).1.mp (hh (.inl v) hv ((ihA h'.1 v).1.mpr hA))
        · rintro hh (y | y) hq hA
          · exact (ihB h'.2 y).1.mpr (hh y hq ((ihA h'.1 y).1.mp hA))
          · exact (ihB h'.2 y).2.mpr (hh y hq.1 ((ihA h'.1 y).2.mp hA))
      · show (∀ q : C.W ⊕ C.W, stRi C (.inr x) q →
              (stretch C).force q A → (stretch C).force q B) ↔
             (∀ v : C.W, C.Ri x v → C.force v A → C.force v B)
        constructor
        · intro hh v hv hA
          exact (ihB h'.2 v).2.mp (hh (.inr v) hv ((ihA h'.1 v).2.mpr hA))
        · rintro hh (y | y) hq hA
          · exact hq.elim
          · exact (ihB h'.2 y).2.mpr (hh y hq ((ihA h'.1 y).2.mp hA))
  | somehow A ih =>
      intro h x
      constructor
      · show (∀ q : C.W ⊕ C.W, stRi C (.inl x) q →
              ∃ r, stRm C q r ∧ (stretch C).force r A) ↔
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
          · obtain ⟨u, hu, hfu⟩ := hh y hq.1
            exact ⟨.inr u, hu, (ih h u).2.mpr hfu⟩
      · show (∀ q : C.W ⊕ C.W, stRi C (.inr x) q →
              ∃ r, stRm C q r ∧ (stretch C).force r A) ↔
             (∀ v : C.W, C.Ri x v → ∃ u, C.Rm v u ∧ C.force u A)
        constructor
        · intro hh v hv
          obtain ⟨r, hr, hfr⟩ := hh (.inr v) hv
          match r, hr, hfr with
          | .inl r₁, hr, _ => exact hr.elim
          | .inr r₁, hr, hfr => exact ⟨r₁, hr, (ih h r₁).2.mp hfr⟩
        · rintro hh (y | y) hq
          · exact hq.elim
          · obtain ⟨u, hu, hfu⟩ := hh y hq
            exact ⟨.inr u, hu, (ih h u).2.mpr hfu⟩

/-- `◯⊥` is variable-free. -/
theorem atomFree_oBot : atomFree oBot = true := rfl

/-- On the ground layer, `p` means "fallible". -/
theorem stretch_p_inl {C : ConstraintModel} (x : C.W) :
    (stretch C).force (.inl x) (PLLFormula.prop pv) ↔ C.force x PLLFormula.falsePLL :=
  Iff.rfl

/-- On the upper layer, `p` is unconditionally true. -/
theorem stretch_p_inr {C : ConstraintModel} (x : C.W) :
    (stretch C).force (.inr x) (PLLFormula.prop pv) := trivial

/-! ## 3.  `φ★` at the stretched world -/

/-- **The heart of the matter.**  If `u ⊩ ¬¬◯⊥` in `C`, then `φ★` holds
at the ground copy of `u` in `stretch C`. -/
theorem stretch_force_phiStar {C : ConstraintModel} {u : C.W}
    (hu : C.force u (nt (nt oBot))) :
    (stretch C).force (.inl u) phiStar := by
  constructor
  · -- `(◯⊥ ⊃ p) ⊃ (◯⊥ ∧ p)`
    rintro (y | y) hq hqimp
    · -- ground layer: `◯⊥ ⊃ p` forces `¬◯⊥` at `y`, so `y` is fallible
      have hny : C.force y (nt oBot) := by
        intro z hz hzbox
        exact hqimp (.inl z) hz ((stretch_transfer atomFree_oBot z).1.mpr hzbox)
      have hyF : C.force y PLLFormula.falsePLL := hu y hq hny
      exact ⟨(stretch_transfer atomFree_oBot y).1.mpr (C.force_of_fallible hyF), hyF⟩
    · -- upper layer: the GUARD has already delivered `◯⊥`, and `p` is free
      exact ⟨(stretch_transfer atomFree_oBot y).2.mpr hq.2, stretch_p_inr y⟩
  · -- `¬¬p`
    rintro (y | y) hq hqn
    · -- `¬p` at `inl y` says the upper copies over `y` are fallible, i.e. `y ⊩ ¬◯⊥`
      have hny : C.force y (nt oBot) := by
        intro z hz hzbox
        exact hqn (.inr z) ⟨hz, hzbox⟩ (stretch_p_inr z)
      exact hu y hq hny
    · -- `¬p` at an upper world applies to the world itself
      exact hqn (.inr y) (C.refl_i y) (stretch_p_inr y)

/-! ## 4.  Minimality, and the theorem -/

/-- **Minimality.**  Every variable-free consequence of `φ★` is a
consequence of `¬¬◯⊥`. -/
theorem phiStar_minimal {χ : PLLFormula} (hχ : atomFree χ = true)
    (h : Deriv [phiStar] χ) : Deriv [nt (nt oBot)] χ := by
  classical
  by_contra hcon
  obtain ⟨C, -, u, hu, hnu⟩ := countermodel_of_not_deriv hcon
  obtain ⟨d⟩ := h
  refine hnu ((stretch_transfer hχ u).1.mp (soundness d (stretch C) (.inl u) ?_))
  intro ψ hψ
  have e : ψ = phiStar := by
    cases hψ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact stretch_force_phiStar hu

/-- **PROVED: `∃p.φ★ = ¬¬◯⊥`.**  The formula that refutes the
substitution-cover method (`phiStar_no_cover`) nonetheless HAS a uniform
post-interpolant over the variable-free fragment, and it is `¬¬◯⊥`.  So
`φ★` is not a counterexample to uniform interpolation; only to the
method. -/
theorem postInterp_phiStar : IsPostInterp phiStar (nt (nt oBot)) :=
  postInterpPhiStarIsNNBox_iff.mpr (fun _ hχ h => phiStar_minimal hχ h)

/-- The settled form of the two questions left open in
`coverfail.lean` §6″. -/
theorem postInterpPhiStarExists_true : PostInterpPhiStarExists :=
  ⟨_, postInterp_phiStar⟩

theorem postInterpPhiStarIsNNBox_true : PostInterpPhiStarIsNNBox :=
  postInterp_phiStar

/-- The interpolant is non-trivial: `¬¬◯⊥` is not `⊥` … -/
theorem postInterp_phiStar_ne_bot : ¬ Deriv [nt (nt oBot)] PLLFormula.falsePLL :=
  fun h => phiStar_consistent (Deriv.cutHead phiStar_nnbox h)

/-- In the fallible-free two-world model `N`, `◯⊥` fails everywhere. -/
theorem N_not_oBot (x : Fin 2) : ¬ N.force x oBot := by
  intro h
  obtain ⟨_, _, hy⟩ := h x (le_refl x)
  exact hy

/-- … and not `⊤`: `¬¬◯⊥` is not a theorem (it fails at the root of the
fallible-free model `N`, where `¬◯⊥` holds vacuously). -/
theorem postInterp_phiStar_ne_top : ¬ Deriv [] (nt (nt oBot)) := by
  rintro ⟨d⟩
  have hs := soundness d N (0 : Fin 2) (fun ψ hψ => by cases hψ)
  exact hs 0 (le_refl (0 : Fin 2)) (fun v _ hv => absurd hv (N_not_oBot v))

/-! ## 5.  The general method behind the proof: the STRETCH TRANSLATION

The stretch is not ad hoc.  Because the ground layer sees the upper
layer only over the `◯⊥`-region, forcing at `inl x` and at `inr x` of
`stretch C` is computed by a pair of mutually recursive VARIABLE-FREE
translations of the one-variable formula:

    Lo p      = ⊥                      Up p      = ⊤
    Lo ⊥      = ⊥                      Up ⊥      = ⊥
    Lo (A∧B)  = Lo A ∧ Lo B            Up (A∧B)  = Up A ∧ Up B
    Lo (A∨B)  = Lo A ∨ Lo B            Up (A∨B)  = Up A ∨ Up B
    Lo (A⊃B)  = (Lo A ⊃ Lo B)          Up (A⊃B)  = Up A ⊃ Up B
                ∧ (◯⊥ ⊃ (Up A ⊃ Up B))
    Lo ◯A     = ◯(Lo A) ∧ (◯⊥ ⊃ ◯(Up A))   Up ◯A = ◯(Up A)

(the `◯⊥ ⊃ …` conjuncts are the guarded quantification over the upper
layer; they are legitimate because the `◯⊥`-region is `Rᵢ`-upward
closed, so a guarded universal collapses to a pointwise one).

The consequence is a NEW general lower-bound principle, parallel to
`inst_below` but not of substitution form:

    Lo φ  ⊢  χ    for every variable-free χ with φ ⊢ χ.

Hence, exactly as with covers, `φ ⊢ Lo φ` suffices for `∃p.φ = Lo φ`
(`postInterp_of_stretch`).  This method is STRICTLY stronger than the
substitution-cover method: `φ★` satisfies it (`hasStretchCover_phiStar`)
and has no substitution cover at all (`phiStar_no_cover`). -/

/-- The pair `(Lo A, Up A)` of variable-free translations: forcing of
`A` at the ground copy and at the upper copy of a world of the stretch. -/
def tr : PLLFormula → PLLFormula × PLLFormula
  | .prop _ => (PLLFormula.falsePLL, truePLL)
  | .falsePLL => (PLLFormula.falsePLL, PLLFormula.falsePLL)
  | .and A B => ((tr A).1.and (tr B).1, (tr A).2.and (tr B).2)
  | .or A B => ((tr A).1.or (tr B).1, (tr A).2.or (tr B).2)
  | .ifThen A B =>
      (((tr A).1.ifThen (tr B).1).and (oBot.ifThen ((tr A).2.ifThen (tr B).2)),
        (tr A).2.ifThen (tr B).2)
  | .somehow A =>
      (((tr A).1.somehow).and (oBot.ifThen ((tr A).2.somehow)), (tr A).2.somehow)

/-- The GROUND translation. -/
def Lo (A : PLLFormula) : PLLFormula := (tr A).1

/-- The UPPER translation. -/
def Up (A : PLLFormula) : PLLFormula := (tr A).2

theorem Lo_prop (a : String) : Lo (PLLFormula.prop a) = PLLFormula.falsePLL := rfl
theorem Up_prop (a : String) : Up (PLLFormula.prop a) = truePLL := rfl
theorem Lo_imp (A B : PLLFormula) :
    Lo (A.ifThen B) = ((Lo A).ifThen (Lo B)).and (oBot.ifThen ((Up A).ifThen (Up B))) := rfl
theorem Up_imp (A B : PLLFormula) : Up (A.ifThen B) = (Up A).ifThen (Up B) := rfl
theorem Lo_box (A : PLLFormula) :
    Lo A.somehow = ((Lo A).somehow).and (oBot.ifThen ((Up A).somehow)) := rfl
theorem Up_box (A : PLLFormula) : Up A.somehow = (Up A).somehow := rfl

/-- **Both translations are variable-free.** -/
theorem atomFree_tr : ∀ A : PLLFormula,
    atomFree (Lo A) = true ∧ atomFree (Up A) = true := by
  intro A
  induction A with
  | prop a => exact ⟨rfl, rfl⟩
  | falsePLL => exact ⟨rfl, rfl⟩
  | and A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show (atomFree (Lo A) && atomFree (Lo B)) = true
        rw [ihA.1, ihB.1]; rfl
      · show (atomFree (Up A) && atomFree (Up B)) = true
        rw [ihA.2, ihB.2]; rfl
  | or A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show (atomFree (Lo A) && atomFree (Lo B)) = true
        rw [ihA.1, ihB.1]; rfl
      · show (atomFree (Up A) && atomFree (Up B)) = true
        rw [ihA.2, ihB.2]; rfl
  | ifThen A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show ((atomFree (Lo A) && atomFree (Lo B)) &&
              (atomFree oBot && (atomFree (Up A) && atomFree (Up B)))) = true
        rw [ihA.1, ihB.1, ihA.2, ihB.2]; rfl
      · show (atomFree (Up A) && atomFree (Up B)) = true
        rw [ihA.2, ihB.2]; rfl
  | somehow A ihA =>
      refine ⟨?_, ?_⟩
      · show (atomFree (Lo A) && (atomFree oBot && atomFree (Up A))) = true
        rw [ihA.1, ihA.2]; rfl
      · show atomFree (Up A) = true
        exact ihA.2

theorem atomFree_Lo (A : PLLFormula) : atomFree (Lo A) = true := (atomFree_tr A).1
theorem atomFree_Up (A : PLLFormula) : atomFree (Up A) = true := (atomFree_tr A).2

/-- **The translation theorem.**  Forcing at either copy of `x` in
`stretch C` is forcing of the corresponding translation at `x`.  (Every
atom is treated like `p`; `stretch C` values them all on the upper
layer.) -/
theorem stretch_tr {C : ConstraintModel} : ∀ (A : PLLFormula) (x : C.W),
    ((stretch C).force (.inl x) A ↔ C.force x (Lo A)) ∧
    ((stretch C).force (.inr x) A ↔ C.force x (Up A)) := by
  intro A
  induction A with
  | prop a => exact fun _ => ⟨Iff.rfl, ⟨fun _ => fun _ _ h => h, fun _ => trivial⟩⟩
  | falsePLL => exact fun _ => ⟨Iff.rfl, Iff.rfl⟩
  | and A B ihA ihB =>
      exact fun x => ⟨and_congr (ihA x).1 (ihB x).1, and_congr (ihA x).2 (ihB x).2⟩
  | or A B ihA ihB =>
      exact fun x => ⟨or_congr (ihA x).1 (ihB x).1, or_congr (ihA x).2 (ihB x).2⟩
  | ifThen A B ihA ihB =>
      intro x
      constructor
      · show (∀ q : C.W ⊕ C.W, stRi C (.inl x) q →
                (stretch C).force q A → (stretch C).force q B) ↔
             (C.force x ((Lo A).ifThen (Lo B)) ∧
              C.force x (oBot.ifThen ((Up A).ifThen (Up B))))
        constructor
        · intro hh
          refine ⟨fun y hy hA => (ihB y).1.mp (hh (.inl y) hy ((ihA y).1.mpr hA)), ?_⟩
          intro y hy hbox z hz hA
          have hzb : C.force z oBot := C.force_hered hz hbox
          exact (ihB z).2.mp
            (hh (.inr z) ⟨C.trans_i hy hz, hzb⟩ ((ihA z).2.mpr hA))
        · rintro ⟨h1, h2⟩ (y | y) hq hA
          · exact (ihB y).1.mpr (h1 y hq ((ihA y).1.mp hA))
          · exact (ihB y).2.mpr
              (h2 y hq.1 hq.2 y (C.refl_i y) ((ihA y).2.mp hA))
      · show (∀ q : C.W ⊕ C.W, stRi C (.inr x) q →
                (stretch C).force q A → (stretch C).force q B) ↔
             (∀ v : C.W, C.Ri x v → C.force v (Up A) → C.force v (Up B))
        constructor
        · intro hh v hv hA
          exact (ihB v).2.mp (hh (.inr v) hv ((ihA v).2.mpr hA))
        · rintro hh (y | y) hq hA
          · exact hq.elim
          · exact (ihB y).2.mpr (hh y hq ((ihA y).2.mp hA))
  | somehow A ih =>
      intro x
      constructor
      · show (∀ q : C.W ⊕ C.W, stRi C (.inl x) q →
                ∃ r, stRm C q r ∧ (stretch C).force r A) ↔
             (C.force x ((Lo A).somehow) ∧
              C.force x (oBot.ifThen ((Up A).somehow)))
        constructor
        · intro hh
          constructor
          · intro v hv
            obtain ⟨r, hr, hfr⟩ := hh (.inl v) hv
            match r, hr, hfr with
            | .inl r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).1.mp hfr⟩
            | .inr r₁, hr, _ => exact hr.elim
          · intro y hy hbox z hz
            have hzb : C.force z oBot := C.force_hered hz hbox
            obtain ⟨r, hr, hfr⟩ := hh (.inr z) ⟨C.trans_i hy hz, hzb⟩
            match r, hr, hfr with
            | .inl r₁, hr, _ => exact hr.elim
            | .inr r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).2.mp hfr⟩
        · rintro ⟨h1, h2⟩ (y | y) hq
          · obtain ⟨u, hu, hfu⟩ := h1 y hq
            exact ⟨.inl u, hu, (ih u).1.mpr hfu⟩
          · obtain ⟨u, hu, hfu⟩ := h2 y hq.1 hq.2 y (C.refl_i y)
            exact ⟨.inr u, hu, (ih u).2.mpr hfu⟩
      · show (∀ q : C.W ⊕ C.W, stRi C (.inr x) q →
                ∃ r, stRm C q r ∧ (stretch C).force r A) ↔
             (∀ v : C.W, C.Ri x v → ∃ u, C.Rm v u ∧ C.force u (Up A))
        constructor
        · intro hh v hv
          obtain ⟨r, hr, hfr⟩ := hh (.inr v) hv
          match r, hr, hfr with
          | .inl r₁, hr, _ => exact hr.elim
          | .inr r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).2.mp hfr⟩
        · rintro hh (y | y) hq
          · exact hq.elim
          · obtain ⟨u, hu, hfu⟩ := hh y hq
            exact ⟨.inr u, hu, (ih u).2.mpr hfu⟩

/-! ## 6.  The stretch lower bound, and the method -/

/-- Completeness in the form used below: a semantically valid
consequence is derivable. -/
theorem deriv_of_valid {A B : PLLFormula}
    (h : ∀ (C : ConstraintModel) (v : C.W), C.force v A → C.force v B) :
    Deriv [A] B := by
  classical
  by_contra hc
  obtain ⟨C, -, v, hA, hB⟩ := countermodel_of_not_deriv hc
  exact hB (h C v hA)

/-- **THE STRETCH LOWER BOUND.**  `Lo φ` lies below every variable-free
consequence of `φ` — the non-substitutional analogue of `inst_below`. -/
theorem stretch_below {φ χ : PLLFormula} (hχ : atomFree χ = true)
    (h : Deriv [φ] χ) : Deriv [Lo φ] χ := by
  classical
  by_contra hcon
  obtain ⟨C, -, u, hu, hnu⟩ := countermodel_of_not_deriv hcon
  obtain ⟨d⟩ := h
  refine hnu ((stretch_transfer hχ u).1.mp (soundness d (stretch C) (.inl u) ?_))
  intro ψ hψ
  have e : ψ = φ := by
    cases hψ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact (stretch_tr _ u).1.mpr hu

/-- **`φ` has a stretch cover**: the stretch lower bound is itself a
consequence of `φ`. -/
def HasStretchCover (φ : PLLFormula) : Prop := Deriv [φ] (Lo φ)

/-- **MASTER REDUCTION for the stretch method.**  A stretch cover makes
`Lo φ` the uniform post-interpolant.  No one-variable hypothesis is
needed: `stretch C` values every atom on the upper layer. -/
theorem postInterp_of_stretch {φ : PLLFormula} (h : HasStretchCover φ) :
    IsPostInterp φ (Lo φ) :=
  ⟨atomFree_Lo φ, h, fun _ hχ hd => stretch_below hχ hd⟩

/-! ## 7.  The method strictly extends the substitution-cover method -/

/-- `¬¬◯⊥ ⊢ Lo φ★` — read off `stretch_force_phiStar` through the
translation theorem. -/
theorem nnbox_to_Lo_phiStar : Deriv [nt (nt oBot)] (Lo phiStar) :=
  deriv_of_valid (fun _ u hu => (stretch_tr phiStar u).1.mp (stretch_force_phiStar hu))

/-- **`φ★` HAS a stretch cover** — while it has no substitution cover
(`phiStar_no_cover`). -/
theorem hasStretchCover_phiStar : HasStretchCover phiStar :=
  Deriv.cutHead phiStar_nnbox nnbox_to_Lo_phiStar

/-- `Lo φ★ ⊣⊢ ¬¬◯⊥`: the translation really does compute the
interpolant. -/
theorem interd_Lo_phiStar : Interd (Lo phiStar) (nt (nt oBot)) :=
  ⟨stretch_below rfl phiStar_nnbox, nnbox_to_Lo_phiStar⟩

/-- **The stretch method is STRICTLY stronger than the substitution
cover method**: some one-variable formula has a stretch cover and no
substitution cover. -/
theorem stretch_beats_cover :
    ∃ φ : PLLFormula, onlyPv φ = true ∧ HasStretchCover φ ∧ ¬ HasCover φ :=
  ⟨phiStar, phiStar_onlyPv, hasStretchCover_phiStar, phiStar_no_cover⟩

/-! ## 8.  The MIXED method, and the new reduction of last-variable `∃p`

The stretch bound and the substitution bounds are independent lower
bounds of the same consequence filter `F(φ)`, so they may be JOINED.
The stretch method alone is incomplete — at the atom `p` itself, where
`Lo p = ⊥` (`stretchCoverConj_false`), while the cover method handles it
with `[⊤]`; the cover method alone is incomplete at `φ★`, where the
stretch handles it.  Neither refutation touches the mixed method, which
subsumes both, and `postUI_of_mixedCoverConj` is the new reduction of
last-variable `∃p` to a purely syntactic question. -/

/-- **`φ` has a mixed cover**: the stretch bound together with finitely
many variable-free substitution instances jointly exhaust `φ`. -/
def HasMixedCover (φ : PLLFormula) : Prop :=
  ∃ S : List PLLFormula, (∀ θ ∈ S, atomFree θ = true) ∧
    Deriv [φ] ((Lo φ).or (bigOr (instList S φ)))

/-- **MASTER REDUCTION for the mixed method.** -/
theorem postInterp_of_mixed {φ : PLLFormula} (hφ : onlyPv φ = true)
    {S : List PLLFormula} (hS : ∀ θ ∈ S, atomFree θ = true)
    (hcov : Deriv [φ] ((Lo φ).or (bigOr (instList S φ)))) :
    IsPostInterp φ ((Lo φ).or (bigOr (instList S φ))) := by
  refine ⟨?_, hcov, ?_⟩
  · show (atomFree (Lo φ) && atomFree (bigOr (instList S φ))) = true
    rw [atomFree_Lo, atomFree_bigOr (atomFree_instList hS hφ)]; rfl
  · intro χ hχ hd
    refine Deriv.orElim (Deriv.iden (.head _)) (Deriv.toHead (stretch_below hχ hd)) ?_
    refine Deriv.bigOrElim (Deriv.iden (.head _)) ?_
    intro ψ hψ
    obtain ⟨θ, -, rfl⟩ := mem_instList hψ
    exact Deriv.toHead (inst_below θ hχ hd)

/-- A substitution cover is a mixed cover. -/
theorem hasMixedCover_of_cover {φ : PLLFormula} (h : HasCover φ) :
    HasMixedCover φ := by
  obtain ⟨S, hS, hd⟩ := h
  exact ⟨S, hS, Deriv.cutHead hd (Deriv.orIntro2 (Deriv.iden (.head _)))⟩

/-- A stretch cover is a mixed cover. -/
theorem hasMixedCover_of_stretch {φ : PLLFormula} (h : HasStretchCover φ) :
    HasMixedCover φ :=
  ⟨[], by intro θ hθ; exact absurd hθ (by simp),
   Deriv.cutHead h (Deriv.orIntro1 (Deriv.iden (.head _)))⟩

/-- **OPEN.**  Every one-variable formula has a mixed cover — the
successor of `CoverConj` after `coverConj_false`. -/
def MixedCoverConj : Prop := ∀ φ : PLLFormula, onlyPv φ = true → HasMixedCover φ

/-- **The new reduction of last-variable `∃p` to the mixed conjecture.** -/
theorem postUI_of_mixedCoverConj (h : MixedCoverConj) :
    ∀ φ : PLLFormula, onlyPv φ = true → ∃ ψ, IsPostInterp φ ψ := by
  intro φ hφ
  obtain ⟨S, hS, hcov⟩ := h φ hφ
  exact ⟨_, postInterp_of_mixed hφ hS hcov⟩

/-- **REFUTED**: the stretch method ALONE is incomplete.  `Lo p = ⊥`
and `p ⊬ ⊥`. -/
def StretchCoverConj : Prop := ∀ φ : PLLFormula, onlyPv φ = true → HasStretchCover φ

theorem Lo_pv : Lo (PLLFormula.prop pv) = PLLFormula.falsePLL := rfl

theorem p_consistent : ¬ Deriv [PLLFormula.prop pv] PLLFormula.falsePLL := by
  rintro ⟨d⟩
  have hs := soundness d N (1 : Fin 2) (fun ψ hψ => by
    have e : ψ = PLLFormula.prop pv := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact (le_refl (1 : Fin 2)))
  exact hs

theorem stretchCoverConj_false : ¬ StretchCoverConj := by
  intro h
  exact p_consistent (h (PLLFormula.prop pv) rfl)

/-- **Both single methods are incomplete; the mixed one survives
both.**  (`coverConj_false` at `φ★`, `stretchCoverConj_false` at `p`;
`φ★` and `p` both have mixed covers.) -/
theorem hasMixedCover_phiStar : HasMixedCover phiStar :=
  hasMixedCover_of_stretch hasStretchCover_phiStar

theorem hasMixedCover_pv : HasMixedCover (PLLFormula.prop pv) :=
  hasMixedCover_of_cover ⟨[truePLL], by
      intro θ hθ; rcases List.mem_singleton.mp hθ with rfl; rfl,
    Deriv.orIntro1 (by
      show Deriv [PLLFormula.prop pv] (inst truePLL (PLLFormula.prop pv))
      rw [inst_var_eq]
      exact topD)⟩

/-! ## 9.  Axiom audit -/

/-- info: 'PLLND.RNEmbed.stretch_transfer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stretch_transfer

/-- info: 'PLLND.RNEmbed.stretch_force_phiStar' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stretch_force_phiStar

/-- info: 'PLLND.RNEmbed.phiStar_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiStar_minimal

/-- info: 'PLLND.RNEmbed.postInterp_phiStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_phiStar

/-- info: 'PLLND.RNEmbed.postInterp_phiStar_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_phiStar_ne_bot

/-- info: 'PLLND.RNEmbed.postInterp_phiStar_ne_top' depends on axioms: [propext] -/
#guard_msgs in
#print axioms postInterp_phiStar_ne_top

/-- info: 'PLLND.RNEmbed.stretch_tr' does not depend on any axioms -/
#guard_msgs in
#print axioms stretch_tr

/-- info: 'PLLND.RNEmbed.deriv_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deriv_of_valid

/-- info: 'PLLND.RNEmbed.stretch_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stretch_below

/-- info: 'PLLND.RNEmbed.postInterp_of_stretch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_stretch

/-- info: 'PLLND.RNEmbed.hasStretchCover_phiStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasStretchCover_phiStar

/-- info: 'PLLND.RNEmbed.interd_Lo_phiStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interd_Lo_phiStar

/-- info: 'PLLND.RNEmbed.stretch_beats_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stretch_beats_cover

/-- info: 'PLLND.RNEmbed.postInterp_of_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_mixed

/-- info: 'PLLND.RNEmbed.postUI_of_mixedCoverConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postUI_of_mixedCoverConj

/-- info: 'PLLND.RNEmbed.stretchCoverConj_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stretchCoverConj_false

/-- info: 'PLLND.RNEmbed.hasMixedCover_phiStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasMixedCover_phiStar

end RNEmbed
end PLLND
