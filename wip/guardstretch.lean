import wip.phistar

/-!
# The GUARDED STRETCH family, and the guarded mixed method

`wip/phistar.lean` builds ONE non-substitutional lower bound on the
consequence filter `F(φ) = {χ variable-free : φ ⊢ χ}`: the stretch of a
model along its `◯⊥`-region, computed syntactically by the pair of
translations `Lo`/`Up`.  Nothing in that construction is special to
`◯⊥`.  This file replaces the guard by an ARBITRARY formula `χ`:

    gstretch C χ :  W = C.W ⊕ C.W
                    Rᵢ (inl x) (inl y)  ⟺  x Rᵢ y
                    Rᵢ (inl x) (inr y)  ⟺  x Rᵢ y  ∧  y ⊩ χ      ← the GUARD
                    Rᵢ (inr x) (inl y)  ⟺  ⊥
                    Rᵢ (inr x) (inr y)  ⟺  x Rᵢ y
                    Rₘ layer-preserving, `F` on both layers,
                    V(a) = whole upper layer ∪ `F`.

`gstretch C χ` is a constraint model for every `χ` — the only property
of the guard region used is that it is `Rᵢ`-upward closed, and a truth
set always is (`C.force_hered`).  So the whole apparatus generalises:

* `gstretch_transfer` — variable-free formulas cannot see the stretch,
  on either layer, for ANY guard;
* `trG χ = (LoG χ, UpG χ)` — the guarded translations, obtained from
  `tr` by replacing `◯⊥` with `χ`;
* `gstretch_tr` — forcing at the two copies of `x` is forcing of
  `LoG χ A` and `UpG χ A` at `x`;
* `gstretch_below` — **`LoG χ φ ⊢ ψ` for every variable-free `ψ` with
  `φ ⊢ ψ`**: a FAMILY of non-substitutional lower bounds on `F(φ)`,
  one per guard, none of substitution form.

`LoG ◯⊥ = Lo` and `gstretch C ◯⊥ = stretch C` hold definitionally
(`LoG_oBot`, `gstretch_oBot`), so `phistar.lean`'s bound is the member
of the family at `χ = ◯⊥`.

Joining the whole family with the substitution instances gives the
strengthened conjecture

    GuardedMixedConj : ∀ φ one-variable, ∃ finite G, S of variable-free
                       formulas,  φ ⊢ ⋁_{χ ∈ G} LoG χ φ ∨ ⋁_{θ ∈ S} φ[p := θ]

whose master reduction `postInterp_of_guardedMixed` again produces the
uniform post-interpolant, so `postUI_of_guardedMixedConj` reduces
last-variable `∃p` to it.  `GuardedMixedConj` is implied by
`MixedCoverConj` (`hasGuardedMixedCover_of_mixed`), so it is the WEAKER
hypothesis: a counterexample to the mixed conjecture need not be one to
the guarded mixed conjecture.

§5 supplies the semantic characterisations `hasMixedCover_iff_semMixed`
and the refutation tools `not_hasMixedCover_of_model` /
`not_hasGuardedMixedCover_of_model` — the mixed analogues of
`hasCover_iff_semCover` / `not_hasCover_of_model` — which is what a
search counterexample has to be fed to.

No sorries.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## 1.  The `χ`-guarded stretch -/

/-- The intuitionistic relation of `gstretch C χ`: the upper layer is
reachable from the ground layer only over the region `‖χ‖`. -/
def gstRi (C : ConstraintModel) (χ : PLLFormula) :
    C.W ⊕ C.W → C.W ⊕ C.W → Prop
  | .inl x, .inl y => C.Ri x y
  | .inl x, .inr y => C.Ri x y ∧ C.force y χ
  | .inr _, .inl _ => False
  | .inr x, .inr y => C.Ri x y

/-- **The `χ`-guarded stretch of `C`.**  (`stRm`, `stF`, `stV` are the
guard-independent components, taken from `wip/phistar.lean`.) -/
@[reducible] def gstretch (C : ConstraintModel) (χ : PLLFormula) : ConstraintModel where
  W := C.W ⊕ C.W
  Ri := gstRi C χ
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

/-- The `◯⊥`-guarded stretch IS `phistar.lean`'s stretch. -/
theorem gstretch_oBot (C : ConstraintModel) : gstretch C oBot = stretch C := rfl

/-! ## 2.  Variable-free formulas cannot see the guarded stretch -/

/-- **Transfer, any guard.**  On BOTH layers, a variable-free formula is
forced at a copy of `x` exactly when it is forced at `x`. -/
theorem gstretch_transfer {C : ConstraintModel} {χ : PLLFormula} :
    ∀ {A : PLLFormula}, atomFree A = true → ∀ x : C.W,
      ((gstretch C χ).force (.inl x) A ↔ C.force x A) ∧
      ((gstretch C χ).force (.inr x) A ↔ C.force x A) := by
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
      · show (∀ q : C.W ⊕ C.W, gstRi C χ (.inl x) q →
              (gstretch C χ).force q A → (gstretch C χ).force q B) ↔
             (∀ v : C.W, C.Ri x v → C.force v A → C.force v B)
        constructor
        · intro hh v hv hA
          exact (ihB h'.2 v).1.mp (hh (.inl v) hv ((ihA h'.1 v).1.mpr hA))
        · rintro hh (y | y) hq hA
          · exact (ihB h'.2 y).1.mpr (hh y hq ((ihA h'.1 y).1.mp hA))
          · exact (ihB h'.2 y).2.mpr (hh y hq.1 ((ihA h'.1 y).2.mp hA))
      · show (∀ q : C.W ⊕ C.W, gstRi C χ (.inr x) q →
              (gstretch C χ).force q A → (gstretch C χ).force q B) ↔
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
      · show (∀ q : C.W ⊕ C.W, gstRi C χ (.inl x) q →
              ∃ r, stRm C q r ∧ (gstretch C χ).force r A) ↔
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
      · show (∀ q : C.W ⊕ C.W, gstRi C χ (.inr x) q →
              ∃ r, stRm C q r ∧ (gstretch C χ).force r A) ↔
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

/-! ## 3.  The guarded translations -/

/-- The guarded pair of translations: `tr` with the guard `◯⊥` replaced
by `χ`. -/
def trG (χ : PLLFormula) : PLLFormula → PLLFormula × PLLFormula
  | .prop _ => (PLLFormula.falsePLL, truePLL)
  | .falsePLL => (PLLFormula.falsePLL, PLLFormula.falsePLL)
  | .and A B => ((trG χ A).1.and (trG χ B).1, (trG χ A).2.and (trG χ B).2)
  | .or A B => ((trG χ A).1.or (trG χ B).1, (trG χ A).2.or (trG χ B).2)
  | .ifThen A B =>
      (((trG χ A).1.ifThen (trG χ B).1).and (χ.ifThen ((trG χ A).2.ifThen (trG χ B).2)),
        (trG χ A).2.ifThen (trG χ B).2)
  | .somehow A =>
      (((trG χ A).1.somehow).and (χ.ifThen ((trG χ A).2.somehow)), (trG χ A).2.somehow)

/-- The GROUND translation guarded by `χ`. -/
def LoG (χ A : PLLFormula) : PLLFormula := (trG χ A).1

/-- The UPPER translation guarded by `χ`. -/
def UpG (χ A : PLLFormula) : PLLFormula := (trG χ A).2

/-- The guarded translations at the guard `◯⊥` ARE `phistar.lean`'s
`Lo`/`Up`. -/
theorem trG_oBot : ∀ A : PLLFormula, trG oBot A = tr A := by
  intro A
  induction A with
  | prop a => rfl
  | falsePLL => rfl
  | and A B ihA ihB =>
      show ((trG oBot A).1.and (trG oBot B).1, (trG oBot A).2.and (trG oBot B).2) = _
      rw [ihA, ihB]; rfl
  | or A B ihA ihB =>
      show ((trG oBot A).1.or (trG oBot B).1, (trG oBot A).2.or (trG oBot B).2) = _
      rw [ihA, ihB]; rfl
  | ifThen A B ihA ihB =>
      show (((trG oBot A).1.ifThen (trG oBot B).1).and
              (oBot.ifThen ((trG oBot A).2.ifThen (trG oBot B).2)),
            (trG oBot A).2.ifThen (trG oBot B).2) = _
      rw [ihA, ihB]; rfl
  | somehow A ihA =>
      show (((trG oBot A).1.somehow).and (oBot.ifThen ((trG oBot A).2.somehow)),
            (trG oBot A).2.somehow) = _
      rw [ihA]; rfl

theorem LoG_oBot (A : PLLFormula) : LoG oBot A = Lo A := by
  show (trG oBot A).1 = (tr A).1
  rw [trG_oBot]

theorem UpG_oBot (A : PLLFormula) : UpG oBot A = Up A := by
  show (trG oBot A).2 = (tr A).2
  rw [trG_oBot]

theorem LoG_prop (χ : PLLFormula) (a : String) :
    LoG χ (PLLFormula.prop a) = PLLFormula.falsePLL := rfl
theorem UpG_prop (χ : PLLFormula) (a : String) :
    UpG χ (PLLFormula.prop a) = truePLL := rfl
theorem LoG_imp (χ A B : PLLFormula) :
    LoG χ (A.ifThen B)
      = ((LoG χ A).ifThen (LoG χ B)).and (χ.ifThen ((UpG χ A).ifThen (UpG χ B))) := rfl
theorem UpG_imp (χ A B : PLLFormula) :
    UpG χ (A.ifThen B) = (UpG χ A).ifThen (UpG χ B) := rfl
theorem LoG_box (χ A : PLLFormula) :
    LoG χ A.somehow = ((LoG χ A).somehow).and (χ.ifThen ((UpG χ A).somehow)) := rfl
theorem UpG_box (χ A : PLLFormula) : UpG χ A.somehow = (UpG χ A).somehow := rfl

/-- **Both guarded translations are variable-free, provided the guard
is.** -/
theorem atomFree_trG {χ : PLLFormula} (hχ : atomFree χ = true) : ∀ A : PLLFormula,
    atomFree (LoG χ A) = true ∧ atomFree (UpG χ A) = true := by
  intro A
  induction A with
  | prop a => exact ⟨rfl, rfl⟩
  | falsePLL => exact ⟨rfl, rfl⟩
  | and A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show (atomFree (LoG χ A) && atomFree (LoG χ B)) = true
        rw [ihA.1, ihB.1]; rfl
      · show (atomFree (UpG χ A) && atomFree (UpG χ B)) = true
        rw [ihA.2, ihB.2]; rfl
  | or A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show (atomFree (LoG χ A) && atomFree (LoG χ B)) = true
        rw [ihA.1, ihB.1]; rfl
      · show (atomFree (UpG χ A) && atomFree (UpG χ B)) = true
        rw [ihA.2, ihB.2]; rfl
  | ifThen A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show ((atomFree (LoG χ A) && atomFree (LoG χ B)) &&
              (atomFree χ && (atomFree (UpG χ A) && atomFree (UpG χ B)))) = true
        rw [ihA.1, ihB.1, ihA.2, ihB.2, hχ]; rfl
      · show (atomFree (UpG χ A) && atomFree (UpG χ B)) = true
        rw [ihA.2, ihB.2]; rfl
  | somehow A ihA =>
      refine ⟨?_, ?_⟩
      · show (atomFree (LoG χ A) && (atomFree χ && atomFree (UpG χ A))) = true
        rw [ihA.1, ihA.2, hχ]; rfl
      · show atomFree (UpG χ A) = true
        exact ihA.2

theorem atomFree_LoG {χ : PLLFormula} (hχ : atomFree χ = true) (A : PLLFormula) :
    atomFree (LoG χ A) = true := (atomFree_trG hχ A).1

theorem atomFree_UpG {χ : PLLFormula} (hχ : atomFree χ = true) (A : PLLFormula) :
    atomFree (UpG χ A) = true := (atomFree_trG hχ A).2

/-- **The guarded translation theorem.**  Forcing at either copy of `x`
in `gstretch C χ` is forcing of the corresponding guarded translation at
`x`. -/
theorem gstretch_tr {C : ConstraintModel} {χ : PLLFormula} :
    ∀ (A : PLLFormula) (x : C.W),
      ((gstretch C χ).force (.inl x) A ↔ C.force x (LoG χ A)) ∧
      ((gstretch C χ).force (.inr x) A ↔ C.force x (UpG χ A)) := by
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
      · show (∀ q : C.W ⊕ C.W, gstRi C χ (.inl x) q →
                (gstretch C χ).force q A → (gstretch C χ).force q B) ↔
             (C.force x ((LoG χ A).ifThen (LoG χ B)) ∧
              C.force x (χ.ifThen ((UpG χ A).ifThen (UpG χ B))))
        constructor
        · intro hh
          refine ⟨fun y hy hA => (ihB y).1.mp (hh (.inl y) hy ((ihA y).1.mpr hA)), ?_⟩
          intro y hy hg z hz hA
          have hzg : C.force z χ := C.force_hered hz hg
          exact (ihB z).2.mp
            (hh (.inr z) ⟨C.trans_i hy hz, hzg⟩ ((ihA z).2.mpr hA))
        · rintro ⟨h1, h2⟩ (y | y) hq hA
          · exact (ihB y).1.mpr (h1 y hq ((ihA y).1.mp hA))
          · exact (ihB y).2.mpr
              (h2 y hq.1 hq.2 y (C.refl_i y) ((ihA y).2.mp hA))
      · show (∀ q : C.W ⊕ C.W, gstRi C χ (.inr x) q →
                (gstretch C χ).force q A → (gstretch C χ).force q B) ↔
             (∀ v : C.W, C.Ri x v → C.force v (UpG χ A) → C.force v (UpG χ B))
        constructor
        · intro hh v hv hA
          exact (ihB v).2.mp (hh (.inr v) hv ((ihA v).2.mpr hA))
        · rintro hh (y | y) hq hA
          · exact hq.elim
          · exact (ihB y).2.mpr (hh y hq ((ihA y).2.mp hA))
  | somehow A ih =>
      intro x
      constructor
      · show (∀ q : C.W ⊕ C.W, gstRi C χ (.inl x) q →
                ∃ r, stRm C q r ∧ (gstretch C χ).force r A) ↔
             (C.force x ((LoG χ A).somehow) ∧
              C.force x (χ.ifThen ((UpG χ A).somehow)))
        constructor
        · intro hh
          constructor
          · intro v hv
            obtain ⟨r, hr, hfr⟩ := hh (.inl v) hv
            match r, hr, hfr with
            | .inl r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).1.mp hfr⟩
            | .inr r₁, hr, _ => exact hr.elim
          · intro y hy hg z hz
            have hzg : C.force z χ := C.force_hered hz hg
            obtain ⟨r, hr, hfr⟩ := hh (.inr z) ⟨C.trans_i hy hz, hzg⟩
            match r, hr, hfr with
            | .inl r₁, hr, _ => exact hr.elim
            | .inr r₁, hr, hfr => exact ⟨r₁, hr, (ih r₁).2.mp hfr⟩
        · rintro ⟨h1, h2⟩ (y | y) hq
          · obtain ⟨u, hu, hfu⟩ := h1 y hq
            exact ⟨.inl u, hu, (ih u).1.mpr hfu⟩
          · obtain ⟨u, hu, hfu⟩ := h2 y hq.1 hq.2 y (C.refl_i y)
            exact ⟨.inr u, hu, (ih u).2.mpr hfu⟩
      · show (∀ q : C.W ⊕ C.W, gstRi C χ (.inr x) q →
                ∃ r, stRm C q r ∧ (gstretch C χ).force r A) ↔
             (∀ v : C.W, C.Ri x v → ∃ u, C.Rm v u ∧ C.force u (UpG χ A))
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

/-! ## 4.  The guarded lower bounds, and the guarded mixed method -/

/-- **THE GUARDED STRETCH LOWER BOUND.**  For EVERY guard `χ`, the
formula `LoG χ φ` lies below every variable-free consequence of `φ`.
(No hypothesis on `χ`; variable-freeness of `χ` is only needed to know
that `LoG χ φ` is itself variable-free.) -/
theorem gstretch_below {χ φ ψ : PLLFormula} (hψ : atomFree ψ = true)
    (h : Deriv [φ] ψ) : Deriv [LoG χ φ] ψ := by
  classical
  by_contra hcon
  obtain ⟨C, -, u, hu, hnu⟩ := countermodel_of_not_deriv hcon
  obtain ⟨d⟩ := h
  refine hnu ((gstretch_transfer hψ u).1.mp (soundness d (gstretch C χ) (.inl u) ?_))
  intro ρ hρ
  have e : ρ = φ := by
    cases hρ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact (gstretch_tr _ u).1.mpr hu

/-- `φ` has a `χ`-guarded stretch cover. -/
def HasGuardedCover (χ φ : PLLFormula) : Prop := Deriv [φ] (LoG χ φ)

/-- **MASTER REDUCTION for a single guard.** -/
theorem postInterp_of_gstretch {χ φ : PLLFormula} (hχ : atomFree χ = true)
    (h : HasGuardedCover χ φ) : IsPostInterp φ (LoG χ φ) :=
  ⟨atomFree_LoG hχ φ, h, fun _ hψ hd => gstretch_below hψ hd⟩

/-- The list of guarded lower bounds of `φ` at the guards in `G`. -/
def loList (G : List PLLFormula) (φ : PLLFormula) : List PLLFormula :=
  G.map (fun χ => LoG χ φ)

theorem mem_loList {G : List PLLFormula} {φ ψ : PLLFormula}
    (h : ψ ∈ loList G φ) : ∃ χ ∈ G, ψ = LoG χ φ := by
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp h
  exact ⟨χ, hχ, rfl⟩

/-- **`φ` has a guarded mixed cover**: finitely many guarded stretch
bounds together with finitely many variable-free substitution instances
jointly exhaust `φ`. -/
def HasGuardedMixedCover (φ : PLLFormula) : Prop :=
  ∃ G S : List PLLFormula, (∀ χ ∈ G, atomFree χ = true) ∧
    (∀ θ ∈ S, atomFree θ = true) ∧
    Deriv [φ] (bigOr (loList G φ ++ instList S φ))

/-- **MASTER REDUCTION for the guarded mixed method.** -/
theorem postInterp_of_guardedMixed {φ : PLLFormula} (hφ : onlyPv φ = true)
    {G S : List PLLFormula} (hG : ∀ χ ∈ G, atomFree χ = true)
    (hS : ∀ θ ∈ S, atomFree θ = true)
    (hcov : Deriv [φ] (bigOr (loList G φ ++ instList S φ))) :
    IsPostInterp φ (bigOr (loList G φ ++ instList S φ)) := by
  refine ⟨atomFree_bigOr ?_, hcov, ?_⟩
  · intro ψ hψ
    rcases List.mem_append.mp hψ with h | h
    · obtain ⟨χ, hχ, rfl⟩ := mem_loList h
      exact atomFree_LoG (hG χ hχ) φ
    · exact atomFree_instList hS hφ ψ h
  · intro ψ hψ hd
    refine Deriv.bigOrElim (Deriv.iden (.head _)) ?_
    intro ρ hρ
    rcases List.mem_append.mp hρ with h | h
    · obtain ⟨χ, -, rfl⟩ := mem_loList h
      exact Deriv.toHead (gstretch_below hψ hd)
    · obtain ⟨θ, -, rfl⟩ := mem_instList h
      exact Deriv.toHead (inst_below θ hψ hd)

/-- **The guarded mixed conjecture** — the weakening of
`MixedCoverConj` in which the stretch may be guarded by any finite set
of variable-free formulas, not just by `◯⊥`. -/
def GuardedMixedConj : Prop := ∀ φ : PLLFormula, onlyPv φ = true → HasGuardedMixedCover φ

/-- **The reduction of last-variable `∃p` to the guarded mixed
conjecture.** -/
theorem postUI_of_guardedMixedConj (h : GuardedMixedConj) :
    ∀ φ : PLLFormula, onlyPv φ = true → ∃ ψ, IsPostInterp φ ψ := by
  intro φ hφ
  obtain ⟨G, S, hG, hS, hcov⟩ := h φ hφ
  exact ⟨_, postInterp_of_guardedMixed hφ hG hS hcov⟩

/-- **A mixed cover is a guarded mixed cover** (guard list `[◯⊥]`): the
guarded conjecture is WEAKER than `MixedCoverConj`. -/
theorem hasGuardedMixedCover_of_mixed {φ : PLLFormula} (h : HasMixedCover φ) :
    HasGuardedMixedCover φ := by
  obtain ⟨S, hS, hd⟩ := h
  refine ⟨[oBot], S, ?_, hS, ?_⟩
  · intro χ hχ; rcases List.mem_singleton.mp hχ with rfl; rfl
  · have e : loList [oBot] φ ++ instList S φ = Lo φ :: instList S φ := by
      show LoG oBot φ :: instList S φ = _
      rw [LoG_oBot]
    rw [e]
    exact hd

/-- … and so is a plain substitution cover, and a plain stretch cover. -/
theorem hasGuardedMixedCover_of_cover {φ : PLLFormula} (h : HasCover φ) :
    HasGuardedMixedCover φ :=
  hasGuardedMixedCover_of_mixed (hasMixedCover_of_cover h)

theorem hasGuardedMixedCover_of_stretch {φ : PLLFormula} (h : HasStretchCover φ) :
    HasGuardedMixedCover φ :=
  hasGuardedMixedCover_of_mixed (hasMixedCover_of_stretch h)

/-! ## 5.  Semantic form of the mixed conjectures, and the refutation tools -/

/-- **The semantic form of a mixed cover `S`.** -/
def SemMixed (φ : PLLFormula) (S : List PLLFormula) : Prop :=
  ∀ (C : ConstraintModel) (w : C.W), C.force w φ →
    C.force w (Lo φ) ∨ (∃ θ ∈ S, C.force w (inst θ φ)) ∨
      C.force w PLLFormula.falsePLL

theorem semMixed_of_deriv {φ : PLLFormula} {S : List PLLFormula}
    (h : Deriv [φ] ((Lo φ).or (bigOr (instList S φ)))) : SemMixed φ S := by
  rintro C w hw
  obtain ⟨d⟩ := h
  have hforce : C.force w ((Lo φ).or (bigOr (instList S φ))) :=
    soundness d C w (fun ψ hψ => by
      have e : ψ = φ := by
        cases hψ with
        | head => rfl
        | tail _ h => cases h
      subst e; exact hw)
  rcases (hforce : C.force w (Lo φ) ∨ C.force w (bigOr (instList S φ))) with h1 | h2
  · exact Or.inl h1
  · rcases force_bigOr h2 with ⟨A, hA, hfA⟩ | hf
    · obtain ⟨θ, hθ, rfl⟩ := mem_instList hA
      exact Or.inr (Or.inl ⟨θ, hθ, hfA⟩)
    · exact Or.inr (Or.inr hf)

theorem deriv_of_semMixed {φ : PLLFormula} {S : List PLLFormula}
    (h : SemMixed φ S) : Deriv [φ] ((Lo φ).or (bigOr (instList S φ))) := by
  classical
  by_contra hcon
  obtain ⟨C, -, v, hv, hnv⟩ := countermodel_of_not_deriv hcon
  rcases h C v hv with h1 | ⟨θ, hθ, hf⟩ | hbot
  · exact hnv (Or.inl h1)
  · exact hnv (Or.inr (force_bigOr_of_mem (List.mem_map.mpr ⟨θ, hθ, rfl⟩) hf))
  · exact hnv (C.force_of_fallible hbot)

/-- **The mixed cover conjecture is a statement about valuations.** -/
theorem hasMixedCover_iff_semMixed {φ : PLLFormula} :
    HasMixedCover φ ↔
      ∃ S : List PLLFormula, (∀ θ ∈ S, atomFree θ = true) ∧ SemMixed φ S :=
  ⟨fun ⟨S, hS, hd⟩ => ⟨S, hS, semMixed_of_deriv hd⟩,
   fun ⟨S, hS, hs⟩ => ⟨S, hS, deriv_of_semMixed hs⟩⟩

/-- **THE REFUTATION TOOL for `MixedCoverConj`.**  One non-fallible
world forcing `φ` at which the stretch bound `Lo φ` fails and no
variable-free instance is forced refutes every mixed cover at once. -/
theorem not_hasMixedCover_of_model {φ : PLLFormula} (C : ConstraintModel) (w : C.W)
    (hw : C.force w φ) (hwF : ¬ C.force w PLLFormula.falsePLL)
    (hLo : ¬ C.force w (Lo φ))
    (hno : ∀ θ : PLLFormula, atomFree θ = true → ¬ C.force w (inst θ φ)) :
    ¬ HasMixedCover φ := by
  rintro ⟨S, hS, hd⟩
  rcases semMixed_of_deriv hd C w hw with h1 | ⟨θ, hθ, hf⟩ | hbot
  · exact hLo h1
  · exact hno θ (hS θ hθ) hf
  · exact hwF hbot

/-- **THE REFUTATION TOOL for `GuardedMixedConj`.**  Same, with EVERY
variable-free guard required to fail. -/
theorem not_hasGuardedMixedCover_of_model {φ : PLLFormula} (C : ConstraintModel)
    (w : C.W) (hw : C.force w φ) (hwF : ¬ C.force w PLLFormula.falsePLL)
    (hLo : ∀ χ : PLLFormula, atomFree χ = true → ¬ C.force w (LoG χ φ))
    (hno : ∀ θ : PLLFormula, atomFree θ = true → ¬ C.force w (inst θ φ)) :
    ¬ HasGuardedMixedCover φ := by
  rintro ⟨G, S, hG, hS, hd⟩
  obtain ⟨d⟩ := hd
  have hforce : C.force w (bigOr (loList G φ ++ instList S φ)) :=
    soundness d C w (fun ψ hψ => by
      have e : ψ = φ := by
        cases hψ with
        | head => rfl
        | tail _ h => cases h
      subst e; exact hw)
  rcases force_bigOr hforce with ⟨A, hA, hfA⟩ | hf
  · rcases List.mem_append.mp hA with h | h
    · obtain ⟨χ, hχ, rfl⟩ := mem_loList h
      exact hLo χ (hG χ hχ) hfA
    · obtain ⟨θ, hθ, rfl⟩ := mem_instList h
      exact hno θ (hS θ hθ) hfA
  · exact hwF hf

/-! ## 6.  The family is genuinely a family: `φ★` again

`φ★` has a `◯⊥`-guarded cover (`hasStretchCover_phiStar`), hence a
guarded mixed cover; the guard `χ = ⊤` does NOT work for it — the
unguarded doubling is exactly what `phistar.lean`'s §1 discussion rules
out — so the family is not collapsed by any single member. -/

/-- The `◯⊥` member of the family gives `φ★` its cover. -/
theorem hasGuardedCover_phiStar : HasGuardedCover oBot phiStar :=
  hasStretchCover_phiStar

theorem hasGuardedMixedCover_phiStar : HasGuardedMixedCover phiStar :=
  hasGuardedMixedCover_of_mixed hasMixedCover_phiStar

/-- **The guard `⊤` OVERSHOOTS at `φ★`**: `LoG ⊤ φ★ ⊢ ◯⊥`.  (Under
the unguarded doubling the upper copy of EVERY world is available, and
`◯⊥ ⊃ p` holds vacuously there because `p` is true throughout the upper
layer; the first conjunct of `φ★` then forces `◯⊥` outright.  In fact
`LoG ⊤ φ★ ⊣⊢ ◯⊥`, strictly below the true interpolant `¬¬◯⊥`.) -/
theorem LoG_top_phiStar_oBot : Deriv [LoG truePLL phiStar] oBot := by
  have h1 : Deriv [LoG truePLL phiStar]
      (truePLL.ifThen ((oBot.ifThen truePLL).ifThen (oBot.and truePLL))) :=
    Deriv.andElim2 (Deriv.andElim1 (Deriv.iden (.head _)))
  have h2 : Deriv [LoG truePLL phiStar]
      ((oBot.ifThen truePLL).ifThen (oBot.and truePLL)) :=
    Deriv.impElim h1 topD
  exact Deriv.andElim1 (Deriv.impElim h2 (Deriv.impIntro topD))

/-- **The `⊤` member of the family does NOT cover `φ★`** — while the
`◯⊥` member does (`hasGuardedCover_phiStar`).  So the guards give
genuinely different bounds, and the family is not collapsed by any
single member. -/
theorem not_hasGuardedCover_top_phiStar : ¬ HasGuardedCover truePLL phiStar :=
  fun h => phiStar_not_oBot (Deriv.cutHead h LoG_top_phiStar_oBot)

/-! ## 7.  Axiom audit -/

/-- info: 'PLLND.RNEmbed.gstretch_transfer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms gstretch_transfer

/-- info: 'PLLND.RNEmbed.gstretch_tr' does not depend on any axioms -/
#guard_msgs in
#print axioms gstretch_tr

/-- info: 'PLLND.RNEmbed.gstretch_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gstretch_below

/-- info: 'PLLND.RNEmbed.postInterp_of_gstretch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_gstretch

/-- info: 'PLLND.RNEmbed.postInterp_of_guardedMixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_guardedMixed

/-- info: 'PLLND.RNEmbed.postUI_of_guardedMixedConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postUI_of_guardedMixedConj

/-- info: 'PLLND.RNEmbed.hasMixedCover_iff_semMixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasMixedCover_iff_semMixed

/-- info: 'PLLND.RNEmbed.not_hasMixedCover_of_model' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_hasMixedCover_of_model

/-- info: 'PLLND.RNEmbed.not_hasGuardedMixedCover_of_model' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_hasGuardedMixedCover_of_model

end RNEmbed
end PLLND
