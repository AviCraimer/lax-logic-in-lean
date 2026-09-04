import wip.mixedfail

/-!
# PROVED: `∃p.φ♦ = ¬¬◯⊥` — the BRANCHING stretch

`wip/mixedfail.lean` refutes `MixedCoverConj` and `GuardedMixedConj` at

    φ♦ = ((◯⊥ ⊃ p) ∨ ◯⊥ ∨ ¬p) ⊃ ((◯⊥ ∧ p) ∨ (◯⊥ ∧ ¬p))

and leaves OPEN whether `φ♦` has a uniform post-interpolant at all
(`PostInterpPhiDiaExists`).  It does, and — as at `φ★` — it is `¬¬◯⊥`.
So uniform interpolation does NOT fail at `φ♦`: the escalation
`p ∨ ¬p → φ★ → φ♦` refutes methods, never UI.

## Why every 2-layer (guarded) stretch had to fail

Read off the forcing condition of `φ♦` at a world `w`.  Since the
consequent `(◯⊥ ∧ p) ∨ (◯⊥ ∧ ¬p)` needs `◯⊥`, and the antecedent
`(◯⊥ ⊃ p) ∨ ◯⊥ ∨ ¬p` contains `◯⊥` outright, `w ⊩ φ♦` says exactly:
for every `v ⊒ w`,

* (α) if `v ⊩ ◯⊥` then `v ⊩ p` or `v ⊩ ¬p`  — the `◯⊥`-region DECIDES `p`;
* (β) if `v ⊮ ◯⊥` then the antecedent must fail at `v`, i.e. there is
  `z ⊒ v` with `z ⊩ ◯⊥` and `z ⊮ p` (killing `◯⊥ ⊃ p`) AND there is
  `z' ⊒ v` with `z' ⊩ p` and `z'` not fallible (killing `¬p`).

(β) is a TWO-SIDED demand: over every world below the `◯⊥`-region one
needs both a `p`-free `◯⊥`-branch and a non-fallible `p`-branch.  A
single upper curtain — `stretch`/`gstretch`, the whole guarded family —
cannot meet it, and `Md_gstretch_fails` is that failure made concrete:
whichever guard is chosen, either a non-fallible ground `◯⊥`-world
acquires an upper `p`-copy and (α) fails there, or the upper layer sits
only over fallible worlds and (β)'s second half fails at the root.

## The construction: FORKING the model at the `◯⊥`-boundary

The repair adds a branch, not a layer.  Take TWO copies of `C` glued
below the guard region and separated on it:

    bstretch C χ :  W = C.W ⊕ C.W
                    Rᵢ (inl x) (inl y)  ⟺  x Rᵢ y
                    Rᵢ (inr x) (inr y)  ⟺  x Rᵢ y
                    Rᵢ (inl x) (inr y)  ⟺  x Rᵢ y  ∧  x ⊮ χ
                    Rᵢ (inr x) (inl y)  ⟺  x Rᵢ y  ∧  x ⊮ χ
                    Rₘ layer-preserving, `F` on both layers,
                    V(a) = ‖χ‖ on the `inl` copy, `F` on the `inr` copy.

The cross guard `x ⊮ χ` is legitimate: `‖χ‖` is `Rᵢ`-upward closed, so
its complement is downward closed, which is exactly what `trans_i`
needs.  Below `‖χ‖` the two copies see each other and are
indistinguishable; on `‖χ‖` they split into an all-`p` branch (`inl`)
and a `p`-free branch (`inr`).  At `χ = ◯⊥` this manufactures the
`M♦` shape itself — an incomparable pair over the `◯⊥`-boundary with a
valuation no variable-free formula can define, since swapping the two
copies is a frame automorphism.

Two facts drive the proof, exactly as at `φ★`:

* `bstretch_transfer` — variable-free formulas cannot see the fork, on
  either copy (the cross edges are guarded, but both copies range over
  the same `C`-worlds);
* `bstretch_force_phiDia` — if `u ⊩ ¬¬◯⊥` in `C` then `inl u ⊩ φ♦` in
  `bstretch C ◯⊥`.  (α) holds because `p` is `◯⊥` on the `inl` copy and
  `⊥` on the `inr` copy; (β) holds because `¬¬◯⊥` delivers, above every
  non-`◯⊥` world of the cone, a non-fallible `◯⊥`-world `y`, whose two
  copies `inl y` (a non-fallible `p`-world) and `inr y` (a `◯⊥`-world
  without `p`) are the two witnesses (β) asks for.

## The general method

Forcing at the two copies is again computed by a mutually recursive
pair of variable-free translations `BLo χ` / `BUp χ` (§4), giving a new
lower-bound principle `bstretch_below` on the consequence filter
`F(φ)`, one per guard, and a master reduction `postInterp_of_branch`.
`φ♦` has a branch cover (`hasBranchCover_phiDia`) and no guarded mixed
cover, so the branching method is strictly stronger than the whole
guarded 2-layer family (`branch_beats_guardedMixed`).  Like the
stretch, the branching method alone is incomplete — `BLo ◯⊥ p = ◯⊥`
and `p ⊬ ◯⊥` (`branchCoverConj_false`) — so the live successor
conjecture is the JOIN of branching, guarded stretching and
substitution (`BranchMixedConj`).

No sorries.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## 1.  The branching (forked) stretch -/

/-- The intuitionistic relation of `bstretch C χ`.  Same-copy edges are
the edges of `C`; the CROSS edges are guarded by `x ⊮ χ`, so the two
copies separate exactly on the region `‖χ‖`. -/
def bRi (C : ConstraintModel) (χ : PLLFormula) :
    C.W ⊕ C.W → C.W ⊕ C.W → Prop
  | .inl x, .inl y => C.Ri x y
  | .inl x, .inr y => C.Ri x y ∧ ¬ C.force x χ
  | .inr x, .inl y => C.Ri x y ∧ ¬ C.force x χ
  | .inr x, .inr y => C.Ri x y

/-- The valuation of `bstretch C χ`: `‖χ‖` on the `inl` copy, the
fallible worlds on the `inr` copy.  So `p` holds throughout the guard
region of the first branch and nowhere but fallibly on the second. -/
def bV (C : ConstraintModel) (χ : PLLFormula) : Set (C.W ⊕ C.W) :=
  fun q => match q with
    | .inl x => C.force x χ
    | .inr x => x ∈ C.F

/-- The complement of a truth set is downward closed. -/
theorem not_force_of_Ri {C : ConstraintModel} {χ : PLLFormula} {x y : C.W}
    (h : C.Ri x y) (hy : ¬ C.force y χ) : ¬ C.force x χ :=
  fun hx => hy (C.force_hered h hx)

/-- **The `χ`-guarded BRANCHING stretch of `C`**: two copies of `C`,
glued below `‖χ‖` and forked on it, the first carrying `p`. -/
@[reducible] def bstretch (C : ConstraintModel) (χ : PLLFormula) : ConstraintModel where
  W := C.W ⊕ C.W
  Ri := bRi C χ
  Rm := stRm C
  F := stF C
  V _ := bV C χ
  refl_i := by rintro (x | x) <;> exact C.refl_i x
  trans_i := by
    rintro (x | x) (y | y) (z | z) h1 h2
    · exact C.trans_i h1 h2
    · exact ⟨C.trans_i h1 h2.1, not_force_of_Ri h1 h2.2⟩
    · exact C.trans_i h1.1 h2.1
    · exact ⟨C.trans_i h1.1 h2, h1.2⟩
    · exact ⟨C.trans_i h1.1 h2, h1.2⟩
    · exact C.trans_i h1.1 h2.1
    · exact ⟨C.trans_i h1 h2.1, not_force_of_Ri h1 h2.2⟩
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
    · exact C.hered_F h.1 hx
    · exact C.hered_F h hx
  hered_V := by
    rintro a (x | x) (y | y) h hx
    · exact C.force_hered h hx
    · exact absurd hx h.2
    · exact C.force_of_fallible (C.hered_F h.1 hx)
    · exact C.hered_F h hx
  full_F := by
    rintro a (x | x) hx
    · exact C.force_of_fallible hx
    · exact hx

/-! ## 2.  Variable-free formulas cannot see the fork -/

/-- **Transfer, any guard.**  On BOTH copies a variable-free formula is
forced at a copy of `x` exactly when it is forced at `x`.  (The `⊃` and
`◯` clauses quantify over the other copy too, but both copies range over
the same `C`-worlds above `x`.) -/
theorem bstretch_transfer {C : ConstraintModel} {χ : PLLFormula} :
    ∀ {A : PLLFormula}, atomFree A = true → ∀ x : C.W,
      ((bstretch C χ).force (.inl x) A ↔ C.force x A) ∧
      ((bstretch C χ).force (.inr x) A ↔ C.force x A) := by
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
      · show (∀ q : C.W ⊕ C.W, bRi C χ (.inl x) q →
              (bstretch C χ).force q A → (bstretch C χ).force q B) ↔
             (∀ v : C.W, C.Ri x v → C.force v A → C.force v B)
        constructor
        · intro hh v hv hA
          exact (ihB h'.2 v).1.mp (hh (.inl v) hv ((ihA h'.1 v).1.mpr hA))
        · rintro hh (y | y) hq hA
          · exact (ihB h'.2 y).1.mpr (hh y hq ((ihA h'.1 y).1.mp hA))
          · exact (ihB h'.2 y).2.mpr (hh y hq.1 ((ihA h'.1 y).2.mp hA))
      · show (∀ q : C.W ⊕ C.W, bRi C χ (.inr x) q →
              (bstretch C χ).force q A → (bstretch C χ).force q B) ↔
             (∀ v : C.W, C.Ri x v → C.force v A → C.force v B)
        constructor
        · intro hh v hv hA
          exact (ihB h'.2 v).2.mp (hh (.inr v) hv ((ihA h'.1 v).2.mpr hA))
        · rintro hh (y | y) hq hA
          · exact (ihB h'.2 y).1.mpr (hh y hq.1 ((ihA h'.1 y).1.mp hA))
          · exact (ihB h'.2 y).2.mpr (hh y hq ((ihA h'.1 y).2.mp hA))
  | somehow A ih =>
      intro h x
      constructor
      · show (∀ q : C.W ⊕ C.W, bRi C χ (.inl x) q →
              ∃ r, stRm C q r ∧ (bstretch C χ).force r A) ↔
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
      · show (∀ q : C.W ⊕ C.W, bRi C χ (.inr x) q →
              ∃ r, stRm C q r ∧ (bstretch C χ).force r A) ↔
             (∀ v : C.W, C.Ri x v → ∃ u, C.Rm v u ∧ C.force u A)
        constructor
        · intro hh v hv
          obtain ⟨r, hr, hfr⟩ := hh (.inr v) hv
          match r, hr, hfr with
          | .inl r₁, hr, _ => exact hr.elim
          | .inr r₁, hr, hfr => exact ⟨r₁, hr, (ih h r₁).2.mp hfr⟩
        · rintro hh (y | y) hq
          · obtain ⟨u, hu, hfu⟩ := hh y hq.1
            exact ⟨.inl u, hu, (ih h u).1.mpr hfu⟩
          · obtain ⟨u, hu, hfu⟩ := hh y hq
            exact ⟨.inr u, hu, (ih h u).2.mpr hfu⟩

/-- On the first copy, `p` means `χ`. -/
theorem bstretch_p_inl {C : ConstraintModel} {χ : PLLFormula} (x : C.W) :
    (bstretch C χ).force (.inl x) (PLLFormula.prop pv) ↔ C.force x χ := Iff.rfl

/-- On the second copy, `p` means "fallible". -/
theorem bstretch_p_inr {C : ConstraintModel} {χ : PLLFormula} (x : C.W) :
    (bstretch C χ).force (.inr x) (PLLFormula.prop pv) ↔
      C.force x PLLFormula.falsePLL := Iff.rfl

/-! ## 3.  `φ♦` at the forked world -/

/-- The content of `¬¬◯⊥`, unpacked: above every non-`◯⊥` world of the
cone there is a NON-FALLIBLE `◯⊥`-world. -/
theorem oBot_witness {C : ConstraintModel} {u : C.W}
    (hu : C.force u (nt (nt oBot))) {x : C.W} (hx : C.Ri u x)
    (hnx : ¬ C.force x oBot) :
    ∃ y, C.Ri x y ∧ C.force y oBot ∧ ¬ C.force y PLLFormula.falsePLL := by
  classical
  by_contra hc
  refine hnx (C.force_of_fallible (hu x hx (fun y hy hyb => ?_)))
  by_contra hyF
  exact hc ⟨y, hy, hyb, hyF⟩

/-- **The heart of the matter.**  If `u ⊩ ¬¬◯⊥` in `C`, then `φ♦` holds
at the first copy of `u` in the `◯⊥`-guarded branching stretch.

At a `◯⊥`-world the consequent holds outright: on the `inl` copy `p` IS
`◯⊥`, on the `inr` copy `p` is `⊥` so `¬p` holds.  At a non-`◯⊥` world
`v` the antecedent fails: `oBot_witness` supplies a non-fallible
`◯⊥`-world `y` above it, and since `v` is outside the guard region BOTH
copies of `y` are above `v` — `inr y` refutes `◯⊥ ⊃ p`, `inl y` refutes
`¬p`. -/
theorem bstretch_force_phiDia {C : ConstraintModel} {u : C.W}
    (hu : C.force u (nt (nt oBot))) :
    (bstretch C oBot).force (.inl u) phiDia := by
  classical
  rintro (x | x) hq hante
  · -- the first copy
    by_cases hbx : C.force x oBot
    · exact Or.inl ⟨(bstretch_transfer atomFree_oBot x).1.mpr hbx, hbx⟩
    · exfalso
      obtain ⟨y, hy, hyb, hyF⟩ := oBot_witness hu hq hbx
      rcases hante with h1 | h2 | h3
      · exact hyF (h1 (.inr y) ⟨hy, hbx⟩
          ((bstretch_transfer atomFree_oBot y).2.mpr hyb))
      · exact hbx ((bstretch_transfer atomFree_oBot x).1.mp h2)
      · exact hyF (h3 (.inl y) hy hyb)
  · -- the second copy
    by_cases hbx : C.force x oBot
    · refine Or.inr ⟨(bstretch_transfer atomFree_oBot x).2.mpr hbx, ?_⟩
      rintro (z | z) hz hp
      · exact absurd hbx hz.2
      · exact hp
    · exfalso
      obtain ⟨y, hy, hyb, hyF⟩ := oBot_witness hu hq.1 hbx
      rcases hante with h1 | h2 | h3
      · exact hyF (h1 (.inr y) hy
          ((bstretch_transfer atomFree_oBot y).2.mpr hyb))
      · exact hbx ((bstretch_transfer atomFree_oBot x).2.mp h2)
      · exact hyF (h3 (.inl y) ⟨hy, hbx⟩ hyb)

/-! ## 4.  Minimality, and the theorem -/

/-- **Minimality.**  Every variable-free consequence of `φ♦` is a
consequence of `¬¬◯⊥`. -/
theorem phiDia_minimal {χ : PLLFormula} (hχ : atomFree χ = true)
    (h : Deriv [phiDia] χ) : Deriv [nt (nt oBot)] χ := by
  classical
  by_contra hcon
  obtain ⟨C, -, u, hu, hnu⟩ := countermodel_of_not_deriv hcon
  obtain ⟨d⟩ := h
  refine hnu ((bstretch_transfer hχ u).1.mp (soundness d (bstretch C oBot) (.inl u) ?_))
  intro ψ hψ
  have e : ψ = phiDia := by
    cases hψ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact bstretch_force_phiDia hu

/-- **PROVED: `∃p.φ♦ = ¬¬◯⊥`.**  The formula that refutes the mixed
method AND the whole guarded-stretch family (`guardedMixedConj_false`)
nonetheless HAS a uniform post-interpolant over the variable-free
fragment, and it is `¬¬◯⊥` — the same value as at `φ★`. -/
theorem postInterp_phiDia : IsPostInterp phiDia (nt (nt oBot)) :=
  ⟨rfl, phiDia_nnbox, fun _ hχ hd => phiDia_minimal hχ hd⟩

/-- The question `mixedfail.lean` left open, settled affirmatively. -/
theorem postInterpPhiDiaExists_true : PostInterpPhiDiaExists :=
  ⟨_, postInterp_phiDia⟩

/-- **The verdict on route (B): UI does NOT fail at `φ♦`.** -/
theorem not_no_post_interp_phiDia : ¬ ¬ ∃ ψ, IsPostInterp phiDia ψ :=
  fun h => h postInterpPhiDiaExists_true

/-- The interpolant is strictly between `◯⊥` and `⊤`: it is not `⊤`
(`postInterpPhiDiaIsTop_false`) and not `⊥`. -/
theorem postInterp_phiDia_ne_bot : ¬ Deriv [nt (nt oBot)] PLLFormula.falsePLL :=
  postInterp_phiStar_ne_bot

theorem postInterp_phiDia_ne_top : ¬ Deriv [] (nt (nt oBot)) :=
  postInterp_phiStar_ne_top

/-! ## 5.  The general method: the BRANCHING TRANSLATION

Forcing at the two copies of `bstretch C χ` is computed by a mutually
recursive pair of variable-free translations.  The guard enters as a
DISJUNCT, not as an implication: the cross edges out of `x` exist only
when `x ⊮ χ`, so a cross-quantified clause `P` contributes
`x ⊩ χ ∨ P` (Kripke disjunction is local, so this is forcing of
`χ ∨ …`).  Note the perfect symmetry between the two components — the
fork's frame is symmetric, only the valuation breaks it:

    BLo p      = χ                     BUp p      = ⊥
    BLo ⊥      = ⊥                     BUp ⊥      = ⊥
    BLo (A∧B)  = BLo A ∧ BLo B         BUp (A∧B)  = BUp A ∧ BUp B
    BLo (A∨B)  = BLo A ∨ BLo B         BUp (A∨B)  = BUp A ∨ BUp B
    BLo (A⊃B)  = (BLo A ⊃ BLo B)       BUp (A⊃B)  = (BUp A ⊃ BUp B)
                 ∧ (χ ∨ (BUp A ⊃ BUp B))            ∧ (χ ∨ (BLo A ⊃ BLo B))
    BLo ◯A     = ◯(BLo A) ∧ (χ ∨ ◯(BUp A))
    BUp ◯A     = ◯(BUp A) ∧ (χ ∨ ◯(BLo A))
-/

/-- The pair of translations of the `χ`-guarded branching stretch. -/
def trB (χ : PLLFormula) : PLLFormula → PLLFormula × PLLFormula
  | .prop _ => (χ, PLLFormula.falsePLL)
  | .falsePLL => (PLLFormula.falsePLL, PLLFormula.falsePLL)
  | .and A B => ((trB χ A).1.and (trB χ B).1, (trB χ A).2.and (trB χ B).2)
  | .or A B => ((trB χ A).1.or (trB χ B).1, (trB χ A).2.or (trB χ B).2)
  | .ifThen A B =>
      (((trB χ A).1.ifThen (trB χ B).1).and (χ.or ((trB χ A).2.ifThen (trB χ B).2)),
        ((trB χ A).2.ifThen (trB χ B).2).and (χ.or ((trB χ A).1.ifThen (trB χ B).1)))
  | .somehow A =>
      (((trB χ A).1.somehow).and (χ.or ((trB χ A).2.somehow)),
        ((trB χ A).2.somehow).and (χ.or ((trB χ A).1.somehow)))

/-- The FIRST-copy translation. -/
def BLo (χ A : PLLFormula) : PLLFormula := (trB χ A).1

/-- The SECOND-copy translation. -/
def BUp (χ A : PLLFormula) : PLLFormula := (trB χ A).2

theorem BLo_prop (χ : PLLFormula) (a : String) : BLo χ (PLLFormula.prop a) = χ := rfl
theorem BUp_prop (χ : PLLFormula) (a : String) :
    BUp χ (PLLFormula.prop a) = PLLFormula.falsePLL := rfl
theorem BLo_imp (χ A B : PLLFormula) :
    BLo χ (A.ifThen B)
      = ((BLo χ A).ifThen (BLo χ B)).and (χ.or ((BUp χ A).ifThen (BUp χ B))) := rfl
theorem BUp_imp (χ A B : PLLFormula) :
    BUp χ (A.ifThen B)
      = ((BUp χ A).ifThen (BUp χ B)).and (χ.or ((BLo χ A).ifThen (BLo χ B))) := rfl
theorem BLo_box (χ A : PLLFormula) :
    BLo χ A.somehow = ((BLo χ A).somehow).and (χ.or ((BUp χ A).somehow)) := rfl
theorem BUp_box (χ A : PLLFormula) :
    BUp χ A.somehow = ((BUp χ A).somehow).and (χ.or ((BLo χ A).somehow)) := rfl

/-- **Both translations are variable-free, provided the guard is.** -/
theorem atomFree_trB {χ : PLLFormula} (hχ : atomFree χ = true) : ∀ A : PLLFormula,
    atomFree (BLo χ A) = true ∧ atomFree (BUp χ A) = true := by
  intro A
  induction A with
  | prop a => exact ⟨hχ, rfl⟩
  | falsePLL => exact ⟨rfl, rfl⟩
  | and A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show (atomFree (BLo χ A) && atomFree (BLo χ B)) = true
        rw [ihA.1, ihB.1]; rfl
      · show (atomFree (BUp χ A) && atomFree (BUp χ B)) = true
        rw [ihA.2, ihB.2]; rfl
  | or A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show (atomFree (BLo χ A) && atomFree (BLo χ B)) = true
        rw [ihA.1, ihB.1]; rfl
      · show (atomFree (BUp χ A) && atomFree (BUp χ B)) = true
        rw [ihA.2, ihB.2]; rfl
  | ifThen A B ihA ihB =>
      refine ⟨?_, ?_⟩
      · show ((atomFree (BLo χ A) && atomFree (BLo χ B)) &&
              (atomFree χ && (atomFree (BUp χ A) && atomFree (BUp χ B)))) = true
        rw [ihA.1, ihB.1, ihA.2, ihB.2, hχ]; rfl
      · show ((atomFree (BUp χ A) && atomFree (BUp χ B)) &&
              (atomFree χ && (atomFree (BLo χ A) && atomFree (BLo χ B)))) = true
        rw [ihA.1, ihB.1, ihA.2, ihB.2, hχ]; rfl
  | somehow A ihA =>
      refine ⟨?_, ?_⟩
      · show (atomFree (BLo χ A) && (atomFree χ && atomFree (BUp χ A))) = true
        rw [ihA.1, ihA.2, hχ]; rfl
      · show (atomFree (BUp χ A) && (atomFree χ && atomFree (BLo χ A))) = true
        rw [ihA.1, ihA.2, hχ]; rfl

theorem atomFree_BLo {χ : PLLFormula} (hχ : atomFree χ = true) (A : PLLFormula) :
    atomFree (BLo χ A) = true := (atomFree_trB hχ A).1

theorem atomFree_BUp {χ : PLLFormula} (hχ : atomFree χ = true) (A : PLLFormula) :
    atomFree (BUp χ A) = true := (atomFree_trB hχ A).2

/-- **The branching translation theorem.**  Forcing at either copy of
`x` in `bstretch C χ` is forcing of the corresponding translation at
`x`.  (Every atom is treated like `p`.) -/
theorem bstretch_tr {C : ConstraintModel} {χ : PLLFormula} :
    ∀ (A : PLLFormula) (x : C.W),
      ((bstretch C χ).force (.inl x) A ↔ C.force x (BLo χ A)) ∧
      ((bstretch C χ).force (.inr x) A ↔ C.force x (BUp χ A)) := by
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
                (bstretch C χ).force q A → (bstretch C χ).force q B) ↔
             (C.force x ((BLo χ A).ifThen (BLo χ B)) ∧
              (C.force x χ ∨ C.force x ((BUp χ A).ifThen (BUp χ B))))
        constructor
        · intro hh
          refine ⟨fun y hy hA => (ihB y).1.mp (hh (.inl y) hy ((ihA y).1.mpr hA)), ?_⟩
          by_cases hx : C.force x χ
          · exact Or.inl hx
          · exact Or.inr (fun y hy hA =>
              (ihB y).2.mp (hh (.inr y) ⟨hy, hx⟩ ((ihA y).2.mpr hA)))
        · rintro ⟨h1, h2⟩ (y | y) hq hA
          · exact (ihB y).1.mpr (h1 y hq ((ihA y).1.mp hA))
          · rcases h2 with hx | h2'
            · exact absurd hx hq.2
            · exact (ihB y).2.mpr (h2' y hq.1 ((ihA y).2.mp hA))
      · show (∀ q : C.W ⊕ C.W, bRi C χ (.inr x) q →
                (bstretch C χ).force q A → (bstretch C χ).force q B) ↔
             (C.force x ((BUp χ A).ifThen (BUp χ B)) ∧
              (C.force x χ ∨ C.force x ((BLo χ A).ifThen (BLo χ B))))
        constructor
        · intro hh
          refine ⟨fun y hy hA => (ihB y).2.mp (hh (.inr y) hy ((ihA y).2.mpr hA)), ?_⟩
          by_cases hx : C.force x χ
          · exact Or.inl hx
          · exact Or.inr (fun y hy hA =>
              (ihB y).1.mp (hh (.inl y) ⟨hy, hx⟩ ((ihA y).1.mpr hA)))
        · rintro ⟨h1, h2⟩ (y | y) hq hA
          · rcases h2 with hx | h2'
            · exact absurd hx hq.2
            · exact (ihB y).1.mpr (h2' y hq.1 ((ihA y).1.mp hA))
          · exact (ihB y).2.mpr (h1 y hq ((ihA y).2.mp hA))
  | somehow A ih =>
      intro x
      constructor
      · show (∀ q : C.W ⊕ C.W, bRi C χ (.inl x) q →
                ∃ r, stRm C q r ∧ (bstretch C χ).force r A) ↔
             (C.force x ((BLo χ A).somehow) ∧
              (C.force x χ ∨ C.force x ((BUp χ A).somehow)))
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
        · rintro ⟨h1, h2⟩ (y | y) hq
          · obtain ⟨u, hu, hfu⟩ := h1 y hq
            exact ⟨.inl u, hu, (ih u).1.mpr hfu⟩
          · rcases h2 with hx | h2'
            · exact absurd hx hq.2
            · obtain ⟨u, hu, hfu⟩ := h2' y hq.1
              exact ⟨.inr u, hu, (ih u).2.mpr hfu⟩
      · show (∀ q : C.W ⊕ C.W, bRi C χ (.inr x) q →
                ∃ r, stRm C q r ∧ (bstretch C χ).force r A) ↔
             (C.force x ((BUp χ A).somehow) ∧
              (C.force x χ ∨ C.force x ((BLo χ A).somehow)))
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
        · rintro ⟨h1, h2⟩ (y | y) hq
          · rcases h2 with hx | h2'
            · exact absurd hx hq.2
            · obtain ⟨u, hu, hfu⟩ := h2' y hq.1
              exact ⟨.inl u, hu, (ih u).1.mpr hfu⟩
          · obtain ⟨u, hu, hfu⟩ := h1 y hq
            exact ⟨.inr u, hu, (ih u).2.mpr hfu⟩

/-! ## 6.  The branching lower bounds, and the method -/

/-- **THE BRANCHING LOWER BOUND, first copy.**  For EVERY guard `χ`,
`BLo χ φ` lies below every variable-free consequence of `φ` — a new
non-substitutional family of lower bounds on `F(φ)`, none of them a
guarded stretch bound. -/
theorem bstretch_below {χ φ ψ : PLLFormula} (hψ : atomFree ψ = true)
    (h : Deriv [φ] ψ) : Deriv [BLo χ φ] ψ := by
  classical
  by_contra hcon
  obtain ⟨C, -, u, hu, hnu⟩ := countermodel_of_not_deriv hcon
  obtain ⟨d⟩ := h
  refine hnu ((bstretch_transfer hψ u).1.mp (soundness d (bstretch C χ) (.inl u) ?_))
  intro ρ hρ
  have e : ρ = φ := by
    cases hρ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact (bstretch_tr _ u).1.mpr hu

/-- **… and the second copy.** -/
theorem bstretch_below_up {χ φ ψ : PLLFormula} (hψ : atomFree ψ = true)
    (h : Deriv [φ] ψ) : Deriv [BUp χ φ] ψ := by
  classical
  by_contra hcon
  obtain ⟨C, -, u, hu, hnu⟩ := countermodel_of_not_deriv hcon
  obtain ⟨d⟩ := h
  refine hnu ((bstretch_transfer hψ u).2.mp (soundness d (bstretch C χ) (.inr u) ?_))
  intro ρ hρ
  have e : ρ = φ := by
    cases hρ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact (bstretch_tr _ u).2.mpr hu

/-- **`φ` has a `χ`-guarded branch cover.** -/
def HasBranchCover (χ φ : PLLFormula) : Prop := Deriv [φ] (BLo χ φ)

/-- **MASTER REDUCTION for the branching method.** -/
theorem postInterp_of_branch {χ φ : PLLFormula} (hχ : atomFree χ = true)
    (h : HasBranchCover χ φ) : IsPostInterp φ (BLo χ φ) :=
  ⟨atomFree_BLo hχ φ, h, fun _ hψ hd => bstretch_below hψ hd⟩

/-! ## 7.  `φ♦` has a branch cover: the method strictly extends the
guarded stretch family -/

/-- `¬¬◯⊥ ⊢ BLo ◯⊥ φ♦` — read off `bstretch_force_phiDia` through the
translation theorem. -/
theorem nnbox_to_BLo_phiDia : Deriv [nt (nt oBot)] (BLo oBot phiDia) :=
  deriv_of_valid (fun _ u hu => (bstretch_tr phiDia u).1.mp (bstretch_force_phiDia hu))

/-- **`φ♦` HAS a branch cover** — while it has no guarded mixed cover at
all (`phiDia_no_guardedMixedCover`). -/
theorem hasBranchCover_phiDia : HasBranchCover oBot phiDia :=
  Deriv.cutHead phiDia_nnbox nnbox_to_BLo_phiDia

/-- `BLo ◯⊥ φ♦ ⊣⊢ ¬¬◯⊥`: the branching translation computes the
interpolant. -/
theorem interd_BLo_phiDia : Interd (BLo oBot phiDia) (nt (nt oBot)) :=
  ⟨bstretch_below rfl phiDia_nnbox, nnbox_to_BLo_phiDia⟩

/-- **The branching method is STRICTLY stronger than the whole guarded
two-layer family joined with substitution**: `φ♦` has a branch cover and
no guarded mixed cover. -/
theorem branch_beats_guardedMixed :
    ∃ φ : PLLFormula, onlyPv φ = true ∧ HasBranchCover oBot φ ∧
      ¬ HasGuardedMixedCover φ :=
  ⟨phiDia, phiDia_onlyPv, hasBranchCover_phiDia, phiDia_no_guardedMixedCover⟩

/-! ## 8.  The branching method alone is incomplete: the successor
conjecture is the JOIN -/

theorem BLo_pv : BLo oBot (PLLFormula.prop pv) = oBot := rfl

/-- **REFUTED**: the branching method ALONE is incomplete, exactly as
the stretch method is — `BLo ◯⊥ p = ◯⊥` and `p ⊬ ◯⊥`. -/
theorem p_not_oBot : ¬ Deriv [PLLFormula.prop pv] oBot := by
  rintro ⟨d⟩
  have hs := soundness d N (1 : Fin 2) (fun ψ hψ => by
    have e : ψ = PLLFormula.prop pv := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact (le_refl (1 : Fin 2)))
  exact N_not_oBot 1 hs

def BranchCoverConj : Prop :=
  ∀ φ : PLLFormula, onlyPv φ = true → HasBranchCover oBot φ

theorem branchCoverConj_false : ¬ BranchCoverConj :=
  fun h => p_not_oBot (h (PLLFormula.prop pv) rfl)

/-- The list of branch lower bounds of `φ` at the guards in `G`. -/
def bloList (G : List PLLFormula) (φ : PLLFormula) : List PLLFormula :=
  G.map (fun χ => BLo χ φ)

theorem mem_bloList {G : List PLLFormula} {φ ψ : PLLFormula}
    (h : ψ ∈ bloList G φ) : ∃ χ ∈ G, ψ = BLo χ φ := by
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp h
  exact ⟨χ, hχ, rfl⟩

/-- **`φ` has a branch-mixed cover**: finitely many guarded STRETCH
bounds, finitely many guarded BRANCH bounds and finitely many
variable-free substitution instances jointly exhaust `φ`. -/
def HasBranchMixedCover (φ : PLLFormula) : Prop :=
  ∃ G B S : List PLLFormula, (∀ χ ∈ G, atomFree χ = true) ∧
    (∀ χ ∈ B, atomFree χ = true) ∧ (∀ θ ∈ S, atomFree θ = true) ∧
    Deriv [φ] (bigOr (loList G φ ++ bloList B φ ++ instList S φ))

/-- **MASTER REDUCTION for the branch-mixed method.** -/
theorem postInterp_of_branchMixed {φ : PLLFormula} (hφ : onlyPv φ = true)
    {G B S : List PLLFormula} (hG : ∀ χ ∈ G, atomFree χ = true)
    (hB : ∀ χ ∈ B, atomFree χ = true) (hS : ∀ θ ∈ S, atomFree θ = true)
    (hcov : Deriv [φ] (bigOr (loList G φ ++ bloList B φ ++ instList S φ))) :
    IsPostInterp φ (bigOr (loList G φ ++ bloList B φ ++ instList S φ)) := by
  refine ⟨atomFree_bigOr ?_, hcov, ?_⟩
  · intro ψ hψ
    rcases List.mem_append.mp hψ with h | h
    · rcases List.mem_append.mp h with h' | h'
      · obtain ⟨χ, hχ, rfl⟩ := mem_loList h'
        exact atomFree_LoG (hG χ hχ) φ
      · obtain ⟨χ, hχ, rfl⟩ := mem_bloList h'
        exact atomFree_BLo (hB χ hχ) φ
    · exact atomFree_instList hS hφ ψ h
  · intro ψ hψ hd
    refine Deriv.bigOrElim (Deriv.iden (.head _)) ?_
    intro ρ hρ
    rcases List.mem_append.mp hρ with h | h
    · rcases List.mem_append.mp h with h' | h'
      · obtain ⟨χ, -, rfl⟩ := mem_loList h'
        exact Deriv.toHead (gstretch_below hψ hd)
      · obtain ⟨χ, -, rfl⟩ := mem_bloList h'
        exact Deriv.toHead (bstretch_below hψ hd)
    · obtain ⟨θ, -, rfl⟩ := mem_instList h
      exact Deriv.toHead (inst_below θ hψ hd)

/-- **OPEN.**  The successor of `GuardedMixedConj` after
`guardedMixedConj_false`: every one-variable formula has a branch-mixed
cover.  `φ★` (stretch), `p` (substitution) and `φ♦` (branch) are all
covered, each by a different member of the join. -/
def BranchMixedConj : Prop := ∀ φ : PLLFormula, onlyPv φ = true → HasBranchMixedCover φ

/-- **The reduction of last-variable `∃p` to the branch-mixed
conjecture.** -/
theorem postUI_of_branchMixedConj (h : BranchMixedConj) :
    ∀ φ : PLLFormula, onlyPv φ = true → ∃ ψ, IsPostInterp φ ψ := by
  intro φ hφ
  obtain ⟨G, B, S, hG, hB, hS, hcov⟩ := h φ hφ
  exact ⟨_, postInterp_of_branchMixed hφ hG hB hS hcov⟩

/-- A guarded mixed cover is a branch-mixed cover (empty branch list). -/
theorem hasBranchMixedCover_of_guardedMixed {φ : PLLFormula}
    (h : HasGuardedMixedCover φ) : HasBranchMixedCover φ := by
  obtain ⟨G, S, hG, hS, hd⟩ := h
  refine ⟨G, [], S, hG, ?_, hS, ?_⟩
  · intro χ hχ; exact absurd hχ (by simp)
  · have e : loList G φ ++ bloList [] φ ++ instList S φ
        = loList G φ ++ instList S φ := by
      show loList G φ ++ [] ++ instList S φ = _
      rw [List.append_nil]
    rw [e]
    exact hd

/-- `φ♦` has a branch-mixed cover, though no guarded mixed cover. -/
theorem hasBranchMixedCover_phiDia : HasBranchMixedCover phiDia := by
  refine ⟨[], [oBot], [], ?_, ?_, ?_, ?_⟩
  · intro χ hχ; exact absurd hχ (by simp)
  · intro χ hχ; rcases List.mem_singleton.mp hχ with rfl; rfl
  · intro θ hθ; exact absurd hθ (by simp)
  · show Deriv [phiDia] (bigOr ([] ++ [BLo oBot phiDia] ++ []))
    exact Deriv.orIntro1 hasBranchCover_phiDia

/-! ## 9.  The instance bound: both Boolean instances of `φ♦` are `◯⊥`

The substitution bounds available at `φ♦` are all `⊣⊢ ◯⊥` at the two
Boolean values, STRICTLY below the interpolant `¬¬◯⊥`
(`postInterp_phiStar_ne_bot` shows `¬¬◯⊥ ⊬ ⊥`; `phiDia_not_oBot` shows
`φ♦ ⊬ ◯⊥`, so `¬¬◯⊥ ⊬ ◯⊥` would follow from minimality — and indeed
`M4`'s root forces `¬¬◯⊥` and not `◯⊥`).  This is why the substitution
method has no chance at `φ♦` and why the value had to be produced by a
construction. -/

/-- The explicit shape of a variable-free instance of `φ♦`
(`inst_phiDia`). -/
def phiDiaInst (θ : PLLFormula) : PLLFormula :=
  ((oBot.ifThen θ).or (oBot.or (θ.ifThen .falsePLL))).ifThen
    ((oBot.and θ).or (oBot.and (θ.ifThen .falsePLL)))

/-- `⊤` is forced everywhere. -/
theorem force_truePLL {C : ConstraintModel} (v : C.W) : C.force v truePLL :=
  fun _ _ h => h

/-- **`φ♦[p := ⊤] ⊣⊢ ◯⊥`.** -/
theorem interd_instTop_phiDia : Interd (inst truePLL phiDia) oBot := by
  rw [inst_phiDia truePLL]
  constructor
  · exact deriv_of_valid (fun C v h => by
      rcases (h v (C.refl_i v) (Or.inl (fun u _ _ => force_truePLL u)) :
          C.force v ((oBot.and truePLL)) ∨ C.force v (oBot.and (truePLL.ifThen _)))
        with ⟨hb, -⟩ | ⟨hb, -⟩
      · exact hb
      · exact hb)
  · exact deriv_of_valid (fun C v h => by
      intro w hw _
      exact Or.inl ⟨C.force_hered hw h, force_truePLL w⟩)

/-- **`φ♦[p := ⊥] ⊣⊢ ◯⊥`.** -/
theorem interd_instBot_phiDia : Interd (inst PLLFormula.falsePLL phiDia) oBot := by
  rw [inst_phiDia PLLFormula.falsePLL]
  constructor
  · exact deriv_of_valid (fun C v h => by
      rcases (h v (C.refl_i v) (Or.inr (Or.inr (fun _ _ hz => hz))) :
          C.force v (oBot.and PLLFormula.falsePLL) ∨
            C.force v (oBot.and (PLLFormula.falsePLL.ifThen _)))
        with ⟨hb, -⟩ | ⟨hb, -⟩
      · exact hb
      · exact hb)
  · exact deriv_of_valid (fun C v h => by
      intro w hw _
      exact Or.inr ⟨C.force_hered hw h, fun _ _ hz => hz⟩)

/-- `¬¬◯⊥ ⊬ ◯⊥`: the interpolant is STRICTLY above every Boolean
instance.  (`M4`'s root forces `¬¬◯⊥`, being a `φ★`-world, and not
`◯⊥`.) -/
theorem nnbox_not_oBot : ¬ Deriv [nt (nt oBot)] oBot :=
  fun h => phiStar_not_oBot (Deriv.cutHead phiStar_nnbox h)

/-! ## 10.  The refutation tool for the successor conjecture

The semantic content of the branch bound is direct: `w ⊩ BLo χ φ` iff
`φ` is forced at the first copy of `w` in the `χ`-fork of the model
(`BLo_iff_fork`).  So a counterexample to `BranchMixedConj` is a
non-fallible `φ`-world `w` at which every variable-free instance fails,
`φ` fails at the ground copy of `w` in every guarded 2-layer stretch,
AND `φ` fails at the first copy of `w` in every guarded fork. -/

theorem BLo_iff_fork {C : ConstraintModel} {χ : PLLFormula} (φ : PLLFormula)
    (w : C.W) : C.force w (BLo χ φ) ↔ (bstretch C χ).force (.inl w) φ :=
  (bstretch_tr φ w).1.symm

/-- **THE REFUTATION TOOL for `BranchMixedConj`.** -/
theorem not_hasBranchMixedCover_of_model {φ : PLLFormula} (C : ConstraintModel)
    (w : C.W) (hw : C.force w φ) (hwF : ¬ C.force w PLLFormula.falsePLL)
    (hLo : ∀ χ : PLLFormula, atomFree χ = true → ¬ C.force w (LoG χ φ))
    (hBr : ∀ χ : PLLFormula, atomFree χ = true → ¬ C.force w (BLo χ φ))
    (hno : ∀ θ : PLLFormula, atomFree θ = true → ¬ C.force w (inst θ φ)) :
    ¬ HasBranchMixedCover φ := by
  rintro ⟨G, B, S, hG, hB, hS, hd⟩
  obtain ⟨d⟩ := hd
  have hforce : C.force w (bigOr (loList G φ ++ bloList B φ ++ instList S φ)) :=
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
      · obtain ⟨χ, hχ, rfl⟩ := mem_bloList h'
        exact hBr χ (hB χ hχ) hfA
    · obtain ⟨θ, hθ, rfl⟩ := mem_instList h
      exact hno θ (hS θ hθ) hfA
  · exact hwF hf

/-! ## 11.  The two non-substitutional methods are INCOMPARABLE

`φ♦` has a branch cover and no guarded stretch cover.  The converse
failure also happens, at `φ★`: the second copy of the fork carries `¬p`
on the whole guard region, so `¬¬p` — the second conjunct of `φ★` —
fails at the ground copy of any root below the region.  Hence neither
family subsumes the other and the join in `BranchMixedConj` genuinely
needs both. -/

/-- The root of `M3` forces `¬¬◯⊥`. -/
theorem M3_root_nnbox : M3.force (0 : Fin 3) (nt (nt oBot)) := by
  intro v _ hvn
  by_contra hcon
  have hv1 : v ≤ 1 := Fin3_ne_two v hcon
  have hbad : (1 : Fin 3) = 2 := hvn 1 hv1 (M3_oBot_of_one (le_refl (1 : Fin 3)))
  exact absurd hbad (by decide)

/-- In the `◯⊥`-fork of `M3` the SECOND copy of world `1` forces `¬p`
and is not fallible, so `¬¬p` fails at the first copy of the root. -/
theorem bstretch_M3_not_phiStar :
    ¬ (bstretch M3 oBot).force (Sum.inl (0 : Fin 3)) phiStar := by
  rintro ⟨-, h2⟩
  have hqn : (bstretch M3 oBot).force (Sum.inr (1 : Fin 3))
      (nt (PLLFormula.prop pv)) := by
    rintro (z | z) hz hp
    · exact absurd (M3_oBot_of_one (le_refl (1 : Fin 3))) hz.2
    · exact hp
  have hbad : (bstretch M3 oBot).force (Sum.inr (1 : Fin 3)) PLLFormula.falsePLL :=
    h2 (Sum.inr (1 : Fin 3))
      ⟨(by decide : (0 : Fin 3) ≤ 1), M3_not_oBot_zero⟩ hqn
  have hbad' : (1 : Fin 3) = 2 := hbad
  exact absurd hbad' (by decide)

/-- **`φ★` has NO branch cover** — while it has a stretch cover
(`hasStretchCover_phiStar`). -/
theorem not_hasBranchCover_phiStar : ¬ HasBranchCover oBot phiStar := by
  intro h
  have hI : Interd (BLo oBot phiStar) (nt (nt oBot)) :=
    postInterp_unique (postInterp_of_branch rfl h) postInterp_phiStar
  obtain ⟨d⟩ := hI.2
  have hs : M3.force (0 : Fin 3) (BLo oBot phiStar) :=
    soundness d M3 0 (fun ψ hψ => by
      have e : ψ = nt (nt oBot) := by
        cases hψ with
        | head => rfl
        | tail _ hh => cases hh
      subst e
      exact M3_root_nnbox)
  exact bstretch_M3_not_phiStar
    ((bstretch_tr (C := M3) (χ := oBot) phiStar (0 : Fin 3)).1.mpr hs)

/-- **INCOMPARABILITY.**  `φ★` separates the stretch method from the
branching method; `φ♦` separates the branching method from the whole
guarded stretch family joined with substitution. -/
theorem branch_stretch_incomparable :
    (HasGuardedCover oBot phiStar ∧ ¬ HasBranchCover oBot phiStar) ∧
      (HasBranchCover oBot phiDia ∧ ¬ HasGuardedMixedCover phiDia) :=
  ⟨⟨hasGuardedCover_phiStar, not_hasBranchCover_phiStar⟩,
   ⟨hasBranchCover_phiDia, phiDia_no_guardedMixedCover⟩⟩

/-- `φ★` still has a branch-mixed cover — via its stretch bound. -/
theorem hasBranchMixedCover_phiStar : HasBranchMixedCover phiStar :=
  hasBranchMixedCover_of_guardedMixed hasGuardedMixedCover_phiStar

/-! ## 12.  PROBE ADDENDUM: `BranchMixedConj` as stated is expected
FALSE, and the corrected family is the PARAMETERISED fork

`wip/branchprobe.lean` is `mixedprobe` with `BLo`/`BUp` coordinates
added (fork-frame cross-check per hit; mode `verify` validates the
compositional arithmetic against explicitly built fork frames — 0
mismatches over all 767 models with `n ≤ 4`, all guards, a battery
including `φ★` and `φ♦`).  Exhaustively at `n ≤ 4`, mode `guarded`:

    n ≤ 4 : 1274 (model, undefinable U) pairs, 4 cover-hit pairs,
            **0 BRANCH-MIXED HITS**

while `mixedprobe` on the same range reports 2 guarded-MIXED hits, both
`φ♦` in `M♦` (at the two symmetric valuations `{1,3}` and `{2,3}`).  So
the branch coordinate kills every `n ≤ 4` defeater of the guarded
two-layer family — machine-verified, and consistent with
`hasBranchCover_phiDia`.

At `n = 5` (partial run, 1500 s cap) the probe found a hit:

    C♣ :  W = {0,1,2,3,4},  0 ⊑ everything,  1 ⊑ 2,  3 and 4 maximal
          Rₘ = id ∪ {(1,2)},   F = {2},   V(p) = {1,2,3}
    D(C♣) = { {2}=⊥, {1,2}=◯⊥, {2,3,4}=¬◯⊥, {1,2,3,4}=¬¬◯⊥, all=⊤ }

    φ♣ = ((p ⊃ ◯⊥) ∨ (¬p ⊃ ◯⊥)) ⊃ (¬◯⊥ ∨ (◯⊥ ∧ p))

`φ♣` is valid in `C♣` under `‖p‖ = {1,2,3}` (undefinable: it separates
the two maximal non-`◯⊥` worlds `3`, `4`), invalid under every
`d ∈ D(C♣)`, and both `LoG χ φ♣` and `BLo χ φ♣` fail at the root for
every `χ ∈ D(C♣)` — re-checked by an independent from-scratch
implementation of the semantics, the stretch and the fork.  Fed to
`not_hasBranchMixedCover_of_model` this would refute `BranchMixedConj`.
(NOT yet pinned in Lean: it needs `C♣` as a `ConstraintModel` plus the
"every variable-free truth set is in `D(C♣)`" argument, which at `M♦`
was got cheaply from a frame automorphism and here is not.)

**The diagnosis, and the repair.**  `bstretch C χ` hard-codes the two
copy valuations as `‖χ‖` and `‖⊥‖`.  That is the member `φ♦` needs, and
it is NOT the general fork.  The general family keeps the frame and
frees the valuations:

    fork C χ δ₁ δ₂ :  same frame as `bstretch C χ`
                      V(a) = ‖δ₁‖ on the inl copy, ‖δ₂‖ on the inr copy,
                      for any variable-free δ₁, δ₂ with δᵢ ⊢ χ

(`δᵢ ⊢ χ` is exactly what `hered_V` needs on the cross edges, and
`full_F` is free since `⊥ ⊢ δᵢ`).  `bstretch C χ = fork C χ χ ⊥`, and
the translations generalise by `BLo p = δ₁`, `BUp p = δ₂`, the guard
clauses unchanged.  Exhaustively over `D(C♣)`, `φ♣` IS forced at the
ground copy of the root of `fork C♣ χ δ₁ δ₂` — at `χ = ¬¬◯⊥` with
`{δ₁, δ₂} = {◯⊥, ¬¬◯⊥}` (and at `k = 3, 4` copies in 6 resp. 14 further
ways).  So `φ♣` is a defeater of the `(χ, ⊥)` member only, not of
branching as such, and the corrected successor conjecture is the join of
substitution, guarded stretching and the PARAMETERISED fork.  Whether
that has a defeater in turn — and whether `k`-copy forks form a strict
hierarchy in `k` — is the live question. -/

/-! ## 13.  Axiom audit -/

/-- info: 'PLLND.RNEmbed.bstretch_transfer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bstretch_transfer

/-- info: 'PLLND.RNEmbed.oBot_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oBot_witness

/-- info: 'PLLND.RNEmbed.bstretch_force_phiDia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bstretch_force_phiDia

/-- info: 'PLLND.RNEmbed.phiDia_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiDia_minimal

/-- info: 'PLLND.RNEmbed.postInterp_phiDia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_phiDia

/-- info: 'PLLND.RNEmbed.postInterpPhiDiaExists_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterpPhiDiaExists_true

/-- info: 'PLLND.RNEmbed.bstretch_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bstretch_tr

/-- info: 'PLLND.RNEmbed.bstretch_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bstretch_below

/-- info: 'PLLND.RNEmbed.postInterp_of_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_branch

/-- info: 'PLLND.RNEmbed.hasBranchCover_phiDia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasBranchCover_phiDia

/-- info: 'PLLND.RNEmbed.branch_beats_guardedMixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms branch_beats_guardedMixed

/-- info: 'PLLND.RNEmbed.branchCoverConj_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms branchCoverConj_false

/-- info: 'PLLND.RNEmbed.postUI_of_branchMixedConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postUI_of_branchMixedConj

/-- info: 'PLLND.RNEmbed.interd_instTop_phiDia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interd_instTop_phiDia

/-- info: 'PLLND.RNEmbed.interd_instBot_phiDia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interd_instBot_phiDia

/-- info: 'PLLND.RNEmbed.nnbox_not_oBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nnbox_not_oBot

/-- info: 'PLLND.RNEmbed.BLo_iff_fork' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BLo_iff_fork

/-- info: 'PLLND.RNEmbed.not_hasBranchMixedCover_of_model' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_hasBranchMixedCover_of_model

/-- info: 'PLLND.RNEmbed.bstretch_M3_not_phiStar' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bstretch_M3_not_phiStar

/-- info: 'PLLND.RNEmbed.not_hasBranchCover_phiStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_hasBranchCover_phiStar

/-- info: 'PLLND.RNEmbed.branch_stretch_incomparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms branch_stretch_incomparable

end RNEmbed
end PLLND
