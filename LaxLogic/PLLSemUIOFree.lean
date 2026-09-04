import LaxLogic.PLLSemUI

/-!
# The ◯-free fragment under the semantic quantifiers: agreement with IPC

For a ◯-free formula `M` in the single variable `p` (the
Rieger–Nishimura fragment RN({p})), Pitts's IPC quantifiers take
CLOSED ◯-free values — for one variable that means `⊤` (when `⊢ M`)
or `⊥` (when `⊬ M`).  Over PLL the closed p-free formulas form the
infinite ladder RN(◯,{}), so a priori a ◯-free row could acquire a
ladder value (`◯⊥`, `¬¬◯⊥`, …) — the quantifier would ESCAPE the
fragment at the ground floor, and the variable-by-variable climb
through the free variables of a general formula would leave every
fragment it enters.

This file PROVES the necessity half of agreement: the value of an
underivable ◯-free row is excluded from BOTH derivability cones over
the ladder's two atoms.

* `topExt C` — the fallible-top extension: one fallible world
  adjoined above everything, constraint-reachable from everywhere.
  `topExt_force_iff`: forcing of ◯-FREE formulas at original worlds
  is unchanged (the top forces everything, so it never constrains an
  implication); `topExt_boxBot`: `◯⊥` becomes GLOBAL.  Hence a
  ◯-free M refuted anywhere is refuted at a ◯⊥-world:
  **no lower bound of M lies in the ◯⊥-cone**
  (`no_lower_bound_above_boxBot`).
* `flat_neg_boxBot`: in a fallibility-free model `¬◯⊥` is global.
  Hence a ◯-free M refuted over such a model (e.g. any IPC
  countermodel, read as a PLL model with `F = ∅`) has
  **no lower bound in the ¬◯⊥-cone**
  (`no_lower_bound_above_negBoxBot` — this half needs no
  ◯-freeness).

Consequently (`semAll_value_bot_of_cones`): a ∀p-value of such an M
that lies in either cone — or is `⊥` — must be `⊥`.  Every closed
ladder rung tested so far lies in one of the two cones
(oracle-checked; the coverage of RN(◯,{}) ∖ {⊥} by the two cones is
the remaining OPEN step to the unconditional statement), so closed
values of underivable ◯-free rows collapse to `⊥` — exactly Pitts's
value, evidence that the semantic route can climb the free variables
without leaving the fragment tower.  The dual ∃-side exclusions
(`semEx_value_not_derives_negBoxBot`, `semEx_value_not_derives_boxBot`)
pin the ∃p-value of a consistent ◯-free row away from both coatoms'
cones dually.

The EXISTENCE half is PROVED as well (final sections): **the ◯-free
one-variable fragment has definable semantic quantifiers with values
in {⊤, ⊥} — Pitts's values, unconditionally**
(`ofree_semAll_definable`, `ofree_semEx_definable`).  Two model
operations do it, both semantic forms of conservativity:

* `flatten C` — restrict to the non-fallible worlds.  For ◯-free
  formulas nothing changes at a non-fallible world
  (`flatten_force_iff`: fallible futures force everything, so they
  never constrain an implication), and the result is
  fallibility-free.  So ANY countermodel of a ◯-free M yields a flat
  one — no IPC decision procedure is consumed, only `completeness`.
* `ofreeGraft C K p` — fibre a flat model K over an arbitrary model C:
  a world `(x, k)` above the base cone of every `x`, never returning
  to the base, `Rₘ` rigid in the K-coordinate, `p` on the graft read
  from K's decoration, everything else inherited from the base
  coordinate.  The base-identity ∪ projection is a total
  p-bisimulation (`ofreeGraft_pbisim`), and at a non-fallible fibre
  the graft forces a ◯-free one-variable θ exactly when K does
  (`ofreeGraft_force_iff`).

Given underivable M: flatten a countermodel, fibre it over any C —
at any non-fallible w the p-variant world `(w, d)` refutes M, which
is exactly the ⊥-spec (`semAll_ofree_bot`); dually a consistent M is
forced at `(w, d)` over a flat model of M, giving the ⊤-spec for ∃p
(`semEx_ofree_top`).  The ⊤/⊥ halves for derivable/inconsistent M
(`semAll_top_of_derivable`, `semEx_bot_of_inconsistent`) hold for
ARBITRARY M.  One uniform construction covers every row of the
fragment — the surgeries do not proliferate below the first ◯.
-/

open PLLFormula

namespace PLLND
namespace SemUI

/-- ◯-freeness, computably. -/
def boxFree : PLLFormula → Bool
  | .prop _ => true
  | .falsePLL => true
  | .and φ ψ => boxFree φ && boxFree ψ
  | .or φ ψ => boxFree φ && boxFree ψ
  | .ifThen φ ψ => boxFree φ && boxFree ψ
  | .somehow _ => false

/-! ## The fallible-top extension -/

/-- One fallible world adjoined above everything, constraint-reachable
from everywhere. -/
def topExt (C : ConstraintModel) : ConstraintModel where
  W := C.W ⊕ Unit
  Ri := fun a b =>
    match a, b with
    | .inl x, .inl y => C.Ri x y
    | .inl _, .inr _ => True
    | .inr _, .inl _ => False
    | .inr _, .inr _ => True
  Rm := fun a b =>
    match a, b with
    | .inl x, .inl y => C.Rm x y
    | .inl _, .inr _ => True
    | .inr _, .inl _ => False
    | .inr _, .inr _ => True
  F := fun a => match a with
    | .inl x => x ∈ C.F
    | .inr _ => True
  V := fun q a => match a with
    | .inl x => x ∈ C.V q
    | .inr _ => True
  refl_i := by
    intro a
    rcases a with x | u
    · exact C.refl_i x
    · exact True.intro
  trans_i := by
    intro a b c h₁ h₂
    rcases a with x | u <;> rcases b with y | t <;> rcases c with y' | s
    · exact C.trans_i h₁ h₂
    · exact True.intro
    · exact h₂.elim
    · exact True.intro
    · exact h₁.elim
    · exact True.intro
    · exact h₂.elim
    · exact True.intro
  refl_m := by
    intro a
    rcases a with x | u
    · exact C.refl_m x
    · exact True.intro
  trans_m := by
    intro a b c h₁ h₂
    rcases a with x | u <;> rcases b with y | t <;> rcases c with y' | s
    · exact C.trans_m h₁ h₂
    · exact True.intro
    · exact h₂.elim
    · exact True.intro
    · exact h₁.elim
    · exact True.intro
    · exact h₂.elim
    · exact True.intro
  sub_mi := by
    intro a b h
    rcases a with x | u <;> rcases b with y | t
    · exact C.sub_mi h
    · exact True.intro
    · exact h.elim
    · exact True.intro
  hered_F := by
    intro a b h hF
    rcases a with x | u <;> rcases b with y | t
    · exact C.hered_F h hF
    · exact True.intro
    · exact h.elim
    · exact True.intro
  hered_V := by
    intro q a b h hV
    rcases a with x | u <;> rcases b with y | t
    · exact C.hered_V h hV
    · exact True.intro
    · exact h.elim
    · exact True.intro
  full_F := by
    intro q a hF
    rcases a with x | u
    · exact C.full_F hF
    · exact True.intro

/-- **Forcing of ◯-free formulas at original worlds is unchanged** by
the fallible top: the new world forces everything, so it never
constrains an implication.  (False for `¬◯⊥`, which the top
destroys — ◯-freeness is essential.) -/
theorem topExt_force_iff (C : ConstraintModel) :
    ∀ {θ : PLLFormula}, boxFree θ = true →
    ∀ x : C.W, ((topExt C).force (.inl x) θ ↔ C.force x θ) := by
  intro θ
  induction θ with
  | prop a => exact fun _ _ => Iff.rfl
  | falsePLL => exact fun _ _ => Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro h x
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [ConstraintModel.force]
      exact and_congr (ihφ h.1 x) (ihψ h.2 x)
  | or φ ψ ihφ ihψ =>
      intro h x
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [ConstraintModel.force]
      exact or_congr (ihφ h.1 x) (ihψ h.2 x)
  | ifThen φ ψ ihφ ihψ =>
      intro h x
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [ConstraintModel.force]
      constructor
      · intro hf v hv hφ
        exact (ihψ h.2 v).mp (hf (.inl v) hv ((ihφ h.1 v).mpr hφ))
      · intro hf b hb hφ
        rcases b with y | u
        · exact (ihψ h.2 y).mpr (hf y hb ((ihφ h.1 y).mp hφ))
        · exact (topExt C).force_of_fallible True.intro
  | somehow φ ih =>
      intro h
      exact absurd h (by simp [boxFree])

/-- `◯⊥` holds everywhere in the extension: the fallible top is a
constraint successor of every world. -/
theorem topExt_boxBot (C : ConstraintModel) (a : (topExt C).W) :
    (topExt C).force a PLLFormula.falsePLL.somehow := by
  intro b hb
  refine ⟨.inr (), ?_, True.intro⟩
  rcases b with y | u
  · exact True.intro
  · exact True.intro

/-! ## The two cone exclusions -/

/-- **No underivable ◯-free formula has a lower bound in the
◯⊥-cone**: if some world of some model refutes M (◯-free), then no ξ
derivable from `◯⊥` derives M — adjoin the fallible top: the refuting
world keeps refuting M but now forces `◯⊥`, hence ξ. -/
theorem no_lower_bound_above_boxBot {M : PLLFormula}
    (hM : boxFree M = true) {D : ConstraintModel} {d : D.W}
    (hd : ¬ D.force d M) {ξ : PLLFormula}
    (hlow : Nonempty (LaxND [ξ] M))
    (hcone : Nonempty (LaxND [PLLFormula.falsePLL.somehow] ξ)) : False := by
  obtain ⟨dlow⟩ := hlow
  obtain ⟨dcone⟩ := hcone
  have hξ : (topExt D).force (.inl d) ξ :=
    soundness dcone (topExt D) (.inl d) (fun χ hχ => by
      simp only [List.mem_singleton] at hχ
      exact hχ ▸ topExt_boxBot D _)
  have hMf : (topExt D).force (.inl d) M :=
    soundness dlow (topExt D) (.inl d) (fun χ hχ => by
      simp only [List.mem_singleton] at hχ
      exact hχ ▸ hξ)
  exact hd ((topExt_force_iff D hM d).mp hMf)

/-- With no fallible worlds, `¬◯⊥` holds everywhere. -/
theorem flat_neg_boxBot {C : ConstraintModel} (hF : C.F = ∅) (w : C.W) :
    C.force w (PLLFormula.falsePLL.somehow.ifThen .falsePLL) := by
  intro v hv hbox
  obtain ⟨u, -, hu⟩ := hbox v (C.refl_i v)
  have hu' : u ∈ C.F := hu
  rw [hF] at hu'
  exact absurd hu' (fun h => h)

/-- **No formula refuted over a fallibility-free model has a lower
bound in the ¬◯⊥-cone** (any IPC countermodel, read as a PLL model
with `F = ∅`, qualifies — here even ◯-freeness is not needed). -/
theorem no_lower_bound_above_negBoxBot {M : PLLFormula}
    {D : ConstraintModel} (hDF : D.F = ∅) {d : D.W}
    (hd : ¬ D.force d M) {ξ : PLLFormula}
    (hlow : Nonempty (LaxND [ξ] M))
    (hcone : Nonempty (LaxND
      [PLLFormula.falsePLL.somehow.ifThen .falsePLL] ξ)) : False := by
  obtain ⟨dlow⟩ := hlow
  obtain ⟨dcone⟩ := hcone
  have hξ : D.force d ξ :=
    soundness dcone D d (fun χ hχ => by
      simp only [List.mem_singleton] at hχ
      exact hχ ▸ flat_neg_boxBot hDF d)
  exact hd (soundness dlow D d (fun χ hχ => by
    simp only [List.mem_singleton] at hχ
    exact hχ ▸ hξ))

/-! ## The value corollaries (∀-side) -/

/-- The ∀p-value of a ◯-free M refuted somewhere never lies in the
◯⊥-cone. -/
theorem semAll_value_not_above_boxBot {p : String} {M ψ : PLLFormula}
    (hM : boxFree M = true) (h : IsSemAll p M ψ)
    {D : ConstraintModel} {d : D.W} (hd : ¬ D.force d M) :
    ¬ Nonempty (LaxND [PLLFormula.falsePLL.somehow] ψ) :=
  fun hcone => no_lower_bound_above_boxBot hM hd (semAll_lower h) hcone

/-- The ∀p-value of an M refuted over a fallibility-free model never
lies in the ¬◯⊥-cone. -/
theorem semAll_value_not_above_negBoxBot {p : String} {M ψ : PLLFormula}
    (h : IsSemAll p M ψ) {D : ConstraintModel} (hDF : D.F = ∅)
    {d : D.W} (hd : ¬ D.force d M) :
    ¬ Nonempty (LaxND [PLLFormula.falsePLL.somehow.ifThen .falsePLL] ψ) :=
  fun hcone => no_lower_bound_above_negBoxBot hDF hd (semAll_lower h) hcone

/-- If `⊢ M` then any ∀p-value of M is derivable — the value is ⊤, in
PLL as in IPC. -/
theorem semAll_value_of_derivable {p : String} {M ψ : PLLFormula}
    (h : IsSemAll p M ψ) (hM : Nonempty (LaxND [] M)) :
    Nonempty (LaxND [] ψ) := by
  obtain ⟨d⟩ := hM
  refine completeness ?_
  intro C w _
  refine (h.2 C w).mpr ?_
  intro v hv N B v' hZ
  exact soundness d N v' (fun χ hχ => absurd hχ List.not_mem_nil)

/-- **Agreement with IPC on ◯-free rows, modulo cone coverage**: an
underivable ◯-free M (refuted at a general world and at a
fallibility-free world) has its ∀p-value excluded from both cones; so
a value lying in either cone — or `≡ ⊥` — is `⊥`, Pitts's value.  The
coverage of RN(◯,{}) ∖ {⊥} by the two cones (every nonzero closed
formula derivable from `◯⊥` or from `¬◯⊥`) is the remaining OPEN step
to the unconditional collapse; it holds for every rung tested. -/
theorem semAll_value_bot_of_cones {p : String} {M ψ : PLLFormula}
    (hM : boxFree M = true) (h : IsSemAll p M ψ)
    {D₁ : ConstraintModel} {d₁ : D₁.W} (hd₁ : ¬ D₁.force d₁ M)
    {D₂ : ConstraintModel} (hDF : D₂.F = ∅) {d₂ : D₂.W}
    (hd₂ : ¬ D₂.force d₂ M)
    (hcov : Nonempty (LaxND [PLLFormula.falsePLL.somehow] ψ) ∨
      Nonempty (LaxND [PLLFormula.falsePLL.somehow.ifThen .falsePLL] ψ) ∨
      Nonempty (LaxND [ψ] .falsePLL)) :
    Nonempty (LaxND [ψ] .falsePLL) := by
  rcases hcov with h1 | h2 | h3
  · exact absurd h1 (semAll_value_not_above_boxBot hM h hd₁)
  · exact absurd h2 (semAll_value_not_above_negBoxBot h hDF hd₂)
  · exact h3

/-! ## The dual exclusions (∃-side) -/

/-- The ∃p-value of a ◯-free M forced at a non-fallible world never
derives `¬◯⊥`: the fallible top gives an M-world forcing `◯⊥`
non-fallibly. -/
theorem semEx_value_not_derives_negBoxBot {p : String} {M ψ : PLLFormula}
    (hM : boxFree M = true) (h : IsSemEx p M ψ)
    {D : ConstraintModel} {d : D.W} (hdF : d ∉ D.F) (hd : D.force d M) :
    ¬ Nonempty (LaxND [ψ]
      (PLLFormula.falsePLL.somehow.ifThen .falsePLL)) := by
  rintro ⟨e⟩
  obtain ⟨u⟩ := semEx_upper h
  have hψ : (topExt D).force (.inl d) ψ :=
    soundness u (topExt D) (.inl d) (fun χ hχ => by
      simp only [List.mem_singleton] at hχ
      exact hχ ▸ (topExt_force_iff D hM d).mpr hd)
  have hneg := soundness e (topExt D) (.inl d) (fun χ hχ => by
    simp only [List.mem_singleton] at hχ
    exact hχ ▸ hψ)
  exact hdF (hneg (.inl d) ((topExt D).refl_i _) (topExt_boxBot D _))

/-- The ∃p-value of an M forced over a fallibility-free model never
derives `◯⊥`. -/
theorem semEx_value_not_derives_boxBot {p : String} {M ψ : PLLFormula}
    (h : IsSemEx p M ψ) {D : ConstraintModel} (hDF : D.F = ∅)
    {d : D.W} (hd : D.force d M) :
    ¬ Nonempty (LaxND [ψ] PLLFormula.falsePLL.somehow) := by
  rintro ⟨e⟩
  obtain ⟨u⟩ := semEx_upper h
  have hψ : D.force d ψ := soundness u D d (fun χ hχ => by
    simp only [List.mem_singleton] at hχ
    exact hχ ▸ hd)
  have hbox := soundness e D d (fun χ hχ => by
    simp only [List.mem_singleton] at hχ
    exact hχ ▸ hψ)
  obtain ⟨y, -, hy⟩ := hbox d (D.refl_i d)
  have hy' : y ∈ D.F := hy
  rw [hDF] at hy'
  exact absurd hy' (fun h => h)

/-! ## Sufficiency: flattening -/

/-- The non-fallible part of a model.  Fallibility-free by
construction; ◯-free forcing at non-fallible worlds is unchanged
(next lemma) — the downward semantic form of conservativity. -/
def flatten (C : ConstraintModel) : ConstraintModel where
  W := {x : C.W // x ∉ C.F}
  Ri := fun a b => C.Ri a.1 b.1
  Rm := fun a b => C.Rm a.1 b.1
  F := ∅
  V := fun q a => a.1 ∈ C.V q
  refl_i := fun a => C.refl_i a.1
  trans_i := fun h₁ h₂ => C.trans_i h₁ h₂
  refl_m := fun a => C.refl_m a.1
  trans_m := fun h₁ h₂ => C.trans_m h₁ h₂
  sub_mi := fun h => C.sub_mi h
  hered_F := fun _ hw => absurd hw (fun h => h)
  hered_V := fun h hw => C.hered_V h hw
  full_F := fun hw => absurd hw (fun h => h)

/-- Restriction to the non-fallible part preserves ◯-free forcing:
fallible futures force everything, so they never constrain an
implication. -/
theorem flatten_force_iff (C : ConstraintModel) :
    ∀ {θ : PLLFormula}, boxFree θ = true →
    ∀ (x : C.W) (hx : x ∉ C.F),
    ((flatten C).force ⟨x, hx⟩ θ ↔ C.force x θ) := by
  intro θ
  induction θ with
  | prop a => exact fun _ x hx => Iff.rfl
  | falsePLL => exact fun _ x hx => iff_of_false (fun h => h) hx
  | and φ ψ ihφ ihψ =>
      intro h x hx
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [ConstraintModel.force]
      exact and_congr (ihφ h.1 x hx) (ihψ h.2 x hx)
  | or φ ψ ihφ ihψ =>
      intro h x hx
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [ConstraintModel.force]
      exact or_congr (ihφ h.1 x hx) (ihψ h.2 x hx)
  | ifThen φ ψ ihφ ihψ =>
      intro h x hx
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [ConstraintModel.force]
      constructor
      · intro hf v hv hφ
        by_cases hvF : v ∈ C.F
        · exact C.force_of_fallible hvF
        · exact (ihψ h.2 v hvF).mp (hf ⟨v, hvF⟩ hv ((ihφ h.1 v hvF).mpr hφ))
      · intro hf b hb hφ
        exact (ihψ h.2 b.1 b.2).mpr (hf b.1 hb ((ihφ h.1 b.1 b.2).mp hφ))
  | somehow φ ih =>
      intro h
      exact absurd h (by simp [boxFree])

/-! ## Sufficiency: the fibred graft -/

/-- The frame of the graft: a copy `(x, k)` of the flat model K in the
fibre over every base world `x`, sitting above the base cone of `x`,
never returning to the base; `Rₘ` rigid in the K-coordinate;
fallibility and all valuations from the base coordinate. -/
def ofreeGraftBase (C K : ConstraintModel) : ConstraintModel where
  W := C.W ⊕ (C.W × K.W)
  Ri := fun a b =>
    match a, b with
    | .inl y, .inl y' => C.Ri y y'
    | .inl y, .inr xk => C.Ri y xk.1
    | .inr _, .inl _ => False
    | .inr xk, .inr xk' => C.Ri xk.1 xk'.1 ∧ K.Ri xk.2 xk'.2
  Rm := fun a b =>
    match a, b with
    | .inl y, .inl y' => C.Rm y y'
    | .inl _, .inr _ => False
    | .inr _, .inl _ => False
    | .inr xk, .inr xk' => C.Rm xk.1 xk'.1 ∧ xk'.2 = xk.2
  F := fun a => match a with
    | .inl y => y ∈ C.F
    | .inr xk => xk.1 ∈ C.F
  V := fun q a => match a with
    | .inl y => y ∈ C.V q
    | .inr xk => xk.1 ∈ C.V q
  refl_i := by
    intro a
    rcases a with y | xk
    · exact C.refl_i y
    · exact ⟨C.refl_i xk.1, K.refl_i xk.2⟩
  trans_i := by
    intro a b c h₁ h₂
    rcases a with y | xk <;> rcases b with y' | xk' <;> rcases c with y'' | xk''
    · exact C.trans_i h₁ h₂
    · exact C.trans_i h₁ h₂
    · exact h₂.elim
    · exact C.trans_i h₁ h₂.1
    · exact h₁.elim
    · exact h₁.elim
    · exact h₂.elim
    · exact ⟨C.trans_i h₁.1 h₂.1, K.trans_i h₁.2 h₂.2⟩
  refl_m := by
    intro a
    rcases a with y | xk
    · exact C.refl_m y
    · exact ⟨C.refl_m xk.1, rfl⟩
  trans_m := by
    intro a b c h₁ h₂
    rcases a with y | xk <;> rcases b with y' | xk' <;> rcases c with y'' | xk''
    · exact C.trans_m h₁ h₂
    · exact h₂.elim
    · exact h₁.elim
    · exact h₁.elim
    · exact h₁.elim
    · exact h₁.elim
    · exact h₂.elim
    · exact ⟨C.trans_m h₁.1 h₂.1, h₂.2.trans h₁.2⟩
  sub_mi := by
    intro a b h
    rcases a with y | xk <;> rcases b with y' | xk'
    · exact C.sub_mi h
    · exact h.elim
    · exact h.elim
    · exact ⟨C.sub_mi h.1, by rw [h.2]; exact K.refl_i _⟩
  hered_F := by
    intro a b h hF
    rcases a with y | xk <;> rcases b with y' | xk'
    · exact C.hered_F h hF
    · exact C.hered_F h hF
    · exact h.elim
    · exact C.hered_F h.1 hF
  hered_V := by
    intro q a b h hV
    rcases a with y | xk <;> rcases b with y' | xk'
    · exact C.hered_V h hV
    · exact C.hered_V h hV
    · exact h.elim
    · exact C.hered_V h.1 hV
  full_F := by
    intro q a hF
    rcases a with y | xk
    · exact C.full_F hF
    · exact C.full_F hF

/-- The graft's `p`-decoration: K's decoration of the caller's atom on
the fibres, plus the fallible worlds. -/
def graftSet (C K : ConstraintModel) (p : String) : Set (ofreeGraftBase C K).W :=
  fun a => match a with
    | .inl y => y ∈ C.F
    | .inr xk => xk.2 ∈ K.V p ∨ xk.1 ∈ C.F

/-- The graft: `p` decorated on `graftSet`. -/
def ofreeGraft (C K : ConstraintModel) (p : String) : ConstraintModel :=
  redecorate (ofreeGraftBase C K) p (graftSet C K p)
    (by intro a b h hS
        rcases a with y | xk <;> rcases b with y' | xk'
        · exact C.hered_F h hS
        · exact Or.inr (C.hered_F h hS)
        · exact h.elim
        · rcases hS with hk | hF
          · exact Or.inl (K.hered_V h.2 hk)
          · exact Or.inr (C.hered_F h.1 hF))
    (by intro a hF
        rcases a with y | xk
        · exact hF
        · exact Or.inr hF)

/-- Base-identity ∪ projection is a p-bisimulation onto the graft:
every fibre world `(x, k)` is a p-variant of its base `x`. -/
def ofreeGraft_pbisim (C K : ConstraintModel) (p : String) :
    PBisim p C (ofreeGraft C K p) where
  Z := fun c a => match a with
    | .inl y => y = c
    | .inr xk => xk.1 = c
  atoms := by
    intro c a hZ q hq
    rcases a with y | ⟨x, k⟩
    · obtain rfl : y = c := hZ
      show y ∈ C.V q ↔ _ ∈ (if q = p then graftSet C K p else (ofreeGraftBase C K).V q)
      rw [if_neg hq]
      exact Iff.rfl
    · obtain rfl : x = c := hZ
      show x ∈ C.V q ↔ _ ∈ (if q = p then graftSet C K p else (ofreeGraftBase C K).V q)
      rw [if_neg hq]
      exact Iff.rfl
  fall := by
    intro c a hZ
    rcases a with y | ⟨x, k⟩
    · obtain rfl : y = c := hZ
      exact Iff.rfl
    · obtain rfl : x = c := hZ
      exact Iff.rfl
  iforth := by
    intro c a hZ v hv
    rcases a with y | ⟨x, k⟩
    · obtain rfl : y = c := hZ
      exact ⟨.inl v, hv, rfl⟩
    · obtain rfl : x = c := hZ
      exact ⟨.inr (v, k), ⟨hv, K.refl_i k⟩, rfl⟩
  iback := by
    intro c a hZ a' ha'
    rcases a with y | ⟨x, k⟩
    · obtain rfl : y = c := hZ
      rcases a' with y' | ⟨x', k'⟩
      · exact ⟨y', ha', rfl⟩
      · exact ⟨x', ha', rfl⟩
    · obtain rfl : x = c := hZ
      rcases a' with y' | ⟨x', k'⟩
      · exact ha'.elim
      · exact ⟨x', ha'.1, rfl⟩
  mforth := by
    intro c a hZ u hu
    rcases a with y | ⟨x, k⟩
    · obtain rfl : y = c := hZ
      exact ⟨.inl u, hu, rfl⟩
    · obtain rfl : x = c := hZ
      exact ⟨.inr (u, k), ⟨hu, rfl⟩, rfl⟩
  mback := by
    intro c a hZ a' ha'
    rcases a with y | ⟨x, k⟩
    · obtain rfl : y = c := hZ
      rcases a' with y' | ⟨x', k'⟩
      · exact ⟨y', ha', rfl⟩
      · exact ha'.elim
    · obtain rfl : x = c := hZ
      rcases a' with y' | ⟨x', k'⟩
      · exact ha'.elim
      · exact ⟨x', ha'.1, rfl⟩

/-- **The graft forces exactly what K forces** at non-fallible fibres,
for ◯-free formulas in the single variable `p`: fallible fibres never
constrain an implication, non-fallible fibres evaluate in the
K-coordinate. -/
theorem ofreeGraft_force_iff (C K : ConstraintModel) (p : String)
    (hKF : K.F = ∅) :
    ∀ {θ : PLLFormula}, boxFree θ = true → (∀ a ∈ θ.atoms, a = p) →
    ∀ (x : C.W) (k : K.W), x ∉ C.F →
    ((ofreeGraft C K p).force (.inr (x, k)) θ ↔ K.force k θ) := by
  intro θ
  induction θ with
  | prop a =>
      intro _ hat x k hx
      obtain rfl := hat a (by simp)
      show _ ∈ (if a = a then graftSet C K a else (ofreeGraftBase C K).V a) ↔ _
      rw [if_pos rfl]
      show (k ∈ K.V a ∨ x ∈ C.F) ↔ k ∈ K.V a
      constructor
      · rintro (hk | hF)
        · exact hk
        · exact absurd hF hx
      · exact fun hk => Or.inl hk
  | falsePLL =>
      intro _ _ x k hx
      refine iff_of_false hx ?_
      intro hk
      have hk' : k ∈ K.F := hk
      rw [hKF] at hk'
      exact hk'
  | and φ ψ ihφ ihψ =>
      intro h hat x k hx
      simp only [boxFree, Bool.and_eq_true] at h
      have hat1 : ∀ a ∈ φ.atoms, a = p := fun a ha => hat a (by simp [ha])
      have hat2 : ∀ a ∈ ψ.atoms, a = p := fun a ha => hat a (by simp [ha])
      simp only [ConstraintModel.force]
      exact and_congr (ihφ h.1 hat1 x k hx) (ihψ h.2 hat2 x k hx)
  | or φ ψ ihφ ihψ =>
      intro h hat x k hx
      simp only [boxFree, Bool.and_eq_true] at h
      have hat1 : ∀ a ∈ φ.atoms, a = p := fun a ha => hat a (by simp [ha])
      have hat2 : ∀ a ∈ ψ.atoms, a = p := fun a ha => hat a (by simp [ha])
      simp only [ConstraintModel.force]
      exact or_congr (ihφ h.1 hat1 x k hx) (ihψ h.2 hat2 x k hx)
  | ifThen φ ψ ihφ ihψ =>
      intro h hat x k hx
      simp only [boxFree, Bool.and_eq_true] at h
      have hat1 : ∀ a ∈ φ.atoms, a = p := fun a ha => hat a (by simp [ha])
      have hat2 : ∀ a ∈ ψ.atoms, a = p := fun a ha => hat a (by simp [ha])
      simp only [ConstraintModel.force]
      constructor
      · intro hf k' hk' hφ
        exact (ihψ h.2 hat2 x k' hx).mp
          (hf (.inr (x, k')) ⟨C.refl_i x, hk'⟩ ((ihφ h.1 hat1 x k' hx).mpr hφ))
      · intro hf b hb hφ
        rcases b with y | ⟨x', k'⟩
        · exact hb.elim
        · by_cases hx' : x' ∈ C.F
          · exact (ofreeGraft C K p).force_of_fallible hx'
          · exact (ihψ h.2 hat2 x' k' hx').mpr
              (hf k' hb.2 ((ihφ h.1 hat1 x' k' hx').mp hφ))
  | somehow φ ih =>
      intro h
      exact absurd h (by simp [boxFree])

/-! ## Sufficiency: the value theorems -/

/-- `⊢ M` gives `∀p.M = ⊤`, for ANY M. -/
theorem semAll_top_of_derivable {p : String} {M : PLLFormula}
    (hM : Nonempty (LaxND [] M)) : IsSemAll p M truePLL := by
  obtain ⟨d⟩ := hM
  refine ⟨by simp [truePLL], ?_⟩
  intro C w
  constructor
  · intro _ v hv N B v' hZ
    exact soundness d N v' (fun χ hχ => absurd hχ List.not_mem_nil)
  · intro _
    exact fun v hv h => h

/-- `M ⊢ ⊥` gives `∃p.M = ⊥`, for ANY M. -/
theorem semEx_bot_of_inconsistent {p : String} {M : PLLFormula}
    (hM : Nonempty (LaxND [M] .falsePLL)) : IsSemEx p M .falsePLL := by
  obtain ⟨d⟩ := hM
  refine ⟨by simp, ?_⟩
  intro C w
  constructor
  · intro hw
    exact ⟨C, ABisim.id _ C, w, rfl, C.force_of_fallible hw⟩
  · rintro ⟨N, B, w', hZ, hM'⟩
    have hbot : N.force w' .falsePLL := soundness d N w' (fun χ hχ => by
      simp only [List.mem_singleton] at hχ
      exact hχ ▸ hM')
    exact (B.fall hZ).mpr hbot

/-- From underivability, classically, a refuting world. -/
theorem exists_refuting_world {M : PLLFormula}
    (hM : ¬ Nonempty (LaxND [] M)) :
    ∃ (D : ConstraintModel) (d : D.W), ¬ D.force d M := by
  by_contra h
  refine hM (completeness ?_)
  intro D d _
  by_contra hd
  exact h ⟨D, d, hd⟩

/-- From consistency, classically, a non-fallible forcing world. -/
theorem exists_forcing_world {M : PLLFormula}
    (hM : ¬ Nonempty (LaxND [M] .falsePLL)) :
    ∃ (D : ConstraintModel) (d : D.W), D.force d M ∧ d ∉ D.F := by
  by_contra h
  refine hM (completeness ?_)
  intro D d hprem
  by_contra hd
  exact h ⟨D, d, hprem M (by simp), hd⟩

/-- **Sufficiency, ∀-side**: an underivable ◯-free one-variable M has
∀p-value ⊥ — the spec is SATISFIED, not merely bounded.  Flatten a
countermodel and fibre it over the given model: at any non-fallible
world w, the p-variant world `(w, d)` refutes M. -/
theorem semAll_ofree_bot {p : String} {M : PLLFormula}
    (hbf : boxFree M = true) (hat : ∀ a ∈ M.atoms, a = p)
    (hM : ¬ Nonempty (LaxND [] M)) : IsSemAll p M .falsePLL := by
  obtain ⟨D, d, hd⟩ := exists_refuting_world hM
  have hdF : d ∉ D.F := fun hF => hd (D.force_of_fallible hF)
  have hK : ¬ (flatten D).force ⟨d, hdF⟩ M :=
    fun h => hd ((flatten_force_iff D hbf d hdF).mp h)
  refine ⟨by simp, ?_⟩
  intro C w
  constructor
  · intro hw v hv N B v' hZ
    exact N.force_of_fallible ((B.fall hZ).mp (C.hered_F hv hw))
  · intro h'
    by_contra hwF
    have hforce := h' w (C.refl_i w) (ofreeGraft C (flatten D) p)
      (ofreeGraft_pbisim C (flatten D) p) (.inr (w, ⟨d, hdF⟩)) rfl
    exact hK ((ofreeGraft_force_iff C (flatten D) p rfl hbf hat w ⟨d, hdF⟩ hwF).mp hforce)

/-- **Sufficiency, ∃-side**: a consistent ◯-free one-variable M has
∃p-value ⊤ — every world has a p-variant forcing M (fallible worlds
force it themselves; non-fallible worlds through the graft). -/
theorem semEx_ofree_top {p : String} {M : PLLFormula}
    (hbf : boxFree M = true) (hat : ∀ a ∈ M.atoms, a = p)
    (hM : ¬ Nonempty (LaxND [M] .falsePLL)) : IsSemEx p M truePLL := by
  obtain ⟨D, d, hdM, hdF⟩ := exists_forcing_world hM
  have hK : (flatten D).force ⟨d, hdF⟩ M :=
    (flatten_force_iff D hbf d hdF).mpr hdM
  refine ⟨by simp [truePLL], ?_⟩
  intro C w
  constructor
  · intro _
    by_cases hwF : w ∈ C.F
    · exact ⟨C, ABisim.id _ C, w, rfl, C.force_of_fallible hwF⟩
    · exact ⟨ofreeGraft C (flatten D) p, ofreeGraft_pbisim C (flatten D) p,
        .inr (w, ⟨d, hdF⟩), rfl,
        (ofreeGraft_force_iff C (flatten D) p rfl hbf hat w ⟨d, hdF⟩ hwF).mpr hK⟩
  · intro _
    exact fun v hv h => h

/-! ## The headline: RN({p}) is definable with Pitts's values -/

/-- **Agreement with IPC, ∀-side, PROVED**: every ◯-free one-variable
formula has a definable semantic ∀p-quantifier with value ⊤ or ⊥ —
exactly Pitts's values. -/
theorem ofree_semAll_definable (p : String) (M : PLLFormula)
    (hbf : boxFree M = true) (hat : ∀ a ∈ M.atoms, a = p) :
    ∃ ψ, IsSemAll p M ψ ∧ (ψ = truePLL ∨ ψ = PLLFormula.falsePLL) := by
  rcases Classical.em (Nonempty (LaxND [] M)) with h | h
  · exact ⟨truePLL, semAll_top_of_derivable h, Or.inl rfl⟩
  · exact ⟨.falsePLL, semAll_ofree_bot hbf hat h, Or.inr rfl⟩

/-- **Agreement with IPC, ∃-side, PROVED**. -/
theorem ofree_semEx_definable (p : String) (M : PLLFormula)
    (hbf : boxFree M = true) (hat : ∀ a ∈ M.atoms, a = p) :
    ∃ ψ, IsSemEx p M ψ ∧ (ψ = truePLL ∨ ψ = PLLFormula.falsePLL) := by
  rcases Classical.em (Nonempty (LaxND [M] .falsePLL)) with h | h
  · exact ⟨.falsePLL, semEx_bot_of_inconsistent h, Or.inr rfl⟩
  · exact ⟨truePLL, semEx_ofree_top hbf hat h, Or.inl rfl⟩

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SemUI.semAll_value_bot_of_cones' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms semAll_value_bot_of_cones

/--
info: 'PLLND.SemUI.ofree_semAll_definable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ofree_semAll_definable

/--
info: 'PLLND.SemUI.ofree_semEx_definable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ofree_semEx_definable

end SemUI
end PLLND
