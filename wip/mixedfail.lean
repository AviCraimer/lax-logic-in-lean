import wip.guardstretch

/-!
# REFUTED: `MixedCoverConj`, and `GuardedMixedConj` with it

`wip/phistar.lean` left the JOIN of the two lower-bound methods open:

    MixedCoverConj : ∀ φ with atoms ⊆ {p}, ∃ finite variable-free S,
                     φ ⊢ Lo φ ∨ ⋁_{θ ∈ S} φ[p := θ]

with `postUI_of_mixedCoverConj` reducing last-variable `∃p` to it.
`wip/guardstretch.lean` weakens it further by allowing the stretch to be
guarded by any finite set of variable-free formulas (`GuardedMixedConj`).
This file refutes BOTH, at

    φ♦ = ((◯⊥ ⊃ p) ∨ ◯⊥ ∨ ¬p) ⊃ ((◯⊥ ∧ p) ∨ (◯⊥ ∧ ¬p)) .

## The countermodel: the DIAMOND

    M♦ :  0 ⊑ 1, 0 ⊑ 2, 1 ⊑ 3, 2 ⊑ 3   (`1`, `2` incomparable)
          Rₘ = id ∪ {(x,3) : x ≠ 0},   F = {3},   V(a) = {1,3}

`◯⊥` holds exactly on `{1,2,3}` (world `0`'s only `Rₘ`-successor is `0`);
`p` holds at `1` and at the fallible `3`, and NOT at `2`.  The
transposition `1 ↔ 2` is a frame automorphism (`sw`), so worlds `1` and
`2` satisfy the same variable-free formulas (`Md_swap`) and `‖p‖` is
undefinable.

At the root, `φ♦` holds: the antecedent fails at `0` (all three
disjuncts do), and above `0` — where `◯⊥` is true — the consequent
reduces to `p ∨ ¬p`, which holds at `1` (`p`), at `2` (`¬p`, since the
only `p`-world above `2` is the fallible `3`) and at `3`.

Every variable-free substitution fails, exactly as at `φ★`
(`Md_inst_fails`): `θ` is true at `1` iff true at `2`, so either `θ`
covers all of `‖◯⊥‖` — and then `◯⊥ ⊃ θ` holds at `0`, so the antecedent
holds at `0` while the consequent cannot (it needs `◯⊥` at `0`) — or `θ`
holds only at the fallible world, and then `¬θ` holds at `0`, again
giving the antecedent.

## Why the stretch does not rescue it, for ANY guard

`gstretch_tr` turns `‖LoG χ φ♦‖` into forcing of `φ♦` at the ground copy
of the root in the `χ`-guarded stretch, and there `φ♦` fails whatever
`χ` is (`Md_gstretch_fails`), by a three-way case split on the guard:

* `1 ⊩ χ` — the upper copy `inr 1` is attached above `inl 1`; it forces
  `p` and is not fallible, so `¬p` fails at `inl 1`, while `p` itself
  fails there (`p` is "fallible" on the ground layer).  So the
  consequent fails at `inl 1` although `◯⊥` — hence the antecedent —
  holds there;
* `2 ⊩ χ` — the same at `inl 2`;
* `1 ⊮ χ` and `2 ⊮ χ` — then the upper layer is attached only over the
  fallible world `3`, so every `p`-world above `inl 0` is fallible and
  `¬p` holds at `inl 0`, giving the antecedent there, while the
  consequent needs `◯⊥` at `inl 0`, which fails.

So `LoG χ φ♦` fails at the root of `M♦` for EVERY guard `χ` — including
guards with variables — and no join of guarded stretch bounds with
substitution instances covers `φ♦`.

## What this does and does not settle

REFUTED: the mixed method, and the guarded mixed method, hence both
reductions `postUI_of_mixedCoverConj` and `postUI_of_guardedMixedConj`
are dead ends as stated.  Uniform interpolation is untouched: as with
`φ★`, whether `∃p.φ♦` exists is OPEN (`PostInterpPhiDiaExists`).  The
only candidate below which it must lie in `M♦` is `⊤`, since the
variable-free truth sets of `M♦` are exactly `{⊥, ◯⊥, ⊤}` and only `⊤`
contains the root; `postInterpPhiDiaIsTop_iff` reduces that candidate to
"every variable-free consequence of `φ♦` is a theorem".

No sorries.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## 1.  The diamond frame -/

/-- The diamond order on `Fin 4`: `0 ⊑ 1, 2 ⊑ 3`, with `1` and `2`
incomparable. -/
def Rd (x y : Fin 4) : Prop := x = 0 ∨ x = y ∨ y = 3

instance (x y : Fin 4) : Decidable (Rd x y) := by unfold Rd; infer_instance

theorem Rd_refl : ∀ x : Fin 4, Rd x x := by decide
theorem Rd_trans : ∀ x y z : Fin 4, Rd x y → Rd y z → Rd x z := by decide
theorem Rd_of_Rm4 : ∀ x y : Fin 4, Rm4 x y → Rd x y := by decide
theorem Rd_hered_F : ∀ x y : Fin 4, Rd x y → x = 3 → y = 3 := by decide
theorem Rd_hered_V : ∀ x y : Fin 4, Rd x y → (x = 1 ∨ x = 3) → (y = 1 ∨ y = 3) := by
  decide
theorem Rd_full_V : ∀ x : Fin 4, x = 3 → (x = 1 ∨ x = 3) := by decide
theorem Rd_ne_zero : ∀ x v : Fin 4, x ≠ 0 → Rd x v → v ≠ 0 := by decide
theorem Rd_two_p : ∀ u : Fin 4, Rd 2 u → (u = 1 ∨ u = 3) → u = 3 := by decide

/-- **The diamond countermodel.**  `p` is true at `1` and at the fallible
top `3`, and false at `0` and `2`; the transposition `1 ↔ 2` is a frame
automorphism, so this valuation is undefinable. -/
@[reducible] def Md : ConstraintModel where
  W := Fin 4
  Ri := Rd
  Rm := Rm4
  F := {x | x = 3}
  V _ := {x | x = 1 ∨ x = 3}
  refl_i := Rd_refl
  trans_i {x y z} h1 h2 := Rd_trans x y z h1 h2
  refl_m := Rm4_refl
  trans_m {x y z} h1 h2 := Rm4_trans x y z h1 h2
  sub_mi {x y} h := Rd_of_Rm4 x y h
  hered_F {x y} h hx := Rd_hered_F x y h hx
  hered_V {_ x y} h hx := Rd_hered_V x y h hx
  full_F {_ x} hx := Rd_full_V x hx

/-- `◯⊥` holds at every world other than the root. -/
theorem Md_oBot_ne_zero : ∀ x : Fin 4, x ≠ 0 → Md.force x oBot := by
  intro x hx v hv
  exact ⟨3, Rm4_top v (Rd_ne_zero x v hx hv), rfl⟩

/-- `◯⊥` fails at the root: `0`'s only `Rₘ`-successor is `0`. -/
theorem Md_not_oBot_zero : ¬ Md.force (0 : Fin 4) oBot := by
  intro h
  obtain ⟨u, hu, hf⟩ := h 0 (Rd_refl 0)
  have hu0 : u = 0 := Rm4_from_zero u hu
  subst hu0
  have hf' : (0 : Fin 4) = 3 := hf
  exact absurd hf' (by decide)

/-! ## 2.  The automorphism `1 ↔ 2` -/

/-- The transposition of the two incomparable worlds. -/
def sw : Fin 4 → Fin 4 := fun x => if x = 1 then 2 else if x = 2 then 1 else x

theorem sw_invol : ∀ x : Fin 4, sw (sw x) = x := by decide
theorem sw_ri : ∀ x y : Fin 4, Rd x y ↔ Rd (sw x) (sw y) := by decide
theorem sw_rm : ∀ x y : Fin 4, Rm4 x y ↔ Rm4 (sw x) (sw y) := by decide
theorem sw_F : ∀ x : Fin 4, x = 3 ↔ sw x = 3 := by decide
theorem sw_one : sw 1 = 2 := by decide
theorem sw_two : sw 2 = 1 := by decide

/-- **The automorphism argument.**  Variable-free formulas cannot tell
a world from its image under the transposition. -/
theorem Md_swap : ∀ {A : PLLFormula}, atomFree A = true → ∀ x : Fin 4,
    (Md.force x A ↔ Md.force (sw x) A) := by
  intro A
  induction A with
  | prop a => intro h; exact absurd h (by simp [atomFree])
  | falsePLL => intro _ x; exact sw_F x
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
        have hv' : Md.Ri x (sw v) := by
          refine (sw_ri x (sw v)).mpr ?_
          rw [sw_invol v]
          exact hv
        exact (ihB h'.2 v).mpr (hh (sw v) hv' ((ihA h'.1 v).mp hA))
      · intro hh v hv hA
        exact (ihB h'.2 v).mpr (hh (sw v) ((sw_ri x v).mp hv) ((ihA h'.1 v).mp hA))
  | somehow A ih =>
      intro h x
      constructor
      · intro hh v hv
        have hv' : Md.Ri x (sw v) := by
          refine (sw_ri x (sw v)).mpr ?_
          rw [sw_invol v]
          exact hv
        obtain ⟨u, hu, hA⟩ := hh (sw v) hv'
        refine ⟨sw u, ?_, (ih h u).mp hA⟩
        refine (sw_rm v (sw u)).mpr ?_
        rw [sw_invol u]
        exact hu
      · intro hh v hv
        obtain ⟨u, hu, hA⟩ := hh (sw v) ((sw_ri x v).mp hv)
        refine ⟨sw u, ?_, (ih h u).mp hA⟩
        refine (sw_rm v (sw u)).mpr ?_
        rw [sw_invol u]
        exact hu

/-- Worlds `1` and `2` satisfy the same variable-free formulas. -/
theorem Md_swap12 {A : PLLFormula} (hA : atomFree A = true) :
    Md.force (1 : Fin 4) A ↔ Md.force (2 : Fin 4) A := by
  have h := Md_swap hA 1
  rwa [sw_one] at h

/-! ## 3.  The formula `φ♦`, and its truth at the root -/

/-- **`φ♦ = ((◯⊥ ⊃ p) ∨ ◯⊥ ∨ ¬p) ⊃ ((◯⊥ ∧ p) ∨ (◯⊥ ∧ ¬p))`.** -/
def phiDia : PLLFormula :=
  ((oBot.ifThen (PLLFormula.prop pv)).or
      (oBot.or (nt (PLLFormula.prop pv)))).ifThen
    ((oBot.and (PLLFormula.prop pv)).or (oBot.and (nt (PLLFormula.prop pv))))

theorem phiDia_onlyPv : onlyPv phiDia = true := by decide

/-- `p` is false at `2`, and `¬p` holds there: the only `p`-world above
`2` is the fallible top. -/
theorem Md_two_neg_p : Md.force (2 : Fin 4) (nt (PLLFormula.prop pv)) := by
  intro u hu hp
  exact Rd_two_p u hu hp

/-- **`φ♦` holds at the root of `M♦`.** -/
theorem Md_force_phiDia : Md.force (0 : Fin 4) phiDia := by
  intro v hv hante
  rcases Fin4_cases v with rfl | rfl | rfl | rfl
  · -- at the root the antecedent is false
    exfalso
    rcases hante with h1 | h2 | h3
    · have h2p : Md.force (2 : Fin 4) (PLLFormula.prop pv) :=
        h1 2 (by decide) (Md_oBot_ne_zero 2 (by decide))
      have h2p' : (2 : Fin 4) = 1 ∨ (2 : Fin 4) = 3 := h2p
      exact absurd h2p' (by decide)
    · exact Md_not_oBot_zero h2
    · have hbad : (1 : Fin 4) = 3 :=
        h3 1 (by decide) (show (1 : Fin 4) = 1 ∨ (1 : Fin 4) = 3 by decide)
      exact absurd hbad (by decide)
  · exact Or.inl ⟨Md_oBot_ne_zero 1 (by decide),
      (show (1 : Fin 4) = 1 ∨ (1 : Fin 4) = 3 by decide)⟩
  · exact Or.inr ⟨Md_oBot_ne_zero 2 (by decide), Md_two_neg_p⟩
  · exact Md.force_of_fallible (show (3 : Fin 4) ∈ Md.F from rfl)

/-! ## 4.  Every variable-free instance fails at the root -/

theorem inst_phiDia (θ : PLLFormula) :
    inst θ phiDia
      = ((oBot.ifThen θ).or (oBot.or (θ.ifThen .falsePLL))).ifThen
          ((oBot.and θ).or (oBot.and (θ.ifThen .falsePLL))) := by
  show (((inst θ oBot).ifThen (inst θ (PLLFormula.prop pv))).or
      ((inst θ oBot).or
        ((inst θ (PLLFormula.prop pv)).ifThen (inst θ PLLFormula.falsePLL)))).ifThen
      (((inst θ oBot).and (inst θ (PLLFormula.prop pv))).or
        ((inst θ oBot).and
          ((inst θ (PLLFormula.prop pv)).ifThen (inst θ PLLFormula.falsePLL)))) = _
  rw [inst_var_eq, inst_atomFree_eq θ (show atomFree oBot = true from rfl)]
  rfl

/-- **No variable-free instance of `φ♦` is forced at the root of `M♦`.**
The consequent needs `◯⊥`, which fails at the root, so it is enough that
the antecedent holds there — and it does: if `θ` reaches world `1` it
reaches `2` as well (`Md_swap12`), hence all of `‖◯⊥‖`, so `◯⊥ ⊃ θ`
holds at `0`; and if it does not, `θ` lives on the fallible world alone,
so `¬θ` holds at `0`. -/
theorem Md_inst_fails {θ : PLLFormula} (hθ : atomFree θ = true) :
    ¬ Md.force (0 : Fin 4) (inst θ phiDia) := by
  classical
  rw [inst_phiDia θ]
  intro h
  have hcons : ¬ Md.force (0 : Fin 4)
      ((oBot.and θ).or (oBot.and (θ.ifThen .falsePLL))) := by
    rintro (⟨hb, -⟩ | ⟨hb, -⟩) <;> exact Md_not_oBot_zero hb
  refine hcons (h 0 (Rd_refl 0) ?_)
  by_cases hone : Md.force (1 : Fin 4) θ
  · refine Or.inl ?_
    have h2 : Md.force (2 : Fin 4) θ := (Md_swap12 hθ).mp hone
    have h3 : Md.force (3 : Fin 4) θ :=
      Md.force_of_fallible (show (3 : Fin 4) ∈ Md.F from rfl)
    intro u _ hb
    rcases Fin4_cases u with rfl | rfl | rfl | rfl
    · exact absurd hb Md_not_oBot_zero
    · exact hone
    · exact h2
    · exact h3
  · refine Or.inr (Or.inr ?_)
    have h2 : ¬ Md.force (2 : Fin 4) θ := fun hh => hone ((Md_swap12 hθ).mpr hh)
    have h0 : ¬ Md.force (0 : Fin 4) θ := fun hh =>
      hone (Md.force_hered (show Md.Ri 0 1 by decide) hh)
    intro u _ hu
    rcases Fin4_cases u with rfl | rfl | rfl | rfl
    · exact absurd hu h0
    · exact absurd hu hone
    · exact absurd hu h2
    · rfl

/-! ## 5.  Every guarded stretch fails at the root -/

/-- **The heart of the refutation.**  For EVERY guard `χ` — variable-free
or not — `φ♦` fails at the ground copy of the root in the `χ`-guarded
stretch of `M♦`. -/
theorem Md_gstretch_fails (χ : PLLFormula) :
    ¬ (gstretch Md χ).force (Sum.inl (0 : Fin 4)) phiDia := by
  classical
  intro h
  by_cases h1 : Md.force (1 : Fin 4) χ
  · -- the upper copy of `1` is attached: `¬p` fails at `inl 1`
    have hante : (gstretch Md χ).force (Sum.inl (1 : Fin 4))
        ((oBot.ifThen (PLLFormula.prop pv)).or (oBot.or (nt (PLLFormula.prop pv)))) :=
      Or.inr (Or.inl ((gstretch_transfer (C := Md) (χ := χ) atomFree_oBot 1).1.mpr
        (Md_oBot_ne_zero 1 (by decide))))
    have hcons := h (Sum.inl (1 : Fin 4)) (show Rd 0 1 by decide) hante
    rcases hcons with ⟨-, hp⟩ | ⟨-, hnp⟩
    · have hp' : (1 : Fin 4) = 3 := hp
      exact absurd hp' (by decide)
    · have hbad : (1 : Fin 4) = 3 :=
        hnp (Sum.inr (1 : Fin 4)) ⟨Rd_refl 1, h1⟩ trivial
      exact absurd hbad (by decide)
  · by_cases h2 : Md.force (2 : Fin 4) χ
    · -- symmetrically at `inl 2`
      have hante : (gstretch Md χ).force (Sum.inl (2 : Fin 4))
          ((oBot.ifThen (PLLFormula.prop pv)).or
            (oBot.or (nt (PLLFormula.prop pv)))) :=
        Or.inr (Or.inl ((gstretch_transfer (C := Md) (χ := χ) atomFree_oBot 2).1.mpr
          (Md_oBot_ne_zero 2 (by decide))))
      have hcons := h (Sum.inl (2 : Fin 4)) (show Rd 0 2 by decide) hante
      rcases hcons with ⟨-, hp⟩ | ⟨-, hnp⟩
      · have hp' : (2 : Fin 4) = 3 := hp
        exact absurd hp' (by decide)
      · have hbad : (2 : Fin 4) = 3 :=
          hnp (Sum.inr (2 : Fin 4)) ⟨Rd_refl 2, h2⟩ trivial
        exact absurd hbad (by decide)
    · -- the upper layer is attached only over the fallible world:
      -- `¬p` holds at `inl 0`, but `◯⊥` does not
      have h0 : ¬ Md.force (0 : Fin 4) χ := fun hh =>
        h1 (Md.force_hered (show Md.Ri 0 1 by decide) hh)
      have hante : (gstretch Md χ).force (Sum.inl (0 : Fin 4))
          ((oBot.ifThen (PLLFormula.prop pv)).or
            (oBot.or (nt (PLLFormula.prop pv)))) := by
        refine Or.inr (Or.inr ?_)
        rintro (y | y) hq hp
        · exact hp
        · have hy3 : y = 3 := by
            rcases Fin4_cases y with rfl | rfl | rfl | rfl
            · exact absurd hq.2 h0
            · exact absurd hq.2 h1
            · exact absurd hq.2 h2
            · rfl
          subst hy3
          exact (rfl : (3 : Fin 4) = 3)
      have hcons := h (Sum.inl (0 : Fin 4)) (Rd_refl 0) hante
      rcases hcons with ⟨hb, -⟩ | ⟨hb, -⟩ <;>
        exact Md_not_oBot_zero ((gstretch_transfer (C := Md) (χ := χ) atomFree_oBot 0).1.mp hb)

/-- **Every guarded stretch bound fails at the root of `M♦`.** -/
theorem Md_LoG_fails (χ : PLLFormula) : ¬ Md.force (0 : Fin 4) (LoG χ phiDia) :=
  fun h => Md_gstretch_fails χ ((gstretch_tr (C := Md) (χ := χ) phiDia 0).1.mpr h)

/-- The `◯⊥`-guarded case: the `phistar.lean` stretch bound itself. -/
theorem Md_Lo_fails : ¬ Md.force (0 : Fin 4) (Lo phiDia) := by
  have h := Md_LoG_fails oBot
  rwa [LoG_oBot] at h

/-! ## 6.  The refutations -/

theorem Md_root_not_fallible : ¬ Md.force (0 : Fin 4) PLLFormula.falsePLL := by
  intro h
  have h' : (0 : Fin 4) = 3 := h
  exact absurd h' (by decide)

/-- **`φ♦` has NO guarded mixed cover.** -/
theorem phiDia_no_guardedMixedCover : ¬ HasGuardedMixedCover phiDia :=
  not_hasGuardedMixedCover_of_model Md 0 Md_force_phiDia Md_root_not_fallible
    (fun χ _ => Md_LoG_fails χ) (fun _ hθ => Md_inst_fails hθ)

/-- **REFUTED: `GuardedMixedConj`.**  Not even the whole family of
guarded stretch bounds, joined with all variable-free substitution
instances, exhausts every one-variable formula. -/
theorem guardedMixedConj_false : ¬ GuardedMixedConj :=
  fun h => phiDia_no_guardedMixedCover (h phiDia phiDia_onlyPv)

/-- **`φ♦` has NO mixed cover.** -/
theorem phiDia_no_mixedCover : ¬ HasMixedCover phiDia :=
  fun h => phiDia_no_guardedMixedCover (hasGuardedMixedCover_of_mixed h)

/-- **REFUTED: `MixedCoverConj`** — the conjecture left open by
`wip/phistar.lean`, and with it the reduction
`postUI_of_mixedCoverConj`. -/
theorem mixedCoverConj_false : ¬ MixedCoverConj :=
  fun h => phiDia_no_mixedCover (h phiDia phiDia_onlyPv)

/-- A fortiori the two single methods fail at `φ♦` as well. -/
theorem phiDia_no_cover : ¬ HasCover phiDia :=
  fun h => phiDia_no_mixedCover (hasMixedCover_of_cover h)

theorem phiDia_no_stretchCover : ¬ HasStretchCover phiDia :=
  fun h => phiDia_no_mixedCover (hasMixedCover_of_stretch h)

/-- `φ♦` is consistent. -/
theorem phiDia_consistent : ¬ Deriv [phiDia] PLLFormula.falsePLL := by
  rintro ⟨d⟩
  refine Md_root_not_fallible (soundness d Md 0 ?_)
  intro ψ hψ
  have e : ψ = phiDia := by
    cases hψ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact Md_force_phiDia

/-- `φ♦ ⊬ ◯⊥`. -/
theorem phiDia_not_oBot : ¬ Deriv [phiDia] oBot := by
  rintro ⟨d⟩
  refine Md_not_oBot_zero (soundness d Md 0 ?_)
  intro ψ hψ
  have e : ψ = phiDia := by
    cases hψ with
    | head => rfl
    | tail _ hh => cases hh
  subst e
  exact Md_force_phiDia

/-! ## 7.  What is left OPEN -/

/-- **OPEN.**  Does `φ♦` have a uniform post-interpolant over the
variable-free fragment at all?  Neither method can produce one. -/
def PostInterpPhiDiaExists : Prop := ∃ ψ, IsPostInterp phiDia ψ

/-- **OPEN.**  Is it `⊤`?  In `M♦` the variable-free truth sets are
`{⊥, ◯⊥, ⊤}` and only `⊤` contains the root, so no other candidate
survives that model. -/
def PostInterpPhiDiaIsTop : Prop := IsPostInterp phiDia truePLL

/-- The candidate `⊤` reduces to: every variable-free consequence of
`φ♦` is a theorem. -/
theorem postInterpPhiDiaIsTop_iff :
    PostInterpPhiDiaIsTop ↔
      ∀ χ, atomFree χ = true → Deriv [phiDia] χ → Deriv [] χ := by
  constructor
  · intro h χ hχ hd
    exact Deriv.cutHead (topD : Deriv [] truePLL) (h.2.2 χ hχ hd)
  · intro h
    exact ⟨rfl, topD, fun χ hχ hd => (h χ hχ hd).rename (by simp)⟩

/-! ## 8.  Axiom audit -/

/-- info: 'PLLND.RNEmbed.Md_swap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Md_swap

/-- info: 'PLLND.RNEmbed.Md_force_phiDia' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Md_force_phiDia

/-- info: 'PLLND.RNEmbed.Md_inst_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Md_inst_fails

/-- info: 'PLLND.RNEmbed.Md_gstretch_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Md_gstretch_fails

/-- info: 'PLLND.RNEmbed.Md_LoG_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Md_LoG_fails

/-- info: 'PLLND.RNEmbed.phiDia_no_guardedMixedCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiDia_no_guardedMixedCover

/-- info: 'PLLND.RNEmbed.guardedMixedConj_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guardedMixedConj_false

/-- info: 'PLLND.RNEmbed.mixedCoverConj_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixedCoverConj_false

/-- info: 'PLLND.RNEmbed.phiDia_consistent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms phiDia_consistent

/-! ## Integration addendum: `⊤` is EXCLUDED, not forced — the successor
question is `∃p.φ♦ =? ¬¬◯⊥`

The remark above §"PostInterpPhiDiaIsTop" inferred from `M♦` that `⊤`
is the only candidate value.  That inference is wrong: `M♦` only shows
any interpolant is ⊤-VALUED ON `M♦`, and `¬¬◯⊥` also has full truth
set there (no world of `M♦` forces `¬◯⊥`).  In fact the same two-line
argument as for `φ★` gives `φ♦ ⊢ ¬¬◯⊥` — assume `¬◯⊥`; then
`◯⊥ ⊃ p` holds vacuously, the antecedent's first disjunct fires, and
either disjunct of the consequent yields `◯⊥`, contradiction — so any
uniform post-interpolant of `φ♦` lies BELOW `¬¬◯⊥` and `⊤` is
excluded.  The live question after `guardedMixedConj_false` is
therefore exactly the `φ★`-shape question one construction further
out: `∃p.φ♦ =? ¬¬◯⊥`, now beyond the reach of every guarded
two-layer stretch. -/

/-- **`φ♦ ⊢ ¬¬◯⊥`** — same mechanism as `phiStar_nnbox`. -/
theorem phiDia_nnbox : Deriv [phiDia] (nt (nt oBot)) := by
  refine Deriv.impIntro ?_
  have hp : Deriv [nt oBot, phiDia] (oBot.ifThen (PLLFormula.prop pv)) :=
    Deriv.impIntro (Deriv.falsoElim _
      (Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))))
  have hcons : Deriv [nt oBot, phiDia]
      ((oBot.and (PLLFormula.prop pv)).or (oBot.and (nt (PLLFormula.prop pv)))) :=
    Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.orIntro1 hp)
  refine Deriv.orElim hcons ?_ ?_
  · exact Deriv.impElim (Deriv.iden (.tail _ (.head _)))
      (Deriv.andElim1 (Deriv.iden (.head _)))
  · exact Deriv.impElim (Deriv.iden (.tail _ (.head _)))
      (Deriv.andElim1 (Deriv.iden (.head _)))

/-- **`∃p.φ♦ ≠ ⊤`**: `¬¬◯⊥` is a non-theorem variable-free consequence
of `φ♦`, so `⊤` is not minimal. -/
theorem postInterpPhiDiaIsTop_false : ¬ PostInterpPhiDiaIsTop := by
  rintro ⟨-, -, hmin⟩
  exact postInterp_phiStar_ne_top
    (Deriv.cutHead topD (hmin (nt (nt oBot)) rfl phiDia_nnbox))

/-- info: 'PLLND.RNEmbed.phiDia_nnbox' does not depend on any axioms -/
#guard_msgs in
#print axioms phiDia_nnbox

/-- info: 'PLLND.RNEmbed.postInterpPhiDiaIsTop_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms postInterpPhiDiaIsTop_false

end RNEmbed
end PLLND
