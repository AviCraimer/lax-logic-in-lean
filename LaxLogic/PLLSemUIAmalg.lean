import LaxLogic.PLLSemUIOFree

/-!
# The amalgamation reduction: ◯-free definability in ALL variables

The one-variable fragment theorem (`ofree_semAll_definable`) is here
generalised to the SKELETON of the induction over propositional
variables that Matthew proposed: for a ◯-free M in ANY variables and
a candidate value ψ, the PLL semantic spec reduces to

  (i)  two derivability facts ([ψ] ⊢ M resp. [M] ⊢ ψ, with ψ p-free
       and ◯-free), and
  (ii) a purely IPC-side amalgamation property over fallibility-free
       models (`FlatAmalgAll` / `FlatAmalgEx`).

So the whole variable-induction lives INSIDE IPC: proving (ii) for
Pitts's interpolants (e.g. the mechanised `uniform_interpolation_IPC`
values) at each variable count yields `IsSemAll p M ψ` over full PLL
constraint models — fallibility and the ◯-machinery are discharged
once and for all by the two reduction lemmas.

The new construction is `relGraft`: the graft ALONG A BISIMULATION.
Given `B₀ : PBisim p (flatten C) K`, fibre the flat model K over C
with one world (x, k) for every B₀-RELATED pair — the fibres follow
the bisimulation, so every atom q ≠ p agrees pointwise between the
two coordinates (`B₀.atoms`), while p is read from K.  Fibres never
return to the base except into its fallible part (which forces
everything and so constrains nothing).  Then:

* `relGraft_pbisim` — base-identity ∪ projection is a p-bisimulation
  C → relGraft: the graft is a p-variant of C;
* `relGraft_force_iff` — a fibre forces a ◯-free θ (ANY atoms) iff K
  does at its K-coordinate;
* `isSemAll_of_flatAmalg` / `isSemEx_of_flatAmalgEx` — the reduction
  theorems;
* `flatAmalgAll_bot` — the one-variable case IS an instance: the
  fixed-countermodel graft of `PLLSemUIOFree` discharges
  `FlatAmalgAll p M ⊥`, and the reduction re-derives
  `semAll_ofree_bot`.  Matthew's "both steps might collapse to one":
  the base case is the skeleton applied to the constant family.

OPEN (the genuine IPC content, where the induction lives):
`FlatAmalgAll p M (Pitts ∀p.M)` for multi-variable ◯-free M — the
semantic amalgamation property of the IPC uniform interpolant,
provable in principle by Ghilardi-style bounded-bisimulation
descriptions over the finite canonical model.
-/

open PLLFormula

namespace PLLND
namespace SemUI

/-! ## The graft along a bisimulation -/

section RelGraft

variable (C K : ConstraintModel) (p : String)
variable (B₀ : PBisim p (flatten C) K)

/-- Fibre worlds: B₀-related pairs (the base coordinate non-fallible,
so it names a world of `flatten C`). -/
def RelFib : Type :=
  {q : C.W × K.W // ∃ h : q.1 ∉ C.F, B₀.Z ⟨q.1, h⟩ q.2}

/-- The graft frame: fibres above the base cone of their base
coordinate, following BOTH coordinates upward; fibres re-enter the
base only at fallible worlds; constraint arrows likewise. -/
def relGraftBase : ConstraintModel where
  W := C.W ⊕ RelFib C K p B₀
  Ri := fun a b =>
    match a, b with
    | .inl y, .inl y' => C.Ri y y'
    | .inl y, .inr q => C.Ri y q.1.1
    | .inr q, .inl y => C.Ri q.1.1 y ∧ y ∈ C.F
    | .inr q, .inr q' => C.Ri q.1.1 q'.1.1 ∧ K.Ri q.1.2 q'.1.2
  Rm := fun a b =>
    match a, b with
    | .inl y, .inl y' => C.Rm y y'
    | .inl _, .inr _ => False
    | .inr q, .inl y => C.Rm q.1.1 y ∧ y ∈ C.F
    | .inr q, .inr q' => C.Rm q.1.1 q'.1.1 ∧ K.Rm q.1.2 q'.1.2
  F := fun a => match a with
    | .inl y => y ∈ C.F
    | .inr _ => False
  V := fun a b => match b with
    | .inl y => y ∈ C.V a
    | .inr q => q.1.1 ∈ C.V a
  refl_i := by
    intro a
    rcases a with y | q
    · exact C.refl_i y
    · exact ⟨C.refl_i q.1.1, K.refl_i q.1.2⟩
  trans_i := by
    intro a b c h₁ h₂
    rcases a with y | q <;> rcases b with y' | q' <;> rcases c with y'' | q''
    · exact C.trans_i h₁ h₂
    · exact C.trans_i h₁ h₂
    · exact C.trans_i h₁ h₂.1
    · exact C.trans_i h₁ h₂.1
    · exact ⟨C.trans_i h₁.1 h₂, C.hered_F h₂ h₁.2⟩
    · obtain ⟨hx'', -⟩ := q''.2
      exact absurd (C.hered_F h₂ h₁.2) hx''
    · exact ⟨C.trans_i h₁.1 h₂.1, h₂.2⟩
    · exact ⟨C.trans_i h₁.1 h₂.1, K.trans_i h₁.2 h₂.2⟩
  refl_m := by
    intro a
    rcases a with y | q
    · exact C.refl_m y
    · exact ⟨C.refl_m q.1.1, K.refl_m q.1.2⟩
  trans_m := by
    intro a b c h₁ h₂
    rcases a with y | q <;> rcases b with y' | q' <;> rcases c with y'' | q''
    · exact C.trans_m h₁ h₂
    · exact h₂.elim
    · exact h₁.elim
    · exact h₁.elim
    · exact ⟨C.trans_m h₁.1 h₂, C.hered_F (C.sub_mi h₂) h₁.2⟩
    · exact h₂.elim
    · exact ⟨C.trans_m h₁.1 h₂.1, h₂.2⟩
    · exact ⟨C.trans_m h₁.1 h₂.1, K.trans_m h₁.2 h₂.2⟩
  sub_mi := by
    intro a b h
    rcases a with y | q <;> rcases b with y' | q'
    · exact C.sub_mi h
    · exact h.elim
    · exact ⟨C.sub_mi h.1, h.2⟩
    · exact ⟨C.sub_mi h.1, K.sub_mi h.2⟩
  hered_F := by
    intro a b h hF
    rcases a with y | q <;> rcases b with y' | q'
    · exact C.hered_F h hF
    · obtain ⟨hx', -⟩ := q'.2
      exact absurd (C.hered_F h hF) hx'
    · exact hF.elim
    · exact hF.elim
  hered_V := by
    intro a x y h hV
    rcases x with y' | q <;> rcases y with y'' | q'
    · exact C.hered_V h hV
    · exact C.hered_V h hV
    · exact C.hered_V h.1 hV
    · exact C.hered_V h.1 hV
  full_F := by
    intro a x hF
    rcases x with y | q
    · exact C.full_F hF
    · exact hF.elim

/-- The graft decoration for `p`: K's decoration on the fibres, the
fallible worlds on the base. -/
def relGraftSet : Set (relGraftBase C K p B₀).W :=
  fun b => match b with
    | .inl y => y ∈ C.F
    | .inr q => q.1.2 ∈ K.V p

theorem relGraftSet_hered :
    ∀ {a b}, (relGraftBase C K p B₀).Ri a b → a ∈ relGraftSet C K p B₀ →
      b ∈ relGraftSet C K p B₀ := by
  intro a b h hS
  rcases a with y | q <;> rcases b with y' | q'
  · exact C.hered_F h hS
  · obtain ⟨hx', -⟩ := q'.2
    exact absurd (C.hered_F h hS) hx'
  · exact h.2
  · exact K.hered_V h.2 hS

theorem relGraftSet_full :
    ∀ {a}, a ∈ (relGraftBase C K p B₀).F → a ∈ relGraftSet C K p B₀ := by
  intro a hF
  rcases a with y | q
  · exact hF
  · exact hF.elim

/-- The graft: `p` redecorated on `relGraftSet`. -/
def relGraft : ConstraintModel :=
  redecorate (relGraftBase C K p B₀) p (relGraftSet C K p B₀)
    (relGraftSet_hered C K p B₀) (relGraftSet_full C K p B₀)

/-- **The graft is a p-variant of the base**: base-identity ∪
projection to the base coordinate. -/
def relGraft_pbisim : PBisim p C (relGraft C K p B₀) where
  Z := fun c b => match b with
    | .inl y => y = c
    | .inr q => q.1.1 = c
  atoms := by
    intro c b hZ q hq
    rcases b with y | ⟨⟨x, k⟩, hq'⟩
    · obtain rfl : y = c := hZ
      show y ∈ C.V q ↔ _ ∈ (if q = p then relGraftSet C K p B₀
        else (relGraftBase C K p B₀).V q)
      rw [if_neg hq]
      exact Iff.rfl
    · obtain rfl : x = c := hZ
      show x ∈ C.V q ↔ _ ∈ (if q = p then relGraftSet C K p B₀
        else (relGraftBase C K p B₀).V q)
      rw [if_neg hq]
      exact Iff.rfl
  fall := by
    intro c b hZ
    rcases b with y | ⟨⟨x, k⟩, hq⟩
    · obtain rfl : y = c := hZ
      exact Iff.rfl
    · obtain rfl : x = c := hZ
      obtain ⟨hx, -⟩ := hq
      exact iff_of_false hx (fun h => h)
  iforth := by
    intro c b hZ v hv
    rcases b with y | ⟨⟨x, k⟩, hq⟩
    · obtain rfl : y = c := hZ
      exact ⟨.inl v, hv, rfl⟩
    · obtain rfl : x = c := hZ
      obtain ⟨hx, hZ₀⟩ := hq
      by_cases hvF : v ∈ C.F
      · exact ⟨.inl v, ⟨hv, hvF⟩, rfl⟩
      · obtain ⟨k', hk', hZ'⟩ := B₀.iforth hZ₀ (show (flatten C).Ri ⟨x, hx⟩ ⟨v, hvF⟩ from hv)
        exact ⟨.inr ⟨(v, k'), hvF, hZ'⟩, ⟨hv, hk'⟩, rfl⟩
  iback := by
    intro c b hZ b' hb'
    rcases b with y | ⟨⟨x, k⟩, hq⟩
    · obtain rfl : y = c := hZ
      rcases b' with y' | ⟨⟨x', k'⟩, hq'⟩
      · exact ⟨y', hb', rfl⟩
      · exact ⟨x', hb', rfl⟩
    · obtain rfl : x = c := hZ
      rcases b' with y' | ⟨⟨x', k'⟩, hq'⟩
      · exact ⟨y', hb'.1, rfl⟩
      · exact ⟨x', hb'.1, rfl⟩
  mforth := by
    intro c b hZ u hu
    rcases b with y | ⟨⟨x, k⟩, hq⟩
    · obtain rfl : y = c := hZ
      exact ⟨.inl u, hu, rfl⟩
    · obtain rfl : x = c := hZ
      obtain ⟨hx, hZ₀⟩ := hq
      by_cases huF : u ∈ C.F
      · exact ⟨.inl u, ⟨hu, huF⟩, rfl⟩
      · obtain ⟨k', hk', hZ'⟩ := B₀.mforth hZ₀ (show (flatten C).Rm ⟨x, hx⟩ ⟨u, huF⟩ from hu)
        exact ⟨.inr ⟨(u, k'), huF, hZ'⟩, ⟨hu, hk'⟩, rfl⟩
  mback := by
    intro c b hZ b' hb'
    rcases b with y | ⟨⟨x, k⟩, hq⟩
    · obtain rfl : y = c := hZ
      rcases b' with y' | ⟨⟨x', k'⟩, hq'⟩
      · exact ⟨y', hb', rfl⟩
      · exact hb'.elim
    · obtain rfl : x = c := hZ
      rcases b' with y' | ⟨⟨x', k'⟩, hq'⟩
      · exact ⟨y', hb'.1, rfl⟩
      · exact ⟨x', hb'.1, rfl⟩

/-- **A fibre forces a ◯-free formula iff K does at its K-coordinate**
— any atoms: q ≠ p agrees pointwise across the fibre by `B₀.atoms`,
p is read from K, fallible base re-entries never constrain an
implication. -/
theorem relGraft_force_iff (hKF : ∀ a, a ∉ K.F) :
    ∀ {θ : PLLFormula}, boxFree θ = true →
    ∀ (x : C.W) (k : K.W) (hx : x ∉ C.F) (hZ₀ : B₀.Z ⟨x, hx⟩ k),
    ((relGraft C K p B₀).force (.inr ⟨(x, k), hx, hZ₀⟩) θ ↔ K.force k θ) := by
  intro θ
  induction θ with
  | prop a =>
      intro _ x k hx hZ₀
      by_cases ha : a = p
      · show _ ∈ (if a = p then relGraftSet C K p B₀
          else (relGraftBase C K p B₀).V a) ↔ _
        rw [if_pos ha, ha]
        exact Iff.rfl
      · show _ ∈ (if a = p then relGraftSet C K p B₀
          else (relGraftBase C K p B₀).V a) ↔ _
        rw [if_neg ha]
        exact B₀.atoms hZ₀ a ha
  | falsePLL =>
      intro _ x k hx hZ₀
      exact iff_of_false (fun h => h) (hKF k)
  | and φ ψ ihφ ihψ =>
      intro h x k hx hZ₀
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [ConstraintModel.force]
      exact and_congr (ihφ h.1 x k hx hZ₀) (ihψ h.2 x k hx hZ₀)
  | or φ ψ ihφ ihψ =>
      intro h x k hx hZ₀
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [ConstraintModel.force]
      exact or_congr (ihφ h.1 x k hx hZ₀) (ihψ h.2 x k hx hZ₀)
  | ifThen φ ψ ihφ ihψ =>
      intro h x k hx hZ₀
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [ConstraintModel.force]
      constructor
      · intro hf k' hk' hφ
        obtain ⟨v, hv, hZ'⟩ := B₀.iback hZ₀ hk'
        obtain ⟨v₀, hv₀⟩ := v
        exact (ihψ h.2 v₀ k' hv₀ hZ').mp
          (hf (.inr ⟨(v₀, k'), hv₀, hZ'⟩) ⟨hv, hk'⟩
            ((ihφ h.1 v₀ k' hv₀ hZ').mpr hφ))
      · intro hf b hb hφ
        rcases b with y | ⟨⟨x', k'⟩, hq'⟩
        · exact (relGraft C K p B₀).force_of_fallible hb.2
        · obtain ⟨hx', hZ'⟩ := hq'
          exact (ihψ h.2 x' k' hx' hZ').mpr
            (hf k' hb.2 ((ihφ h.1 x' k' hx' hZ').mp hφ))
  | somehow φ ih =>
      intro h
      exact absurd h (by simp [boxFree])

end RelGraft

/-! ## The reduction theorems -/

/-- **Flat amalgamation, ∀-side** — the IPC-side content: every
fallibility-free world refuting ψ has a future with a p-variant
(over fallibility-free models) refuting M. -/
def FlatAmalgAll (p : String) (M ψ : PLLFormula) : Prop :=
  ∀ (K : ConstraintModel), (∀ a, a ∉ K.F) → ∀ k : K.W, ¬ K.force k ψ →
    ∃ v, K.Ri k v ∧
      ∃ (K' : ConstraintModel) (B : PBisim p K K') (k' : K'.W),
        (∀ a, a ∉ K'.F) ∧ B.Z v k' ∧ ¬ K'.force k' M

/-- **Flat amalgamation, ∃-side**: every fallibility-free world
forcing ψ has a p-variant (over fallibility-free models) forcing M. -/
def FlatAmalgEx (p : String) (M ψ : PLLFormula) : Prop :=
  ∀ (K : ConstraintModel), (∀ a, a ∉ K.F) → ∀ k : K.W, K.force k ψ →
    ∃ (K' : ConstraintModel) (B : PBisim p K K') (k' : K'.W),
      (∀ a, a ∉ K'.F) ∧ B.Z k k' ∧ K'.force k' M

/-- `flatten` is fallibility-free. -/
theorem flatten_flat (C : ConstraintModel) : ∀ a, a ∉ (flatten C).F :=
  fun _ h => h

/-- **The ∀-side reduction**: for ◯-free M, a p-free ◯-free ψ with
`[ψ] ⊢ M` and flat amalgamation SATISFIES the semantic spec — the
whole variable-induction reduces to IPC. -/
theorem isSemAll_of_flatAmalg {p : String} {M ψ : PLLFormula}
    (hMbf : boxFree M = true) (hψbf : boxFree ψ = true)
    (hψp : p ∉ ψ.atoms) (hlow : Nonempty (LaxND [ψ] M))
    (hamalg : FlatAmalgAll p M ψ) : IsSemAll p M ψ := by
  obtain ⟨dlow⟩ := hlow
  have hAψ : ∀ a ∈ ψ.atoms, a ≠ p := fun a ha he => hψp (he ▸ ha)
  refine ⟨hψp, ?_⟩
  intro C w
  constructor
  · intro hw v hv N B v' hZ
    have hψ' : N.force v' ψ :=
      (force_iff_of_bisim B hAψ hZ).mp (C.force_hered hv hw)
    exact soundness dlow N v' (fun χ hχ => by
      simp only [List.mem_singleton] at hχ
      exact hχ ▸ hψ')
  · intro h'
    by_contra hnw
    have hwF : w ∉ C.F := fun hF => hnw (C.force_of_fallible hF)
    have hK₀ : ¬ (flatten C).force ⟨w, hwF⟩ ψ :=
      fun h => hnw ((flatten_force_iff C hψbf w hwF).mp h)
    obtain ⟨⟨v₀, hv₀⟩, hkv, K', B₀, k', hK'F, hZ₀, hk'M⟩ :=
      hamalg (flatten C) (flatten_flat C) ⟨w, hwF⟩ hK₀
    have hforce := h' v₀ hkv (relGraft C K' p B₀)
      (relGraft_pbisim C K' p B₀) (.inr ⟨(v₀, k'), hv₀, hZ₀⟩) rfl
    exact hk'M
      ((relGraft_force_iff C K' p B₀ hK'F hMbf v₀ k' hv₀ hZ₀).mp hforce)

/-- **The ∃-side reduction**: for ◯-free M, a p-free ◯-free ψ with
`[M] ⊢ ψ` and flat ∃-amalgamation satisfies the semantic spec. -/
theorem isSemEx_of_flatAmalgEx {p : String} {M ψ : PLLFormula}
    (hMbf : boxFree M = true) (hψbf : boxFree ψ = true)
    (hψp : p ∉ ψ.atoms) (hup : Nonempty (LaxND [M] ψ))
    (hamalg : FlatAmalgEx p M ψ) : IsSemEx p M ψ := by
  obtain ⟨dup⟩ := hup
  have hAψ : ∀ a ∈ ψ.atoms, a ≠ p := fun a ha he => hψp (he ▸ ha)
  refine ⟨hψp, ?_⟩
  intro C w
  constructor
  · intro hw
    by_cases hwF : w ∈ C.F
    · exact ⟨C, ABisim.id _ C, w, rfl, C.force_of_fallible hwF⟩
    · have hK₀ : (flatten C).force ⟨w, hwF⟩ ψ :=
        (flatten_force_iff C hψbf w hwF).mpr hw
      obtain ⟨K', B₀, k', hK'F, hZ₀, hk'M⟩ :=
        hamalg (flatten C) (flatten_flat C) ⟨w, hwF⟩ hK₀
      exact ⟨relGraft C K' p B₀, relGraft_pbisim C K' p B₀,
        .inr ⟨(w, k'), hwF, hZ₀⟩, rfl,
        (relGraft_force_iff C K' p B₀ hK'F hMbf w k' hwF hZ₀).mpr hk'M⟩
  · rintro ⟨N, B, w', hZ, hM'⟩
    have hψ' : N.force w' ψ := soundness dup N w' (fun χ hχ => by
      simp only [List.mem_singleton] at hχ
      exact hχ ▸ hM')
    exact (force_iff_of_bisim B hAψ hZ).mpr hψ'

/-! ## The one-variable case is an instance -/

/-- The fixed-countermodel graft discharges the ∀-side amalgamation
for the value ⊥ on one-variable rows: the base case of the induction
is the skeleton applied to the constant family. -/
theorem flatAmalgAll_bot {p : String} {M : PLLFormula}
    (hMbf : boxFree M = true) (hat : ∀ a ∈ M.atoms, a = p)
    {D : ConstraintModel} (hDF : D.F = ∅) {d : D.W}
    (hd : ¬ D.force d M) : FlatAmalgAll p M .falsePLL := by
  intro K hKF k _
  refine ⟨k, K.refl_i k, ofreeGraft K D p, ofreeGraft_pbisim K D p,
    .inr (k, d), ?_, rfl, ?_⟩
  · intro a
    rcases a with y | xk
    · exact hKF y
    · exact hKF xk.1
  · intro hf
    exact hd ((ofreeGraft_force_iff K D p hDF hMbf hat k d (hKF k)).mp hf)

/-- `semAll_ofree_bot`, re-derived through the reduction: base case =
skeleton at the constant family. -/
theorem semAll_ofree_bot' {p : String} {M : PLLFormula}
    (hbf : boxFree M = true) (hat : ∀ a ∈ M.atoms, a = p)
    (hM : ¬ Nonempty (LaxND [] M)) : IsSemAll p M .falsePLL := by
  obtain ⟨D, d, hd⟩ := exists_refuting_world hM
  have hdF : d ∉ D.F := fun hF => hd (D.force_of_fallible hF)
  have hDflat : (flatten D).F = ∅ := rfl
  have hKd : ¬ (flatten D).force ⟨d, hdF⟩ M :=
    fun h => hd ((flatten_force_iff D hbf d hdF).mp h)
  refine isSemAll_of_flatAmalg hbf rfl (by simp) ?_ ?_
  · exact completeness (fun N v hv =>
      (N.force_of_fallible (hv PLLFormula.falsePLL (by simp))))
  · exact flatAmalgAll_bot hbf hat hDflat hKd

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SemUI.isSemAll_of_flatAmalg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isSemAll_of_flatAmalg

/--
info: 'PLLND.SemUI.semAll_ofree_bot'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms semAll_ofree_bot'

end SemUI
end PLLND
