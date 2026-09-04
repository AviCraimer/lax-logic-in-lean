import wip.depth

/-!
# The `◯`-depth hierarchy of RN(◯,{}) does NOT collapse at depth 2

The witness is exactly the commission's sharpest instance, `◯g 1`, and the
instrument is ONE seven-world Fairtlough–Mendler constraint model `M7`.

## The instrument

For any constraint model the truth sets of formulas form a Heyting algebra
(the upsets containing the fallible set `F`, with `⊥` read as `F`), and `◯`
acts on it as a nucleus.  Fix the valuation `V a = F` for every atom, so that
atoms carry no more information than `⊥`.  Write

    L0 = the truth sets of formulas with `boxDepth ≤ 0`
    L1 = the truth sets of formulas with `boxDepth ≤ 1`
    L2 = the truth sets of formulas with `boxDepth ≤ 2`

Each `Ln` is given in `M7` as an EXPLICIT finite list (`L0list`, `L1list`,
`L2list` — 2, 5 and 8 sets), and `tv_mem0/1/2` prove by induction on the
formula that every formula of that syntactic depth lands in it.  Only that
INCLUSION is machine-checked, which is the direction the lower bounds need;
the lists were computed to be exactly the three layers, but their exactness
is not claimed here.
Interderivable formulas have equal truth sets (`interd_tv`, through the
repository's own `PLLND.soundness`), so a formula whose truth set is OUTSIDE
`L2list` has class depth at least 3 — a statement about ALL formulas of depth
≤ 2 at once, which no finite battery of pairwise separations could deliver.

## The model

Worlds `0..6`; `Rᵢ` and `Rₘ` as tabulated in `riRow` / `rmRow`; `F = {3}`.
The ladder evaluates to

    t0 = {3}   t1 = {2,3}   t2 = {3,5}   t3 = {2,3,5}   t4 = {2,3}
    t5 = {2,3,5}   t6 = ⊤   t7 = ⊤   t8 = {2,3,5}   t m = ⊤ for m ≥ 9

so `L1list = [{3}, {2,3}, {3,5}, {2,3,5}, ⊤]`, and boxing `L1list` adds
`c 1 = ◯t3 = {2,3,5,6}`, whose Heyting closure with `L1list` is the eight-set
`L2list`.  Then

    g 1 = ◯t3 ⊃ t3 = {1,2,3,5}   ∈ L2list
    ◯g 1                = {1,2,3,4,5,6}   ∉ L2list

## What is PROVED here

* `not_depthLe_two_box_gap_one` : `¬ DepthLe 2 (◯ g 1)` — **collapse at
  depth 2 is REFUTED**, with `◯g 1` the witness.
* `depth_box_gap_one_exact` : the class depth of `◯g 1` is EXACTLY 3.
* `not_depthLe_one_*` : `c 1`, `g 1`, `s 1`, `r 1`, `w 1` have class depth
  exactly 2 (the upper bounds are in `wip/depth.lean`).
* `not_depthLe_zero_rnSub_one` : `t 1 = ◯⊥` has class depth exactly 1.

Every lower bound has the same shape: a truth set outside the relevant
`Lnlist`.
-/

open PLLFormula

namespace PLLND
namespace Depth

open SemUI RNEmbed

/-! ## The seven-world constraint model `M7` -/

/-- `Rᵢ`-successors, tabulated. -/
def riRow (w : Fin 7) : List (Fin 7) :=
  match w.val with
  | 0 => [0, 1, 2, 3, 5, 6]
  | 1 => [1, 2, 3, 5]
  | 2 => [2, 3]
  | 3 => [3]
  | 4 => [1, 2, 3, 4, 5, 6]
  | 5 => [5]
  | _ => [2, 3, 5, 6]

/-- `Rₘ`-successors, tabulated. -/
def rmRow (w : Fin 7) : List (Fin 7) :=
  match w.val with
  | 0 => [0]
  | 1 => [1]
  | 2 => [2, 3]
  | 3 => [3]
  | 4 => [1, 4]
  | 5 => [5]
  | _ => [5, 6]

def riB (w v : Fin 7) : Bool := (riRow w).contains v
def rmB (w v : Fin 7) : Bool := (rmRow w).contains v

/-- The fallible set is the single world `3`. -/
def fB (w : Fin 7) : Bool := w.val == 3

theorem ri_refl : ∀ w : Fin 7, riB w w = true := by decide
theorem ri_trans : ∀ w v u : Fin 7, riB w v = true → riB v u = true → riB w u = true := by
  decide
theorem rm_refl : ∀ w : Fin 7, rmB w w = true := by decide
theorem rm_trans : ∀ w v u : Fin 7, rmB w v = true → rmB v u = true → rmB w u = true := by
  decide
theorem rm_sub_ri : ∀ w v : Fin 7, rmB w v = true → riB w v = true := by decide
theorem f_hered : ∀ w v : Fin 7, riB w v = true → fB w = true → fB v = true := by decide

/-- The seven-world model.  Atoms are valued at `F`, so they carry exactly the
information of `⊥`; every statement below therefore covers formulas WITH
atoms, not only closed ones. -/
def M7 : ConstraintModel where
  W := Fin 7
  Ri := fun w v => riB w v = true
  Rm := fun w v => rmB w v = true
  F := fun w => fB w = true
  V := fun _ w => fB w = true
  refl_i := ri_refl
  trans_i := fun {w v u} h₁ h₂ => ri_trans w v u h₁ h₂
  refl_m := rm_refl
  trans_m := fun {w v u} h₁ h₂ => rm_trans w v u h₁ h₂
  sub_mi := fun {w v} h => rm_sub_ri w v h
  hered_F := fun {w v} h₁ h₂ => f_hered w v h₁ h₂
  hered_V := fun {_ w v} h₁ h₂ => f_hered w v h₁ h₂
  full_F := fun {_ _} h => h

/-! ## Truth sets as a seven-`Bool` record

A record with structural `DecidableEq` keeps every `decide` in this file
inside `Bool` and `List`, away from `Finset`. -/

structure TS where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
deriving DecidableEq, Repr

namespace TS

def get (a : TS) (w : Fin 7) : Bool :=
  match w.val with
  | 0 => a.b0 | 1 => a.b1 | 2 => a.b2 | 3 => a.b3 | 4 => a.b4 | 5 => a.b5 | _ => a.b6

def ofFun (f : Fin 7 → Bool) : TS := ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6⟩

theorem get_ofFun (f : Fin 7 → Bool) (w : Fin 7) : (ofFun f).get w = f w := by
  match w with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl

theorem ext : ∀ {a b : TS}, (∀ w, a.get w = b.get w) → a = b
  | ⟨_, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _⟩, h => by
      have h0 : _ = _ := h 0
      have h1 : _ = _ := h 1
      have h2 : _ = _ := h 2
      have h3 : _ = _ := h 3
      have h4 : _ = _ := h 4
      have h5 : _ = _ := h 5
      have h6 : _ = _ := h 6
      simp only [get] at h0 h1 h2 h3 h4 h5 h6
      subst h0; subst h1; subst h2; subst h3; subst h4; subst h5; subst h6
      rfl

end TS

/-- The seven worlds, as a list, for kernel-cheap quantification. -/
def worlds : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

theorem mem_worlds : ∀ w : Fin 7, w ∈ worlds := by decide

theorem allW_iff (f : Fin 7 → Bool) : (worlds.all f) = true ↔ ∀ v, f v = true := by
  rw [List.all_eq_true]
  exact ⟨fun h v => h v (mem_worlds v), fun h v _ => h v⟩

theorem anyW_iff (f : Fin 7 → Bool) : (worlds.any f) = true ↔ ∃ v, f v = true := by
  rw [List.any_eq_true]
  exact ⟨fun ⟨v, _, h⟩ => ⟨v, h⟩, fun ⟨v, h⟩ => ⟨v, mem_worlds v, h⟩⟩

/-! ## The Heyting operations and the nucleus, on truth sets -/

def andT (a b : TS) : TS := TS.ofFun fun w => a.get w && b.get w
def orT (a b : TS) : TS := TS.ofFun fun w => a.get w || b.get w
def impT (a b : TS) : TS :=
  TS.ofFun fun w => worlds.all fun v => !riB w v || !a.get v || b.get v
def boxT (a : TS) : TS :=
  TS.ofFun fun w => worlds.all fun v => !riB w v || worlds.any fun u => rmB v u && a.get u
def botT : TS := TS.ofFun fB

/-- Truth-set evaluation, mirroring `ConstraintModel.force` on `M7`. -/
def tv : PLLFormula → TS
  | .prop _ => botT
  | .falsePLL => botT
  | .and A B => andT (tv A) (tv B)
  | .or A B => orT (tv A) (tv B)
  | .ifThen A B => impT (tv A) (tv B)
  | .somehow A => boxT (tv A)

/-- **The bridge**: `tv` computes the truth set of `force` in `M7`. -/
theorem tv_iff : ∀ (A : PLLFormula) (w : Fin 7), (tv A).get w = true ↔ M7.force w A := by
  intro A
  induction A with
  | prop a => intro w; rw [tv, botT, TS.get_ofFun]; exact Iff.rfl
  | falsePLL => intro w; rw [tv, botT, TS.get_ofFun]; exact Iff.rfl
  | and A B ihA ihB =>
      intro w
      rw [tv, andT, TS.get_ofFun, Bool.and_eq_true, ihA w, ihB w]
      exact Iff.rfl
  | or A B ihA ihB =>
      intro w
      rw [tv, orT, TS.get_ofFun, Bool.or_eq_true, ihA w, ihB w]
      exact Iff.rfl
  | ifThen A B ihA ihB =>
      intro w
      rw [tv, impT, TS.get_ofFun, allW_iff]
      constructor
      · intro h v hwv hA
        have hr : riB w v = true := hwv
        have ha : (tv A).get v = true := (ihA v).mpr hA
        have hv := h v
        rw [hr, ha] at hv
        simp only [Bool.not_true, Bool.false_or] at hv
        exact (ihB v).mp hv
      · intro h v
        cases hr : riB w v with
        | false => simp
        | true =>
            cases ha : (tv A).get v with
            | false => simp
            | true =>
                have : M7.force v B := h v hr ((ihA v).mp ha)
                simp [(ihB v).mpr this]
  | somehow A ih =>
      intro w
      rw [tv, boxT, TS.get_ofFun, allW_iff]
      constructor
      · intro h v hwv
        have hr : riB w v = true := hwv
        have hv := h v
        rw [hr] at hv
        simp only [Bool.not_true, Bool.false_or] at hv
        rw [anyW_iff] at hv
        obtain ⟨u, hu⟩ := hv
        rw [Bool.and_eq_true] at hu
        exact ⟨u, hu.1, (ih u).mp hu.2⟩
      · intro h v
        cases hr : riB w v with
        | false => simp
        | true =>
            obtain ⟨u, hvu, hu⟩ := h v hr
            have hany : (worlds.any fun u => rmB v u && (tv A).get u) = true := by
              rw [anyW_iff]
              exact ⟨u, by rw [Bool.and_eq_true]; exact ⟨hvu, (ih u).mpr hu⟩⟩
            simp [hany]

/-- Interderivable formulas have the SAME truth set in `M7`. -/
theorem interd_tv {A B : PLLFormula} (h : Interd A B) : tv A = tv B := by
  obtain ⟨p⟩ := h.1
  obtain ⟨q⟩ := h.2
  refine TS.ext fun w => ?_
  have hAB : M7.force w A → M7.force w B := fun hw =>
    PLLND.soundness p M7 w (by
      intro ψ hψ; cases hψ with | head => exact hw | tail _ hh => cases hh)
  have hBA : M7.force w B → M7.force w A := fun hw =>
    PLLND.soundness q M7 w (by
      intro ψ hψ; cases hψ with | head => exact hw | tail _ hh => cases hh)
  refine Bool.eq_iff_iff.mpr ?_
  rw [tv_iff A w, tv_iff B w]
  exact ⟨hAB, hBA⟩

/-! ## The three layers, computed -/

/-- `L0 = {⊥, ⊤}` — the truth sets of `◯`-free formulas. -/
def L0list : List TS :=
  [⟨false, false, false, true, false, false, false⟩,
   ⟨true, true, true, true, true, true, true⟩]

/-- `L1` — the ladder: `{3}`, `{2,3}`, `{3,5}`, `{2,3,5}`, `⊤`. -/
def L1list : List TS :=
  [⟨false, false, false, true, false, false, false⟩,
   ⟨false, false, true, true, false, false, false⟩,
   ⟨false, false, false, true, false, true, false⟩,
   ⟨false, false, true, true, false, true, false⟩,
   ⟨true, true, true, true, true, true, true⟩]

/-- `L2` — the ladder together with `c 1 = {2,3,5,6}`, `g 1 = {1,2,3,5}` and
their join `{1,2,3,5,6}`. -/
def L2list : List TS :=
  [⟨false, false, false, true, false, false, false⟩,
   ⟨false, false, true, true, false, false, false⟩,
   ⟨false, false, false, true, false, true, false⟩,
   ⟨false, false, true, true, false, true, false⟩,
   ⟨false, true, true, true, false, true, false⟩,
   ⟨false, false, true, true, false, true, true⟩,
   ⟨false, true, true, true, false, true, true⟩,
   ⟨true, true, true, true, true, true, true⟩]

/-! ### Closure of the layers, by kernel computation -/

theorem L0_closed :
    ∀ a ∈ L0list, ∀ b ∈ L0list,
      andT a b ∈ L0list ∧ orT a b ∈ L0list ∧ impT a b ∈ L0list := by decide

theorem L1_closed :
    ∀ a ∈ L1list, ∀ b ∈ L1list,
      andT a b ∈ L1list ∧ orT a b ∈ L1list ∧ impT a b ∈ L1list := by decide

theorem L2_closed :
    ∀ a ∈ L2list, ∀ b ∈ L2list,
      andT a b ∈ L2list ∧ orT a b ∈ L2list ∧ impT a b ∈ L2list := by decide

theorem L0_box : ∀ a ∈ L0list, boxT a ∈ L1list := by decide

theorem L1_box : ∀ a ∈ L1list, boxT a ∈ L2list := by decide

theorem bot_mem_L0 : botT ∈ L0list := by decide
theorem bot_mem_L1 : botT ∈ L1list := by decide
theorem bot_mem_L2 : botT ∈ L2list := by decide

/-! ### Every formula of syntactic depth ≤ n has its truth set in `Ln` -/

theorem tv_mem0 : ∀ A : PLLFormula, boxDepth A ≤ 0 → tv A ∈ L0list := by
  intro A
  induction A with
  | prop a => intro _; exact bot_mem_L0
  | falsePLL => intro _; exact bot_mem_L0
  | and A B ihA ihB =>
      intro h
      simp only [boxDepth_and, Nat.max_le] at h
      exact (L0_closed _ (ihA h.1) _ (ihB h.2)).1
  | or A B ihA ihB =>
      intro h
      simp only [boxDepth_or, Nat.max_le] at h
      exact (L0_closed _ (ihA h.1) _ (ihB h.2)).2.1
  | ifThen A B ihA ihB =>
      intro h
      simp only [boxDepth_imp, Nat.max_le] at h
      exact (L0_closed _ (ihA h.1) _ (ihB h.2)).2.2
  | somehow A _ => intro h; simp only [boxDepth_box] at h; omega

theorem tv_mem1 : ∀ A : PLLFormula, boxDepth A ≤ 1 → tv A ∈ L1list := by
  intro A
  induction A with
  | prop a => intro _; exact bot_mem_L1
  | falsePLL => intro _; exact bot_mem_L1
  | and A B ihA ihB =>
      intro h
      simp only [boxDepth_and, Nat.max_le] at h
      exact (L1_closed _ (ihA h.1) _ (ihB h.2)).1
  | or A B ihA ihB =>
      intro h
      simp only [boxDepth_or, Nat.max_le] at h
      exact (L1_closed _ (ihA h.1) _ (ihB h.2)).2.1
  | ifThen A B ihA ihB =>
      intro h
      simp only [boxDepth_imp, Nat.max_le] at h
      exact (L1_closed _ (ihA h.1) _ (ihB h.2)).2.2
  | somehow A _ =>
      intro h
      simp only [boxDepth_box] at h
      exact L0_box _ (tv_mem0 A (by omega))

theorem tv_mem2 : ∀ A : PLLFormula, boxDepth A ≤ 2 → tv A ∈ L2list := by
  intro A
  induction A with
  | prop a => intro _; exact bot_mem_L2
  | falsePLL => intro _; exact bot_mem_L2
  | and A B ihA ihB =>
      intro h
      simp only [boxDepth_and, Nat.max_le] at h
      exact (L2_closed _ (ihA h.1) _ (ihB h.2)).1
  | or A B ihA ihB =>
      intro h
      simp only [boxDepth_or, Nat.max_le] at h
      exact (L2_closed _ (ihA h.1) _ (ihB h.2)).2.1
  | ifThen A B ihA ihB =>
      intro h
      simp only [boxDepth_imp, Nat.max_le] at h
      exact (L2_closed _ (ihA h.1) _ (ihB h.2)).2.2
  | somehow A _ =>
      intro h
      simp only [boxDepth_box] at h
      exact L1_box _ (tv_mem1 A (by omega))

/-! ## The lower-bound machine -/

theorem not_depthLe_zero {A : PLLFormula} (h : tv A ∉ L0list) : ¬ DepthLe 0 A := by
  rintro ⟨B, hI, hd⟩
  exact h (interd_tv hI ▸ tv_mem0 B hd)

theorem not_depthLe_one {A : PLLFormula} (h : tv A ∉ L1list) : ¬ DepthLe 1 A := by
  rintro ⟨B, hI, hd⟩
  exact h (interd_tv hI ▸ tv_mem1 B hd)

theorem not_depthLe_two {A : PLLFormula} (h : tv A ∉ L2list) : ¬ DepthLe 2 A := by
  rintro ⟨B, hI, hd⟩
  exact h (interd_tv hI ▸ tv_mem2 B hd)

/-! ## THE VERDICT: the hierarchy does not collapse at depth 2 -/

/-- **`◯g 1` is not interderivable with ANY formula of `◯`-depth ≤ 2.** -/
theorem not_depthLe_two_box_gap_one : ¬ DepthLe 2 (PLLFormula.somehow (gap 1)) :=
  not_depthLe_two (by decide)

/-- **The class depth of `◯g 1` is EXACTLY 3** — so `D₂ ⊊ D₃`, and the
`◯`-depth stratification of RN(◯,{}) does not collapse at 2. -/
theorem depth_box_gap_one_exact :
    DepthLe 3 (PLLFormula.somehow (gap 1)) ∧ ¬ DepthLe 2 (PLLFormula.somehow (gap 1)) :=
  ⟨depth_bg 1, not_depthLe_two_box_gap_one⟩

/-- `◯g 2` escapes depth 2 as well, in the same model. -/
theorem not_depthLe_two_box_gap_two : ¬ DepthLe 2 (PLLFormula.somehow (gap 2)) :=
  not_depthLe_two (by decide)

/-- **The counting statement, at the level `M7` reaches**: depth 3 contributes
NEW classes, at least the two boxed gaps `◯g 1` and `◯g 2`.  Whether the whole
`◯g` antichain (pairwise incomparable for `j ≠ k ≥ 2`,
`RNEmbed.bg_incomparable`) sits at class depth exactly 3 — which would make
the depth-3 layer infinite — is OPEN: `M7`'s ladder saturates at `t m = ⊤`
for `m ≥ 9`, so `gap k = ⊤` in `M7` from `k = 3` on and this model cannot
reach the rest of the family. -/
theorem depth_three_is_inhabited :
    ¬ DepthLe 2 (PLLFormula.somehow (gap 1)) ∧ ¬ DepthLe 2 (PLLFormula.somehow (gap 2)) :=
  ⟨not_depthLe_two_box_gap_one, not_depthLe_two_box_gap_two⟩

/-! ## Class depth exactly 2 for the depth-2 families -/

theorem not_depthLe_one_chain_one : ¬ DepthLe 1 (RNEmbed.chainF 1) :=
  not_depthLe_one (by decide)

theorem depth_chain_one_exact :
    DepthLe 2 (RNEmbed.chainF 1) ∧ ¬ DepthLe 1 (RNEmbed.chainF 1) :=
  ⟨depth_chainF 1, not_depthLe_one_chain_one⟩

theorem not_depthLe_one_chain_two : ¬ DepthLe 1 (RNEmbed.chainF 2) :=
  not_depthLe_one (by decide)

theorem not_depthLe_one_gap_one : ¬ DepthLe 1 (gap 1) :=
  not_depthLe_one (by decide)

theorem not_depthLe_one_gap_two : ¬ DepthLe 1 (gap 2) :=
  not_depthLe_one (by decide)

theorem depth_gap_one_exact : DepthLe 2 (gap 1) ∧ ¬ DepthLe 1 (gap 1) :=
  ⟨depth_gap 1, not_depthLe_one_gap_one⟩

theorem not_depthLe_one_sC_one : ¬ DepthLe 1 (sC 1) :=
  not_depthLe_one (by decide)

theorem depth_sC_one_exact : DepthLe 2 (sC 1) ∧ ¬ DepthLe 1 (sC 1) :=
  ⟨depth_sC 1, not_depthLe_one_sC_one⟩

theorem not_depthLe_one_rC_one : ¬ DepthLe 1 (rC 1) :=
  not_depthLe_one (by decide)

theorem depth_rC_one_exact : DepthLe 2 (rC 1) ∧ ¬ DepthLe 1 (rC 1) :=
  ⟨depth_rC 1, not_depthLe_one_rC_one⟩

theorem not_depthLe_one_wC_one : ¬ DepthLe 1 ((gap 1).and (rnSub 6)) :=
  not_depthLe_one (by decide)

theorem depth_wC_one_exact :
    DepthLe 2 ((gap 1).and (rnSub 6)) ∧ ¬ DepthLe 1 ((gap 1).and (rnSub 6)) :=
  ⟨depth_wC 1, not_depthLe_one_wC_one⟩

/-- `Gmeet 0 = g 1` and `Gmeet 1 = g 1 ∧ g 2` are at class depth exactly 2. -/
theorem not_depthLe_one_Gmeet_zero : ¬ DepthLe 1 (Gmeet 0) :=
  not_depthLe_one (by decide)

theorem not_depthLe_one_Gmeet_one : ¬ DepthLe 1 (Gmeet 1) :=
  not_depthLe_one (by decide)

/-- The ladder rung `t 1 = ◯⊥` is not at class depth 0. -/
theorem not_depthLe_zero_rnSub_one : ¬ DepthLe 0 (rnSub 1) :=
  not_depthLe_zero (by decide)

theorem depth_rnSub_one_exact : DepthLe 1 (rnSub 1) ∧ ¬ DepthLe 0 (rnSub 1) :=
  ⟨depth_rnSub 1, not_depthLe_zero_rnSub_one⟩

theorem not_depthLe_zero_rnSub_three : ¬ DepthLe 0 (rnSub 3) :=
  not_depthLe_zero (by decide)

/-! ## Axiom pins -/

/-- info: 'PLLND.Depth.tv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tv_iff

/-- info: 'PLLND.Depth.interd_tv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interd_tv

/-- info: 'PLLND.Depth.tv_mem2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tv_mem2

/--
info: 'PLLND.Depth.not_depthLe_two_box_gap_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_depthLe_two_box_gap_one

/--
info: 'PLLND.Depth.depth_box_gap_one_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms depth_box_gap_one_exact

/--
info: 'PLLND.Depth.depth_chain_one_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms depth_chain_one_exact

end Depth
end PLLND
