import wip.depth

/-!
# PCLL control: `◯A ⊣⊢ A ∨ ◯⊥` is REFUTED, schema and CLOSED instance alike

PCLL is PLL + the distribution axiom `◯(A ∨ B) ⊃ (◯A ∨ ◯B)` — the system
`DerivU` of `LaxLogic/PLLConfluentComplete.lean`.  Its frame condition,
stated explicitly, is **mutual confluence** (`PLLFrames.MutuallyConfluent`):

    ∀ x w v,  x Rₘ w → x Rᵢ v → ∃ u,  w Rᵢ u  ∧  v Rₘ u

and `derivU_sound` is soundness of `DerivU` over exactly those models.
Algebraically: a nucleus `j` on a Heyting algebra preserves binary joins iff
its fixed-point set is closed under join, and that does NOT force the fixed
points to be the whole up-set of `j(⊥)` — which is why the closed-form law
`j(a) = a ∨ j(⊥)` fails even though `j` distributes over `∨`.

## What is refuted, and where

* `not_derivU_box_atom` — **the schema**, on Matthew's two-world model `M2`:
  worlds `{0,1}` with `0 ≤ 1`, no fallible world, `V p = {1}`, `Rₘ` sending
  everything to `1`.  Then `0 ⊩ ◯p`, `0 ⊮ p`, and `0 ⊮ ◯⊥` (nothing forces
  `⊥` at all), so `◯p ⊬ p ∨ ◯⊥` in PCLL.  In `M2` the whole variable-free
  fragment degenerates (`◯⊥` is false everywhere), which is exactly why it
  cannot settle the closed question.

* `not_derivU_chain_one_rnSub_three` — **the closed instance**, on the
  four-world model `M4`, where `◯⊥` IS forced (at world 1) so the ladder
  evaluates properly:

      t0 = ⊥ = {3}   t1 = ◯⊥ = {1,3}   t2 = {2,3}   t3 = {1,2,3}
      c 1 = ◯t3 = {0,1,2,3} = ⊤

  so `c 1 ⊬ t3` in PCLL: `◯t3 ⊬ t3`, hence `◯A ⊢ A ∨ ◯⊥` fails at the
  closed `A = t3` as well.  `not_derivU_box_rnSub_two` is the same refutation
  in the equivalent form `◯t2 ⊬ t3` (`◯t2 ⊣⊢ ◯t3` in PLL already).
  `M4` is mutually confluent (`conf4`), so this is a PCLL refutation and a
  fortiori a PLL one.

* `M4_ladder_nondegenerate` records that `M4` does not trivialise: `t1` is
  forced at world 1 and refuted at world 0.

## The fold-back law that survives

`box_rnSub_four : ◯t4 ⊣⊢ t4` — PROVED in PLL, as an instance of
`Depth.box_imp_box`, because `t4 = t3 ⊃ t1` and `t1 = ◯⊥` is a box.  This is
the ingredient behind the PCLL merge `c 2 ⊣⊢ s 1`
(`◯t5 = ◯(t3 ∨ t4) = ◯t3 ∨ ◯t4 = c 1 ∨ t4`), whose distribution half is not
mechanised here.
-/

open PLLFormula

namespace PLLND
namespace DepthPCLL

open SemUI RNEmbed PLLND.ConfluentU

/-! Each model below carries its own truth-set calculator `tvN` and bridge
`tvN_iff` to `ConstraintModel.force`; everything stays in `Bool` and `List`,
so the verdicts are `decide`. -/

/-! ## `M2` — Matthew's two-world refutation of the SCHEMA -/

def ws2 : List (Fin 2) := [0, 1]
theorem mem_ws2 : ∀ w : Fin 2, w ∈ ws2 := by decide

def ri2 (w v : Fin 2) : Bool := w.val ≤ v.val
def rm2Row (w : Fin 2) : List (Fin 2) :=
  match w.val with
  | 0 => [0, 1]
  | _ => [1]
def rm2 (w v : Fin 2) : Bool := (rm2Row w).contains v
def fal2 (_ : Fin 2) : Bool := false
def val2 (w : Fin 2) : Bool := w.val == 1

theorem ri2_refl : ∀ w : Fin 2, ri2 w w = true := by decide
theorem ri2_trans : ∀ w v u : Fin 2, ri2 w v = true → ri2 v u = true → ri2 w u = true := by
  decide
theorem rm2_refl : ∀ w : Fin 2, rm2 w w = true := by decide
theorem rm2_trans : ∀ w v u : Fin 2, rm2 w v = true → rm2 v u = true → rm2 w u = true := by
  decide
theorem rm2_sub : ∀ w v : Fin 2, rm2 w v = true → ri2 w v = true := by decide
theorem fal2_hered : ∀ w v : Fin 2, ri2 w v = true → fal2 w = true → fal2 v = true := by decide
theorem val2_hered : ∀ w v : Fin 2, ri2 w v = true → val2 w = true → val2 v = true := by decide
theorem val2_full : ∀ w : Fin 2, fal2 w = true → val2 w = true := by decide

/-- Two worlds `0 ≤ 1`, infallible, `V p = {1}`, every world `Rₘ`-reaching `1`. -/
def M2 : ConstraintModel where
  W := Fin 2
  Ri := fun w v => ri2 w v = true
  Rm := fun w v => rm2 w v = true
  F := fun w => fal2 w = true
  V := fun _ w => val2 w = true
  refl_i := ri2_refl
  trans_i := fun {w v u} h₁ h₂ => ri2_trans w v u h₁ h₂
  refl_m := rm2_refl
  trans_m := fun {w v u} h₁ h₂ => rm2_trans w v u h₁ h₂
  sub_mi := fun {w v} h => rm2_sub w v h
  hered_F := fun {w v} h₁ h₂ => fal2_hered w v h₁ h₂
  hered_V := fun {_ w v} h₁ h₂ => val2_hered w v h₁ h₂
  full_F := fun {_ w} h => val2_full w h

def tv2 : PLLFormula → Fin 2 → Bool
  | .prop _ => val2
  | .falsePLL => fal2
  | .and A B => fun w => tv2 A w && tv2 B w
  | .or A B => fun w => tv2 A w || tv2 B w
  | .ifThen A B => fun w => ws2.all fun v => !ri2 w v || !tv2 A v || tv2 B v
  | .somehow A => fun w => ws2.all fun v => !ri2 w v || ws2.any fun u => rm2 v u && tv2 A u

theorem tv2_iff : ∀ (A : PLLFormula) (w : Fin 2), tv2 A w = true ↔ M2.force w A := by
  intro A
  induction A with
  | prop a => intro w; exact Iff.rfl
  | falsePLL => intro w; exact Iff.rfl
  | and A B ihA ihB =>
      intro w; rw [tv2, Bool.and_eq_true, ihA w, ihB w]; exact Iff.rfl
  | or A B ihA ihB =>
      intro w; rw [tv2, Bool.or_eq_true, ihA w, ihB w]; exact Iff.rfl
  | ifThen A B ihA ihB =>
      intro w
      rw [tv2, List.all_eq_true]
      constructor
      · intro h v hwv hA
        have hr : ri2 w v = true := hwv
        have ha : tv2 A v = true := (ihA v).mpr hA
        have hv := h v (mem_ws2 v)
        rw [hr, ha] at hv
        simp only [Bool.not_true, Bool.false_or] at hv
        exact (ihB v).mp hv
      · intro h v _
        cases hr : ri2 w v with
        | false => simp
        | true =>
            cases ha : tv2 A v with
            | false => simp
            | true => simp [(ihB v).mpr (h v hr ((ihA v).mp ha))]
  | somehow A ih =>
      intro w
      rw [tv2, List.all_eq_true]
      constructor
      · intro h v hwv
        have hr : ri2 w v = true := hwv
        have hv := h v (mem_ws2 v)
        rw [hr] at hv
        simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at hv
        obtain ⟨u, _, hu⟩ := hv
        rw [Bool.and_eq_true] at hu
        exact ⟨u, hu.1, (ih u).mp hu.2⟩
      · intro h v _
        cases hr : ri2 w v with
        | false => simp
        | true =>
            obtain ⟨u, hvu, hu⟩ := h v hr
            have hany : (ws2.any fun u => rm2 v u && tv2 A u) = true := by
              rw [List.any_eq_true]
              exact ⟨u, mem_ws2 u, by rw [Bool.and_eq_true]; exact ⟨hvu, (ih u).mpr hu⟩⟩
            simp [hany]

theorem conf2' : ∀ x w v : Fin 2,
    rm2 x w = true → ri2 x v = true → ∃ u, ri2 w u = true ∧ rm2 v u = true := by decide

theorem conf2 : MutuallyConfluent M2 := fun {x w v} h₁ h₂ => conf2' x w v h₁ h₂

/-- **The SCHEMA is REFUTED in PCLL**: `◯p ⊬ p ∨ ◯⊥`. -/
theorem not_derivU_box_atom :
    ¬ DerivU [(PLLFormula.prop "p").somehow] ((PLLFormula.prop "p").or oBot) := by
  intro h
  have hp : M2.force (0 : Fin 2) ((PLLFormula.prop "p").somehow) :=
    (tv2_iff ((PLLFormula.prop "p").somehow) (0 : Fin 2)).mp (by decide)
  have := derivU_sound h conf2 (0 : Fin 2) (by
    intro ψ hψ; cases hψ with | head => exact hp | tail _ hh => cases hh)
  have hno : tv2 ((PLLFormula.prop "p").or oBot) (0 : Fin 2) = false := by decide
  have := (tv2_iff ((PLLFormula.prop "p").or oBot) (0 : Fin 2)).mpr this
  rw [hno] at this
  exact Bool.noConfusion this

/-- The same refutation in PLL. -/
theorem not_deriv_box_atom :
    ¬ Deriv [(PLLFormula.prop "p").somehow] ((PLLFormula.prop "p").or oBot) :=
  fun h => not_derivU_box_atom (h.elim fun d => .of_nd d)

/-! ## `M4` — a confluent model where the ladder does NOT degenerate -/

def ws4 : List (Fin 4) := [0, 1, 2, 3]
theorem mem_ws4 : ∀ w : Fin 4, w ∈ ws4 := by decide

/-- `Rᵢ`: `0 ≤ 1, 2, 3`; `1 ≤ 3`; `2 ≤ 3`. -/
def ri4Row (w : Fin 4) : List (Fin 4) :=
  match w.val with
  | 0 => [0, 1, 2, 3]
  | 1 => [1, 3]
  | 2 => [2, 3]
  | _ => [3]

/-- `Rₘ`: `0 ⇝ 2`, `1 ⇝ 3`, plus reflexivity. -/
def rm4Row (w : Fin 4) : List (Fin 4) :=
  match w.val with
  | 0 => [0, 2]
  | 1 => [1, 3]
  | 2 => [2]
  | _ => [3]

def ri4 (w v : Fin 4) : Bool := (ri4Row w).contains v
def rm4 (w v : Fin 4) : Bool := (rm4Row w).contains v
def fal4 (w : Fin 4) : Bool := w.val == 3

theorem ri4_refl : ∀ w : Fin 4, ri4 w w = true := by decide
theorem ri4_trans : ∀ w v u : Fin 4, ri4 w v = true → ri4 v u = true → ri4 w u = true := by
  decide
theorem rm4_refl : ∀ w : Fin 4, rm4 w w = true := by decide
theorem rm4_trans : ∀ w v u : Fin 4, rm4 w v = true → rm4 v u = true → rm4 w u = true := by
  decide
theorem rm4_sub : ∀ w v : Fin 4, rm4 w v = true → ri4 w v = true := by decide
theorem fal4_hered : ∀ w v : Fin 4, ri4 w v = true → fal4 w = true → fal4 v = true := by decide

def M4 : ConstraintModel where
  W := Fin 4
  Ri := fun w v => ri4 w v = true
  Rm := fun w v => rm4 w v = true
  F := fun w => fal4 w = true
  V := fun _ w => fal4 w = true
  refl_i := ri4_refl
  trans_i := fun {w v u} h₁ h₂ => ri4_trans w v u h₁ h₂
  refl_m := rm4_refl
  trans_m := fun {w v u} h₁ h₂ => rm4_trans w v u h₁ h₂
  sub_mi := fun {w v} h => rm4_sub w v h
  hered_F := fun {w v} h₁ h₂ => fal4_hered w v h₁ h₂
  hered_V := fun {_ w v} h₁ h₂ => fal4_hered w v h₁ h₂
  full_F := fun {_ _} h => h

def tv4 : PLLFormula → Fin 4 → Bool
  | .prop _ => fal4
  | .falsePLL => fal4
  | .and A B => fun w => tv4 A w && tv4 B w
  | .or A B => fun w => tv4 A w || tv4 B w
  | .ifThen A B => fun w => ws4.all fun v => !ri4 w v || !tv4 A v || tv4 B v
  | .somehow A => fun w => ws4.all fun v => !ri4 w v || ws4.any fun u => rm4 v u && tv4 A u

theorem tv4_iff : ∀ (A : PLLFormula) (w : Fin 4), tv4 A w = true ↔ M4.force w A := by
  intro A
  induction A with
  | prop a => intro w; exact Iff.rfl
  | falsePLL => intro w; exact Iff.rfl
  | and A B ihA ihB =>
      intro w; rw [tv4, Bool.and_eq_true, ihA w, ihB w]; exact Iff.rfl
  | or A B ihA ihB =>
      intro w; rw [tv4, Bool.or_eq_true, ihA w, ihB w]; exact Iff.rfl
  | ifThen A B ihA ihB =>
      intro w
      rw [tv4, List.all_eq_true]
      constructor
      · intro h v hwv hA
        have hr : ri4 w v = true := hwv
        have ha : tv4 A v = true := (ihA v).mpr hA
        have hv := h v (mem_ws4 v)
        rw [hr, ha] at hv
        simp only [Bool.not_true, Bool.false_or] at hv
        exact (ihB v).mp hv
      · intro h v _
        cases hr : ri4 w v with
        | false => simp
        | true =>
            cases ha : tv4 A v with
            | false => simp
            | true => simp [(ihB v).mpr (h v hr ((ihA v).mp ha))]
  | somehow A ih =>
      intro w
      rw [tv4, List.all_eq_true]
      constructor
      · intro h v hwv
        have hr : ri4 w v = true := hwv
        have hv := h v (mem_ws4 v)
        rw [hr] at hv
        simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at hv
        obtain ⟨u, _, hu⟩ := hv
        rw [Bool.and_eq_true] at hu
        exact ⟨u, hu.1, (ih u).mp hu.2⟩
      · intro h v _
        cases hr : ri4 w v with
        | false => simp
        | true =>
            obtain ⟨u, hvu, hu⟩ := h v hr
            have hany : (ws4.any fun u => rm4 v u && tv4 A u) = true := by
              rw [List.any_eq_true]
              exact ⟨u, mem_ws4 u, by rw [Bool.and_eq_true]; exact ⟨hvu, (ih u).mpr hu⟩⟩
            simp [hany]

theorem conf4' : ∀ x w v : Fin 4,
    rm4 x w = true → ri4 x v = true → ∃ u, ri4 w u = true ∧ rm4 v u = true := by decide

theorem conf4 : MutuallyConfluent M4 := fun {x w v} h₁ h₂ => conf4' x w v h₁ h₂

/-- `M4` does not trivialise the closed fragment: `◯⊥` is forced at world `1`
and refuted at world `0`. -/
theorem M4_ladder_nondegenerate :
    M4.force (1 : Fin 4) (rnSub 1) ∧ ¬ M4.force (0 : Fin 4) (rnSub 1) := by
  constructor
  · exact (tv4_iff (rnSub 1) (1 : Fin 4)).mp (by decide)
  · intro h
    have := (tv4_iff (rnSub 1) (0 : Fin 4)).mpr h
    rw [show tv4 (rnSub 1) (0 : Fin 4) = false from by decide] at this
    exact Bool.noConfusion this

/-- **The CLOSED instance is REFUTED in PCLL**: `c 1 = ◯t3 ⊬ t3`.  So
`◯A ⊢ A ∨ ◯⊥` fails at the closed `A = t3` (note `t1 ≤ t3`, so
`t3 ∨ ◯⊥ = t3`). -/
theorem not_derivU_chain_one_rnSub_three :
    ¬ DerivU [RNEmbed.chainF 1] (rnSub 3) := by
  intro h
  have hp : M4.force (0 : Fin 4) (RNEmbed.chainF 1) :=
    (tv4_iff (RNEmbed.chainF 1) (0 : Fin 4)).mp (by decide)
  have hf := derivU_sound h conf4 (0 : Fin 4) (by
    intro ψ hψ; cases hψ with | head => exact hp | tail _ hh => cases hh)
  have := (tv4_iff (rnSub 3) (0 : Fin 4)).mpr hf
  rw [show tv4 (rnSub 3) (0 : Fin 4) = false from by decide] at this
  exact Bool.noConfusion this

/-- The same, in the form `◯t2 ⊬ t3` (and `◯t2 ⊣⊢ ◯t3` already in PLL). -/
theorem not_derivU_box_rnSub_two :
    ¬ DerivU [(rnSub 2).somehow] (rnSub 3) := by
  intro h
  have hp : M4.force (0 : Fin 4) ((rnSub 2).somehow) :=
    (tv4_iff ((rnSub 2).somehow) (0 : Fin 4)).mp (by decide)
  have hf := derivU_sound h conf4 (0 : Fin 4) (by
    intro ψ hψ; cases hψ with | head => exact hp | tail _ hh => cases hh)
  have := (tv4_iff (rnSub 3) (0 : Fin 4)).mpr hf
  rw [show tv4 (rnSub 3) (0 : Fin 4) = false from by decide] at this
  exact Bool.noConfusion this

/-- And in PLL. -/
theorem not_deriv_chain_one_rnSub_three : ¬ Deriv [RNEmbed.chainF 1] (rnSub 3) :=
  fun h => not_derivU_chain_one_rnSub_three (h.elim fun d => .of_nd d)

/-! ## The surviving fold-back law: `◯t4 ⊣⊢ t4` -/

theorem rnSub_one_eq : rnSub 1 = oBot := rfl

theorem rnSub_four_eq : rnSub 4 = (rnSub 3).ifThen (rnSub 1) := by
  show embed (rn 4) = _
  rw [show (4 : Nat) = 2 * 0 + 4 from rfl, rn_even_rec 0]
  rfl

/-- **`◯t4 ⊣⊢ t4`** — an instance of `Depth.box_imp_box`, because
`t4 = t3 ⊃ ◯⊥`.  The even rung `t4` is a fixed point of `◯`. -/
theorem box_rnSub_four : Interd ((rnSub 4).somehow) (rnSub 4) := by
  rw [rnSub_four_eq, rnSub_one_eq]
  exact Depth.box_imp_box (rnSub 3) .falsePLL

/-! ## Axiom pins -/

/--
info: 'PLLND.DepthPCLL.not_derivU_box_atom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_derivU_box_atom

/--
info: 'PLLND.DepthPCLL.not_derivU_chain_one_rnSub_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_derivU_chain_one_rnSub_three

/--
info: 'PLLND.DepthPCLL.M4_ladder_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms M4_ladder_nondegenerate

/-- info: 'PLLND.DepthPCLL.box_rnSub_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms box_rnSub_four

end DepthPCLL
end PLLND
