import LaxLogic.PLLG4UITrunc

/-!
# WIP: syntactic fuel-indifference for the truncated quantifiers (v3.1)

Above the recursion measure `mu`, the fuel parameter of `itpE`/`itpA`
is invisible: raising the fuel by one changes nothing — literally
(`Eq`), not just up to interderivability.  Chained, this makes every
fuel above the threshold give the *same* formula, so the adequacy
theorem's "every fuel above the consumer's height" packages into a
single fuel-free formula (instantiate at `mu S W0 b slot Γ + 1`).

Shape of the induction: plain induction on the fuel `f`.  At `f' + 1`
both sides unfold one level (`itpE_succ`/`itpA_succ`) into clause
tables whose only fuel-sensitive spots are recursive calls at
`f' + 1` vs `f'`; each such call strictly decreases `mu`, so the IH
(at `f'`) applies.

Compared to the handoff statement, both halves carry one extra
hypothesis: a weight cap on the context, `∀ F ∈ Γ, F.weight ≤ W0`.
It is forced by the two clause families with *no* space gate on the
formula that becomes the next goal slot:

* the `impLImp` fresh-piece branch (`B⊃D ∈ S ∖ Γ`, goal `A⊃B` where
  `(A⊃B)⊃D` is only known to be *in the context*), and
* the `A13` γ-loop (`X = ◯x` fresh, goal `◯A` where `◯A⊃B` is only
  known to be in the context).

There `slot' ≤ W0` (needed for `mu_growth_lt`: the defect drop buys
exactly `W0 + 1`) is available only through the context cap.  The cap
is preserved by every context extension (all extensions are space
pieces, context members, or goal pieces), and the adequacy consumer
runs inside the space, so its contexts satisfy it.
-/

open PLLFormula

set_option maxHeartbeats 4000000

namespace PLLND

/-! ### New `mu` variants -/

/-- Strict defect drop with a non-increasing slot: `mu` drops.
(The same-goal environment moves of the `A`-quantifier.) -/
theorem mu_defect_lt {S : Finset PLLFormula} {W0 b slot slot' : Nat}
    {Γ Γ' : List PLLFormula} (hd : defect S Γ' < defect S Γ)
    (hs : slot' ≤ slot) : mu S W0 b slot' Γ' < mu S W0 b slot Γ := by
  unfold mu
  have h1 : (defect S Γ' + b + 1) * (W0 + 1) ≤
      (defect S Γ + b) * (W0 + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : (defect S Γ' + b + 1) * (W0 + 1)
      = (defect S Γ' + b) * (W0 + 1) + (W0 + 1) := by ring
  omega

/-- Non-increasing defect with a strictly dropping slot: `mu` drops.
(The goal-piece moves: fresh implication antecedents.) -/
theorem mu_slot_le_lt {S : Finset PLLFormula} {W0 b slot slot' : Nat}
    {Γ Γ' : List PLLFormula} (hd : defect S Γ' ≤ defect S Γ)
    (hs : slot' < slot) : mu S W0 b slot' Γ' < mu S W0 b slot Γ := by
  unfold mu
  have h1 : (defect S Γ' + b) * (W0 + 1) ≤
      (defect S Γ + b) * (W0 + 1) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- Budget jump with a non-increasing defect and a capped slot:
`mu` drops.  (Jump calls under a context extension by a present
piece.)  Subsumes `mu_jump_lt` (`Γ' = Γ`). -/
theorem mu_jump_le_lt {S : Finset PLLFormula} {W0 b slot slot' : Nat}
    {Γ Γ' : List PLLFormula} (hd : defect S Γ' ≤ defect S Γ)
    (hs : slot' ≤ W0) : mu S W0 b slot' Γ' < mu S W0 (b + 1) slot Γ := by
  unfold mu
  have h1 : (defect S Γ' + b + 1) * (W0 + 1) ≤
      (defect S Γ + (b + 1)) * (W0 + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : (defect S Γ' + b + 1) * (W0 + 1)
      = (defect S Γ' + b) * (W0 + 1) + (W0 + 1) := by ring
  omega

/-- Two-piece context growth, at least one piece fresh, both pieces
gated (present or in the space): the defect strictly drops. -/
theorem defect_cons₂_lt {S : Finset PLLFormula} {A B : PLLFormula}
    {Γ : List PLLFormula} (hnot : ¬(A ∈ Γ ∧ B ∈ Γ))
    (hA : A ∈ Γ ∨ A ∈ S) (hB : B ∈ Γ ∨ B ∈ S) :
    defect S (A :: B :: Γ) < defect S Γ := by
  by_cases hBΓ : B ∈ Γ
  · have hAΓ : A ∉ Γ := fun h => hnot ⟨h, hBΓ⟩
    have hAS : A ∈ S := hA.resolve_left hAΓ
    have hA' : A ∉ B :: Γ := by
      intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact hAΓ hBΓ
      · exact hAΓ h
    calc defect S (A :: B :: Γ) < defect S (B :: Γ) :=
          defect_cons_lt hAS hA'
      _ = defect S Γ := defect_cons_eq hBΓ
  · have hBS : B ∈ S := hB.resolve_left hBΓ
    exact lt_of_le_of_lt (defect_cons_le S A (B :: Γ))
      (defect_cons_lt hBS hBΓ)

/-! ### Context weight-cap bookkeeping -/

/-- Extending a capped context by a capped formula. -/
private theorem cap_cons {W0 : Nat} {x : PLLFormula} {Γ : List PLLFormula}
    (hx : x.weight ≤ W0) (h : ∀ F ∈ Γ, F.weight ≤ W0) :
    ∀ F ∈ x :: Γ, F.weight ≤ W0 := by
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hx
  · exact h F hF

/-! ### The indifference lemma -/

/-- **Fuel indifference.**  Above `mu`, one extra unit of fuel changes
the truncated quantifiers *syntactically not at all*: over a capped
context (`∀ F ∈ Γ, F.weight ≤ W0`, with `W0` also bounding the
space), `itpE p S (f+1) b Γ = itpE p S f b Γ` as soon as
`mu S W0 b 0 Γ < f`, and likewise for `itpA` at a capped goal with
slot `C.weight`. -/
theorem itp_indiff (p : String) (S : Finset PLLFormula) (W0 : Nat)
    (hW : S.sup PLLFormula.weight ≤ W0) : ∀ (f : Nat),
    (∀ b Γ, (∀ F ∈ Γ, F.weight ≤ W0) → mu S W0 b 0 Γ < f →
      itpE p S (f + 1) b Γ = itpE p S f b Γ) ∧
    (∀ b Γ C, (∀ F ∈ Γ, F.weight ≤ W0) → C.weight ≤ W0 →
      mu S W0 b C.weight Γ < f →
      itpA p S (f + 1) b Γ C = itpA p S f b Γ C) := by
  intro f
  induction f with
  | zero =>
      exact ⟨fun b Γ _ h => absurd h (Nat.not_lt_zero _),
        fun b Γ C _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ f' IH =>
      obtain ⟨ihE0, ihA0⟩ := IH
      constructor
      · -- E-half
        intro b Γ hcap hmu
        have hle : mu S W0 b 0 Γ ≤ f' := Nat.lt_succ_iff.mp hmu
        have ihE : ∀ {b' : Nat} {Γ' : List PLLFormula},
            (∀ F ∈ Γ', F.weight ≤ W0) →
            mu S W0 b' 0 Γ' < mu S W0 b 0 Γ →
            itpE p S (f' + 1) b' Γ' = itpE p S f' b' Γ' :=
          fun hc hm => ihE0 _ _ hc (lt_of_lt_of_le hm hle)
        have ihA : ∀ {b' : Nat} {Γ' : List PLLFormula} {C' : PLLFormula},
            (∀ F ∈ Γ', F.weight ≤ W0) → C'.weight ≤ W0 →
            mu S W0 b' C'.weight Γ' < mu S W0 b 0 Γ →
            itpA p S (f' + 1) b' Γ' C' = itpA p S f' b' Γ' C' :=
          fun hc hw hm => ihA0 _ _ _ hc hw (lt_of_lt_of_le hm hle)
        have wmem : ∀ {x : PLLFormula}, x ∈ Γ ∨ x ∈ S → x.weight ≤ W0 :=
          fun h => h.elim (fun hg => hcap _ hg)
            (fun hs => weight_le_of_mem_left hW hs)
        rw [itpE_succ p S (f' + 1) b Γ, itpE_succ p S f' b Γ]
        congr 1
        unfold itpEcls
        congr 1
        refine List.flatMap_congr ?_
        intro F hF
        cases F with
        | prop q => rfl
        | falsePLL => rfl
        | and A B =>
            dsimp only
            split_ifs with h1 h2
            · rfl
            · rw [ihE (cap_cons (wmem h2.1) (cap_cons (wmem h2.2) hcap))
                (mu_growth_lt (defect_cons₂_lt h1 h2.1 h2.2) (Nat.zero_le _))]
            · rfl
        | or A B =>
            dsimp only
            split_ifs with h1 h2
            · rfl
            · push_neg at h1
              rw [ihE (cap_cons (weight_le_of_mem_left hW h2.1) hcap)
                  (mu_growth_lt (defect_cons_lt h2.1 h1.1) (Nat.zero_le _)),
                ihE (cap_cons (weight_le_of_mem_left hW h2.2) hcap)
                  (mu_growth_lt (defect_cons_lt h2.2 h1.2) (Nat.zero_le _))]
            · rfl
        | somehow χ =>
            dsimp only
            split_ifs with h1
            · rfl
            · push_neg at h1
              rw [ihE (cap_cons (weight_le_of_mem_left hW h1.2) hcap)
                (mu_growth_lt (defect_cons_lt h1.2 h1.1) (Nat.zero_le _))]
        | ifThen X D =>
            cases X with
            | falsePLL => rfl
            | prop q =>
                dsimp only
                split_ifs with h1 h2 h3 h4
                · rfl
                · rw [ihE (cap_cons (weight_le_of_mem_left hW h2) hcap)
                    (mu_growth_lt (defect_cons_lt h2 h1) (Nat.zero_le _))]
                · rfl
                · rw [ihE (cap_cons (weight_le_of_mem_left hW h2) hcap)
                    (mu_growth_lt (defect_cons_lt h2 h1) (Nat.zero_le _))]
                · rfl
            | and A B =>
                dsimp only
                split_ifs with h1 h2
                · rfl
                · rw [ihE (cap_cons (weight_le_of_mem_left hW h2) hcap)
                    (mu_growth_lt (defect_cons_lt h2 h1) (Nat.zero_le _))]
                · rfl
            | or A B =>
                dsimp only
                split_ifs with h1 h2
                · rfl
                · rw [ihE (cap_cons (wmem h2.1) (cap_cons (wmem h2.2) hcap))
                    (mu_growth_lt (defect_cons₂_lt h1 h2.1 h2.2) (Nat.zero_le _))]
                · rfl
            | ifThen A B =>
                -- F = (A⊃B)⊃D
                dsimp only
                split_ifs with h1 h2 h3 h4 h5
                · rfl
                · -- jump branch: B⊃D present, (A⊃B)⊃D in the space
                  cases b with
                  | zero => rfl
                  | succ b' =>
                      dsimp only
                      have wAB : (A.ifThen B).weight ≤ W0 := by
                        have := weight_le_of_mem_left hW h4
                        simp only [PLLFormula.weight] at this ⊢
                        omega
                      rw [ihE hcap (mu_jump_lt (Nat.zero_le _)),
                        ihA hcap wAB (mu_jump_lt wAB),
                        ihE (cap_cons (weight_le_of_mem_left hW h2) hcap)
                          (mu_growth_lt (defect_cons_lt h2 h1) (Nat.zero_le _))]
                · rfl
                · -- fresh-piece branch: B⊃D ∈ S ∖ Γ
                  have wAB : (A.ifThen B).weight ≤ W0 := by
                    have := hcap _ hF
                    simp only [PLLFormula.weight] at this ⊢
                    omega
                  rw [ihE (cap_cons (weight_le_of_mem_left hW h5) hcap)
                      (mu_growth_lt (defect_cons_lt h5 h3) (Nat.zero_le _)),
                    ihA (cap_cons (weight_le_of_mem_left hW h5) hcap) wAB
                      (mu_growth_lt (defect_cons_lt h5 h3) wAB),
                    ihE (cap_cons (weight_le_of_mem_left hW h2) hcap)
                      (mu_growth_lt (defect_cons_lt h2 h1) (Nat.zero_le _))]
                · rfl
                · rfl
            | somehow A =>
                -- F = ◯A⊃D
                dsimp only
                split_ifs with h1 h2 h3
                · rfl
                · -- present-branch live: ◯A⊃D ∈ S
                  have wOA : (A.somehow).weight ≤ W0 ∧ A.weight ≤ W0 := by
                    have := weight_le_of_mem_left hW h3
                    simp only [PLLFormula.weight] at this ⊢
                    omega
                  congr 1
                  · cases b with
                    | zero => rfl
                    | succ b' =>
                        dsimp only
                        rw [ihA hcap wOA.2 (mu_jump_lt wOA.2),
                          ihE (cap_cons (weight_le_of_mem_left hW h2) hcap)
                            (mu_growth_lt (defect_cons_lt h2 h1) (Nat.zero_le _)),
                          ihE hcap (mu_jump_lt (Nat.zero_le _)),
                          ihA hcap wOA.1 (mu_jump_lt wOA.1)]
                  · refine List.filterMap_congr ?_
                    intro X _
                    cases X with
                    | prop _ => rfl
                    | falsePLL => rfl
                    | and _ _ => rfl
                    | or _ _ => rfl
                    | ifThen _ _ => rfl
                    | somehow x =>
                        dsimp only
                        split_ifs with hx
                        · rfl
                        · push_neg at hx
                          have wOA' : (A.somehow).weight ≤ W0 := by
                            have := hcap _ hF
                            simp only [PLLFormula.weight] at this ⊢
                            omega
                          rw [ihE (cap_cons (weight_le_of_mem_left hW hx.2) hcap)
                              (mu_growth_lt (defect_cons_lt hx.2 hx.1) (Nat.zero_le _)),
                            ihA (cap_cons (weight_le_of_mem_left hW hx.2) hcap) wOA'
                              (mu_growth_lt (defect_cons_lt hx.2 hx.1) wOA'),
                            ihE (cap_cons (weight_le_of_mem_left hW h2) hcap)
                              (mu_growth_lt (defect_cons_lt h2 h1) (Nat.zero_le _))]
                · -- present-branch dead: only the γ-loop
                  congr 1
                  refine List.filterMap_congr ?_
                  intro X _
                  cases X with
                  | prop _ => rfl
                  | falsePLL => rfl
                  | and _ _ => rfl
                  | or _ _ => rfl
                  | ifThen _ _ => rfl
                  | somehow x =>
                      dsimp only
                      split_ifs with hx
                      · rfl
                      · push_neg at hx
                        have wOA' : (A.somehow).weight ≤ W0 := by
                          have := hcap _ hF
                          simp only [PLLFormula.weight] at this ⊢
                          omega
                        rw [ihE (cap_cons (weight_le_of_mem_left hW hx.2) hcap)
                            (mu_growth_lt (defect_cons_lt hx.2 hx.1) (Nat.zero_le _)),
                          ihA (cap_cons (weight_le_of_mem_left hW hx.2) hcap) wOA'
                            (mu_growth_lt (defect_cons_lt hx.2 hx.1) wOA'),
                          ihE (cap_cons (weight_le_of_mem_left hW h2) hcap)
                            (mu_growth_lt (defect_cons_lt h2 h1) (Nat.zero_le _))]
                · rfl
      · -- A-half
        intro b Γ C hcap hCw hmu
        have hle : mu S W0 b C.weight Γ ≤ f' := Nat.lt_succ_iff.mp hmu
        have ihE : ∀ {b' : Nat} {Γ' : List PLLFormula},
            (∀ F ∈ Γ', F.weight ≤ W0) →
            mu S W0 b' 0 Γ' < mu S W0 b C.weight Γ →
            itpE p S (f' + 1) b' Γ' = itpE p S f' b' Γ' :=
          fun hc hm => ihE0 _ _ hc (lt_of_lt_of_le hm hle)
        have ihA : ∀ {b' : Nat} {Γ' : List PLLFormula} {C' : PLLFormula},
            (∀ F ∈ Γ', F.weight ≤ W0) → C'.weight ≤ W0 →
            mu S W0 b' C'.weight Γ' < mu S W0 b C.weight Γ →
            itpA p S (f' + 1) b' Γ' C' = itpA p S f' b' Γ' C' :=
          fun hc hw hm => ihA0 _ _ _ hc hw (lt_of_lt_of_le hm hle)
        have wmem : ∀ {x : PLLFormula}, x ∈ Γ ∨ x ∈ S → x.weight ≤ W0 :=
          fun h => h.elim (fun hg => hcap _ hg)
            (fun hs => weight_le_of_mem_left hW hs)
        rw [itpA_succ p S (f' + 1) b Γ C, itpA_succ p S f' b Γ C]
        have hgoal : itpAgoal p S (f' + 1) b Γ C = itpAgoal p S f' b Γ C := by
          cases C with
          | prop q => rfl
          | falsePLL => rfl
          | and C₁ C₂ =>
              have hw : C₁.weight ≤ W0 ∧ C₂.weight ≤ W0 := by
                simp only [PLLFormula.weight] at hCw
                omega
              simp only [itpAgoal]
              rw [ihA hcap hw.1
                  (mu_slot_lt (by simp only [PLLFormula.weight]; omega)),
                ihA hcap hw.2
                  (mu_slot_lt (by simp only [PLLFormula.weight]; omega))]
          | or C₁ C₂ =>
              have hw : C₁.weight ≤ W0 ∧ C₂.weight ≤ W0 := by
                simp only [PLLFormula.weight] at hCw
                omega
              simp only [itpAgoal]
              rw [ihA hcap hw.1
                  (mu_slot_lt (by simp only [PLLFormula.weight]; omega)),
                ihA hcap hw.2
                  (mu_slot_lt (by simp only [PLLFormula.weight]; omega))]
          | ifThen C₁ C₂ =>
              have hw : C₁.weight ≤ W0 ∧ C₂.weight ≤ W0 := by
                simp only [PLLFormula.weight] at hCw
                omega
              simp only [itpAgoal]
              split_ifs with h1
              · cases b with
                | zero => rfl
                | succ b' =>
                    dsimp only
                    rw [ihE (cap_cons (hcap _ h1) hcap)
                        (mu_jump_le_lt (le_of_eq (defect_cons_eq h1))
                          (Nat.zero_le _)),
                      ihA (cap_cons (hcap _ h1) hcap) hw.2
                        (mu_same_set_lt h1
                          (by simp only [PLLFormula.weight]; omega))]
              · rw [ihE (cap_cons hw.1 hcap)
                    (mu_slot_le_lt (defect_cons_le S C₁ Γ)
                      (PLLFormula.weight_pos _)),
                  ihA (cap_cons hw.1 hcap) hw.2
                    (mu_slot_le_lt (defect_cons_le S C₁ Γ)
                      (by simp only [PLLFormula.weight]; omega))]
          | somehow D =>
              have hw : D.weight ≤ W0 := by
                simp only [PLLFormula.weight] at hCw
                omega
              simp only [itpAgoal]
              cases b with
              | zero => rfl
              | succ b' =>
                  dsimp only
                  rw [ihE hcap (mu_jump_lt (Nat.zero_le _)),
                    ihA hcap hw
                      (mu_slot_lt (by simp only [PLLFormula.weight]; omega))]
        have henv : itpAenv p S (f' + 1) b Γ C = itpAenv p S f' b Γ C := by
          unfold itpAenv
          refine List.flatMap_congr ?_
          intro F hF
          cases F with
          | prop q => rfl
          | falsePLL => rfl
          | and A B =>
              dsimp only
              split_ifs with h1 h2
              · rfl
              · rw [ihA (cap_cons (wmem h2.1) (cap_cons (wmem h2.2) hcap)) hCw
                  (mu_defect_lt (defect_cons₂_lt h1 h2.1 h2.2) (Nat.le_refl _))]
              · rfl
          | or A B =>
              dsimp only
              split_ifs with h1 h2
              · rfl
              · push_neg at h1
                rw [ihE (cap_cons (weight_le_of_mem_left hW h2.1) hcap)
                    (mu_growth_lt (defect_cons_lt h2.1 h1.1) (Nat.zero_le _)),
                  ihA (cap_cons (weight_le_of_mem_left hW h2.1) hcap) hCw
                    (mu_defect_lt (defect_cons_lt h2.1 h1.1) (Nat.le_refl _)),
                  ihE (cap_cons (weight_le_of_mem_left hW h2.2) hcap)
                    (mu_growth_lt (defect_cons_lt h2.2 h1.2) (Nat.zero_le _)),
                  ihA (cap_cons (weight_le_of_mem_left hW h2.2) hcap) hCw
                    (mu_defect_lt (defect_cons_lt h2.2 h1.2) (Nat.le_refl _))]
              · rfl
          | somehow χ =>
              cases C with
              | prop _ => rfl
              | falsePLL => rfl
              | and _ _ => rfl
              | or _ _ => rfl
              | ifThen _ _ => rfl
              | somehow D =>
                  dsimp only
                  split_ifs with h1
                  · rfl
                  · push_neg at h1
                    rw [ihE (cap_cons (weight_le_of_mem_left hW h1.2) hcap)
                        (mu_growth_lt (defect_cons_lt h1.2 h1.1) (Nat.zero_le _)),
                      ihA (cap_cons (weight_le_of_mem_left hW h1.2) hcap) hCw
                        (mu_defect_lt (defect_cons_lt h1.2 h1.1) (Nat.le_refl _))]
          | ifThen X D =>
              cases X with
              | falsePLL => rfl
              | prop q =>
                  dsimp only
                  split_ifs with h1 h2 h3 h4
                  · rfl
                  · rw [ihA (cap_cons (weight_le_of_mem_left hW h2) hcap) hCw
                      (mu_defect_lt (defect_cons_lt h2 h1) (Nat.le_refl _))]
                  · rfl
                  · rw [ihA (cap_cons (weight_le_of_mem_left hW h2) hcap) hCw
                      (mu_defect_lt (defect_cons_lt h2 h1) (Nat.le_refl _))]
                  · rfl
              | and A B =>
                  dsimp only
                  split_ifs with h1 h2
                  · rfl
                  · rw [ihA (cap_cons (weight_le_of_mem_left hW h2) hcap) hCw
                      (mu_defect_lt (defect_cons_lt h2 h1) (Nat.le_refl _))]
                  · rfl
              | or A B =>
                  dsimp only
                  split_ifs with h1 h2
                  · rfl
                  · rw [ihA (cap_cons (wmem h2.1) (cap_cons (wmem h2.2) hcap)) hCw
                      (mu_defect_lt (defect_cons₂_lt h1 h2.1 h2.2) (Nat.le_refl _))]
                  · rfl
              | ifThen A B =>
                  -- F = (A⊃B)⊃D
                  dsimp only
                  split_ifs with h1 h2 h3 h4 h5
                  · rfl
                  · cases b with
                    | zero => rfl
                    | succ b' =>
                        dsimp only
                        have wAB : (A.ifThen B).weight ≤ W0 := by
                          have := weight_le_of_mem_left hW h4
                          simp only [PLLFormula.weight] at this ⊢
                          omega
                        rw [ihE hcap (mu_jump_lt (Nat.zero_le _)),
                          ihA hcap wAB (mu_jump_lt wAB),
                          ihA (cap_cons (weight_le_of_mem_left hW h2) hcap) hCw
                            (mu_defect_lt (defect_cons_lt h2 h1) (Nat.le_refl _))]
                  · rfl
                  · have wAB : (A.ifThen B).weight ≤ W0 := by
                      have := hcap _ hF
                      simp only [PLLFormula.weight] at this ⊢
                      omega
                    rw [ihE (cap_cons (weight_le_of_mem_left hW h5) hcap)
                        (mu_growth_lt (defect_cons_lt h5 h3) (Nat.zero_le _)),
                      ihA (cap_cons (weight_le_of_mem_left hW h5) hcap) wAB
                        (mu_growth_lt (defect_cons_lt h5 h3) wAB),
                      ihA (cap_cons (weight_le_of_mem_left hW h2) hcap) hCw
                        (mu_defect_lt (defect_cons_lt h2 h1) (Nat.le_refl _))]
                  · rfl
                  · rfl
              | somehow A =>
                  -- F = ◯A⊃D
                  dsimp only
                  split_ifs with h1 h2 h3
                  · rfl
                  · have wOA : (A.somehow).weight ≤ W0 ∧ A.weight ≤ W0 := by
                      have := weight_le_of_mem_left hW h3
                      simp only [PLLFormula.weight] at this ⊢
                      omega
                    congr 1
                    · cases b with
                      | zero => rfl
                      | succ b' =>
                          dsimp only
                          rw [ihA hcap wOA.2 (mu_jump_lt wOA.2),
                            ihA (cap_cons (weight_le_of_mem_left hW h2) hcap) hCw
                              (mu_defect_lt (defect_cons_lt h2 h1) (Nat.le_refl _)),
                            ihE hcap (mu_jump_lt (Nat.zero_le _)),
                            ihA hcap wOA.1 (mu_jump_lt wOA.1)]
                    · refine List.filterMap_congr ?_
                      intro X _
                      cases X with
                      | prop _ => rfl
                      | falsePLL => rfl
                      | and _ _ => rfl
                      | or _ _ => rfl
                      | ifThen _ _ => rfl
                      | somehow x =>
                          dsimp only
                          split_ifs with hx
                          · rfl
                          · push_neg at hx
                            have wOA' : (A.somehow).weight ≤ W0 := by
                              have := hcap _ hF
                              simp only [PLLFormula.weight] at this ⊢
                              omega
                            rw [ihE (cap_cons (weight_le_of_mem_left hW hx.2) hcap)
                                (mu_growth_lt (defect_cons_lt hx.2 hx.1)
                                  (Nat.zero_le _)),
                              ihA (cap_cons (weight_le_of_mem_left hW hx.2) hcap)
                                wOA'
                                (mu_growth_lt (defect_cons_lt hx.2 hx.1) wOA'),
                              ihA (cap_cons (weight_le_of_mem_left hW h2) hcap)
                                hCw
                                (mu_defect_lt (defect_cons_lt h2 h1)
                                  (Nat.le_refl _))]
                  · congr 1
                    refine List.filterMap_congr ?_
                    intro X _
                    cases X with
                    | prop _ => rfl
                    | falsePLL => rfl
                    | and _ _ => rfl
                    | or _ _ => rfl
                    | ifThen _ _ => rfl
                    | somehow x =>
                        dsimp only
                        split_ifs with hx
                        · rfl
                        · push_neg at hx
                          have wOA' : (A.somehow).weight ≤ W0 := by
                            have := hcap _ hF
                            simp only [PLLFormula.weight] at this ⊢
                            omega
                          rw [ihE (cap_cons (weight_le_of_mem_left hW hx.2) hcap)
                              (mu_growth_lt (defect_cons_lt hx.2 hx.1)
                                (Nat.zero_le _)),
                            ihA (cap_cons (weight_le_of_mem_left hW hx.2) hcap)
                              wOA'
                              (mu_growth_lt (defect_cons_lt hx.2 hx.1) wOA'),
                            ihA (cap_cons (weight_le_of_mem_left hW h2) hcap)
                              hCw
                              (mu_defect_lt (defect_cons_lt h2 h1)
                                (Nat.le_refl _))]
                  · rfl
        have hoth : itpAoth p S (f' + 1) b Γ C = itpAoth p S f' b Γ C := by
          unfold itpAoth
          rw [hgoal, henv]
        congr 1
        cases C with
        | prop q => exact hoth
        | falsePLL => exact hoth
        | and _ _ => exact hoth
        | or _ _ => exact hoth
        | ifThen _ _ => exact hoth
        | somehow D =>
            simp only [itpAfull]
            rw [hoth]
            congr 1
            split_ifs with hemp
            · rfl
            · cases b with
              | zero => rfl
              | succ b' =>
                  dsimp only
                  rw [ihE hcap (mu_jump_lt (Nat.zero_le _))]

/-! ### Chained corollaries: any two fuels above `mu` agree -/

private theorem itpE_add (p : String) (S : Finset PLLFormula) (W0 : Nat)
    (hW : S.sup PLLFormula.weight ≤ W0) {b : Nat} {Γ : List PLLFormula}
    (hcap : ∀ F ∈ Γ, F.weight ≤ W0) {f : Nat} (hf : mu S W0 b 0 Γ < f) :
    ∀ k, itpE p S (f + k) b Γ = itpE p S f b Γ := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      have h1 := (itp_indiff p S W0 hW (f + k)).1 b Γ hcap
        (lt_of_lt_of_le hf (Nat.le_add_right f k))
      show itpE p S (f + k + 1) b Γ = itpE p S f b Γ
      rw [h1, ih]

private theorem itpA_add (p : String) (S : Finset PLLFormula) (W0 : Nat)
    (hW : S.sup PLLFormula.weight ≤ W0) {b : Nat} {Γ : List PLLFormula}
    {C : PLLFormula} (hcap : ∀ F ∈ Γ, F.weight ≤ W0) (hCw : C.weight ≤ W0)
    {f : Nat} (hf : mu S W0 b C.weight Γ < f) :
    ∀ k, itpA p S (f + k) b Γ C = itpA p S f b Γ C := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      have h1 := (itp_indiff p S W0 hW (f + k)).2 b Γ C hcap hCw
        (lt_of_lt_of_le hf (Nat.le_add_right f k))
      show itpA p S (f + k + 1) b Γ C = itpA p S f b Γ C
      rw [h1, ih]

/-- **Fuel indifference, chained (E).**  Any two fuels above the
measure give the *same* formula. -/
theorem itpE_indiff_ge (p : String) (S : Finset PLLFormula) (W0 : Nat)
    (hW : S.sup PLLFormula.weight ≤ W0) {f g b : Nat}
    {Γ : List PLLFormula} (hcap : ∀ F ∈ Γ, F.weight ≤ W0)
    (hf : mu S W0 b 0 Γ < f) (hg : mu S W0 b 0 Γ < g) :
    itpE p S f b Γ = itpE p S g b Γ := by
  rcases Nat.le_total f g with h | h
  · obtain ⟨k, rfl⟩ := Nat.le.dest h
    exact (itpE_add p S W0 hW hcap hf k).symm
  · obtain ⟨k, rfl⟩ := Nat.le.dest h
    exact itpE_add p S W0 hW hcap hg k

/-- **Fuel indifference, chained (A).** -/
theorem itpA_indiff_ge (p : String) (S : Finset PLLFormula) (W0 : Nat)
    (hW : S.sup PLLFormula.weight ≤ W0) {f g b : Nat}
    {Γ : List PLLFormula} {C : PLLFormula}
    (hcap : ∀ F ∈ Γ, F.weight ≤ W0) (hCw : C.weight ≤ W0)
    (hf : mu S W0 b C.weight Γ < f) (hg : mu S W0 b C.weight Γ < g) :
    itpA p S f b Γ C = itpA p S g b Γ C := by
  rcases Nat.le_total f g with h | h
  · obtain ⟨k, rfl⟩ := Nat.le.dest h
    exact (itpA_add p S W0 hW hcap hCw hf k).symm
  · obtain ⟨k, rfl⟩ := Nat.le.dest h
    exact itpA_add p S W0 hW hcap hCw hg k

end PLLND
