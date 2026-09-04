import wip.rnClass

/-!
# RN classification, stages 4–5: the derivations, and im h = rungs ∪ {⊤}

`docs/rn-classification-plan.md` stages 4 and 5.  Stage 4 turns each
row of the three Heyting tables (`meetC`, `joinC`, `impC` of
`wip/rnClass.lean`) into an interderivability between substituted
rungs (`meet_interd`, `join_interd`, `imp_interd`).  The easy sides
are all rung order through `rnSub_order`; the hard sides are ≤ 4-step
modus-ponens compositions through the Rieger–Nishimura recursion

    rn (2a+2) = rn (2a+1) ⊃ rn (2a−1)      (ℕ-truncated: at a = 0 this is ¬p = p ⊃ ⊥)
    rn (2a+3) = rn (2a+1) ∨ rn (2a+2)

under the substitution `p ↦ ◯⊥`.  Stage 5 is the structural induction
`rn_classification`: every ◯-free formula in the single variable `p`
is, after the substitution, interderivable with a substituted rung or
with `⊤`.  That discharges the standing caveat: `q5`, `◯q11`, and the
whole chain `chainF k` are off the image of `h` *simpliciter*, and
RN(◯,{}) ∖ im h is infinite with no side condition.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND UpCode

/-! ## The formula named by a code -/

/-- The rung (or `⊤ = q1`) named by a code. -/
def toS : UpCode → PLLFormula
  | .bot => rnSub 0
  | .odd a => rnSub (2 * a + 1)
  | .even a => rnSub (2 * a + 2)
  | .top => q1

/-! ## The recursion equations under the substitution -/

theorem rnSub_zero : rnSub 0 = PLLFormula.falsePLL := rfl

/-- The even-rung recursion, ℕ-truncated so it holds at EVERY index:
`rnSub (2a+2) = rnSub (2a+1) ⊃ rnSub (2a−1)`.  At `a = 0` this reads
`¬◯⊥ = ◯⊥ ⊃ ⊥` (with `2·0−1 = 0` and `rnSub 0 = ⊥`). -/
theorem rnSub_even_eq (a : Nat) :
    rnSub (2 * a + 2) = (rnSub (2 * a + 1)).ifThen (rnSub (2 * a - 1)) := by
  cases a with
  | zero =>
      show embed (rn 2) = (embed (rn 1)).ifThen (embed (rn 0))
      rw [rn_zero, rn_one, rn_two]
      rfl
  | succ k =>
      have e1 : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
      have e2 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      have e3 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [e1, e2, e3]
      show embed (rn (2 * k + 4))
          = (embed (rn (2 * k + 3))).ifThen (embed (rn (2 * k + 1)))
      rw [rn_even_rec k]
      rfl

/-- The odd-rung recursion under the substitution:
`rnSub (2a+3) = rnSub (2a+1) ∨ rnSub (2a+2)`. -/
theorem rnSub_odd_eq (a : Nat) :
    rnSub (2 * a + 3) = (rnSub (2 * a + 1)).or (rnSub (2 * a + 2)) := by
  show embed (rn (2 * a + 3))
      = (embed (rn (2 * a + 1))).or (embed (rn (2 * a + 2)))
  rw [rn_odd_rec a]
  rfl

/-- `toS (predOdd a) = rnSub (2a−1)`, uniformly (truncation at 0). -/
theorem toS_predOdd (a : Nat) : toS (predOdd a) = rnSub (2 * a - 1) := by
  cases a with
  | zero => rfl
  | succ k =>
      have e : predOdd (k + 1) = UpCode.odd k := by simp [predOdd]
      have e2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [e, e2]
      rfl

/-! ## Rung order at parameterised indices

Each lemma is truth-set containment made arithmetic, in the style of
`odd_chain` / `even_le_even`; `rungD` converts to a derivation through
`rnSub_order`. -/

/-- Rung order to derivation: the workhorse. -/
theorem rungD {i j : Nat} (h : rungLe i j = true) :
    Deriv [rnSub i] (rnSub j) :=
  (rnSub_order i j).mpr h

theorem bot_le (n : Nat) : rungLe 0 n = true := by
  simp only [rungLe, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  intro w _
  exact Or.inl (rungMem_zero w)

theorem oo_le {a b : Nat} (h : a ≤ b) :
    rungLe (2 * a + 1) (2 * b + 1) = true := by
  simp only [rungLe, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  intro w _
  by_cases hw : rungMem (2 * a + 1) w = true
  · refine Or.inr ?_
    rw [rungMem_odd] at hw
    rw [rungMem_odd]
    simp only [decide_eq_true_eq] at hw
    simp only [decide_eq_true_eq]
    omega
  · exact Or.inl (by simpa using hw)

theorem oe_le {a b : Nat} (h : a + 1 ≤ b) :
    rungLe (2 * a + 1) (2 * b + 2) = true := by
  simp only [rungLe, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  intro w _
  by_cases hw : rungMem (2 * a + 1) w = true
  · refine Or.inr ?_
    rw [rungMem_odd] at hw
    rw [rungMem_even]
    simp only [decide_eq_true_eq] at hw
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  · exact Or.inl (by simpa using hw)

theorem eo_le {a b : Nat} (h : a + 1 ≤ b) :
    rungLe (2 * a + 2) (2 * b + 1) = true := by
  simp only [rungLe, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  intro w _
  by_cases hw : rungMem (2 * a + 2) w = true
  · refine Or.inr ?_
    rw [rungMem_even] at hw
    rw [rungMem_odd]
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hw
    simp only [decide_eq_true_eq]
    omega
  · exact Or.inl (by simpa using hw)

theorem pred_oo_le {a b : Nat} (h : a ≤ b + 1) :
    rungLe (2 * a - 1) (2 * b + 1) = true := by
  cases a with
  | zero => exact bot_le _
  | succ k =>
      have e : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [e]
      exact oo_le (by omega)

theorem pred_oe_le {a b : Nat} (h : a ≤ b) :
    rungLe (2 * a - 1) (2 * b + 2) = true := by
  cases a with
  | zero => exact bot_le _
  | succ k =>
      have e : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [e]
      exact oe_le (by omega)

/-! ## Small derivation kit -/

/-- `⊤` (as `q1 = ⊥ ⊃ ⊥`) is derivable in any context. -/
theorem dTop {Γ : List PLLFormula} : Deriv Γ q1 :=
  Deriv.impIntro (Deriv.iden (.head _))

/-- From `⊥` (as `rnSub 0`) anything follows. -/
theorem dBot {X : PLLFormula} : Deriv [rnSub 0] X := by
  refine Deriv.falsoElim _ ?_
  rw [rnSub_zero]
  exact Deriv.iden (.head _)

/-! ## The schema derivations (the hard sides of the diagonal rows) -/

/-- **Meet, diagonal**: `rnSub (2a+1) ∧ rnSub (2a+2) ⊢ rnSub (2a−1)` —
modus ponens of the conjuncts through the even-rung recursion. -/
theorem meet_diag (a : Nat) :
    Deriv [(rnSub (2 * a + 1)).and (rnSub (2 * a + 2))] (rnSub (2 * a - 1)) := by
  have h2 : Deriv [(rnSub (2 * a + 1)).and (rnSub (2 * a + 2))]
      ((rnSub (2 * a + 1)).ifThen (rnSub (2 * a - 1))) := by
    rw [← rnSub_even_eq a]
    exact Deriv.andElim2 (Deriv.iden (.head _))
  exact Deriv.impElim h2 (Deriv.andElim1 (Deriv.iden (.head _)))

/-- **Meet, consecutive evens**:
`rnSub (2a+2) ∧ rnSub (2a+4) ⊢ rnSub (2a−1)`.  The right conjunct is
`rnSub (2a+3) ⊃ rnSub (2a+1)`; the left conjunct climbs to
`rnSub (2a+3)` by rung order, modus ponens lands `rnSub (2a+1)`, and a
second modus ponens through the left conjunct's own recursion lands
`rnSub (2a−1)`. -/
theorem meet_evens (a : Nat) :
    Deriv [(rnSub (2 * a + 2)).and (rnSub (2 * a + 4))] (rnSub (2 * a - 1)) := by
  have h1 : Deriv [(rnSub (2 * a + 2)).and (rnSub (2 * a + 4))]
      (rnSub (2 * a + 2)) := Deriv.andElim1 (Deriv.iden (.head _))
  have h2 : Deriv [(rnSub (2 * a + 2)).and (rnSub (2 * a + 4))]
      ((rnSub (2 * a + 3)).ifThen (rnSub (2 * a + 1))) := by
    have e4 : (2 : Nat) * a + 4 = 2 * (a + 1) + 2 := by omega
    have e3 : (2 : Nat) * a + 3 = 2 * (a + 1) + 1 := by omega
    have e1 : (2 : Nat) * a + 1 = 2 * (a + 1) - 1 := by omega
    rw [e3, e1, ← rnSub_even_eq (a + 1), ← e4]
    exact Deriv.andElim2 (Deriv.iden (.head _))
  have hup : Deriv [(rnSub (2 * a + 2)).and (rnSub (2 * a + 4))]
      (rnSub (2 * a + 3)) := by
    refine Deriv.cutHead h1 ?_
    have := rungD (eo_le (show a + 1 ≤ a + 1 from Nat.le_refl _))
    rw [show (2 * (a + 1) + 1 : Nat) = 2 * a + 3 from by omega] at this
    exact this
  have hO : Deriv [(rnSub (2 * a + 2)).and (rnSub (2 * a + 4))]
      (rnSub (2 * a + 1)) := Deriv.impElim h2 hup
  have h1' : Deriv [(rnSub (2 * a + 2)).and (rnSub (2 * a + 4))]
      ((rnSub (2 * a + 1)).ifThen (rnSub (2 * a - 1))) := by
    rw [← rnSub_even_eq a]
    exact h1
  exact Deriv.impElim h1' hO

/-- **Join, consecutive evens**:
`rnSub (2a+5) ⊢ rnSub (2a+2) ∨ rnSub (2a+4)` — unfold the odd-rung
recursion twice; the even branches inject, the odd branch rises by
rung order. -/
theorem join_evens (a : Nat) :
    Deriv [rnSub (2 * a + 5)] ((rnSub (2 * a + 2)).or (rnSub (2 * a + 4))) := by
  have d0 : Deriv [rnSub (2 * a + 5)]
      ((rnSub (2 * a + 3)).or (rnSub (2 * a + 4))) := by
    rw [show (2 * a + 5 : Nat) = 2 * (a + 1) + 3 from by omega,
        rnSub_odd_eq (a + 1),
        show (2 * (a + 1) + 1 : Nat) = 2 * a + 3 from by omega,
        show (2 * (a + 1) + 2 : Nat) = 2 * a + 4 from by omega]
    exact Deriv.iden (.head _)
  refine Deriv.orElim d0 ?_ ?_
  · -- the rnSub (2a+3) branch: unfold once more
    have d1 : Deriv [rnSub (2 * a + 3)]
        ((rnSub (2 * a + 1)).or (rnSub (2 * a + 2))) := by
      rw [rnSub_odd_eq a]
      exact Deriv.iden (.head _)
    refine Deriv.orElim (Deriv.cutHead (Deriv.iden (.head _)) d1) ?_ ?_
    · -- rnSub (2a+1) ≤ rnSub (2a+4)
      refine Deriv.orIntro2 ?_
      have := rungD (oe_le (show a + 1 ≤ a + 1 from Nat.le_refl _))
      rw [show (2 * (a + 1) + 2 : Nat) = 2 * a + 4 from by omega] at this
      exact Deriv.toHead this
    · exact Deriv.orIntro1 (Deriv.iden (.head _))
  · exact Deriv.orIntro2 (Deriv.iden (.head _))

/-! ## Stage 4: the three table lemmas -/

/-- **Meet.**  The conjunction of two coded rungs is interderivable
with the coded meet. -/
theorem meet_interd (c d : UpCode) :
    Interd ((toS c).and (toS d)) (toS (meetC c d)) := by
  rcases c with _ | a | a | _ <;> rcases d with _ | b | b | _ <;>
    simp only [meetC]
  case bot.bot =>
    exact ⟨Deriv.andElim1 (Deriv.iden (.head _)), dBot⟩
  case bot.odd =>
    exact ⟨Deriv.andElim1 (Deriv.iden (.head _)), dBot⟩
  case bot.even =>
    exact ⟨Deriv.andElim1 (Deriv.iden (.head _)), dBot⟩
  case bot.top =>
    exact ⟨Deriv.andElim1 (Deriv.iden (.head _)), dBot⟩
  case odd.bot =>
    exact ⟨Deriv.andElim2 (Deriv.iden (.head _)), dBot⟩
  case even.bot =>
    exact ⟨Deriv.andElim2 (Deriv.iden (.head _)), dBot⟩
  case top.bot =>
    exact ⟨Deriv.andElim2 (Deriv.iden (.head _)), dBot⟩
  case top.top =>
    exact ⟨Deriv.andElim1 (Deriv.iden (.head _)),
           Deriv.andIntro dTop dTop⟩
  case top.odd =>
    exact ⟨Deriv.andElim2 (Deriv.iden (.head _)),
           Deriv.andIntro dTop (Deriv.iden (.head _))⟩
  case top.even =>
    exact ⟨Deriv.andElim2 (Deriv.iden (.head _)),
           Deriv.andIntro dTop (Deriv.iden (.head _))⟩
  case odd.top =>
    exact ⟨Deriv.andElim1 (Deriv.iden (.head _)),
           Deriv.andIntro (Deriv.iden (.head _)) dTop⟩
  case even.top =>
    exact ⟨Deriv.andElim1 (Deriv.iden (.head _)),
           Deriv.andIntro (Deriv.iden (.head _)) dTop⟩
  case odd.odd =>
    rcases Nat.le_total a b with h | h
    · rw [Nat.min_eq_left h]
      exact ⟨Deriv.andElim1 (Deriv.iden (.head _)),
             Deriv.andIntro (Deriv.iden (.head _)) (rungD (oo_le h))⟩
    · rw [Nat.min_eq_right h]
      exact ⟨Deriv.andElim2 (Deriv.iden (.head _)),
             Deriv.andIntro (rungD (oo_le h)) (Deriv.iden (.head _))⟩
  case odd.even =>
    split_ifs with h1 h2
    · -- a < b: meet = odd a
      simp only [toS]
      exact ⟨Deriv.andElim1 (Deriv.iden (.head _)),
             Deriv.andIntro (Deriv.iden (.head _)) (rungD (oe_le (by omega)))⟩
    · -- b < a: meet = even b
      simp only [toS]
      exact ⟨Deriv.andElim2 (Deriv.iden (.head _)),
             Deriv.andIntro (rungD (eo_le (by omega))) (Deriv.iden (.head _))⟩
    · -- a = b: meet = predOdd b
      have e : a = b := by omega
      subst e
      rw [toS_predOdd]
      exact ⟨meet_diag a,
             Deriv.andIntro (rungD (pred_oo_le (by omega)))
               (rungD (pred_oe_le (by omega)))⟩
  case even.odd =>
    split_ifs with h1 h2
    · -- b < a: meet = odd b
      simp only [toS]
      exact ⟨Deriv.andElim2 (Deriv.iden (.head _)),
             Deriv.andIntro (rungD (oe_le (by omega))) (Deriv.iden (.head _))⟩
    · -- a < b: meet = even a
      simp only [toS]
      exact ⟨Deriv.andElim1 (Deriv.iden (.head _)),
             Deriv.andIntro (Deriv.iden (.head _)) (rungD (eo_le (by omega)))⟩
    · -- a = b: meet = predOdd a
      have e : a = b := by omega
      subst e
      rw [toS_predOdd]
      constructor
      · refine Deriv.cutHead ?_ (meet_diag a)
        exact Deriv.andIntro (Deriv.andElim2 (Deriv.iden (.head _)))
          (Deriv.andElim1 (Deriv.iden (.head _)))
      · exact Deriv.andIntro (rungD (pred_oe_le (by omega)))
          (rungD (pred_oo_le (by omega)))
  case even.even =>
    split_ifs with h1 h2 h3 h4
    · -- a = b
      subst h1
      exact ⟨Deriv.andElim1 (Deriv.iden (.head _)),
             Deriv.andIntro (Deriv.iden (.head _)) (Deriv.iden (.head _))⟩
    · -- a + 2 ≤ b: meet = even a
      exact ⟨Deriv.andElim1 (Deriv.iden (.head _)),
             Deriv.andIntro (Deriv.iden (.head _))
               (rungD (even_le_even a b (Or.inr h2)))⟩
    · -- b + 2 ≤ a: meet = even b
      exact ⟨Deriv.andElim2 (Deriv.iden (.head _)),
             Deriv.andIntro (rungD (even_le_even b a (Or.inr h3)))
               (Deriv.iden (.head _))⟩
    · -- a < b with b = a + 1: meet = predOdd a
      have e : b = a + 1 := by omega
      subst e
      rw [toS_predOdd]
      constructor
      · simp only [toS]
        rw [show (2 : Nat) * (a + 1) + 2 = 2 * a + 4 from by omega]
        exact meet_evens a
      · refine Deriv.andIntro (rungD (pred_oe_le (by omega))) ?_
        have := rungD (pred_oe_le (show a ≤ a + 1 from by omega))
        exact this
    · -- b < a with a = b + 1: meet = predOdd b
      have e : a = b + 1 := by omega
      subst e
      rw [toS_predOdd]
      constructor
      · simp only [toS]
        rw [show (2 : Nat) * (b + 1) + 2 = 2 * b + 4 from by omega]
        refine Deriv.cutHead ?_ (meet_evens b)
        exact Deriv.andIntro (Deriv.andElim2 (Deriv.iden (.head _)))
          (Deriv.andElim1 (Deriv.iden (.head _)))
      · refine Deriv.andIntro ?_ (rungD (pred_oe_le (by omega)))
        exact rungD (pred_oe_le (by omega))

/-- **Join.**  The disjunction of two coded rungs is interderivable
with the coded join. -/
theorem join_interd (c d : UpCode) :
    Interd ((toS c).or (toS d)) (toS (joinC c d)) := by
  rcases c with _ | a | a | _ <;> rcases d with _ | b | b | _ <;>
    simp only [joinC]
  case top.bot =>
    exact ⟨dTop, Deriv.orIntro1 (Deriv.iden (.head _))⟩
  case top.odd =>
    exact ⟨dTop, Deriv.orIntro1 (Deriv.iden (.head _))⟩
  case top.even =>
    exact ⟨dTop, Deriv.orIntro1 (Deriv.iden (.head _))⟩
  case top.top =>
    exact ⟨dTop, Deriv.orIntro1 (Deriv.iden (.head _))⟩
  case bot.top =>
    exact ⟨dTop, Deriv.orIntro2 (Deriv.iden (.head _))⟩
  case odd.top =>
    exact ⟨dTop, Deriv.orIntro2 (Deriv.iden (.head _))⟩
  case even.top =>
    exact ⟨dTop, Deriv.orIntro2 (Deriv.iden (.head _))⟩
  case bot.bot =>
    exact ⟨Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _))
             (Deriv.iden (.head _)),
           Deriv.orIntro1 (Deriv.iden (.head _))⟩
  case bot.odd =>
    exact ⟨Deriv.orElim (Deriv.iden (.head _)) (Deriv.toHead dBot)
             (Deriv.iden (.head _)),
           Deriv.orIntro2 (Deriv.iden (.head _))⟩
  case bot.even =>
    exact ⟨Deriv.orElim (Deriv.iden (.head _)) (Deriv.toHead dBot)
             (Deriv.iden (.head _)),
           Deriv.orIntro2 (Deriv.iden (.head _))⟩
  case odd.bot =>
    exact ⟨Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _))
             (Deriv.toHead dBot),
           Deriv.orIntro1 (Deriv.iden (.head _))⟩
  case even.bot =>
    exact ⟨Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _))
             (Deriv.toHead dBot),
           Deriv.orIntro1 (Deriv.iden (.head _))⟩
  case odd.odd =>
    rcases Nat.le_total a b with h | h
    · rw [Nat.max_eq_right h]
      exact ⟨Deriv.orElim (Deriv.iden (.head _))
               (Deriv.toHead (rungD (oo_le h))) (Deriv.iden (.head _)),
             Deriv.orIntro2 (Deriv.iden (.head _))⟩
    · rw [Nat.max_eq_left h]
      exact ⟨Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _))
               (Deriv.toHead (rungD (oo_le h))),
             Deriv.orIntro1 (Deriv.iden (.head _))⟩
  case odd.even =>
    split_ifs with h1 h2
    · -- b < a: join = odd a
      simp only [toS]
      exact ⟨Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _))
               (Deriv.toHead (rungD (eo_le (by omega)))),
             Deriv.orIntro1 (Deriv.iden (.head _))⟩
    · -- a < b: join = even b
      simp only [toS]
      exact ⟨Deriv.orElim (Deriv.iden (.head _))
               (Deriv.toHead (rungD (oe_le (by omega))))
               (Deriv.iden (.head _)),
             Deriv.orIntro2 (Deriv.iden (.head _))⟩
    · -- a = b: join = odd (b+1), definitionally the disjunction itself
      have e : a = b := by omega
      subst e
      simp only [toS]
      rw [show (2 * (a + 1) + 1 : Nat) = 2 * a + 3 from by omega,
          rnSub_odd_eq a]
      exact Interd.refl _
  case even.odd =>
    split_ifs with h1 h2
    · -- a < b: join = odd b
      simp only [toS]
      exact ⟨Deriv.orElim (Deriv.iden (.head _))
               (Deriv.toHead (rungD (eo_le (by omega))))
               (Deriv.iden (.head _)),
             Deriv.orIntro2 (Deriv.iden (.head _))⟩
    · -- b < a: join = even a
      simp only [toS]
      exact ⟨Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _))
               (Deriv.toHead (rungD (oe_le (by omega)))),
             Deriv.orIntro1 (Deriv.iden (.head _))⟩
    · -- a = b: join = odd (a+1); flip then the definitional unfold
      have e : a = b := by omega
      subst e
      simp only [toS]
      rw [show (2 * (a + 1) + 1 : Nat) = 2 * a + 3 from by omega,
          rnSub_odd_eq a]
      constructor
      · exact Deriv.orElim (Deriv.iden (.head _))
          (Deriv.orIntro2 (Deriv.iden (.head _)))
          (Deriv.orIntro1 (Deriv.iden (.head _)))
      · exact Deriv.orElim (Deriv.iden (.head _))
          (Deriv.orIntro2 (Deriv.iden (.head _)))
          (Deriv.orIntro1 (Deriv.iden (.head _)))
  case even.even =>
    split_ifs with h1 h2 h3 h4
    · -- a = b
      subst h1
      exact ⟨Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _))
               (Deriv.iden (.head _)),
             Deriv.orIntro1 (Deriv.iden (.head _))⟩
    · -- a + 2 ≤ b: join = even b
      exact ⟨Deriv.orElim (Deriv.iden (.head _))
               (Deriv.toHead (rungD (even_le_even a b (Or.inr h2))))
               (Deriv.iden (.head _)),
             Deriv.orIntro2 (Deriv.iden (.head _))⟩
    · -- b + 2 ≤ a: join = even a
      exact ⟨Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _))
               (Deriv.toHead (rungD (even_le_even b a (Or.inr h3)))),
             Deriv.orIntro1 (Deriv.iden (.head _))⟩
    · -- a < b with b = a + 1: join = odd (a+2)
      have e : b = a + 1 := by omega
      subst e
      constructor
      · refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
        · exact Deriv.toHead (rungD (eo_le (show a + 1 ≤ a + 2 from by omega)))
        · exact Deriv.toHead (rungD (eo_le (show (a + 1) + 1 ≤ a + 2 from by omega)))
      · have := join_evens a
        rw [show (2 * a + 5 : Nat) = 2 * (a + 2) + 1 from by omega,
            show (2 * a + 4 : Nat) = 2 * (a + 1) + 2 from by omega] at this
        exact this
    · -- b < a with a = b + 1: join = odd (b+2); flip
      have e : a = b + 1 := by omega
      subst e
      constructor
      · refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
        · exact Deriv.toHead (rungD (eo_le (show (b + 1) + 1 ≤ b + 2 from by omega)))
        · exact Deriv.toHead (rungD (eo_le (show b + 1 ≤ b + 2 from by omega)))
      · have hj := join_evens b
        rw [show (2 * b + 5 : Nat) = 2 * (b + 2) + 1 from by omega,
            show (2 * b + 4 : Nat) = 2 * (b + 1) + 2 from by omega] at hj
        refine Deriv.cutHead hj ?_
        exact Deriv.orElim (Deriv.iden (.head _))
          (Deriv.orIntro2 (Deriv.iden (.head _)))
          (Deriv.orIntro1 (Deriv.iden (.head _)))

/-- **Implication.**  The implication between two coded rungs is
interderivable with the coded Heyting implication. -/
theorem imp_interd (c d : UpCode) :
    Interd ((toS c).ifThen (toS d)) (toS (impC c d)) := by
  rcases c with _ | a | a | _ <;> rcases d with _ | b | b | _ <;>
    simp only [impC]
  -- source ⊥: implication is ⊤
  case bot.bot =>
    exact ⟨dTop, Deriv.impIntro (Deriv.toHead dBot)⟩
  case bot.odd =>
    exact ⟨dTop, Deriv.impIntro (Deriv.toHead dBot)⟩
  case bot.even =>
    exact ⟨dTop, Deriv.impIntro (Deriv.toHead dBot)⟩
  case bot.top =>
    exact ⟨dTop, Deriv.impIntro (Deriv.toHead dBot)⟩
  -- target ⊤: implication is ⊤
  case odd.top =>
    exact ⟨dTop, Deriv.impIntro dTop⟩
  case even.top =>
    exact ⟨dTop, Deriv.impIntro dTop⟩
  case top.top =>
    exact ⟨dTop, Deriv.impIntro dTop⟩
  -- source ⊤: implication is the target
  case top.bot =>
    exact ⟨Deriv.impElim (Deriv.iden (.head _)) dTop,
           Deriv.impIntro (Deriv.iden (.tail _ (.head _)))⟩
  case top.odd =>
    exact ⟨Deriv.impElim (Deriv.iden (.head _)) dTop,
           Deriv.impIntro (Deriv.iden (.tail _ (.head _)))⟩
  case top.even =>
    exact ⟨Deriv.impElim (Deriv.iden (.head _)) dTop,
           Deriv.impIntro (Deriv.iden (.tail _ (.head _)))⟩
  -- ¬(odd a)
  case odd.bot =>
    split_ifs with h1
    · -- a = 0: ¬◯⊥, definitionally rnSub 2
      subst h1
      simp only [toS]
      rw [rnSub_even_eq 0]
      exact Interd.refl _
    · -- a ≥ 1: the negation is ⊥
      simp only [toS]
      constructor
      · -- [rnSub (2a+1) ⊃ ⊥] ⊢ ⊥
        have hE0 : Deriv [(rnSub (2 * a + 1)).ifThen (rnSub 0)]
            (rnSub (2 * 0 + 2)) := by
          rw [rnSub_even_eq 0]
          refine Deriv.impIntro ?_
          have hup : Deriv [rnSub (2 * 0 + 1),
              (rnSub (2 * a + 1)).ifThen (rnSub 0)] (rnSub (2 * a + 1)) :=
            Deriv.cutHead (Deriv.iden (.head _)) (rungD (oo_le (Nat.zero_le a)))
          exact Deriv.impElim (Deriv.iden (.tail _ (.head _))) hup
        have hOa : Deriv [(rnSub (2 * a + 1)).ifThen (rnSub 0)]
            (rnSub (2 * a + 1)) :=
          Deriv.cutHead hE0 (rungD (eo_le (show 0 + 1 ≤ a from by omega)))
        exact Deriv.impElim (Deriv.iden (.head _)) hOa
      · exact dBot
  -- ¬(even a)
  case even.bot =>
    split_ifs with h1 h2
    · -- a = 0: ¬¬◯⊥ ≡ rnSub 4
      subst h1
      simp only [toS]
      constructor
      · -- [rnSub 2 ⊃ ⊥] ⊢ rnSub 4
        rw [rnSub_even_eq 1,
            show (2 * 1 + 1 : Nat) = 2 * 0 + 3 from by omega,
            show (2 * 1 - 1 : Nat) = 2 * 0 + 1 from by omega]
        refine Deriv.impIntro ?_
        -- ctx [rnSub (2·0+3), H] ⊢ rnSub (2·0+1)
        rw [rnSub_odd_eq 0]
        refine Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _)) ?_
        -- ctx [rnSub (2·0+2), or-form, H] ⊢ rnSub (2·0+1)
        refine Deriv.falsoElim _ ?_
        have hH : Deriv [rnSub (2 * 0 + 2),
            (rnSub (2 * 0 + 1)).or (rnSub (2 * 0 + 2)),
            (rnSub (2 * 0 + 2)).ifThen (rnSub 0)] ((rnSub (2 * 0 + 2)).ifThen (rnSub 0)) :=
          Deriv.iden (.tail _ (.tail _ (.head _)))
        have h0 := Deriv.impElim hH (Deriv.iden (.head _))
        rw [rnSub_zero] at h0
        exact h0
      · -- [rnSub 4] ⊢ rnSub 2 ⊃ ⊥
        refine Deriv.impIntro ?_
        -- ctx [rnSub (2·0+2), rnSub 4] ⊢ ⊥
        have hup : Deriv [rnSub (2 * 0 + 2), rnSub (2 * 1 + 2)]
            (rnSub (2 * 0 + 3)) :=
          Deriv.cutHead (Deriv.iden (.head _))
            (by
              have := rungD (eo_le (show 0 + 1 ≤ 1 from by omega))
              rw [show (2 * 1 + 1 : Nat) = 2 * 0 + 3 from by omega] at this
              exact this)
        have hE1 : Deriv [rnSub (2 * 0 + 2), rnSub (2 * 1 + 2)]
            ((rnSub (2 * 0 + 3)).ifThen (rnSub (2 * 0 + 1))) := by
          have h := Deriv.iden (φ := rnSub (2 * 1 + 2))
            (Γ := [rnSub (2 * 0 + 2), rnSub (2 * 1 + 2)]) (.tail _ (.head _))
          rw [rnSub_even_eq 1,
              show (2 * 1 + 1 : Nat) = 2 * 0 + 3 from by omega,
              show (2 * 1 - 1 : Nat) = 2 * 0 + 1 from by omega] at h
          exact h
        have hO0 := Deriv.impElim hE1 hup
        have hE0 : Deriv [rnSub (2 * 0 + 2), rnSub (2 * 1 + 2)]
            ((rnSub (2 * 0 + 1)).ifThen (rnSub (2 * 0 - 1))) := by
          have h := Deriv.iden (φ := rnSub (2 * 0 + 2))
            (Γ := [rnSub (2 * 0 + 2), rnSub (2 * 1 + 2)]) (.head _)
          rw [rnSub_even_eq 0] at h
          exact h
        have hb := Deriv.impElim hE0 hO0
        rw [show (2 * 0 - 1 : Nat) = 0 from by omega, rnSub_zero] at hb
        exact hb
    · -- a = 1: ¬(rnSub 4) ≡ rnSub 2
      subst h2
      simp only [toS]
      constructor
      · -- [rnSub 4 ⊃ ⊥] ⊢ rnSub 2
        rw [rnSub_even_eq 0]
        refine Deriv.impIntro ?_
        -- ctx [rnSub (2·0+1), H] ⊢ rnSub (2·0−1) = ⊥
        have hup : Deriv [rnSub (2 * 0 + 1),
            (rnSub (2 * 1 + 2)).ifThen (rnSub 0)] (rnSub (2 * 1 + 2)) :=
          Deriv.cutHead (Deriv.iden (.head _))
            (rungD (oe_le (show 0 + 1 ≤ 1 from by omega)))
        have h0 := Deriv.impElim (Deriv.iden (.tail _ (.head _))) hup
        rw [rnSub_zero] at h0
        rw [show (2 * 0 - 1 : Nat) = 0 from by omega, rnSub_zero]
        exact h0
      · -- [rnSub 2] ⊢ rnSub 4 ⊃ ⊥
        refine Deriv.impIntro ?_
        -- ctx [rnSub (2·1+2), rnSub (2·0+2)] ⊢ ⊥
        have hup : Deriv [rnSub (2 * 1 + 2), rnSub (2 * 0 + 2)]
            (rnSub (2 * 0 + 3)) :=
          Deriv.cutHead (Deriv.iden (.tail _ (.head _)))
            (by
              have := rungD (eo_le (show 0 + 1 ≤ 1 from by omega))
              rw [show (2 * 1 + 1 : Nat) = 2 * 0 + 3 from by omega] at this
              exact this)
        have hE1 : Deriv [rnSub (2 * 1 + 2), rnSub (2 * 0 + 2)]
            ((rnSub (2 * 0 + 3)).ifThen (rnSub (2 * 0 + 1))) := by
          have h := Deriv.iden (φ := rnSub (2 * 1 + 2))
            (Γ := [rnSub (2 * 1 + 2), rnSub (2 * 0 + 2)]) (.head _)
          rw [rnSub_even_eq 1,
              show (2 * 1 + 1 : Nat) = 2 * 0 + 3 from by omega,
              show (2 * 1 - 1 : Nat) = 2 * 0 + 1 from by omega] at h
          exact h
        have hO0 := Deriv.impElim hE1 hup
        have hE0 : Deriv [rnSub (2 * 1 + 2), rnSub (2 * 0 + 2)]
            ((rnSub (2 * 0 + 1)).ifThen (rnSub (2 * 0 - 1))) := by
          have h := Deriv.iden (φ := rnSub (2 * 0 + 2))
            (Γ := [rnSub (2 * 1 + 2), rnSub (2 * 0 + 2)]) (.tail _ (.head _))
          rw [rnSub_even_eq 0] at h
          exact h
        have hb := Deriv.impElim hE0 hO0
        rw [show (2 * 0 - 1 : Nat) = 0 from by omega, rnSub_zero] at hb
        exact hb
    · -- a ≥ 2: the negation is ⊥
      simp only [toS]
      constructor
      · -- [rnSub (2a+2) ⊃ ⊥] ⊢ ⊥
        have hE0 : Deriv [(rnSub (2 * a + 2)).ifThen (rnSub 0)]
            (rnSub (2 * 0 + 2)) := by
          rw [rnSub_even_eq 0]
          refine Deriv.impIntro ?_
          have hup : Deriv [rnSub (2 * 0 + 1),
              (rnSub (2 * a + 2)).ifThen (rnSub 0)] (rnSub (2 * a + 2)) :=
            Deriv.cutHead (Deriv.iden (.head _))
              (rungD (oe_le (show 0 + 1 ≤ a from by omega)))
          exact Deriv.impElim (Deriv.iden (.tail _ (.head _))) hup
        have hEa : Deriv [(rnSub (2 * a + 2)).ifThen (rnSub 0)]
            (rnSub (2 * a + 2)) :=
          Deriv.cutHead hE0 (rungD (even_le_even 0 a (Or.inr (by omega))))
        exact Deriv.impElim (Deriv.iden (.head _)) hEa
      · exact dBot
  -- odd ⊃ odd
  case odd.odd =>
    split_ifs with h1 h2
    · -- a ≤ b: ⊤
      simp only [toS]
      exact ⟨dTop, Deriv.impIntro (Deriv.toHead (rungD (oo_le h1)))⟩
    · -- a = b + 1: definitionally even (b+1)
      subst h2
      simp only [toS]
      rw [rnSub_even_eq (b + 1),
          show (2 * (b + 1) - 1 : Nat) = 2 * b + 1 from by omega]
      exact Interd.refl _
    · -- a ≥ b + 2: the implication collapses to its consequent
      simp only [toS]
      constructor
      · -- [O_a ⊃ O_b] ⊢ O_b
        have hE : Deriv [(rnSub (2 * a + 1)).ifThen (rnSub (2 * b + 1))]
            (rnSub (2 * (b + 1) + 2)) := by
          rw [rnSub_even_eq (b + 1),
              show (2 * (b + 1) - 1 : Nat) = 2 * b + 1 from by omega,
              show (2 * (b + 1) + 1 : Nat) = 2 * b + 3 from by omega]
          refine Deriv.impIntro ?_
          have hup : Deriv [rnSub (2 * b + 3),
              (rnSub (2 * a + 1)).ifThen (rnSub (2 * b + 1))]
              (rnSub (2 * a + 1)) :=
            Deriv.cutHead (Deriv.iden (.head _))
              (by
                have := rungD (oo_le (show b + 1 ≤ a from by omega))
                rw [show (2 * (b + 1) + 1 : Nat) = 2 * b + 3 from by omega] at this
                exact this)
          exact Deriv.impElim (Deriv.iden (.tail _ (.head _))) hup
        have hOa : Deriv [(rnSub (2 * a + 1)).ifThen (rnSub (2 * b + 1))]
            (rnSub (2 * a + 1)) :=
          Deriv.cutHead hE (rungD (eo_le (show (b + 1) + 1 ≤ a from by omega)))
        exact Deriv.impElim (Deriv.iden (.head _)) hOa
      · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))
  -- odd ⊃ even
  case odd.even =>
    split_ifs with h1
    · -- a + 1 ≤ b: ⊤
      simp only [toS]
      exact ⟨dTop, Deriv.impIntro (Deriv.toHead (rungD (oe_le h1)))⟩
    · -- a ≥ b: the implication collapses to its consequent
      simp only [toS]
      constructor
      · have core : Deriv [(rnSub (2 * a + 1)).ifThen (rnSub (2 * b + 2))]
            ((rnSub (2 * b + 1)).ifThen (rnSub (2 * b - 1))) := by
          refine Deriv.impIntro ?_
          have hup : Deriv [rnSub (2 * b + 1),
              (rnSub (2 * a + 1)).ifThen (rnSub (2 * b + 2))]
              (rnSub (2 * a + 1)) :=
            Deriv.cutHead (Deriv.iden (.head _))
              (rungD (oo_le (show b ≤ a from by omega)))
          have hEb := Deriv.impElim (Deriv.iden (.tail _ (.head _))) hup
          have hEb' : Deriv [rnSub (2 * b + 1),
              (rnSub (2 * a + 1)).ifThen (rnSub (2 * b + 2))]
              ((rnSub (2 * b + 1)).ifThen (rnSub (2 * b - 1))) := by
            rw [← rnSub_even_eq b]
            exact hEb
          exact Deriv.impElim hEb' (Deriv.iden (.head _))
        have conv : Deriv [(rnSub (2 * b + 1)).ifThen (rnSub (2 * b - 1))]
            (rnSub (2 * b + 2)) := by
          rw [rnSub_even_eq b]
          exact Deriv.iden (.head _)
        exact Deriv.cutHead core conv
      · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))
  -- even ⊃ odd
  case even.odd =>
    split_ifs with h1 h2 h3
    · -- a + 1 ≤ b: ⊤
      simp only [toS]
      exact ⟨dTop, Deriv.impIntro (Deriv.toHead (rungD (eo_le h1)))⟩
    · -- b ≤ a ≤ b + 1: the value is even (a+1)
      simp only [toS]
      constructor
      · -- [E_a ⊃ O_b] ⊢ E_{a+1}
        rw [rnSub_even_eq (a + 1),
            show (2 * (a + 1) - 1 : Nat) = 2 * a + 1 from by omega,
            show (2 * (a + 1) + 1 : Nat) = 2 * a + 3 from by omega]
        refine Deriv.impIntro ?_
        -- ctx [rnSub (2a+3), H] ⊢ rnSub (2a+1)
        rw [rnSub_odd_eq a]
        refine Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _)) ?_
        -- ctx [rnSub (2a+2), or-form, H] ⊢ rnSub (2a+1)
        have hOb : Deriv [rnSub (2 * a + 2),
            (rnSub (2 * a + 1)).or (rnSub (2 * a + 2)),
            (rnSub (2 * a + 2)).ifThen (rnSub (2 * b + 1))]
            (rnSub (2 * b + 1)) :=
          Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
            (Deriv.iden (.head _))
        exact Deriv.cutHead hOb (rungD (oo_le (show b ≤ a from by omega)))
      · -- [E_{a+1}] ⊢ E_a ⊃ O_b
        refine Deriv.impIntro ?_
        -- ctx [rnSub (2a+2), rnSub (2(a+1)+2)] ⊢ rnSub (2b+1)
        have hand : Deriv [rnSub (2 * a + 2), rnSub (2 * (a + 1) + 2)]
            ((rnSub (2 * a + 2)).and (rnSub (2 * a + 4))) := by
          refine Deriv.andIntro (Deriv.iden (.head _)) ?_
          have h := Deriv.iden (φ := rnSub (2 * (a + 1) + 2))
            (Γ := [rnSub (2 * a + 2), rnSub (2 * (a + 1) + 2)])
            (.tail _ (.head _))
          rw [show (2 * (a + 1) + 2 : Nat) = 2 * a + 4 from by omega] at h
          exact h
        have hpred := Deriv.cutHead hand (meet_evens a)
        exact Deriv.cutHead hpred (rungD (pred_oo_le (show a ≤ b + 1 from by omega)))
    · -- b + 2 = a: the value is even (a−1)
      simp only [toS]
      have e : a = b + 2 := by omega
      subst e
      constructor
      · -- [E_{b+2} ⊃ O_b] ⊢ E_{b+1}
        rw [show (2 * (b + 2 - 1) + 2 : Nat) = 2 * (b + 1) + 2 from by omega,
            rnSub_even_eq (b + 1),
            show (2 * (b + 1) - 1 : Nat) = 2 * b + 1 from by omega,
            show (2 * (b + 1) + 1 : Nat) = 2 * b + 3 from by omega]
        refine Deriv.impIntro ?_
        rw [rnSub_odd_eq b]
        refine Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _)) ?_
        -- ctx [rnSub (2b+2), or-form, H] ⊢ rnSub (2b+1)
        have hup : Deriv [rnSub (2 * b + 2),
            (rnSub (2 * b + 1)).or (rnSub (2 * b + 2)),
            (rnSub (2 * (b + 2) + 2)).ifThen (rnSub (2 * b + 1))]
            (rnSub (2 * (b + 2) + 2)) :=
          Deriv.cutHead (Deriv.iden (.head _))
            (rungD (even_le_even b (b + 2) (Or.inr (by omega))))
        exact Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _)))) hup
      · -- [E_{b+1}] ⊢ E_{b+2} ⊃ O_b
        rw [show (2 * (b + 2 - 1) + 2 : Nat) = 2 * (b + 1) + 2 from by omega]
        refine Deriv.impIntro ?_
        -- ctx [rnSub (2(b+2)+2), rnSub (2(b+1)+2)] ⊢ rnSub (2b+1)
        have hand : Deriv [rnSub (2 * (b + 2) + 2), rnSub (2 * (b + 1) + 2)]
            ((rnSub (2 * (b + 1) + 2)).and (rnSub (2 * (b + 1) + 4))) := by
          refine Deriv.andIntro (Deriv.iden (.tail _ (.head _))) ?_
          have h := Deriv.iden (φ := rnSub (2 * (b + 2) + 2))
            (Γ := [rnSub (2 * (b + 2) + 2), rnSub (2 * (b + 1) + 2)]) (.head _)
          rw [show (2 * (b + 2) + 2 : Nat) = 2 * (b + 1) + 4 from by omega] at h
          exact h
        have hpred := Deriv.cutHead hand (meet_evens (b + 1))
        have e2 : (2 : Nat) * (b + 1) - 1 = 2 * b + 1 := by omega
        rw [e2] at hpred
        exact hpred
    · -- b + 3 ≤ a: the implication collapses to its consequent
      simp only [toS]
      constructor
      · -- [E_a ⊃ O_b] ⊢ O_b
        have hE : Deriv [(rnSub (2 * a + 2)).ifThen (rnSub (2 * b + 1))]
            (rnSub (2 * (b + 1) + 2)) := by
          rw [rnSub_even_eq (b + 1),
              show (2 * (b + 1) - 1 : Nat) = 2 * b + 1 from by omega,
              show (2 * (b + 1) + 1 : Nat) = 2 * b + 3 from by omega]
          refine Deriv.impIntro ?_
          have hup : Deriv [rnSub (2 * b + 3),
              (rnSub (2 * a + 2)).ifThen (rnSub (2 * b + 1))]
              (rnSub (2 * a + 2)) :=
            Deriv.cutHead (Deriv.iden (.head _))
              (by
                have := rungD (oe_le (show (b + 1) + 1 ≤ a from by omega))
                rw [show (2 * (b + 1) + 1 : Nat) = 2 * b + 3 from by omega] at this
                exact this)
          exact Deriv.impElim (Deriv.iden (.tail _ (.head _))) hup
        have hEa : Deriv [(rnSub (2 * a + 2)).ifThen (rnSub (2 * b + 1))]
            (rnSub (2 * a + 2)) :=
          Deriv.cutHead hE (rungD (even_le_even (b + 1) a (Or.inr (by omega))))
        exact Deriv.impElim (Deriv.iden (.head _)) hEa
      · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))
  -- even ⊃ even
  case even.even =>
    split_ifs with h1
    · -- a = b or a + 2 ≤ b: ⊤
      simp only [toS]
      refine ⟨dTop, Deriv.impIntro (Deriv.toHead (rungD (even_le_even a b h1)))⟩
    · -- otherwise: the implication collapses to its consequent
      simp only [toS]
      rcases Nat.lt_or_ge b (a + 1) with hlt | hge
      · -- b ≤ a, b ≠ a: b < a
        have hb : b + 1 ≤ a := by omega
        constructor
        · have core : Deriv [(rnSub (2 * a + 2)).ifThen (rnSub (2 * b + 2))]
              ((rnSub (2 * b + 1)).ifThen (rnSub (2 * b - 1))) := by
            refine Deriv.impIntro ?_
            have hup : Deriv [rnSub (2 * b + 1),
                (rnSub (2 * a + 2)).ifThen (rnSub (2 * b + 2))]
                (rnSub (2 * a + 2)) :=
              Deriv.cutHead (Deriv.iden (.head _)) (rungD (oe_le hb))
            have hEb := Deriv.impElim (Deriv.iden (.tail _ (.head _))) hup
            have hEb' : Deriv [rnSub (2 * b + 1),
                (rnSub (2 * a + 2)).ifThen (rnSub (2 * b + 2))]
                ((rnSub (2 * b + 1)).ifThen (rnSub (2 * b - 1))) := by
              rw [← rnSub_even_eq b]
              exact hEb
            exact Deriv.impElim hEb' (Deriv.iden (.head _))
          have conv : Deriv [(rnSub (2 * b + 1)).ifThen (rnSub (2 * b - 1))]
              (rnSub (2 * b + 2)) := by
            rw [rnSub_even_eq b]
            exact Deriv.iden (.head _)
          exact Deriv.cutHead core conv
        · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))
      · -- b ≥ a + 1 with ¬(a + 2 ≤ b): b = a + 1
        have e : b = a + 1 := by omega
        subst e
        constructor
        · -- [E_a ⊃ E_{a+1}] ⊢ E_{a+1}
          have core : Deriv [(rnSub (2 * a + 2)).ifThen (rnSub (2 * (a + 1) + 2))]
              ((rnSub (2 * a + 3)).ifThen (rnSub (2 * a + 1))) := by
            refine Deriv.impIntro ?_
            -- ctx [rnSub (2a+3), H] ⊢ rnSub (2a+1)
            have hd : Deriv [rnSub (2 * a + 3),
                (rnSub (2 * a + 2)).ifThen (rnSub (2 * (a + 1) + 2))]
                ((rnSub (2 * a + 1)).or (rnSub (2 * a + 2))) := by
              have d1 : Deriv [rnSub (2 * a + 3)]
                  ((rnSub (2 * a + 1)).or (rnSub (2 * a + 2))) := by
                rw [rnSub_odd_eq a]
                exact Deriv.iden (.head _)
              exact Deriv.cutHead (Deriv.iden (.head _)) d1
            refine Deriv.orElim hd (Deriv.iden (.head _)) ?_
            -- ctx [rnSub (2a+2), rnSub (2a+3), H] ⊢ rnSub (2a+1)
            have hE1 : Deriv [rnSub (2 * a + 2), rnSub (2 * a + 3),
                (rnSub (2 * a + 2)).ifThen (rnSub (2 * (a + 1) + 2))]
                (rnSub (2 * (a + 1) + 2)) :=
              Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
                (Deriv.iden (.head _))
            have conv1 : Deriv [rnSub (2 * (a + 1) + 2)]
                ((rnSub (2 * a + 3)).ifThen (rnSub (2 * a + 1))) := by
              rw [rnSub_even_eq (a + 1),
                  show (2 * (a + 1) - 1 : Nat) = 2 * a + 1 from by omega,
                  show (2 * (a + 1) + 1 : Nat) = 2 * a + 3 from by omega]
              exact Deriv.iden (.head _)
            have hE1' := Deriv.cutHead hE1 conv1
            exact Deriv.impElim hE1' (Deriv.iden (.tail _ (.head _)))
          have conv2 : Deriv [(rnSub (2 * a + 3)).ifThen (rnSub (2 * a + 1))]
              (rnSub (2 * (a + 1) + 2)) := by
            rw [rnSub_even_eq (a + 1),
                show (2 * (a + 1) - 1 : Nat) = 2 * a + 1 from by omega,
                show (2 * (a + 1) + 1 : Nat) = 2 * a + 3 from by omega]
            exact Deriv.iden (.head _)
          exact Deriv.cutHead core conv2
        · exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

/-! ## Stage 5: the classification -/

/-- The single-variable check: every atom is `p`. -/
def onlyP : PLLFormula → Bool
  | .prop a => decide (a = pv)
  | .falsePLL => true
  | .and A B => onlyP A && onlyP B
  | .or A B => onlyP A && onlyP B
  | .ifThen A B => onlyP A && onlyP B
  | .somehow A => onlyP A

/-- **The RN classification, mechanised (stage 5).**  Every ◯-free
formula in the single variable `p` is, after the substitution
`p ↦ ◯⊥`, interderivable with `toS` of its code — a substituted rung
or `⊤`. -/
theorem rn_classification : ∀ {A : PLLFormula},
    boxFree A = true → onlyP A = true →
    Interd (embed A) (toS (cls A)) := by
  intro A
  induction A with
  | prop a =>
      intro _ hp
      have ha : a = pv := by simpa [onlyP] using hp
      subst ha
      have e : cls (.prop pv) = .odd 0 := by simp [cls]
      rw [e]
      show Interd (embed (.prop pv)) (rnSub (2 * 0 + 1))
      have e2 : rnSub (2 * 0 + 1) = embed (.prop pv) := by
        show embed (rn 1) = embed (.prop pv)
        rw [rn_one]
      rw [e2]
      exact Interd.refl _
  | falsePLL =>
      intro _ _
      exact Interd.refl _
  | and A B ihA ihB =>
      intro h hp
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [onlyP, Bool.and_eq_true] at hp
      have hA := ihA h.1 hp.1
      have hB := ihB h.2 hp.2
      show Interd ((embed A).and (embed B)) (toS (meetC (cls A) (cls B)))
      exact (Interd.and_congr hA hB).trans (meet_interd (cls A) (cls B))
  | or A B ihA ihB =>
      intro h hp
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [onlyP, Bool.and_eq_true] at hp
      have hA := ihA h.1 hp.1
      have hB := ihB h.2 hp.2
      show Interd ((embed A).or (embed B)) (toS (joinC (cls A) (cls B)))
      exact (Interd.or_congr hA hB).trans (join_interd (cls A) (cls B))
  | ifThen A B ihA ihB =>
      intro h hp
      simp only [boxFree, Bool.and_eq_true] at h
      simp only [onlyP, Bool.and_eq_true] at hp
      have hA := ihA h.1 hp.1
      have hB := ihB h.2 hp.2
      show Interd ((embed A).ifThen (embed B)) (toS (impC (cls A) (cls B)))
      exact (Interd.imp_congr hA hB).trans (imp_interd (cls A) (cls B))
  | somehow A ih =>
      intro h _
      simp only [boxFree] at h
      exact Bool.noConfusion h

/-- **im h = rungs ∪ {⊤}**: the image of every ◯-free one-variable
formula is interderivable with a substituted rung or with `⊤`. -/
theorem image_classification {A : PLLFormula}
    (h : boxFree A = true) (hp : onlyP A = true) :
    (∃ n, Interd (embed A) (rnSub n)) ∨ Interd (embed A) q1 := by
  have hc := rn_classification h hp
  rcases e : cls A with _ | a | a | _ <;> rw [e] at hc
  · exact Or.inl ⟨0, hc⟩
  · exact Or.inl ⟨2 * a + 1, hc⟩
  · exact Or.inl ⟨2 * a + 2, hc⟩
  · exact Or.inr hc

/-! ## The caveat dischargers -/

/-- Membership of the image of `h : RN({p}) → RN(◯,{})`, up to
interderivability: `X ∈ im h` iff `X` is interderivable with the
substitution image of some ◯-free one-variable formula. -/
def InImage (X : PLLFormula) : Prop :=
  ∃ A, boxFree A = true ∧ onlyP A = true ∧ Interd X (embed A)

/-- Off the rungs and not `⊤` = off the image, with no caveat. -/
theorem not_inImage_of_offRungs {X : PLLFormula}
    (hr : ∀ n, ¬ Interd (rnSub n) X) (ht : ¬ Interd q1 X) :
    ¬ InImage X := by
  rintro ⟨A, hA, hp, hI⟩
  rcases image_classification hA hp with ⟨n, hn⟩ | hn
  · exact hr n (hn.symm.trans hI.symm)
  · exact ht (hn.symm.trans hI.symm)

/-- **`q5 ∉ im h`, unconditionally** (`q5_not_top` is the pinned
separation `sep_1_5` from `wip/offImage.lean`). -/
theorem q5_off_image : ¬ InImage q5 :=
  not_inImage_of_offRungs q5_not_any_rung q5_not_top

/-- `q11` is interderivable with `rnSub 7` — an instance of the
classification, applied to `¬¬p ∨ (¬¬p ⊃ p)`. -/
theorem q11_rn7 : Interd q11 (rnSub 7) := by
  have h := rn_classification
    (A := (((PLLFormula.prop pv).ifThen .falsePLL).ifThen .falsePLL).or
      (((((PLLFormula.prop pv).ifThen .falsePLL).ifThen .falsePLL)).ifThen
        (.prop pv)))
    (by decide) (by decide)
  have e1 : embed ((((PLLFormula.prop pv).ifThen .falsePLL).ifThen .falsePLL).or
      (((((PLLFormula.prop pv).ifThen .falsePLL).ifThen .falsePLL)).ifThen
        (.prop pv))) = q11 := by decide
  have e2 : cls ((((PLLFormula.prop pv).ifThen .falsePLL).ifThen .falsePLL).or
      (((((PLLFormula.prop pv).ifThen .falsePLL).ifThen .falsePLL)).ifThen
        (.prop pv))) = .odd 3 := by decide
  rw [e1, e2] at h
  exact h

/-- **`◯q11 ∉ im h`, unconditionally** — through `◯q11 ≡ chainF 3`. -/
theorem boxq11_off_image : ¬ InImage (q11.somehow) := by
  have hb : Interd (q11.somehow) (chainF 3) := Interd.box_congr q11_rn7
  refine not_inImage_of_offRungs (fun n hI => ?_) (fun hI => ?_)
  · exact chain_not_any_rung (by omega) n (hI.trans hb)
  · exact chain_not_top 3 (hI.trans hb)

/-- **`chainF k ∉ im h` for every `k ≥ 2`, unconditionally.** -/
theorem chain_off_image {k : Nat} (hk : 2 ≤ k) : ¬ InImage (chainF k) :=
  not_inImage_of_offRungs (chain_not_any_rung hk) (chain_not_top k)

/-- **RN(◯,{}) ∖ im h is infinite — no caveat left**: for every
`k ≥ 2` the boxed odd rung `chainF k` is off the image, and the
`chainF k` are pairwise non-interderivable. -/
theorem complement_infinite_final (k : Nat) (hk : 2 ≤ k) :
    ¬ InImage (chainF k) ∧ ∀ j, j ≠ k → ¬ Interd (chainF j) (chainF k) :=
  ⟨chain_off_image hk, fun _ hj => chain_pairwise hj⟩

/-! ## Axiom audits — sorry-free throughout -/

/-- info: 'PLLND.RNEmbed.rn_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rn_classification

/-- info: 'PLLND.RNEmbed.image_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms image_classification

/-- info: 'PLLND.RNEmbed.q5_off_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms q5_off_image

/-- info: 'PLLND.RNEmbed.boxq11_off_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boxq11_off_image

/-- info: 'PLLND.RNEmbed.complement_infinite_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms complement_infinite_final

end RNEmbed
end PLLND
