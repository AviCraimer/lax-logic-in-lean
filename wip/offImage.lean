import wip.overlap
import wip.ladder8
import wip.rnSep

/-!
# `◯¬◯⊥` is not on the ladder: the complement of `im h` is inhabited

The question is whether RN(◯,{}) ∖ im(h) is infinite.  Before that can
be asked, membership of even one class in the complement has to be a
theorem — and it was not: "off-image" had only ever been checked
against finitely many rungs by the searcher.  This file certifies the
first full member:

    q5_not_any_rung :  ∀ n, ¬ Interd (rnSub n) q5
    q5_not_top      :  ¬ Interd q1 q5

Together: `◯¬◯⊥` is interderivable with NO rung and not with `⊤`.  By
the classical Rieger–Nishimura classification, every one-variable pure
Heyting formula is IPC-equivalent to a rung or to `⊤`, so these two
facts say `◯¬◯⊥ ∉ im h` — with the caveat, flagged OPEN, that the
classification itself is not yet mechanised in this repository; what
is fully machine-checked is the displayed pair.

## How the quantifier over all rungs is discharged

Four certified facts pin `q5` against the arithmetic of the ladder:

* A. `rn 3 ⊢ q5`  (`guard_q5`; `rnSub 3` IS the guard, definitionally),
* B. `q5 ⊬ rn 5`  (`five_q5_nle_q7` through the bridge `rnSub 5 ⊢ q7`),
* C. `q5 ⊢ rn 6`  (the two-line derivation `d_q5_q10` composed with
     the bridge `q10 ⊢ rnSub 6`),
* D. `rn 6 ⊬ q5`  (four-world countermodel, `ref_q10_q5`).

If `q5 ≡ rn n`: A forces `rungLe 3 n`, B refutes `rungLe n 5`, and the
two together force `n ≥ 6` (a finite check).  C forces `rungLe n 6`,
and no rung `n ≥ 7` satisfies that — world 2 lies in every such rung's
truth set but not in rung 6's (`rungMem_at2_of_ge7`).  So `n = 6`, and
D refutes exactly that.  The rung arithmetic is `rnSub_order`, so no
search and no table is involved in the quantifier step.

## Bonus: the meet identity

The hunt for a fresh embedding seed needed the one visible off-image
meet candidate settled.  It collapses INTO the image, at the bottom:

    meet_q5_q6 :  ◯¬◯⊥ ∧ ¬¬◯⊥ ⊣⊢ ◯⊥

so the guard cone's underside gives nothing new: the candidate region
for non-dense off-image classes remains empty as far as is known.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-! ## Pinned bridges (searcher-found, kernel-checked on elaboration) -/

/-- `rnSub 5 ⊢ q7` (23 nodes). -/
theorem d_rn5_q7 : Deriv [rnSub 5] q7 :=
  ofG4 (.orL (.head _) (.orL (.head _) (.orR2 (.impR (.impLLaxLax (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _))))) (.orR1 (.impR (.impLLaxLax (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR2 (.impR (.impLOr (.tail _ (.head _)) (.impLImp (.tail _ (.head _)) (.impR (.impLLaxLax (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (.tail _ (.tail _ (.tail _ (.head _)))) (.head _) (.botL (.head _)) (.botL (.head _))))))))

/-- `q10 ⊢ rnSub 6` (25 nodes). -/
theorem d_q10_rn6 : Deriv [q10] (rnSub 6) :=
  ofG4 (.impR (.orL (.head _) (.orL (.head _) (.orR1 (.laxL (.head _) (.botL (.head _)))) (.orR2 (.impR (.impLLaxLax (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _)))))) (.orR1 (.impLOr (.head _) (.impLImp (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.impR (.impLImp (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLLaxLax (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.impLLaxLax (.tail _ (.head _)) (.head _) (.botL (.head _)) (.botL (.head _))))) (.laxL (.head _) (.botL (.head _))))))))

/-- **The meet identity**: `◯¬◯⊥ ∧ ¬¬◯⊥ ⊣⊢ ◯⊥` (9 + 7 nodes). -/
theorem meet_q5_q6 : Interd (q5.and q6) q2 :=
  ⟨ofG4 (.andL (.head _) (.laxL (.head _) (.laxR (.impLImp (.tail _ (.tail _ (.head _))) (.impR (.impLLaxLax (.tail _ (.tail _ (.head _))) (.head _) (.botL (.head _)) (.botL (.head _)))) (.botL (.head _)))))),
   ofG4 (.andR (.laxL (.head _) (.botL (.head _))) (.impR (.impLLaxLax (.head _) (.tail _ (.head _)) (.botL (.head _)) (.botL (.head _)))))⟩

/-- `q5 ⊢ q10`: open `◯¬◯⊥` against `¬¬◯⊥`, contradiction, ex falso. -/
theorem d_q5_q10 : Deriv [q5] q10 :=
  Deriv.impIntro (dSomehowElim (Deriv.iden (.tail _ (.head _)))
    (Deriv.falsoElim _
      (Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _)))))

/-- `q10 ⊬ q5`: four-world countermodel. -/
theorem ref_q10_q5 : ¬ Deriv [q10] q5 :=
  FinCM.not_provable_of_check
    (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩)
    (w := 0) (by decide)

/-! ## The rung arithmetic -/

/-- Every rung from 7 up contains world 2. -/
theorem rungMem_at2_of_ge7 {n : Nat} (h : 7 ≤ n) : rungMem n 2 = true := by
  rcases parity3 n with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · omega
  · rw [rungMem_odd]
    simp only [decide_eq_true_eq]
    omega
  · rw [rungMem_even]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (by omega)

/-- Above rung 3 but not below rung 5 forces `n ≥ 6`. -/
theorem ge6_of_bounds {n : Nat} (h1 : rungLe 3 n = true)
    (h2 : rungLe n 5 = false) : 6 ≤ n := by
  by_contra hlt
  have hlt' : n < 6 := by omega
  interval_cases n <;> revert h1 h2 <;> decide

/-- At or above 6 and below rung 6 forces `n = 6`. -/
theorem eq6_of_bounds {n : Nat} (h6 : 6 ≤ n) (hL : rungLe n 6 = true) :
    n = 6 := by
  by_contra hne
  have h7 : 7 ≤ n := by omega
  simp only [rungLe, List.all_eq_true] at hL
  have h2m := hL 2 (List.mem_range.mpr (by omega))
  rw [rungMem_at2_of_ge7 h7, show rungMem 6 2 = false from by decide] at h2m
  simp at h2m

/-! ## The theorem -/

/-- **`◯¬◯⊥` is interderivable with no rung.** -/
theorem q5_not_any_rung : ∀ n : Nat, ¬ Interd (rnSub n) q5 := by
  rintro n ⟨h1, h2⟩
  -- A: rn 3 ⊢ rn n
  have e3 : rnSub 3 = guard := by decide
  have hA : rungLe 3 n = true :=
    (rnSub_order 3 n).mp (Deriv.cutHead (e3 ▸ guard_q5) h2)
  -- B: ¬ (rn n ⊢ rn 5), else q5 ⊢ q7
  have hB : rungLe n 5 = false := by
    cases hc : rungLe n 5 with
    | false => rfl
    | true =>
        exact (five_q5_nle_q7
          (Deriv.cutHead (Deriv.cutHead h2 ((rnSub_order n 5).mpr hc))
            d_rn5_q7)).elim
  have h6 : 6 ≤ n := ge6_of_bounds hA hB
  -- C: rn n ⊢ rn 6
  have hC : rungLe n 6 = true :=
    (rnSub_order n 6).mp
      (Deriv.cutHead (Deriv.cutHead h1 d_q5_q10) d_q10_rn6)
  have hn : n = 6 := eq6_of_bounds h6 hC
  subst hn
  -- D: rn 6 ⊬ q5
  exact ref_q10_q5 (Deriv.cutHead d_q10_rn6 h1)

/-- `q5` is not the top class either (`rnSep.sep_1_5`). -/
theorem q5_not_top : ¬ Interd q1 q5 := sep_1_5

/-! ## Axiom audits — sorry-free throughout -/

/-- info: 'PLLND.RNEmbed.q5_not_any_rung' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms q5_not_any_rung

/-- info: 'PLLND.RNEmbed.meet_q5_q6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms meet_q5_q6

end RNEmbed
end PLLND
