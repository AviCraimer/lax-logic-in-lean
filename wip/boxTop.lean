import wip.offImage
import LaxLogic.PLLG4HComp

/-!
# `◯` reflects theoremhood — and `◯q11 ≢ ⊤`

**The inversion.**  The repaired calculus G4iLL″ is cut-free, and every
left rule demands either a membership in the context or a permutation
of the context exposing a compound formula.  With the EMPTY context
both are impossible, so a derivation of `⊢ ◯A` can only end in the
`◯`-right rule, whose premise is `⊢ A`:

    box_reflects_thm :  ⊢ ◯A  →  ⊢ A          (the unit gives the converse)

No search, no countermodel — pure inversion on the last rule, carried
through `G4c.equiv_nd` to natural deduction.

**Consequences.**

* `cBox11_not_top`: `◯q11 ≢ ⊤`.  The first of the three candidate
  values `[⊤, q11, q13]` for the open cell `cBox_11` is REFUTED: were
  `⊤ ⊢ ◯q11`, then `⊢ q11`, making rung 7 a theorem, against
  `sep_1_11`.

* `rung_not_derivable`: no rung is a theorem — for every `n`, the rung
  `2n + 3` fails to derive `rn n` (world `n+1` witnesses, by
  `rungMem_bound`), so nothing does.

* `chain_never_top`: `◯(rnSub n) ≢ ⊤` for EVERY `n`.  The ◯-chain over
  the odd rungs — the candidate infinite family in the complement of
  `im h` — can never terminate at `⊤`.  The termination scenario for
  the infinitude question is eliminated wholesale: what remains is
  strictness of the chain, a different and attackable question.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-- **Empty-context inversion for `◯`**: a G4iLL″ derivation of
`⊢ ◯A` can only end in `laxR`. -/
theorem G4h_nil_lax {n : Nat} {A : PLLFormula}
    (h : G4h n [] A.somehow) : ∃ m, G4h m [] A := by
  cases h with
  | botL hm => cases hm
  | laxR g => exact ⟨_, g⟩
  | laxL hm _ => cases hm
  | andL hp _ => exact absurd hp.length_eq (by simp)
  | orL hp _ _ => exact absurd hp.length_eq (by simp)
  | impLProp hp _ _ => exact absurd hp.length_eq (by simp)
  | impLBot hp _ => exact absurd hp.length_eq (by simp)
  | impLAnd hp _ => exact absurd hp.length_eq (by simp)
  | impLOr hp _ => exact absurd hp.length_eq (by simp)
  | impLImp hp _ _ => exact absurd hp.length_eq (by simp)
  | impLLax hp _ _ => exact absurd hp.length_eq (by simp)
  | impLLaxLax hp _ _ _ => exact absurd hp.length_eq (by simp)

/-- **`◯` reflects theoremhood**: `⊢ ◯A` implies `⊢ A`.  With the unit
`A ⊢ ◯A` this makes `⊢ ◯A` and `⊢ A` equivalent. -/
theorem box_reflects_thm {A : PLLFormula} (h : Deriv [] A.somehow) :
    Deriv [] A := by
  obtain ⟨n, g⟩ := G4c.equiv_nd.mpr h
  obtain ⟨m, gm⟩ := G4h_nil_lax g
  exact G4c.equiv_nd.mp ⟨m, gm⟩

/-- **`◯q11 ≢ ⊤`** — the `⊤` candidate for the open cell `cBox_11` is
refuted.  Rung 7 would otherwise be a theorem. -/
theorem cBox11_not_top : ¬ Interd (q11.somehow) q1 := by
  rintro ⟨-, h2⟩
  -- h2 : [⊤] ⊢ ◯q11, so ⊢ ◯q11, so ⊢ q11
  have htop : Deriv [] q1 := Deriv.impIntro (Deriv.iden (.head _))
  have hq11 : Deriv [] q11 := box_reflects_thm (Deriv.cutHead htop h2)
  exact sep_1_11 ⟨wkHead _ hq11, Deriv.impIntro (Deriv.iden (.head _))⟩

/-- No rung is a theorem: rung `2n+3` refuses to derive `rn n` (world
`n+1` lies in its truth set but beyond rung `n`'s bound). -/
theorem rung_not_derivable : ∀ n : Nat, ¬ Deriv [] (rnSub n) := by
  intro n h
  have hw : Deriv [rnSub (2 * n + 3)] (rnSub n) := wkHead _ h
  have hle : rungLe (2 * n + 3) n = true :=
    (rnSub_order (2 * n + 3) n).mp hw
  simp only [rungLe, List.all_eq_true] at hle
  have h1 := hle (n + 1) (List.mem_range.mpr (by omega))
  have hm : rungMem (2 * n + 3) (n + 1) = true := by
    have e : 2 * n + 3 = 2 * (n + 1) + 1 := by omega
    rw [e, rungMem_odd]
    simp only [decide_eq_true_eq]
    omega
  rw [hm] at h1
  cases hb : rungMem n (n + 1) with
  | false => rw [hb] at h1; simp at h1
  | true => exact absurd (rungMem_bound hb) (by omega)

/-- **The ◯-chain never reaches `⊤`**: `◯(rnSub n) ≢ ⊤` for every `n`. -/
theorem chain_never_top : ∀ n : Nat, ¬ Deriv [] ((rnSub n).somehow) :=
  fun n h => rung_not_derivable n (box_reflects_thm h)

/-! ## Axiom audits — sorry-free throughout -/

/-- info: 'PLLND.RNEmbed.box_reflects_thm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms box_reflects_thm

/-- info: 'PLLND.RNEmbed.cBox11_not_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cBox11_not_top

/-- info: 'PLLND.RNEmbed.chain_never_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_never_top

end RNEmbed
end PLLND
