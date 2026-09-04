import wip.families

/-!
# How the families attach to the ladder — the connectivity map

**Everything here is PLL.**  Answers to: "are the chain formulae
connected to anything besides themselves? how about the gaps?"

Positive connections (derivations, all levels `k`):

    t(2k+1)  ⊢  c k        (the unit — the odd rung sits under its box)
    t(2k+1)  ⊢  g k        (weakening — `rung_le_gap`)
    c k      ⊢  s k        (inject — `chain_le_sC`)
    s j      ⊢  c k        for j < k (`sC_le_chain`)
    g k      ⊢  ◯g k       (the unit — `gap_le_bg`)

Negative connections (each level `k ≥ 2`, refuted on the edged lifts):

    c k ⊬ g k  and  g k ⊬ c k     — chain and gap INCOMPARABLE at each level
    c k ⊬ t(2k+3),  c k ⊬ t(2k+4) — the chain does not re-enter the ladder
    t(2k+3) ⊬ g k,  t(2k+2) ⊬ g k — the ladder does not climb into the gap

The last two lines kill, from level 2 up, the "level-1 accidents" the
dictionary shows: `q7 ⊢ q8` and `q6 ⊢ q8` (proved here as
`d_q7_q8`, `d_q6_q8`: at level 1 the odd/even rungs DO reach the gap)
and the pinned `q5 ⊢ q10` (`c 1 ⊢ t 6`: the chain re-enters the
ladder at level 1 only).

So the picture: each family member at level `k` is anchored to the
ladder from below through `t(2k+1)` alone (gaps) or sits above it
(chain, s), rises to `⊤`, and is otherwise incomparable with its own
level — the families are "combs" clipped onto the odd rungs.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-! ## Positive connections -/

/-- `t(2k+1) ⊢ g k` — weakening (K): the rung implies the implication
with itself as consequent. -/
theorem rung_le_gap (k : Nat) : Deriv [rnSub (2 * k + 1)] (gap k) :=
  Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

/-- `g k ⊢ ◯g k` — the unit. -/
theorem gap_le_bg (k : Nat) : Deriv [gap k] ((gap k).somehow) :=
  dSomehowIntro (Deriv.iden (.head _))

/-- `c k ⊢ s k` — injection. -/
theorem chain_le_sC (k : Nat) : Deriv [chainF k] (sC k) :=
  Deriv.orIntro1 (Deriv.iden (.head _))

/-- `s j ⊢ c k` for `j < k`: both disjuncts climb into the box. -/
theorem sC_le_chain {j k : Nat} (h : j < k) : Deriv [sC j] (chainF k) := by
  refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
  · exact Deriv.toHead (chain_up (Nat.le_of_lt h))
  · refine Deriv.toHead ?_
    refine Deriv.cutHead (rungD (eo_le (show j + 1 ≤ k from h))) ?_
    exact dSomehowIntro (Deriv.iden (.head _))

/-- `t(2k+3) ⊢ s k` — EN MASSE (generalising `q7 ⊢ q9`): unfold the
odd rung; the odd disjunct climbs into the box, the even injects. -/
theorem odd_le_sC (k : Nat) : Deriv [rnSub (2 * k + 3)] (sC k) := by
  have d1 : Deriv [rnSub (2 * k + 3)]
      ((rnSub (2 * k + 1)).or (rnSub (2 * k + 2))) := by
    rw [rnSub_odd_eq k]
    exact Deriv.iden (.head _)
  refine Deriv.orElim d1 ?_ ?_
  · refine Deriv.toHead (Deriv.orIntro1 ?_)
    exact dSomehowIntro (Deriv.iden (.head _))
  · exact Deriv.toHead (Deriv.orIntro2 (Deriv.iden (.head _)))

/-- `s k ⊬ c k` — with `chain_le_sC` this makes `c k < s k` STRICT at
every level, generalising `q5 < q9`. -/
theorem sC_not_le_chain (k : Nat) : ¬ Deriv [sC k] (chainF k) := by
  rintro ⟨d⟩
  have hs := soundness d ladder.cm (some (k + 1)) (fun ψ hψ => by
    have e : ψ = sC k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact (sC_plain_iff k (k + 1)).mpr (by omega))
  have := (chainF_force_iff k (k + 1)).mp hs
  omega

/-! ## The level-1 accidents, derived (they are real at level 1) -/

/-- `q7 ⊢ q8` (`t 5 ⊢ g 1` in the new labels): at level 1 the odd
rung DOES climb into the gap — from `¬◯⊥` inject; from `¬¬◯⊥` and
`◯¬◯⊥`, bind the box, explode inside it, and land in `◯⊥`. -/
theorem d_q7_q8 : Deriv [q7] q8 := by
  refine Deriv.impIntro ?_
  -- ctx [q5, q7] ⊢ q4
  refine Deriv.orElim (Deriv.iden (.tail _ (.head _))) ?_ ?_
  · -- q3 branch: q4 = q2 ∨ q3
    exact Deriv.orIntro2 (Deriv.iden (.head _))
  · -- q6 branch: with q5 = ◯q3 in context, derive ◯⊥ = q2
    refine Deriv.orIntro1 ?_
    refine dSomehowElim (Deriv.iden (.tail _ (.head _))) ?_
    -- ctx [q3, q6, q5, q7] ⊢ ◯q0 = q2
    refine Deriv.falsoElim _ ?_
    exact Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))

/-- `q6 ⊢ q8` (`t 4 ⊢ g 1`): through `q6 ⊢ q7`. -/
theorem d_q6_q8 : Deriv [q6] q8 :=
  Deriv.cutHead (Deriv.orIntro2 (Deriv.iden (.head _))) d_q7_q8

/-! ## Chain vs gap at the same level: incomparable -/

/-- `c k ⊬ g k` (`k ≥ 1`): at the edge world the box holds by escape
while the collapse fails. -/
theorem chain_not_le_gap {k : Nat} (hk : 1 ≤ k) :
    ¬ Deriv [chainF k] (gap k) := by
  rintro ⟨d⟩
  have hs := soundness d (cmE (k - 1)) (some ((k - 1) + 3)) (fun ψ hψ => by
    have e : ψ = chainF k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact (cmE_chainF (k - 1) k ((k - 1) + 3)).mpr (Or.inr ⟨rfl, by omega⟩))
  exact gap_fails (k - 1) k (by omega) (by omega) hs

/-- `g k ⊬ c k`: the gap is forced everywhere on the plain lift, the
box is bounded. -/
theorem gap_not_le_chain (k : Nat) : ¬ Deriv [gap k] (chainF k) := by
  rintro ⟨d⟩
  have hs := soundness d ladder.cm (some (k + 1)) (fun ψ hψ => by
    have e : ψ = gap k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact plain_forces_gap k (some (k + 1)))
  have := (chainF_force_iff k (k + 1)).mp hs
  omega

/-! ## The accidents die at level 2 -/

/-- `c k ⊬ t(2k+3)` (`k ≥ 1`): the chain does not re-enter the ladder
at the next odd rung. -/
theorem chain_not_le_odd {k : Nat} (hk : 1 ≤ k) :
    ¬ Deriv [chainF k] (rnSub (2 * k + 3)) := by
  rintro ⟨d⟩
  have hs := soundness d (cmE (k - 1)) (some ((k - 1) + 3)) (fun ψ hψ => by
    have e : ψ = chainF k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact (cmE_chainF (k - 1) k ((k - 1) + 3)).mpr (Or.inr ⟨rfl, by omega⟩))
  have := (sat_rn_odd (k + 1) ((k - 1) + 3)).mp
    ((cmE_transfer (k - 1) (rn_boxFree _) _).mp (by
      have e : (2 : Nat) * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [e]
      exact hs))
  omega

/-- `c k ⊬ t(2k+4)` for `k ≥ 2` — while `c 1 ⊢ t 6` (the pinned
`q5 ⊢ q10`) holds: the chain's re-entry into the ladder at the next
even rung is a level-1 accident. -/
theorem chain_not_le_even {k : Nat} (hk : 2 ≤ k) :
    ¬ Deriv [chainF k] (rnSub (2 * k + 4)) := by
  rintro ⟨d⟩
  have hs := soundness d (cmE (k - 2)) (some ((k - 2) + 3)) (fun ψ hψ => by
    have e : ψ = chainF k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact (cmE_chainF (k - 2) k ((k - 2) + 3)).mpr (Or.inr ⟨rfl, by omega⟩))
  have := (sat_rn_even (k + 1) ((k - 2) + 3)).mp
    ((cmE_transfer (k - 2) (rn_boxFree _) _).mp (by
      have e : (2 : Nat) * (k + 1) + 2 = 2 * k + 4 := by omega
      rw [e]
      exact hs))
  omega

/-- `t(2k+3) ⊬ g k` for `k ≥ 2` — while `t 5 ⊢ g 1` (`d_q7_q8`)
holds: from level 2 the ladder does not climb into the gap. -/
theorem odd_not_le_gap {k : Nat} (hk : 2 ≤ k) :
    ¬ Deriv [rnSub (2 * k + 3)] (gap k) := by
  rintro ⟨d⟩
  have hs := soundness d (cmE (k - 2)) (some ((k - 2) + 3)) (fun ψ hψ => by
    have e : ψ = rnSub (2 * k + 3) := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    refine (cmE_transfer (k - 2) (rn_boxFree _) _).mpr ?_
    rw [show (2 * k + 3 : Nat) = 2 * (k + 1) + 1 from by omega]
    exact (sat_rn_odd (k + 1) _).mpr (by omega))
  exact gap_fails_above (k - 2) k ((k - 2) + 3) (by omega) (by omega)
    (Or.inl rfl) hs

/-- `t(2k+2) ⊬ g k` for `k ≥ 2` — while `t 4 ⊢ g 1` (`d_q6_q8`)
holds. -/
theorem even_not_le_gap {k : Nat} (hk : 2 ≤ k) :
    ¬ Deriv [rnSub (2 * k + 2)] (gap k) := by
  rintro ⟨d⟩
  have hs := soundness d (cmE (k - 2)) (some ((k - 2) + 3)) (fun ψ hψ => by
    have e : ψ = rnSub (2 * k + 2) := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    refine (cmE_transfer (k - 2) (rn_boxFree _) _).mpr ?_
    rw [show (2 * k + 2 : Nat) = 2 * k + 2 from rfl]
    exact (sat_rn_even k _).mpr (by omega))
  exact gap_fails_above (k - 2) k ((k - 2) + 3) (by omega) (by omega)
    (Or.inl rfl) hs

/-! ## Axiom audits — sorry-free, all PLL -/

/-- info: 'PLLND.RNEmbed.d_q7_q8' does not depend on any axioms -/
#guard_msgs in
#print axioms d_q7_q8

/-- info: 'PLLND.RNEmbed.chain_not_le_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_not_le_gap

/-- info: 'PLLND.RNEmbed.odd_not_le_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms odd_not_le_gap

/-- info: 'PLLND.RNEmbed.chain_not_le_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_not_le_even

end RNEmbed
end PLLND
