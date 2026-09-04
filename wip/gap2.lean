import wip.seeds

/-!
# Second-order gaps COLLAPSE; the co-gaps are a new family — all PLL

The probe `◯g k ⊃ g k` is settled, negatively for novelty and
positively for structure:

**The collapse, en masse** (`imp_gap_collapse`): for ANY `X` with
`c k ⊢ X`,

    (X ⊃ g k)  ≡  g k

Proof of the nontrivial half: given `H : X ⊃ g k` and `c k`, the chain
climbs into the boxed gap (`c k ⊢ ◯g k ⊢ X`... in the general form
`c k ⊢ X` is the hypothesis), `H` turns `X` into `g k`, and `g k`
fires on the `c k` already in hand.  Instances: `X = ◯g k`
(`gap2_collapse` — the second-order gap IS the gap, since
`c k ⊢ ◯g k` is `chain_le_bg`), `X = c k` (`c_imp_gap`).

This also explains the model blindness that prompted the "new model"
hunt: on ANY lift of the ladder skeleton, a world forcing `◯t(2k+1)`
automatically forces `◯g k` (each box-witness lands in `[0,k] ∪ F`,
and both regions force `g k`), so no such model can separate — and the
reason they can't is precisely the derivation above.

**The dual does NOT collapse**: the co-gap

    dC k := g k ⊃ c k

is strictly above `c k` (`chain_le_dC`, `dC_not_le_chain` — separated
on the edged lift at world `k+3`, where every cone point either fails
`g k` or lands low enough to force `c k`), matches no rung, is not
`⊤`, and is off the image (`dC_off_image`).  The order structure of
`{dC k}` among themselves is OPEN.

Also recorded: `c k ⊢ r k` (`chain_le_rC`) — the r-antichain, like
`◯g`, sits above the chain.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-! ## The collapse -/

/-- **En-masse collapse**: `(X ⊃ g k) ≡ g k` for any `X` above the
chain (`c k ⊢ X`). -/
theorem imp_gap_collapse {k : Nat} {X : PLLFormula}
    (h : Deriv [chainF k] X) :
    Interd (X.ifThen (gap k)) (gap k) := by
  constructor
  · -- [X ⊃ g k] ⊢ c k ⊃ t(2k+1)
    refine Deriv.impIntro ?_
    -- ctx [chainF k, X ⊃ g k] ⊢ rnSub (2k+1)
    have hX : Deriv [chainF k, X.ifThen (gap k)] X :=
      Deriv.cutHead (Deriv.iden (.head _)) h
    have hg : Deriv [chainF k, X.ifThen (gap k)] (gap k) :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) hX
    exact Deriv.impElim hg (Deriv.iden (.head _))
  · -- weakening
    exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

/-- **The second-order gap collapses**: `(◯g k ⊃ g k) ≡ g k`. -/
theorem gap2_collapse (k : Nat) :
    Interd (((gap k).somehow).ifThen (gap k)) (gap k) :=
  imp_gap_collapse (chain_le_bg k)

/-- `(c k ⊃ g k) ≡ g k`. -/
theorem c_imp_gap (k : Nat) :
    Interd ((chainF k).ifThen (gap k)) (gap k) :=
  imp_gap_collapse (Deriv.iden (.head _))

/-- `c k ⊢ r k` — the r-antichain also sits above the chain. -/
theorem chain_le_rC (k : Nat) : Deriv [chainF k] (rC k) :=
  Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

/-! ## The co-gap `dC k := g k ⊃ c k` does not collapse -/

/-- The co-gap. -/
def dC (k : Nat) : PLLFormula := (gap k).ifThen (chainF k)

/-- `c k ⊢ dC k` — weakening. -/
theorem chain_le_dC (k : Nat) : Deriv [chainF k] (dC k) :=
  Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

/-- Below the edge's reach, `gap k` is forced in `cmE m`. -/
theorem gap_forced_low (m k : Nat) {x : Nat} (hx : x ≤ m + 2) :
    (cmE m).force (some x) (gap k) := by
  show ∀ v : Option Nat, (cmE m).Ri (some x) v →
    (cmE m).force v (chainF k) → (cmE m).force v (rnSub (2 * k + 1))
  intro v hv hcf
  cases v with
  | none => exact (cmE m).force_of_fallible rfl
  | some y =>
      have hy : y = x ∨ y + 2 ≤ x := hv
      refine (cmE_transfer m (rn_boxFree _) _).mpr ((sat_rn_odd k y).mpr ?_)
      rcases (cmE_chainF m k y).mp hcf with h | ⟨rfl, -⟩ <;> omega

/-- The co-gap is forced at world `k+3` of `cmE (k−2)`: every cone
point either fails `g k` (the edge world `k+1` and `k+3` itself) or
lands at `≤ k`, where `c k` holds. -/
theorem dC_forced_at_edge {k : Nat} (hk : 2 ≤ k) :
    (cmE (k - 2)).force (some (k + 3)) (dC k) := by
  show ∀ v : Option Nat, (cmE (k - 2)).Ri (some (k + 3)) v →
    (cmE (k - 2)).force v (gap k) → (cmE (k - 2)).force v (chainF k)
  intro v hv hg
  cases v with
  | none => exact (cmE (k - 2)).force_of_fallible rfl
  | some y =>
      have hy : y = k + 3 ∨ y + 2 ≤ k + 3 := hv
      rcases Nat.lt_or_ge y (k + 1) with hlow | hhigh
      · -- y ≤ k: the chain member holds outright
        exact (cmE_chainF (k - 2) k y).mpr (Or.inl (by omega))
      · -- y ∈ {k+1, k+3}: gap k fails there, absurd
        rcases Nat.eq_or_lt_of_le hhigh with heq | hgt
        · -- y = k+1 = the edge world
          have hgf := gap_fails (k - 2) k (by omega) (by omega)
          rw [show (k - 2) + 3 = k + 1 from by omega] at hgf
          subst heq
          exact absurd hg hgf
        · -- y = k+3
          have hy3 : y = k + 3 := by omega
          subst hy3
          exact absurd hg
            (gap_fails_above (k - 2) k (k + 3) (by omega) (by omega)
              (Or.inr (by omega)))

/-- **`dC k ⊬ c k`** (`k ≥ 2`): the co-gap does NOT collapse onto the
chain. -/
theorem dC_not_le_chain {k : Nat} (hk : 2 ≤ k) :
    ¬ Deriv [dC k] (chainF k) := by
  rintro ⟨d⟩
  have hs := soundness d (cmE (k - 2)) (some (k + 3)) (fun ψ hψ => by
    have e : ψ = dC k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact dC_forced_at_edge hk)
  rcases (cmE_chainF (k - 2) k (k + 3)).mp hs with h | ⟨h, -⟩ <;> omega

/-- On the plain lift the co-gap wears the chain's truth set `[0,k]`
(the gap antecedent is forced everywhere). -/
theorem dC_plain_iff (k w : Nat) :
    ladder.cm.force (some w) (dC k) ↔ w ≤ k := by
  constructor
  · intro h
    have h' : ∀ v : Option Nat, ladder.cm.Ri (some w) v →
        ladder.cm.force v (gap k) → ladder.cm.force v (chainF k) := h
    exact (chainF_force_iff k w).mp
      (h' (some w) (Or.inl rfl) (plain_forces_gap k (some w)))
  · intro hw
    show ∀ v : Option Nat, ladder.cm.Ri (some w) v →
      ladder.cm.force v (gap k) → ladder.cm.force v (chainF k)
    intro v hv _
    cases v with
    | none => exact ladder.cm.force_of_fallible rfl
    | some y =>
        have hy : y = w ∨ y + 2 ≤ w := hv
        exact (chainF_force_iff k y).mpr (by omega)

/-- The co-gap matches no rung (`k ≥ 2`): plain agreement pins rung
`2k+1`, and `dC_forced_at_edge` breaks that on the edged lift. -/
theorem dC_not_rung {k : Nat} (hk : 2 ≤ k) (n : Nat) :
    ¬ Interd (rnSub n) (dC k) := by
  rintro ⟨h1, h2⟩
  have hpt : ∀ w : Nat, ladder.sat (rn n) w ↔ w ≤ k := by
    intro w
    constructor
    · intro hw
      obtain ⟨d⟩ := h1
      have hf := soundness d ladder.cm (some w) (fun ψ hψ => by
        cases hψ with
        | head => exact (ladder.transfer (rn_boxFree n) w).mpr hw
        | tail _ h => cases h)
      exact (dC_plain_iff k w).mp hf
    · intro hw
      obtain ⟨d⟩ := h2
      have hf := soundness d ladder.cm (some w) (fun ψ hψ => by
        cases hψ with
        | head => exact (dC_plain_iff k w).mpr hw
        | tail _ h => cases h)
      exact (ladder.transfer (rn_boxFree n) w).mp hf
  have hI : Interd (rnSub n) (rnSub (2 * k + 1)) := by
    constructor
    · exact (rnSub_deriv_iff n (2 * k + 1)).mpr
        (fun w hw => (sat_rn_odd k w).mpr ((hpt w).mp hw))
    · exact (rnSub_deriv_iff (2 * k + 1) n).mpr
        (fun w hw => (hpt w).mpr ((sat_rn_odd k w).mp hw))
  have hn : n = 2 * k + 1 := by
    by_contra hne
    exact rn_pairwise_pll hne hI
  subst hn
  -- refute `dC k ⊢ t(2k+1)` on the edged lift at world k+3
  obtain ⟨d⟩ := h2
  have hs := soundness d (cmE (k - 2)) (some (k + 3)) (fun ψ hψ => by
    have e : ψ = dC k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact dC_forced_at_edge hk)
  have := (sat_rn_odd k (k + 3)).mp
    ((cmE_transfer (k - 2) (rn_boxFree _) (k + 3)).mp hs)
  omega

/-- The co-gap is not `⊤`. -/
theorem dC_not_top (k : Nat) : ¬ Interd q1 (dC k) := by
  rintro ⟨h1, -⟩
  have h0 : Deriv [] (dC k) :=
    Deriv.cutHead (Deriv.impIntro (Deriv.iden (.head _))) h1
  obtain ⟨d⟩ := h0
  have hs := soundness d ladder.cm (some (k + 1)) (fun ψ hψ => by cases hψ)
  have := (dC_plain_iff k (k + 1)).mp hs
  omega

/-- **`dC k ∉ im h`** (`k ≥ 2`): the co-gaps are a NEW off-image
family; their order among themselves is open. -/
theorem dC_off_image {k : Nat} (hk : 2 ≤ k) : ¬ InImage (dC k) :=
  not_inImage_of_offRungs (dC_not_rung hk) (dC_not_top k)

/-! ## The unit rows of the operation tables, closed en masse

Matthew's observation: `⊤ ∧ φ ≡ φ`, so the `⊤`-row of the harvested
tables is redundant — and likewise every `⊤`/`⊥` unit row.  Stated for
EVERY formula, so all such "open" cells close at once.  (`q1 = ⊤`,
`q0 = ⊥`; `φ ⊃ ⊥` is deliberately absent — negation rows are genuine
content.) -/

theorem top_and_interd (φ : PLLFormula) : Interd (q1.and φ) φ :=
  ⟨Deriv.andElim2 (Deriv.iden (.head _)),
   Deriv.andIntro dTop (Deriv.iden (.head _))⟩

theorem and_top_interd (φ : PLLFormula) : Interd (φ.and q1) φ :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _)) dTop⟩

theorem top_or_interd (φ : PLLFormula) : Interd (q1.or φ) q1 :=
  ⟨dTop, Deriv.orIntro1 (Deriv.iden (.head _))⟩

theorem or_top_interd (φ : PLLFormula) : Interd (φ.or q1) q1 :=
  ⟨dTop, Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem top_imp_interd (φ : PLLFormula) : Interd (q1.ifThen φ) φ :=
  ⟨Deriv.impElim (Deriv.iden (.head _)) dTop,
   Deriv.impIntro (Deriv.iden (.tail _ (.head _)))⟩

theorem imp_top_interd (φ : PLLFormula) : Interd (φ.ifThen q1) q1 :=
  ⟨dTop, Deriv.impIntro dTop⟩

theorem bot_and_interd (φ : PLLFormula) : Interd (q0.and φ) q0 :=
  ⟨Deriv.andElim1 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.iden (.head _))
     (Deriv.falsoElim _ (Deriv.iden (.head _)))⟩

theorem and_bot_interd (φ : PLLFormula) : Interd (φ.and q0) q0 :=
  ⟨Deriv.andElim2 (Deriv.iden (.head _)),
   Deriv.andIntro (Deriv.falsoElim _ (Deriv.iden (.head _)))
     (Deriv.iden (.head _))⟩

theorem bot_or_interd (φ : PLLFormula) : Interd (q0.or φ) φ :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
     (Deriv.toHead (Deriv.falsoElim _ (Deriv.iden (.head _))))
     (Deriv.iden (.head _)),
   Deriv.orIntro2 (Deriv.iden (.head _))⟩

theorem or_bot_interd (φ : PLLFormula) : Interd (φ.or q0) φ :=
  ⟨Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _))
     (Deriv.toHead (Deriv.falsoElim _ (Deriv.iden (.head _)))),
   Deriv.orIntro1 (Deriv.iden (.head _))⟩

theorem bot_imp_interd (φ : PLLFormula) : Interd (q0.ifThen φ) q1 :=
  ⟨dTop, Deriv.impIntro
     (Deriv.toHead (Deriv.falsoElim _ (Deriv.iden (.head _))))⟩

/-! ## Axiom audits — sorry-free, all PLL -/

/-- info: 'PLLND.RNEmbed.imp_gap_collapse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms imp_gap_collapse

/-- info: 'PLLND.RNEmbed.gap2_collapse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms gap2_collapse

/-- info: 'PLLND.RNEmbed.dC_not_le_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dC_not_le_chain

/-- info: 'PLLND.RNEmbed.dC_off_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dC_off_image

end RNEmbed
end PLLND
