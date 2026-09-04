import wip.uiObstruct

/-!
# The witness hunt: a near-witness, a collapse lever, and im h closed off

All PLL.  Three results toward constructing-or-refuting the UI witness
of `wip/uiObstruct.lean`.

**1. The interpolant-candidate ideal `L` is bigger than it looked.**
`L := {χ variable-free : ∀ k ≥ 1, χ ⊢ g k}` (where a post-interpolant
of any gap-entailing formula must live).  Proved: `t5 ∈ L`
(`t5_in_L` — via the level-1 accident `q7 ⊢ q8`) and `w15 ∈ L`
(`w15_below_all_gaps` — the k = 2 case descends INSIDE the box through
`t6 = t5 ⊃ t3`), with `t3 ≤ w15` (`t3_le_w15`) and `w15 ⊬ t3`
(`w15_not_le_t3`).  So the floor of the antichain climbs strictly
above `t3`, and `L` contains the incomparable pair `t5`, `w15`: the
ideal has width.  (`t6 ∉ L` and `t7 ∉ L` by `even_not_le_gap` /
`odd_not_le_gap`.)

**2. A near-witness and the collapse lever.**

    phi1 := ◯p ⊃ ◯(p ∧ t3)

* `c1_le_phi1`: `c 1 ⊢ phi1` (bind both boxes; at level 1 the guard
  `t3` IS the anchor rung, so it is available inside).
* `c2_not_le_phi1`: `c 2 ⊬ phi1` — refuted on `cmP`, the plain lift
  with EVERY atom true everywhere (a new two-line model: the standard
  lift's proofs carry over, only the valuation fields change).  So
  `phi1` fails the schema hypothesis `hc` at k = 2: NOT a witness.
* But the OTHER schema hypothesis holds for it, by the substitution
  lever (`substND` at `p ↦ ⊤`): any variable-free `χ ⊢ phi1` has
  `χ ⊢ ◯(⊤ ∧ t3) ⊢ c 1` (`bound_collapse`), so no variable-free bound
  of the c-chain entails `phi1` (`phi1_hU`) — else `c 2 ⊢ c 1`,
  against chain strictness.  The lever is reusable: ANY witness of
  shape `◯p ⊃ ◯(p ∧ Y)` gets its `hU` for free whenever `◯Y` is not
  above the chain.

**3. Within im h, the ∀-side is CLOSED**: `inimage_chain_bound_top` —
any class in im h bounding the whole c-chain is `⊤` (via the
mechanised classification and `rung_cofinal`).  Consequently a
one-variable witness `φ` is blocked only if some OFF-IMAGE
variable-free class bounds the c-chain — and every known off-image
family has already been proved not to (§35–38).

**Where this leaves the hypothesis test**: the ∀-side witness question
is now: (a) find `φ` with `∀k, c k ⊢ φ` beyond theorems — the bind
mechanism reduces this to a one-variable bound of the RUNG chain, a
strictly simpler-looking question of the same shape; or (b) prove
every variable-free bound of the c-chain is `⊤` (true within im h and
for every known family; open in general), which with (a)-impossible
would defeat this attack on UI.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## 1. The ideal L climbs: t5 and w15 are both in it -/

/-- `t5 ⊢ g k` for every `k ≥ 1`: level 1 by the accident `q7 ⊢ q8`,
levels ≥ 2 by rung order. -/
theorem t5_in_L : ∀ {k : Nat}, 1 ≤ k → Deriv [rnSub 5] (gap k) := by
  intro k hk
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · -- k = 1: through q7 ⊢ q8 ≡ gap 1
    have hk1 : k = 1 := by omega
    subst hk1
    exact Deriv.cutHead (Deriv.cutHead q7_rn5.2 d_q7_q8) gap_one_q8.2
  · -- k ≥ 2: t5 = O 2 ≤ O k, then weakening into the gap
    exact Deriv.cutHead (rungD (oo_le h2)) (rung_le_gap k)

/-- **`w15 ⊢ g k` for every `k ≥ 1`** — the meet class `w15 = g1 ∧ t6`
lies under the whole antichain.  The k = 2 case is the two-step: bind
`c 2`, descend inside the box through `t6 = t5 ⊃ t3`, exit via `g 1`,
climb by rung order. -/
theorem w15_below_all_gaps : ∀ {k : Nat}, 1 ≤ k → Deriv [wC 1] (gap k) := by
  intro k hk
  match k, hk with
  | 1, _ => exact Deriv.andElim1 (Deriv.iden (.head _))
  | 2, _ =>
      refine Deriv.impIntro ?_
      -- ctx [chainF 2, wC 1] ⊢ rnSub (2*2+1)
      have hE : Deriv [chainF 2, wC 1]
          ((rnSub 5).ifThen (rnSub 3)) := by
        have h := Deriv.andElim2
          (Deriv.iden (φ := wC 1) (Γ := [chainF 2, wC 1]) (.tail _ (.head _)))
        rw [(rnSub_even_eq 2 : rnSub 6 = (rnSub 5).ifThen (rnSub 3))] at h
        exact h
      have hbox : Deriv [chainF 2, wC 1] ((rnSub 3).somehow) := by
        refine dSomehowElim (Deriv.iden (.head _)) ?_
        -- ctx [rnSub 5, chainF 2, wC 1] ⊢ (rnSub 3).somehow
        refine dSomehowIntro ?_
        exact Deriv.impElim
          (Deriv.rename (fun χ hχ => .tail _ hχ) hE) (Deriv.iden (.head _))
      have hg1 : Deriv [chainF 2, wC 1] (gap 1) :=
        Deriv.andElim1 (Deriv.iden (.tail _ (.head _)))
      have hO1 : Deriv [chainF 2, wC 1] (rnSub 3) :=
        Deriv.impElim hg1 hbox
      exact Deriv.cutHead hO1 (rungD (by decide))
  | (k + 3), _ =>
      -- k ≥ 3: t6 = E 2 ≤ O (k+3), then weakening into the gap
      refine Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) ?_
      exact Deriv.cutHead (rungD (eo_le (show 2 + 1 ≤ k + 3 from by omega)))
        (rung_le_gap (k + 3))

/-- `t3 ⊢ w15`: the old floor sits under the new one. -/
theorem t3_le_w15 : Deriv [rnSub 3] (wC 1) :=
  Deriv.andIntro (t3_below_gap (le_refl 1)) (rungD (by decide))

/-- `w15 ⊬ t3`: the climb is strict (plain-lift world 3). -/
theorem w15_not_le_t3 : ¬ Deriv [wC 1] (rnSub 3) := by
  rintro ⟨d⟩
  have hs := soundness d ladder.cm (some 3) (fun ψ hψ => by
    have e : ψ = wC 1 := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact (wC_plain_iff 1 3).mpr (by omega))
  have := (sat_rn_odd 1 3).mp ((ladder.transfer (rn_boxFree 3) 3).mp hs)
  omega

/-! ## 2. The near-witness phi1 and the collapse lever -/

/-- `phi1 := ◯p ⊃ ◯(p ∧ t3)`. -/
def phi1 : PLLFormula :=
  ((PLLFormula.prop pv).somehow).ifThen
    (((PLLFormula.prop pv).and (rnSub 3)).somehow)

/-- `c 1 ⊢ phi1`: bind both boxes; at level 1 the guard is the anchor. -/
theorem c1_le_phi1 : Deriv [chainF 1] phi1 := by
  refine Deriv.impIntro ?_
  -- ctx [◯p, chainF 1] ⊢ ◯(p ∧ t3)
  refine dSomehowElim (Deriv.iden (.head _)) ?_
  -- ctx [p, ◯p, chainF 1]
  refine dSomehowElim (Deriv.iden (.tail _ (.tail _ (.head _)))) ?_
  -- ctx [rnSub 3, p, ◯p, chainF 1] ⊢ ◯(p ∧ t3)
  exact dSomehowIntro (Deriv.andIntro (Deriv.iden (.tail _ (.head _)))
    (Deriv.iden (.head _)))

/-- The plain lift with EVERY atom true everywhere — same frame, new
valuation; only the two valuation proofs change. -/
@[reducible] def cmP : ConstraintModel :=
  { ladder.cm with
    V := fun _ => Set.univ
    hered_V := fun {_ _ _} _ _ => trivial
    full_F := fun {_ _} _ => trivial }

/-- Forcing of atom-free formulas is valuation-independent: `cmP` and
the plain lift agree on them. -/
theorem cmP_agree : ∀ {A : PLLFormula}, atomFree A = true →
    ∀ w : Option Nat, (cmP.force w A ↔ ladder.cm.force w A) := by
  intro A
  induction A with
  | prop a =>
      intro h w
      exact absurd h (by simp [atomFree])
  | falsePLL =>
      intro _ w
      exact Iff.rfl
  | and A B ihA ihB =>
      intro h w
      simp only [atomFree, Bool.and_eq_true] at h
      exact and_congr (ihA h.1 w) (ihB h.2 w)
  | or A B ihA ihB =>
      intro h w
      simp only [atomFree, Bool.and_eq_true] at h
      exact or_congr (ihA h.1 w) (ihB h.2 w)
  | ifThen A B ihA ihB =>
      intro h w
      simp only [atomFree, Bool.and_eq_true] at h
      show (∀ v, cmP.Ri w v → cmP.force v A → cmP.force v B) ↔
        (∀ v, ladder.cm.Ri w v → ladder.cm.force v A → ladder.cm.force v B)
      exact forall_congr' fun v => imp_congr Iff.rfl
        (imp_congr (ihA h.1 v) (ihB h.2 v))
  | somehow A ih =>
      intro h w
      show (∀ v, cmP.Ri w v → ∃ u, cmP.Rm v u ∧ cmP.force u A) ↔
        (∀ v, ladder.cm.Ri w v → ∃ u, ladder.cm.Rm v u ∧ ladder.cm.force u A)
      exact forall_congr' fun v => imp_congr Iff.rfl
        (exists_congr fun u => and_congr Iff.rfl (ih h u))

/-- `phi1` fails at world 2 of `cmP`: with `p` true everywhere, `◯p`
holds but `◯(p ∧ t3)` needs `t3` at world 2, which fails. -/
theorem cmP_not_phi1 : ¬ cmP.force (some 2) phi1 := by
  intro hs
  have h' : ∀ v : Option Nat, cmP.Ri (some 2) v →
      cmP.force v ((PLLFormula.prop pv).somehow) →
      cmP.force v (((PLLFormula.prop pv).and (rnSub 3)).somehow) := hs
  have hbox : cmP.force (some 2) ((PLLFormula.prop pv).somehow) := by
    intro v hv
    cases v with
    | none => exact ⟨none, trivial, cmP.force_of_fallible rfl⟩
    | some y => exact ⟨some y, rfl, trivial⟩
  obtain ⟨u, hm, hf⟩ := h' (some 2) (Or.inl rfl) hbox (some 2) (Or.inl rfl)
  cases u with
  | none =>
      have h2 : (2 : Nat) ∈ ladder.U := hm
      exact absurd (ladder_U.mp h2) (by omega)
  | some z =>
      have hz : (2 : Nat) = z := hm
      subst hz
      have h3 := (cmP_agree (rnSub_atomFree 3) (some 2)).mp
        (hf : cmP.force (some 2) ((PLLFormula.prop pv).and (rnSub 3))).2
      have := (sat_rn_odd 1 2).mp ((ladder.transfer (rn_boxFree 3) 2).mp h3)
      omega

/-- `c 2 ⊬ phi1` — so `phi1` is NOT the witness (the schema hypothesis
`hc` fails at k = 2). -/
theorem c2_not_le_phi1 : ¬ Deriv [chainF 2] phi1 := by
  rintro ⟨d⟩
  refine cmP_not_phi1 (soundness d cmP (some 2) (fun ψ hψ => ?_))
  have e : ψ = chainF 2 := by
    cases hψ with
    | head => rfl
    | tail _ h => cases h
  subst e
  exact (cmP_agree (chainF_atomFree 2) (some 2)).mpr
    ((chainF_force_iff 2 2).mpr (le_refl 2))

/-- `phi1` is not a theorem. -/
theorem not_thm_phi1 : ¬ Deriv [] phi1 := by
  rintro ⟨d⟩
  exact cmP_not_phi1 (soundness d cmP (some 2) (fun ψ hψ => by cases hψ))

/-- Substitution for `Deriv` (wrapping `substND`). -/
theorem Deriv.substP' {Γ : List PLLFormula} {φ : PLLFormula}
    (p : String) (χ : PLLFormula) :
    Deriv Γ φ → Deriv (Γ.map (substP p χ)) (substP p χ φ)
  | ⟨d⟩ => ⟨substND p χ d⟩

/-- **The collapse lever**: any variable-free `χ ⊢ phi1` entails
`c 1` — substitute `p ↦ ⊤` and feed the box `⊢ ◯⊤`. -/
theorem bound_collapse {χ : PLLFormula} (ha : atomFree χ = true)
    (h : Deriv [χ] phi1) : Deriv [χ] (chainF 1) := by
  have h1 := Deriv.substP' pv q1 h
  rw [show [χ].map (substP pv q1) = [χ] from by
        rw [List.map_cons, List.map_nil, substP_atomFree pv q1 χ ha],
      show substP pv q1 phi1
        = (q1.somehow).ifThen ((q1.and (rnSub 3)).somehow) from by decide] at h1
  have htop : Deriv [χ] (q1.somehow) := dSomehowIntro dTop
  have hbox := Deriv.impElim h1 htop
  refine Deriv.cutHead hbox ?_
  exact box_mono (Deriv.andElim2 (Deriv.iden (.head _)))

/-- **No variable-free bound of the c-chain entails `phi1`** — else
`c 2 ⊢ c 1`, against chain strictness.  So `phi1` satisfies the `hU`
hypothesis of `no_pre_interp_schema`; only `hc` fails for it. -/
theorem phi1_hU : ∀ χ, atomFree χ = true →
    (∀ k, Deriv [chainF k] χ) → ¬ Deriv [χ] phi1 := by
  intro χ ha hb hc
  exact chain_lt_strict (show 1 < 2 from by omega)
    (Deriv.cutHead (hb 2) (bound_collapse ha hc))

/-! ## 3. Within im h, only ⊤ bounds the c-chain -/

/-- No rung bounds the odd rungs: `O (n+1) ⊬ t n`. -/
theorem rung_cofinal (n : Nat) :
    ¬ Deriv [rnSub (2 * (n + 1) + 1)] (rnSub n) := by
  rintro ⟨d⟩
  have hs := soundness d ladder.cm (some (n + 1)) (fun ψ hψ => by
    have e : ψ = rnSub (2 * (n + 1) + 1) := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact (ladder.transfer (rn_boxFree _) (n + 1)).mpr
      ((sat_rn_odd (n + 1) (n + 1)).mpr (le_refl _)))
  have hb := rungMem_bound
    ((sat_rung n (n + 1)).mp ((ladder.transfer (rn_boxFree n) (n + 1)).mp hs))
  omega

/-- **Within im h the ∀-side closes**: any image class bounding the
whole c-chain is `⊤`. -/
theorem inimage_chain_bound_top {X : PLLFormula} (hX : InImage X)
    (hb : ∀ k, Deriv [chainF k] X) : Interd q1 X := by
  obtain ⟨A, hA, hp, hI⟩ := hX
  rcases image_classification hA hp with ⟨n, hn⟩ | hn
  · -- X ≡ rung n: the chain would bound the rungs, against cofinality
    exfalso
    have hrn : Deriv [rnSub (2 * (n + 1) + 1)] X :=
      Deriv.cutHead (dSomehowIntro (Deriv.iden (.head _))) (hb (n + 1))
    exact rung_cofinal n
      (Deriv.cutHead hrn (hI.trans hn).1)
  · exact (hI.trans hn).symm

/-! ## Axiom audits — sorry-free, all PLL -/

/-- info: 'PLLND.RNEmbed.w15_below_all_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms w15_below_all_gaps

/-- info: 'PLLND.RNEmbed.c2_not_le_phi1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms c2_not_le_phi1

/-- info: 'PLLND.RNEmbed.phi1_hU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phi1_hU

/-- info: 'PLLND.RNEmbed.inimage_chain_bound_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inimage_chain_bound_top

end RNEmbed
end PLLND
