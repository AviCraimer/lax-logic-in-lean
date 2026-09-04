import wip.witness

/-!
# The gap antichain has NO greatest lower bound — the ∃-side floor question, settled

**Everything here is PLL.**  The question: does the landing ideal

    L := { χ : atomFree χ,  ∀ k ≥ 1, χ ⊢ g k }

(the variable-free common lower bounds of the gap antichain) contain a
formula valid on the plain ladder — equivalently, is the meet of the
antichain attained?  Answer: **NO**, and much more sharply.

The mechanism has three parts.

**(1) Below-edge agreement** (`cmE_agree_below`).  The edged lift
`cmE m` differs from the plain lift only in the two extra `Rₘ`-edges
LEAVING world `m+3`.  A world `y ≤ m+2` never sees `m+3` in its
intuitionistic cone (`cone y ⊆ [0,y]`), so by induction on the formula
the two models force exactly the same formulas at every such world.

**(2) Trace dichotomy** (`plain_trace_dichotomy`).  Forcing is
hereditary along `Rᵢ`, and the cone of `some x` on the ladder is
`{x} ∪ [0, x−2]`; so an unbounded truth set is downward-absorbing and
must be ALL of ℕ.  Every formula's plain-ladder trace is therefore
either everything or bounded.

**(3) Edge stability** (`edge_stability`).  For every formula `φ` there
is `M(φ)` with

    ∀ m ≥ M(φ),   (cmE m, m+3) ⊨ φ  ↔  (ladder, m+3) ⊨ φ.

Induction on `φ`: atoms and `⊥` are false at every skeleton world in
both models; `∧`,`∨`,`⊃` combine (the `⊃`-clause splits its cone into
`m+3`, where the IH applies, and `[0,m+1]`, where (1) applies); and the
`◯`-clause is where the edge lives —

    (cmE m, m+3) ⊨ ◯N  ↔  ∀ y ∈ [1, m+1], (ladder, y) ⊨ N
    (ladder, m+3) ⊨ ◯N  ↔  (∀ y ∈ [1, m+1], (ladder, y) ⊨ N) ∧ (ladder, m+3) ⊨ N

so the two differ only by the last conjunct, and (2) kills the
difference for `m` past `N`'s trace bound (either `N` is ladder-valid,
when both hold, or `N` fails at some `B+1 ≤ m+1`, when both fail).
Note this needs the trace dichotomy for `N`, NOT the IH for `N`.

**The theorem** (`L_bounded`).  If `χ ⊢ g k` for every `k ≥ 1` then
`χ`'s plain-ladder trace is bounded.  Indeed `g (m+1)` fails at
`(cmE m, m+3)` (`gap_fails`), so by soundness `χ` fails there for
EVERY `m`; were `χ`'s trace unbounded it would be everything, so `χ`
would hold at `(ladder, m+3)` for every `m` — contradicting edge
stability at `m = M(χ)`.  No `atomFree` hypothesis is needed: the two
lifts interpret every atom as the fallible singleton, so the statement
holds for one-variable formulas too.

**Consequences.**

* `no_ladder_valid_lower_bound`: no lower bound of the antichain is
  valid on the plain ladder — while every `g k` IS (`plain_forces_gap`).
* `gap_meet_not_attained`: for every lower bound `χ` and every `N`
  there is a world `n ≥ N` forcing every gap but not `χ`.
* `no_lower_bound_above_odd_rungs`: no lower bound sits above cofinally
  many odd rungs.

**The floor does not exist.**  Generalising the `w15` mechanism
(`Wit_below_all_gaps`) gives, for every `b`, a variable-free lower
bound

    Wit b := (g 1 ∧ … ∧ g (b+1)) ∧ t(2b+6)

whose plain trace contains `b+3`.  Since a greatest lower bound would
have to sit above every `Wit b`, its trace would be unbounded — refuted
by `L_bounded`.  Hence `gap_no_glb`: the family `{ g k : k ≥ 1 }` has
NO greatest lower bound in PLL, variable-free or otherwise; the
descending meet-chain `Gmeet` of `wip/uiObstruct.lean` has no floor.

The two derivation lemmas behind `Wit` are of independent interest and
generalise `w15_below_all_gaps` off its `a = 2` instance:

* `even_rung_gap`: `t(2a+2) ⊢ g k` for every `k ≥ a+1` — the exact
  rung-order threshold;
* `wC_gap_step`: `wC (j+1) = g (j+1) ∧ t(2j+6) ⊢ g (j+2)` — the box
  descent, which buys the one level `k = a` that rung order misses.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## 0. The plain ◯-clause, with ℕ-annotated binders

`Skel.box_force` quantifies over `S.W`, a defeq alias of `ℕ` that
`omega` silently drops; this restatement pins the binder to `Nat`. -/

/-- The plain lift's ◯-clause, in the shape of `cmE_box_force`: a cone
point is the abyss escape `0` or must force the body. -/
theorem ladder_box_force (N : PLLFormula) (x : Nat) :
    ladder.cm.force (some x) N.somehow ↔
      ∀ y : Nat, ladder.le x y → (y = 0 ∨ ladder.cm.force (some y) N) := by
  refine (ladder.box_force N x).trans ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · rcases h y hy with h0 | hf
    · exact Or.inl (ladder_U.mp h0)
    · exact Or.inr hf
  · rcases h y hy with h0 | hf
    · exact Or.inl (ladder_U.mpr h0)
    · exact Or.inr hf

/-! ## 1. Below the edge, the two lifts agree -/

/-- **Below-edge agreement**: the extra `Rₘ`-edges of `cmE m` all leave
world `m+3`, and no world `y ≤ m+2` has `m+3` in its intuitionistic
cone, so the edged and the plain lift force the same formulas at every
such world. -/
theorem cmE_agree_below (m : Nat) : ∀ (φ : PLLFormula) (y : Nat), y ≤ m + 2 →
    ((cmE m).force (some y) φ ↔ ladder.cm.force (some y) φ) := by
  intro φ
  induction φ with
  | prop a => intro y _; exact Iff.rfl
  | falsePLL => intro y _; exact Iff.rfl
  | and A B ihA ihB =>
      intro y hy
      show ((cmE m).force (some y) A ∧ (cmE m).force (some y) B) ↔
        (ladder.cm.force (some y) A ∧ ladder.cm.force (some y) B)
      exact and_congr (ihA y hy) (ihB y hy)
  | or A B ihA ihB =>
      intro y hy
      show ((cmE m).force (some y) A ∨ (cmE m).force (some y) B) ↔
        (ladder.cm.force (some y) A ∨ ladder.cm.force (some y) B)
      exact or_congr (ihA y hy) (ihB y hy)
  | ifThen A B ihA ihB =>
      intro y hy
      show (∀ v : Option Nat, (cmE m).Ri (some y) v →
            (cmE m).force v A → (cmE m).force v B) ↔
        (∀ v : Option Nat, ladder.cm.Ri (some y) v →
            ladder.cm.force v A → ladder.cm.force v B)
      constructor
      · intro h v hv hA
        cases v with
        | none => exact ladder.cm.force_of_fallible rfl
        | some z =>
            have hz : z ≤ m + 2 := by
              rcases (hv : z = y ∨ z + 2 ≤ y) with rfl | h2 <;> omega
            exact (ihB z hz).mp (h (some z) hv ((ihA z hz).mpr hA))
      · intro h v hv hA
        cases v with
        | none => exact (cmE m).force_of_fallible rfl
        | some z =>
            have hz : z ≤ m + 2 := by
              rcases (hv : z = y ∨ z + 2 ≤ y) with rfl | h2 <;> omega
            exact (ihB z hz).mpr (h (some z) hv ((ihA z hz).mp hA))
  | somehow N ih =>
      intro y hy
      refine (cmE_box_force m N y).trans
        (Iff.trans ?_ (ladder_box_force N y).symm)
      constructor
      · intro h z hz
        have hzy : z ≤ m + 2 := by
          rcases (hz : z = y ∨ z + 2 ≤ y) with rfl | h2 <;> omega
        rcases h z hz with h0 | h3 | hf
        · exact Or.inl h0
        · omega
        · exact Or.inr ((ih z hzy).mp hf)
      · intro h z hz
        have hzy : z ≤ m + 2 := by
          rcases (hz : z = y ∨ z + 2 ≤ y) with rfl | h2 <;> omega
        rcases h z hz with h0 | hf
        · exact Or.inl h0
        · exact Or.inr (Or.inr ((ih z hzy).mpr hf))

/-! ## 2. The plain trace is bounded or everything -/

/-- **Trace dichotomy**: on the plain lift, the truth set of a formula
restricted to skeleton worlds is either all of ℕ or bounded.  Pure
heredity: the cone of `some x` contains `[0, x−2]`. -/
theorem plain_trace_dichotomy (φ : PLLFormula) :
    (∀ n : Nat, ladder.cm.force (some n) φ) ∨
    (∃ B : Nat, ∀ n : Nat, B ≤ n → ¬ ladder.cm.force (some n) φ) := by
  by_cases h : ∃ B : Nat, ∀ n : Nat, B ≤ n → ¬ ladder.cm.force (some n) φ
  · exact Or.inr h
  · refine Or.inl fun n => ?_
    have hx : ∃ x : Nat, n + 2 ≤ x ∧ ladder.cm.force (some x) φ := by
      by_contra hc
      exact h ⟨n + 2, fun x hxn hf => hc ⟨x, hxn, hf⟩⟩
    obtain ⟨x, hx1, hx2⟩ := hx
    exact ladder.cm.force_hered
      (show ladder.cm.Ri (some x) (some n) from Or.inr (by omega)) hx2

/-! ## 3. Edge stability -/

/-- **Edge stability**: every formula eventually stops noticing the
edge.  For `m ≥ M(φ)` the edged lift `cmE m` and the plain lift agree
on `φ` at the edge world `m+3`. -/
theorem edge_stability (φ : PLLFormula) :
    ∃ M : Nat, ∀ m : Nat, M ≤ m →
      ((cmE m).force (some (m + 3)) φ ↔ ladder.cm.force (some (m + 3)) φ) := by
  induction φ with
  | prop a => exact ⟨0, fun _ _ => Iff.rfl⟩
  | falsePLL => exact ⟨0, fun _ _ => Iff.rfl⟩
  | and A B ihA ihB =>
      obtain ⟨MA, hA⟩ := ihA
      obtain ⟨MB, hB⟩ := ihB
      refine ⟨max MA MB, fun m hm => ?_⟩
      have h1 := hA m (le_trans (le_max_left MA MB) hm)
      have h2 := hB m (le_trans (le_max_right MA MB) hm)
      show ((cmE m).force (some (m + 3)) A ∧ (cmE m).force (some (m + 3)) B) ↔
        (ladder.cm.force (some (m + 3)) A ∧ ladder.cm.force (some (m + 3)) B)
      exact and_congr h1 h2
  | or A B ihA ihB =>
      obtain ⟨MA, hA⟩ := ihA
      obtain ⟨MB, hB⟩ := ihB
      refine ⟨max MA MB, fun m hm => ?_⟩
      have h1 := hA m (le_trans (le_max_left MA MB) hm)
      have h2 := hB m (le_trans (le_max_right MA MB) hm)
      show ((cmE m).force (some (m + 3)) A ∨ (cmE m).force (some (m + 3)) B) ↔
        (ladder.cm.force (some (m + 3)) A ∨ ladder.cm.force (some (m + 3)) B)
      exact or_congr h1 h2
  | ifThen A B ihA ihB =>
      obtain ⟨MA, hA⟩ := ihA
      obtain ⟨MB, hB⟩ := ihB
      refine ⟨max MA MB, fun m hm => ?_⟩
      have h1 := hA m (le_trans (le_max_left MA MB) hm)
      have h2 := hB m (le_trans (le_max_right MA MB) hm)
      show (∀ v : Option Nat, (cmE m).Ri (some (m + 3)) v →
            (cmE m).force v A → (cmE m).force v B) ↔
        (∀ v : Option Nat, ladder.cm.Ri (some (m + 3)) v →
            ladder.cm.force v A → ladder.cm.force v B)
      constructor
      · intro h v hv hA'
        cases v with
        | none => exact ladder.cm.force_of_fallible rfl
        | some z =>
            have hcone : z = m + 3 ∨ z + 2 ≤ m + 3 := hv
            rcases hcone with heq | hlo
            · subst heq
              exact h2.mp (h (some (m + 3)) hv (h1.mpr hA'))
            · exact (cmE_agree_below m B z (by omega)).mp
                (h (some z) hv ((cmE_agree_below m A z (by omega)).mpr hA'))
      · intro h v hv hA'
        cases v with
        | none => exact (cmE m).force_of_fallible rfl
        | some z =>
            have hcone : z = m + 3 ∨ z + 2 ≤ m + 3 := hv
            rcases hcone with heq | hlo
            · subst heq
              exact h2.mpr (h (some (m + 3)) hv (h1.mp hA'))
            · exact (cmE_agree_below m B z (by omega)).mpr
                (h (some z) hv ((cmE_agree_below m A z (by omega)).mp hA'))
  | somehow N _ =>
      rcases plain_trace_dichotomy N with hall | ⟨B, hB⟩
      · -- `N` is ladder-valid: the box holds at the edge world in both
        refine ⟨0, fun m _ => ?_⟩
        constructor
        · intro _
          exact (ladder_box_force N (m + 3)).mpr fun z _ => Or.inr (hall z)
        · intro _
          refine (cmE_box_force m N (m + 3)).mpr fun z hz => ?_
          have hcone : z = m + 3 ∨ z + 2 ≤ m + 3 := hz
          rcases hcone with heq | h2
          · exact Or.inr (Or.inl heq)
          · exact Or.inr (Or.inr
              ((cmE_agree_below m N z (by omega)).mpr (hall z)))
      · -- `N` fails from `B` on: past `m ≥ B` the witness `B+1` sits in
        -- the cone of `m+3`, strictly between `0` and the edge world
        refine ⟨B, fun m hm => ?_⟩
        have hcone : ladder.le (m + 3) (B + 1) := Or.inr (by omega)
        constructor
        · intro h
          exfalso
          rcases (cmE_box_force m N (m + 3)).mp h (B + 1) hcone with h0 | h3 | hf
          · omega
          · omega
          · exact hB (B + 1) (by omega)
              ((cmE_agree_below m N (B + 1) (by omega)).mp hf)
        · intro h
          exfalso
          rcases (ladder_box_force N (m + 3)).mp h (B + 1) hcone with h0 | hf
          · omega
          · exact hB (B + 1) (by omega) hf

/-! ## 4. The main theorem: every lower bound of the antichain has
bounded plain trace -/

/-- **The floor theorem.**  Any `χ` entailing every gap has a bounded
plain-ladder trace.  (No variable-freeness needed: both lifts read
every atom as the fallible singleton.) -/
theorem L_bounded {χ : PLLFormula} (h : ∀ k : Nat, 1 ≤ k → Deriv [χ] (gap k)) :
    ∃ B : Nat, ∀ n : Nat, B ≤ n → ¬ ladder.cm.force (some n) χ := by
  rcases plain_trace_dichotomy χ with hall | hb
  · exfalso
    obtain ⟨M, hM⟩ := edge_stability χ
    obtain ⟨d⟩ := h (M + 1) (by omega)
    have hforce : (cmE M).force (some (M + 3)) χ :=
      (hM M (le_refl M)).mpr (hall (M + 3))
    have hs := soundness d (cmE M) (some (M + 3)) (fun ψ hψ => by
      have e : ψ = χ := by
        cases hψ with
        | head => rfl
        | tail _ h' => cases h'
      subst e
      exact hforce)
    exact gap_fails M (M + 1) (le_refl (M + 1)) (by omega) hs
  · exact hb

/-- **No lower bound of the antichain is ladder-valid** — while every
gap is (`plain_forces_gap`). -/
theorem no_ladder_valid_lower_bound {χ : PLLFormula}
    (h : ∀ k : Nat, 1 ≤ k → Deriv [χ] (gap k)) :
    ¬ (∀ v : Option Nat, ladder.cm.force v χ) := by
  intro hv
  obtain ⟨B, hB⟩ := L_bounded h
  exact hB B (le_refl B) (hv (some B))

/-- **The antichain's meet is attained at no formula, pointwise**: for
every lower bound `χ` and every `N` there is a ladder world `n ≥ N`
forcing every gap but refuting `χ`. -/
theorem gap_meet_not_attained {χ : PLLFormula}
    (h : ∀ k : Nat, 1 ≤ k → Deriv [χ] (gap k)) (N : Nat) :
    ∃ n : Nat, N ≤ n ∧ (∀ k : Nat, ladder.cm.force (some n) (gap k)) ∧
      ¬ ladder.cm.force (some n) χ :=
  let ⟨B, hB⟩ := L_bounded h
  ⟨max N B, le_max_left N B,
    fun k => plain_forces_gap k (some (max N B)), hB _ (le_max_right N B)⟩

/-- **No lower bound sits above cofinally many odd rungs**: for every
`χ` under the antichain there is `K` with `t(2k+1) ⊬ χ` for all
`k ≥ K`. -/
theorem no_lower_bound_above_odd_rungs {χ : PLLFormula}
    (h : ∀ k : Nat, 1 ≤ k → Deriv [χ] (gap k)) :
    ∃ K : Nat, ∀ k : Nat, K ≤ k → ¬ Deriv [rnSub (2 * k + 1)] χ := by
  obtain ⟨B, hB⟩ := L_bounded h
  refine ⟨B, fun k hk hd => ?_⟩
  obtain ⟨d⟩ := hd
  have hs := soundness d ladder.cm (some k) (fun ψ hψ => by
    have e : ψ = rnSub (2 * k + 1) := by
      cases hψ with
      | head => rfl
      | tail _ h' => cases h'
    subst e
    exact (ladder.transfer (rn_boxFree _) k).mpr
      ((sat_rn_odd k k).mpr (le_refl k)))
  exact hB k hk hs

/-! ## 5. The landing ideal has members of unbounded trace -/

/-- Every conjunct of a partial meet is available. -/
theorem Gmeet_proj : ∀ (n k : Nat), 1 ≤ k → k ≤ n + 1 → Deriv [Gmeet n] (gap k) := by
  intro n
  induction n with
  | zero =>
      intro k h1 h2
      have e : k = 1 := by omega
      subst e
      exact Deriv.iden (.head _)
  | succ n ih =>
      intro k h1 h2
      rcases Nat.lt_or_ge k (n + 2) with hlt | hge
      · exact Deriv.cutHead
          (show Deriv [Gmeet (n + 1)] (Gmeet n) from
            Deriv.andElim1 (Deriv.iden (.head _)))
          (ih k h1 (by omega))
      · have e : k = n + 2 := by omega
        subst e
        exact Deriv.andElim2 (Deriv.iden (.head _))

/-- **The even rungs reach the gaps by rung order, above the exact
threshold**: `t(2a+2) ⊢ g k` whenever `a + 1 ≤ k`.  (`w15`'s `a = 2`
instance covers `k ≥ 2`; the one extra level `k = a` is exactly what
the box-descent below buys, at the cost of the `g (a−1)` conjunct.) -/
theorem even_rung_gap {a k : Nat} (h : a + 1 ≤ k) :
    Deriv [rnSub (2 * a + 2)] (gap k) :=
  Deriv.cutHead (rungD (eo_le h)) (rung_le_gap k)

/-- **The generalised `w15` descent, at every level**:
`g (j+1) ∧ t(2j+6) ⊢ g (j+2)`, i.e. `wC (j+1) ⊢ g (j+2)`.  Bind the
box `◯t(2j+5)`; inside it walk down through
`t(2j+6) = t(2j+5) ⊃ t(2j+3)`, so `◯t(2j+3) = c (j+1)` holds; exit
through `g (j+1)` to `t(2j+3)`; climb back by rung order.  The `j = 0`
instance is the `k = 2` case of `w15_below_all_gaps`. -/
theorem wC_gap_step (j : Nat) : Deriv [wC (j + 1)] (gap (j + 2)) := by
  have hEven : rnSub (2 * (j + 1) + 4)
      = (rnSub (2 * (j + 2) + 1)).ifThen (rnSub (2 * (j + 1) + 1)) := by
    have e1 : 2 * (j + 1) + 4 = 2 * (j + 2) + 2 := by omega
    have e2 : 2 * (j + 1) + 1 = 2 * (j + 2) - 1 := by omega
    rw [e1, e2]
    exact rnSub_even_eq (j + 2)
  show Deriv [wC (j + 1)] ((chainF (j + 2)).ifThen (rnSub (2 * (j + 2) + 1)))
  refine Deriv.impIntro ?_
  -- ctx [chainF (j+2), wC (j+1)] ⊢ t(2(j+2)+1)
  have hE : Deriv [chainF (j + 2), wC (j + 1)]
      ((rnSub (2 * (j + 2) + 1)).ifThen (rnSub (2 * (j + 1) + 1))) := by
    have h := Deriv.andElim2
      (Deriv.iden (φ := wC (j + 1)) (Γ := [chainF (j + 2), wC (j + 1)])
        (.tail _ (.head _)))
    rw [hEven] at h
    exact h
  have hbox : Deriv [chainF (j + 2), wC (j + 1)] (chainF (j + 1)) := by
    show Deriv [chainF (j + 2), wC (j + 1)] ((rnSub (2 * (j + 1) + 1)).somehow)
    refine dSomehowElim
      (show Deriv [chainF (j + 2), wC (j + 1)]
          ((rnSub (2 * (j + 2) + 1)).somehow) from Deriv.iden (.head _)) ?_
    refine dSomehowIntro ?_
    exact Deriv.impElim
      (Deriv.rename (fun χ hχ => .tail _ hχ) hE) (Deriv.iden (.head _))
  have hg : Deriv [chainF (j + 2), wC (j + 1)]
      ((chainF (j + 1)).ifThen (rnSub (2 * (j + 1) + 1))) :=
    Deriv.andElim1 (Deriv.iden (.tail _ (.head _)))
  exact Deriv.cutHead (Deriv.impElim hg hbox)
    (rungD (oo_le (show j + 1 ≤ j + 2 from by omega)))

/-- The generalised `w15`: `Wit b = (g 1 ∧ … ∧ g (b+1)) ∧ t(2b+6)`.
`Wit 0 = w15`. -/
def Wit (b : Nat) : PLLFormula := (Gmeet b).and (rnSub (2 * b + 6))

theorem Wit_zero : Wit 0 = wC 1 := rfl

theorem Wit_atomFree (b : Nat) : atomFree (Wit b) = true := by
  have hG : ∀ n : Nat, atomFree (Gmeet n) = true := by
    intro n
    induction n with
    | zero => exact gap_atomFree 1
    | succ n ih =>
        show (atomFree (Gmeet n) && atomFree (gap (n + 2))) = true
        rw [ih, gap_atomFree]
        rfl
  show (atomFree (Gmeet b) && atomFree (rnSub (2 * b + 6))) = true
  rw [hG, rnSub_atomFree]
  rfl

/-- **`Wit b` lies under the whole gap antichain.**  Three regimes:
`k ≤ b+1` by projection out of the partial meet (`Gmeet_proj`);
`k = b+2` by the generalised `w15` box-descent (`wC_gap_step`);
`k ≥ b+3` by rung order out of `t(2b+6) = E (b+2)`
(`even_rung_gap`). -/
theorem Wit_below_all_gaps (b : Nat) :
    ∀ {k : Nat}, 1 ≤ k → Deriv [Wit b] (gap k) := by
  intro k hk
  have hEven : Deriv [Wit b] (rnSub (2 * (b + 1) + 4)) := by
    rw [show 2 * (b + 1) + 4 = 2 * b + 6 from by omega]
    exact Deriv.andElim2 (Deriv.iden (.head _))
  rcases Nat.lt_or_ge k (b + 2) with hlo | hhi
  · -- k ≤ b+1: project out of the partial meet
    exact Deriv.cutHead
      (show Deriv [Wit b] (Gmeet b) from Deriv.andElim1 (Deriv.iden (.head _)))
      (Gmeet_proj b k hk (by omega))
  rcases Nat.lt_or_ge (b + 2) k with hgt | heq
  · -- k ≥ b+3: rung order out of t(2b+6)
    refine Deriv.cutHead hEven ?_
    rw [show 2 * (b + 1) + 4 = 2 * (b + 2) + 2 from by omega]
    exact even_rung_gap (show b + 2 + 1 ≤ k from by omega)
  · -- k = b+2: the box-descent through wC (b+1)
    have e : k = b + 2 := by omega
    subst e
    refine Deriv.cutHead
      (show Deriv [Wit b] (wC (b + 1)) from
        Deriv.andIntro
          (Deriv.cutHead
            (show Deriv [Wit b] (Gmeet b) from
              Deriv.andElim1 (Deriv.iden (.head _)))
            (Gmeet_proj b (b + 1) (by omega) (le_refl (b + 1))))
          hEven)
      (wC_gap_step b)

/-- `Wit b` is forced at plain-ladder world `b+3`: the gaps are forced
everywhere, and `t(2b+6) = E (b+2)` has truth set `[0, b+1] ∪ {b+3}`. -/
theorem Wit_force_high (b : Nat) : ladder.cm.force (some (b + 3)) (Wit b) := by
  have hG : ∀ n : Nat, ∀ x : Nat, ladder.cm.force (some x) (Gmeet n) := by
    intro n
    induction n with
    | zero => exact fun x => plain_forces_gap 1 (some x)
    | succ n ih =>
        intro x
        exact ⟨ih x, plain_forces_gap (n + 2) (some x)⟩
  refine ⟨hG b (b + 3), ?_⟩
  refine (ladder.transfer (rn_boxFree _) (b + 3)).mpr ?_
  have e : 2 * b + 6 = 2 * (b + 2) + 2 := by omega
  rw [e]
  exact (sat_rn_even (b + 2) (b + 3)).mpr (by omega)

/-! ## 6. The floor does not exist -/

/-- **The gap antichain has NO greatest lower bound.**  A glb would be
a lower bound above every `Wit b`, hence forced at plain-ladder world
`b+3` for every `b` — an unbounded trace, refuted by `L_bounded`.
(The statement quantifies over ALL formulas, so the meet fails to exist
even in the one-variable fragment, a fortiori in RN(◯,{}).) -/
theorem gap_no_glb :
    ¬ ∃ χ : PLLFormula, (∀ k : Nat, 1 ≤ k → Deriv [χ] (gap k)) ∧
      (∀ ψ : PLLFormula, (∀ k : Nat, 1 ≤ k → Deriv [ψ] (gap k)) →
        Deriv [ψ] χ) := by
  rintro ⟨χ, hlow, hglb⟩
  obtain ⟨B, hB⟩ := L_bounded hlow
  obtain ⟨d⟩ := hglb (Wit B) (fun k hk => Wit_below_all_gaps B hk)
  have hs := soundness d ladder.cm (some (B + 3)) (fun ψ hψ => by
    have e : ψ = Wit B := by
      cases hψ with
      | head => rfl
      | tail _ h' => cases h'
    subst e
    exact Wit_force_high B)
  exact hB (B + 3) (by omega) hs

/-- **The landing ideal `L` has no greatest element** — the
variable-free reading of `gap_no_glb`. -/
theorem L_no_greatest :
    ¬ ∃ χ : PLLFormula, atomFree χ = true ∧
      (∀ k : Nat, 1 ≤ k → Deriv [χ] (gap k)) ∧
      (∀ ψ : PLLFormula, atomFree ψ = true →
        (∀ k : Nat, 1 ≤ k → Deriv [ψ] (gap k)) → Deriv [ψ] χ) := by
  rintro ⟨χ, -, hlow, hglb⟩
  obtain ⟨B, hB⟩ := L_bounded hlow
  obtain ⟨d⟩ := hglb (Wit B) (Wit_atomFree B) (fun k hk => Wit_below_all_gaps B hk)
  have hs := soundness d ladder.cm (some (B + 3)) (fun ψ hψ => by
    have e : ψ = Wit B := by
      cases hψ with
      | head => rfl
      | tail _ h' => cases h'
    subst e
    exact Wit_force_high B)
  exact hB (B + 3) (by omega) hs

/-! ## Axiom audits — sorry-free, all PLL -/

/-- info: 'PLLND.RNEmbed.cmE_agree_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cmE_agree_below

/-- info: 'PLLND.RNEmbed.edge_stability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms edge_stability

/-- info: 'PLLND.RNEmbed.L_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms L_bounded

/-- info: 'PLLND.RNEmbed.gap_meet_not_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_meet_not_attained

/-- info: 'PLLND.RNEmbed.Wit_below_all_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wit_below_all_gaps

/-- info: 'PLLND.RNEmbed.even_rung_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms even_rung_gap

/-- info: 'PLLND.RNEmbed.wC_gap_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wC_gap_step

/-- info: 'PLLND.RNEmbed.gap_no_glb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_no_glb

/-- info: 'PLLND.RNEmbed.ladder_box_force' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ladder_box_force

/-- info: 'PLLND.RNEmbed.plain_trace_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms plain_trace_dichotomy

/-- info: 'PLLND.RNEmbed.no_ladder_valid_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_ladder_valid_lower_bound

/-- info: 'PLLND.RNEmbed.no_lower_bound_above_odd_rungs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_lower_bound_above_odd_rungs

/-- info: 'PLLND.RNEmbed.Gmeet_proj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Gmeet_proj

/-- info: 'PLLND.RNEmbed.Wit_force_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Wit_force_high

/-- info: 'PLLND.RNEmbed.Wit_atomFree' does not depend on any axioms -/
#guard_msgs in
#print axioms Wit_atomFree

/-- info: 'PLLND.RNEmbed.L_no_greatest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms L_no_greatest

end RNEmbed
end PLLND
