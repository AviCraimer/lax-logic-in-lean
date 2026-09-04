import wip.chainStrict

/-!
# The second lift: the chain is OFF the image, at every level — so
# RN(◯,{}) ∖ im h is infinite

`docs/chain-strictness.md` §"What comes next" carried out.  The abyss
lift cannot separate `◯rnSub m` from `rnSub m` (a world lies in its own
cone), so a second model family is built: the **edged lift** `cmE k` —
the lifted ladder with ONE extra internal `Rₘ`-edge

    (k+3) ⇝ 0

(plus `(k+3) ⇝ none` to keep `Rₘ` transitive).  The side condition
from the plan holds: the edge does not enlarge the truth set of `◯⊥`,
because world `1` still witnesses failure everywhere it did — this is
`cmE_force_oBot`, and it feeds a re-run of the transfer induction
(`cmE_transfer`), so the substituted rungs keep their rung truth sets.

At world `k+3` the edge makes `◯rnSub(2k+5)` true (the cone escapes
through `0`) while `rnSub(2k+5)` itself stays false — giving, for
every `k`,

    box_not_fix : ◯rnSub(2(k+2)+1) ⊬ rnSub(2(k+2)+1)

("the unit is strict on the odd rungs from rung 5 up").

**The off-image argument** then needs no `q5`-style squeeze at all.
If `chainF k ≡ rnSub n`, evaluate BOTH on the plain abyss lift: there
`chainF k` wears the truth set `[0, k]` (`chainF_force_iff`), so by
soundness both directions transfer pointwise, `rnSub_deriv_iff` turns
the pointwise agreement into `Interd (rnSub n) (rnSub (2k+1))`, and
`rn_pairwise_pll` forces `n = 2k+1` — exactly the identification that
`box_not_fix` refutes.  `⊤` was already excluded for the whole chain
(`chain_never_top`).  Hence, modulo the classical Rieger–Nishimura
classification (`im h` = rungs ∪ {⊤}, not yet mechanised — the same
caveat as `q5_not_any_rung`):

    the pairwise-distinct family { chainF k : k ≥ 2 } lies entirely
    outside im h  —  RN(◯,{}) ∖ im h is INFINITE.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-! ## The edged lift -/

/-- `Rₘ` with one internal edge `(k+3) ⇝ 0` (and `(k+3) ⇝ none`, for
transitivity through the abyss-jump of `0 ∈ U`). -/
def RmE (k : Nat) : Option Nat → Option Nat → Prop
  | some v, some w => v = w ∨ (v = k + 3 ∧ w = 0)
  | some v, none   => v = 0 ∨ v = k + 3
  | none,   none   => True
  | none,   some _ => False

/-- The edged lift of the ladder. -/
@[reducible] def cmE (k : Nat) : ConstraintModel where
  W := Option Nat
  Ri := riL ladder
  Rm := RmE k
  F := {x | x = none}
  V _ := {x | x = none}
  refl_i x := by
    cases x with
    | none => exact trivial
    | some a => exact ladder.refl a
  trans_i {x y z} h1 h2 := by
    cases x with
    | none =>
        cases y with
        | some b => exact (h1 : False).elim
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact trivial
    | some a =>
        cases y with
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact trivial
        | some b =>
            cases z with
            | none => exact trivial
            | some c => exact ladder.trans h1 h2
  refl_m x := by
    cases x with
    | none => exact trivial
    | some a => exact Or.inl rfl
  trans_m {x y z} h1 h2 := by
    cases x with
    | none =>
        cases y with
        | some b => exact (h1 : False).elim
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact trivial
    | some a =>
        cases y with
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact h1
        | some b =>
            cases z with
            | none =>
                rcases (h1 : a = b ∨ (a = k + 3 ∧ b = 0)) with rfl | ⟨ha, rfl⟩
                · exact h2
                · exact Or.inr ha
            | some c =>
                rcases (h1 : a = b ∨ (a = k + 3 ∧ b = 0)) with rfl | ⟨ha, rfl⟩
                · exact h2
                · rcases (h2 : (0 : Nat) = c ∨ ((0 : Nat) = k + 3 ∧ c = 0))
                    with rfl | ⟨h0, _⟩
                  · exact Or.inr ⟨ha, rfl⟩
                  · omega
  sub_mi {x y} h := by
    cases x with
    | none =>
        cases y with
        | some b => exact (h : False).elim
        | none => exact trivial
    | some a =>
        cases y with
        | none => exact trivial
        | some b =>
            rcases (h : a = b ∨ (a = k + 3 ∧ b = 0)) with rfl | ⟨rfl, rfl⟩
            · exact ladder.refl a
            · show (0 : Nat) = k + 3 ∨ 0 + 2 ≤ k + 3
              omega
  hered_F {x y} h hx := by
    obtain rfl := (hx : x = none)
    cases y with
    | some b => exact (h : False).elim
    | none => exact rfl
  hered_V {a x y} h hx := by
    obtain rfl := (hx : x = none)
    cases y with
    | some b => exact (h : False).elim
    | none => exact rfl
  full_F {a x} hx := hx

/-- **The side condition**: the edge does not enlarge `T(◯⊥)` — the
truth set of `◯⊥` on the skeleton part is still exactly `{0}`. -/
theorem cmE_force_oBot (k : Nat) (x : Nat) :
    (cmE k).force (some x) oBot ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    rcases Nat.lt_or_ge x 3 with h3 | h3
    · -- x ∈ {1, 2}: witness v = x itself
      obtain ⟨u, hm, hu⟩ := h (some x) (Or.inl rfl)
      cases u with
      | some z =>
          rcases (hm : x = z ∨ (x = k + 3 ∧ z = 0)) with rfl | ⟨he, _⟩
          · exact absurd (hu : (some x : Option Nat) = none)
              (Option.some_ne_none x)
          · omega
      | none =>
          rcases (hm : x = 0 ∨ x = k + 3) with rfl | he <;> omega
    · -- x ≥ 3: witness v = 1
      obtain ⟨u, hm, hu⟩ := h (some 1) (Or.inr (by omega))
      cases u with
      | some z =>
          rcases (hm : 1 = z ∨ ((1 : Nat) = k + 3 ∧ z = 0)) with rfl | ⟨he, _⟩
          · exact absurd (hu : (some 1 : Option Nat) = none)
              (Option.some_ne_none 1)
          · omega
      | none =>
          rcases (hm : (1 : Nat) = 0 ∨ (1 : Nat) = k + 3) with he | he <;> omega
  · rintro rfl v hv
    cases v with
    | none => exact ⟨none, trivial, rfl⟩
    | some y =>
        have hy : y = 0 := by
          rcases (hv : y = 0 ∨ y + 2 ≤ 0) with rfl | h <;> omega
        subst hy
        exact ⟨none, Or.inl rfl, rfl⟩

/-- **The transfer, re-run on the edged lift**: for ◯-free `A`, forcing
of `A[p := ◯⊥]` at a skeleton world is IPC forcing on the ladder.  The
same induction as `Skel.transfer`; the atom case is `cmE_force_oBot`. -/
theorem cmE_transfer (k : Nat) :
    ∀ {A : PLLFormula}, boxFree A = true →
      ∀ w : Nat, ((cmE k).force (some w) (substP pv oBot A) ↔ ladder.sat A w) := by
  intro A
  induction A with
  | prop a =>
      intro _ w
      by_cases ha : a = pv
      · subst ha
        show (cmE k).force (some w) oBot ↔ ladder.sat (.prop pv) w
        rw [cmE_force_oBot k w]
        exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
      · have he : substP pv oBot (.prop a) = .prop a := by
          show (if a = pv then oBot else .prop a) = .prop a
          exact if_neg ha
        rw [he]
        constructor
        · intro h
          exact absurd (h : (some w : Option Nat) = none) (Option.some_ne_none w)
        · intro h
          exact absurd h.1 ha
  | falsePLL =>
      intro _ w
      show ((some w : Option Nat) = none) ↔ False
      exact iff_false_intro (Option.some_ne_none w)
  | and A B ihA ihB =>
      intro h w
      simp only [boxFree, Bool.and_eq_true] at h
      show ((cmE k).force (some w) (substP pv oBot A) ∧
            (cmE k).force (some w) (substP pv oBot B)) ↔
          (ladder.sat A w ∧ ladder.sat B w)
      exact and_congr (ihA h.1 w) (ihB h.2 w)
  | or A B ihA ihB =>
      intro h w
      simp only [boxFree, Bool.and_eq_true] at h
      show ((cmE k).force (some w) (substP pv oBot A) ∨
            (cmE k).force (some w) (substP pv oBot B)) ↔
          (ladder.sat A w ∨ ladder.sat B w)
      exact or_congr (ihA h.1 w) (ihB h.2 w)
  | ifThen A B ihA ihB =>
      intro h w
      simp only [boxFree, Bool.and_eq_true] at h
      show (∀ v, (cmE k).Ri (some w) v →
            (cmE k).force v (substP pv oBot A) →
            (cmE k).force v (substP pv oBot B)) ↔
          (∀ y, ladder.le w y → ladder.sat A y → ladder.sat B y)
      constructor
      · intro hf y hle hsy
        exact (ihB h.2 y).mp (hf (some y) hle ((ihA h.1 y).mpr hsy))
      · intro hs v hv hvA
        cases v with
        | none => exact (cmE k).force_of_fallible rfl
        | some y => exact (ihB h.2 y).mpr (hs y hv ((ihA h.1 y).mp hvA))
  | somehow A ih =>
      intro h w
      simp only [boxFree] at h
      exact Bool.noConfusion h

/-! ## The unit is strict on the odd rungs from rung 5 up -/

/-- **`◯rnSub(2(k+2)+1) ⊬ rnSub(2(k+2)+1)`**: on the edged lift, world
`k+3` forces the box (its cone escapes through the edge and through the
low rungs) but not the rung itself. -/
theorem box_not_fix (k : Nat) :
    ¬ Deriv [chainF (k + 2)] (rnSub (2 * (k + 2) + 1)) := by
  rintro ⟨d⟩
  have hs := soundness d (cmE k) (some (k + 3)) ?_
  · -- conclusion not forced at k+3
    have h := (cmE_transfer k (rn_boxFree (2 * (k + 2) + 1)) (k + 3)).mp hs
    rw [show 2 * (k + 2) + 1 = 2 * (k + 2) + 1 from rfl] at h
    have := (sat_rn_odd (k + 2) (k + 3)).mp h
    omega
  · -- the hypothesis chainF (k+2) IS forced at k+3
    intro ψ hψ
    have e : ψ = chainF (k + 2) := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    show (cmE k).force (some (k + 3)) ((rnSub (2 * (k + 2) + 1)).somehow)
    intro v hv
    cases v with
    | none => exact ⟨none, trivial, (cmE k).force_of_fallible rfl⟩
    | some y =>
        rcases (hv : y = k + 3 ∨ y + 2 ≤ k + 3) with rfl | hy
        · -- through the edge to world 0
          refine ⟨some 0, Or.inr ⟨rfl, rfl⟩, ?_⟩
          exact (cmE_transfer k (rn_boxFree _) 0).mpr
            ((sat_rn_odd (k + 2) 0).mpr (by omega))
        · -- stay put: y ≤ k+1 lies inside the rung
          refine ⟨some y, Or.inl rfl, ?_⟩
          exact (cmE_transfer k (rn_boxFree _) y).mpr
            ((sat_rn_odd (k + 2) y).mpr (by omega))

/-! ## The truth set of the chain on the plain abyss lift -/

/-- On the plain abyss lift, `chainF k` wears exactly the truth set of
rung `2k+1`. -/
theorem chainF_force_iff (k w : Nat) :
    ladder.cm.force (some w) (chainF k) ↔ w ≤ k := by
  show ladder.cm.force (some w) ((rnSub (2 * k + 1)).somehow) ↔ _
  rw [ladder_box_rn]
  constructor
  · intro h
    rcases h w (Or.inl rfl) with h0 | hs
    · omega
    · exact (sat_rn_odd k w).mp hs
  · intro hw y hy
    refine Or.inr ((sat_rn_odd k y).mpr ?_)
    rcases (ladder_le.mp hy) with h | h <;> omega

/-! ## The chain is off the image -/

/-- **`chainF k` is interderivable with no rung** (`k ≥ 2`).  If it
were `rnSub n`, both would wear the same truth set on the abyss lift,
so `n = 2k+1` by `rnSub_deriv_iff` + `rn_pairwise_pll` — the one
identification `box_not_fix` refutes. -/
theorem chain_not_any_rung {k : Nat} (hk : 2 ≤ k) :
    ∀ n : Nat, ¬ Interd (rnSub n) (chainF k) := by
  rintro n ⟨h1, h2⟩
  have hpt : ∀ w, ladder.sat (rn n) w ↔ w ≤ k := by
    intro w
    constructor
    · intro hw
      obtain ⟨d⟩ := h1
      have hf := soundness d ladder.cm (some w) (fun ψ hψ => by
        cases hψ with
        | head => exact (ladder.transfer (rn_boxFree n) w).mpr hw
        | tail _ h => cases h)
      exact (chainF_force_iff k w).mp hf
    · intro hw
      obtain ⟨d⟩ := h2
      have hf := soundness d ladder.cm (some w) (fun ψ hψ => by
        cases hψ with
        | head => exact (chainF_force_iff k w).mpr hw
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
  exact box_not_fix (k - 2) (by
    rw [show (k - 2) + 2 = k from by omega]
    exact h2)

/-- `chainF k` is not the top class either. -/
theorem chain_not_top (k : Nat) : ¬ Interd q1 (chainF k) := by
  rintro ⟨h1, -⟩
  exact chain_never_top (2 * k + 1)
    (Deriv.cutHead (Deriv.impIntro (Deriv.iden (.head _))) h1)

/-- **RN(◯,{}) ∖ im h is infinite** (modulo the classical RN
classification `im h` = rungs ∪ {⊤}, not yet mechanised — the same
caveat as `q5_not_any_rung`): for every `k ≥ 2`, `chainF k` is
interderivable with no rung and not with `⊤`, and the `chainF k` are
pairwise non-interderivable (`chain_pairwise`). -/
theorem complement_infinite (k : Nat) (hk : 2 ≤ k) :
    (∀ n, ¬ Interd (rnSub n) (chainF k)) ∧
    (¬ Interd q1 (chainF k)) ∧
    (∀ j, j ≠ k → ¬ Interd (chainF j) (chainF k)) :=
  ⟨chain_not_any_rung hk, chain_not_top k, fun _ hj => chain_pairwise hj⟩

/-! ## Axiom audits — sorry-free throughout -/

/-- info: 'PLLND.RNEmbed.box_not_fix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms box_not_fix

/-- info: 'PLLND.RNEmbed.chain_not_any_rung' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_not_any_rung

/-- info: 'PLLND.RNEmbed.complement_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms complement_infinite

end RNEmbed
end PLLND
