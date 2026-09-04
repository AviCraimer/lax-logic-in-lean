import LaxLogic.PLLFrames
import LaxLogic.PLLCompleteness

/-!
# The closed lax fragment RN(◯,{}) is a rich intuitionistic structure

The closed lax fragment RN(◯,{}) is the Lindenbaum algebra of variable-free PLL
formulas (`⊥, ∧, ∨, ⊃, ◯`) — the free Heyting-algebra-with-nucleus on 0 generators.

## What is proved here (fully mechanised)

1. `not_entails_of_force` / `Ineq` / `ineq_imp_notEquiv` — a **reusable separation
   tool**: a single finite constraint model that forces one closed formula and
   refutes another witnesses their non-⊣⊢-equivalence (via `soundness`).

2. `closed_lax_ge_eight` — an explicit list of **eight pairwise ⊣⊢-inequivalent
   closed lax formulas**, separated by one finite constraint model `MC`.  In
   particular `◯(¬◯⊥)` is a genuinely new closed element, distinct from
   `⊥, ◯⊥, ¬◯⊥, ¬¬◯⊥, ¬¬◯⊥⊃◯⊥, ¬◯⊥∨¬¬◯⊥, ⊤`.  (The `◯`-free closed IPL fragment
   collapses to `{⊥,⊤}`; RN(p) shows only 7 classes up to Dyckhoff weight 8.)

## The model `MC` (comb + fallible top)

`MC` realises `◯⊥` as an RN-style generator.  Worlds `Fin 7`:
`A₁ A₂ A₃` (a "spine of a-points") and `B₁ B₂ B₃` (a linear b-spine) form the
finite Rieger–Nishimura comb of height 3, with a fallible top `f`.  `⊑_m` steps
only `B₁ ⤳ f`, so `MC ⊨ ◯⊥` exactly at `{B₁}` (plus the fallible `f`) — i.e. `◯⊥`
behaves as the free-generator upset `↑B₁`.

## Full infinitude — the reduction (this file)

RN(◯,{}) is in fact **infinite**: the map `p ↦ ◯⊥` embeds the free Heyting
algebra on one generator RN({p}) (the infinite Rieger–Nishimura lattice) into
RN(◯,{}).

This file mechanises the **reduction** of that infinitude to its genuine crux,
sorry-free:

* `infinite_of_strict_chain` — **the engine.**  Any `ℕ`-indexed STRICT ascending
  chain of closed formulas yields `Infinite (Quotient closedSetoid)`, the
  `⊣⊢`-Lindenbaum quotient over atom-free formulas.  Proof: `le_mono` +
  `no_reverse` (transitivity) give pairwise `NotEquiv` (`chain_notEquiv`), and
  `ℕ` injects into the quotient.  Uses only the soundness/completeness bridge
  `consequence_iff_derivable` — no explicit model.  Clean axioms.
* `disjLadder` / `disjLadder_fwd` / `disjLadder_atomFree` — packaging the chain
  as a disjunctive ladder makes the **forward** entailments free (an `∨`-intro,
  valid in every model — `disjLadder_fwd` needs *no* axioms) and preserves
  closedness.
* `force_subOb` — **the embedding, `◯⊥` is a free Heyting generator** (mechanised,
  only `propext`).  A base IPC constraint model `P` (empty `F`, valuation constant
  `= U := P.V "p"`) is lifted to `P⁺ := lift P` by adjoining one fallible top
  `f = none`; then `◯⊥` is realised exactly as `U` (`force_Ob`), and for every IPC
  `γ`, `force_{P⁺} (some w) (subOb γ) ↔ P.force w γ` (induction on `γ`; the added
  fallible successor `f` makes the `⊃`-clause trivial).  Hence `not_Le_subOb`:
  every IPC separation transports to a *closed* one.  This mechanises the previous
  run's key rigorous-but-unmechanised claim.
* `exists_escaping_rungs` — derived `sorry`-free from `ipc_escaping` via the
  embedding (rungs `= subOb ∘ ρ`).
* `ipc_escaping` — **the former residual, now proved `sorry`-free.**  Entirely
  `◯`-free: a one-variable IPC disjunctive ladder each of whose rungs strictly
  escapes the running join, witnessed by base IPC models.  This is exactly the
  classical infinitude of the one-generated free Heyting algebra RN({p}) (the
  Rieger–Nishimura lattice).  It cannot be met by a *single finite* model — every
  finite model caps the fragment (checked: ≤ 9 classes for all height-≤ 8 combs,
  and `MC = C₃` already realises the 8 of `closed_lax_ge_eight`) — so the witness
  is one *infinite* model `rnModel`, a clean `ℕ`-presentation of de Jongh's
  one-variable universal model (`w ⊑ v :⟺ v = w ∨ v + 1 < w`, generator `p` at the
  top world `0`).  On it the RN ladder `sLad` is forced *exactly* on the initial
  segment `{0, …, n}` (`rn_staircase`), so `sₙ₊₁` escapes `sₙ` at world `n + 1`;
  the rungs `rhoLad` package it as `disjLadder rhoLad n = sLad n` (`rn_disj_eq`).
-/

open PLLFormula

namespace PLLND
namespace LaxInfinite

/-! ### The comb-plus-fallible model `MC` -/

-- Fin 7:  0=A₁ 1=A₂ 2=A₃ | 3=B₁ 4=B₂ 5=B₃ | 6=f (fallible).
def ile (x y : Fin 7) : Prop :=
  x = y ∨
  (y.val = 6 ∧ x.val ≠ 0) ∨
  (x.val ≤ 2 ∧ y.val ≤ 2 ∧ y.val ≤ x.val) ∨
  (x.val ≤ 2 ∧ 3 ≤ y.val ∧ y.val ≤ 5 ∧ y.val < x.val + 3) ∨
  (3 ≤ x.val ∧ x.val ≤ 5 ∧ 3 ≤ y.val ∧ y.val ≤ 5 ∧ y.val ≤ x.val)
instance : DecidableRel ile := fun x y => by unfold ile; infer_instance

def ilm (x y : Fin 7) : Prop := x = y ∨ (x.val = 3 ∧ y.val = 6)
instance : DecidableRel ilm := fun x y => by unfold ilm; infer_instance

@[reducible] def MC : ConstraintModel where
  W := Fin 7
  Ri := ile
  Rm := ilm
  F := {x | x.val = 6}
  V _ := {x | x.val = 6}
  refl_i _ := .inl rfl
  trans_i {x y z} h h' := by
    revert h h'; exact (by decide : ∀ x y z : Fin 7, ile x y → ile y z → ile x z) x y z
  trans_m {x y z} h h' := by
    revert h h'; exact (by decide : ∀ x y z : Fin 7, ilm x y → ilm y z → ilm x z) x y z
  refl_m _ := .inl rfl
  sub_mi {x y} h := by
    revert h; exact (by decide : ∀ x y : Fin 7, ilm x y → ile x y) x y
  hered_F {x y} h hw := by
    revert h hw; exact (by decide : ∀ x y : Fin 7, ile x y → x.val = 6 → y.val = 6) x y
  hered_V {_ x y} h hw := by
    revert h hw; exact (by decide : ∀ x y : Fin 7, ile x y → x.val = 6 → y.val = 6) x y
  full_F hw := hw

instance (φ : PLLFormula) (w : MC.W) : Decidable (MC.force w φ) := MC.decForce φ w

/-! ### Reusable separation tool -/

/-- If a model forces `a` and refutes `b` at some world, then `a ⊬ b`. -/
theorem not_entails_of_force {C : ConstraintModel} (w : C.W) {a b : PLLFormula}
    (ha : C.force w a) (hb : ¬ C.force w b) : ¬ Nonempty (LaxND [a] b) := by
  rintro ⟨p⟩
  refine hb (soundness p C w ?_)
  intro ψ hψ
  rw [List.mem_singleton.mp hψ]; exact ha

/-- Two formulas are non-⊣⊢-equivalent: not derivable in both directions. -/
def NotEquiv (a b : PLLFormula) : Prop :=
  ¬ (Nonempty (LaxND [a] b) ∧ Nonempty (LaxND [b] a))

/-- Decidable, `MC`-checkable witness of inequivalence. -/
def Ineq (a b : PLLFormula) : Prop :=
  (∃ w : Fin 7, MC.force w a ∧ ¬ MC.force w b) ∨
  (∃ w : Fin 7, MC.force w b ∧ ¬ MC.force w a)

instance (a b : PLLFormula) : Decidable (Ineq a b) := by unfold Ineq; infer_instance

theorem ineq_imp_notEquiv {a b : PLLFormula} (h : Ineq a b) : NotEquiv a b := by
  intro hh
  rcases h with ⟨w, ha, hb⟩ | ⟨w, hb, ha⟩
  · exact not_entails_of_force (C := MC) w ha hb hh.1
  · exact not_entails_of_force (C := MC) w hb ha hh.2

/-! ### Eight pairwise-inequivalent closed lax formulas -/

def bot : PLLFormula := falsePLL
def Ob : PLLFormula := bot.somehow                  -- ◯⊥
def neg (x : PLLFormula) : PLLFormula := x.ifThen bot

/-- No propositional atoms occur (the formula is *closed*). -/
def atomFree : PLLFormula → Bool
  | .prop _ => false
  | .falsePLL => true
  | .and a b => atomFree a && atomFree b
  | .or a b => atomFree a && atomFree b
  | .ifThen a b => atomFree a && atomFree b
  | .somehow a => atomFree a

/-- The eight closed witnesses, each with a distinct `MC`-forcing pattern. -/
def witnesses : List PLLFormula :=
  [ bot,                                 -- ⊥
    Ob,                                  -- ◯⊥
    neg Ob,                              -- ¬◯⊥
    neg (neg Ob),                        -- ¬¬◯⊥
    (neg Ob).somehow,                    -- ◯(¬◯⊥)   ← the genuinely new element
    (neg (neg Ob)).ifThen Ob,            -- ¬¬◯⊥ ⊃ ◯⊥
    (neg Ob).or (neg (neg Ob)),          -- ¬◯⊥ ∨ ¬¬◯⊥
    neg bot ]                            -- ⊤

/-- All witnesses are closed (atom-free). -/
theorem witnesses_atomFree : witnesses.all atomFree = true := by decide

/-- **Eight pairwise ⊣⊢-inequivalent closed lax formulas.**  The closed lax
fragment RN(◯,{}) therefore has at least eight elements, and `◯(¬◯⊥)` is a new
closed element beyond `{⊥, ◯⊥, ¬◯⊥, ¬¬◯⊥, ¬¬◯⊥⊃◯⊥, ¬◯⊥∨¬¬◯⊥, ⊤}`. -/
theorem closed_lax_ge_eight : witnesses.Pairwise NotEquiv := by
  have h : witnesses.Pairwise Ineq := by decide
  exact h.imp (fun hab => ineq_imp_notEquiv hab)

/-- `◯(¬◯⊥)` is inequivalent to each of the seven other closed witnesses. -/
theorem somehow_neg_box_new :
    ∀ ψ ∈ [bot, Ob, neg Ob, neg (neg Ob), (neg (neg Ob)).ifThen Ob,
            (neg Ob).or (neg (neg Ob)), neg bot],
      NotEquiv ((neg Ob).somehow) ψ := by
  intro ψ hψ
  fin_cases hψ <;> exact ineq_imp_notEquiv (by decide)

/-! ### Strict ascending chains give an infinite Lindenbaum quotient

The reusable engine: any `ℕ`-indexed family of closed formulas that forms a
STRICT ascending chain in the entailment order yields infinitely many
`⊣⊢`-inequivalence classes.  This reduces "infinitely many closed classes" to
"consecutive separation" (`Le (e n) (e (n+1))` and `¬ Le (e (n+1)) (e n)`);
transitivity does the rest.  Nothing here needs an explicit model — only the
soundness/completeness bridge `consequence_iff_derivable`. -/

/-- The Lindenbaum (entailment) preorder, stated semantically: `a ⊢ b` holds at
every world of every constraint model.  By soundness+completeness this is exactly
single-hypothesis derivability (`le_iff_nonempty`). -/
def Le (a b : PLLFormula) : Prop :=
  ∀ (M : ConstraintModel) (w : M.W), M.force w a → M.force w b

theorem Le.refl (a : PLLFormula) : Le a a := fun _ _ h => h

theorem Le.trans {a b c : PLLFormula} (h₁ : Le a b) (h₂ : Le b c) : Le a c :=
  fun M w h => h₂ M w (h₁ M w h)

/-- `Le` coincides with single-hypothesis derivability. -/
theorem le_iff_nonempty {a b : PLLFormula} : Le a b ↔ Nonempty (LaxND [a] b) := by
  rw [← consequence_iff_derivable]
  constructor
  · intro h M w hΓ; exact h M w (hΓ a (List.mem_cons_self ..))
  · intro h M w ha
    exact h M w (fun ψ hψ => by rw [List.mem_singleton.mp hψ]; exact ha)

/-- Forward steps compose: `i ≤ j → Le (e i) (e j)`. -/
theorem le_mono {e : ℕ → PLLFormula} (hfwd : ∀ n, Le (e n) (e (n+1))) :
    ∀ {i j : ℕ}, i ≤ j → Le (e i) (e j) := by
  intro i j hij
  induction hij with
  | refl => exact Le.refl _
  | step _ ih => exact Le.trans ih (hfwd _)

/-- In a strict chain the order is never reversed across a gap. -/
theorem no_reverse {e : ℕ → PLLFormula} (hfwd : ∀ n, Le (e n) (e (n+1)))
    (hsep : ∀ n, ¬ Le (e (n+1)) (e n)) :
    ∀ {i j : ℕ}, i < j → ¬ Le (e j) (e i) := by
  intro i j hij hrev
  exact hsep i (Le.trans (le_mono hfwd hij) hrev)

/-- A strict ascending chain is pairwise `⊣⊢`-inequivalent. -/
theorem chain_notEquiv {e : ℕ → PLLFormula} (hfwd : ∀ n, Le (e n) (e (n+1)))
    (hsep : ∀ n, ¬ Le (e (n+1)) (e n)) :
    ∀ {i j : ℕ}, i ≠ j → NotEquiv (e i) (e j) := by
  intro i j hne hpair
  rcases Nat.lt_or_ge i j with h | h
  · exact no_reverse hfwd hsep h (le_iff_nonempty.mpr hpair.2)
  · exact no_reverse hfwd hsep (lt_of_le_of_ne h (Ne.symm hne))
      (le_iff_nonempty.mpr hpair.1)

/-! ### The closed-fragment Lindenbaum quotient -/

/-- `⊣⊢`-equivalence, stated via `Le`. -/
def LaxEquiv (a b : PLLFormula) : Prop := Le a b ∧ Le b a

/-- The carrier: closed (atom-free) `PLL` formulas. -/
def Closed := {φ : PLLFormula // atomFree φ = true}

/-- The `⊣⊢` setoid on closed formulas. -/
instance closedSetoid : Setoid Closed where
  r x y := LaxEquiv x.1 y.1
  iseqv :=
    ⟨fun x => ⟨Le.refl x.1, Le.refl x.1⟩,
     fun h => ⟨h.2, h.1⟩,
     fun h₁ h₂ => ⟨Le.trans h₁.1 h₂.1, Le.trans h₂.2 h₁.2⟩⟩

/-- `NotEquiv` is exactly failure of `LaxEquiv`. -/
theorem notEquiv_iff {a b : PLLFormula} : NotEquiv a b ↔ ¬ LaxEquiv a b := by
  unfold NotEquiv LaxEquiv
  rw [le_iff_nonempty, le_iff_nonempty]

/-- **The engine.**  A strict ascending chain of closed formulas gives infinitely
many `⊣⊢`-inequivalence classes: the closed-fragment Lindenbaum quotient is
`Infinite`. -/
theorem infinite_of_strict_chain (e : ℕ → PLLFormula)
    (hAF : ∀ n, atomFree (e n) = true)
    (hfwd : ∀ n, Le (e n) (e (n+1)))
    (hsep : ∀ n, ¬ Le (e (n+1)) (e n)) :
    Infinite (Quotient closedSetoid) := by
  refine Infinite.of_injective (fun n => Quotient.mk closedSetoid ⟨e n, hAF n⟩) ?_
  intro i j hij
  by_contra hne
  have hEq : LaxEquiv (e i) (e j) := Quotient.exact hij
  exact (notEquiv_iff.mp (chain_notEquiv hfwd hsep hne)) hEq

/-! ### A disjunctive ladder: the forward direction is free

Package the family as a *disjunctive* ladder `L 0 = r 0`, `L (n+1) = L n ∨ r (n+1)`.
Every forward step is then a weakening (`orIntro₁`), so `hfwd` is discharged
unconditionally.  The *entire* remaining content — the actual infinitude — is
whether each new rung `r (n+1)` STRICTLY ESCAPES the running join; after the
`◯⊥`-embedding below this is reduced to the `◯`-free residual `ipc_escaping`. -/

/-- The disjunctive ladder over a rung family. -/
def disjLadder (r : ℕ → PLLFormula) : ℕ → PLLFormula
  | 0 => r 0
  | (n+1) => (disjLadder r n).or (r (n+1))

/-- A disjunctive ladder of closed rungs is closed. -/
theorem disjLadder_atomFree {r : ℕ → PLLFormula} (hr : ∀ n, atomFree (r n) = true)
    (n : ℕ) : atomFree (disjLadder r n) = true := by
  induction n with
  | zero => exact hr 0
  | succ k ih =>
      show atomFree ((disjLadder r k).or (r (k+1))) = true
      simp only [atomFree, Bool.and_eq_true]
      exact ⟨ih, hr (k+1)⟩

/-- **Forward entailment is free** for a disjunctive ladder: each step is an
`∨`-introduction, valid in every model. -/
theorem disjLadder_fwd (r : ℕ → PLLFormula) (n : ℕ) :
    Le (disjLadder r n) (disjLadder r (n+1)) := by
  intro M w h; exact Or.inl h

/-! ### The embedding: `◯⊥` is a free Heyting generator

Mechanises the previous run's key claim.  A *base* IPC constraint model `P`
(empty `F`, valuation constant `= U := P.V "p"`) is lifted to `P⁺` by adjoining a
single fallible top `f`; then `◯⊥` is realised exactly as `U`, and forcing of the
substitution `subOb γ` (`p ↦ ◯⊥`) in `P⁺` matches base forcing of `γ` for every
IPC `γ` (`force_subOb`).  So every IPC separation transports to a *closed* lax
separation — reducing the escaping-rungs residual to the `◯`-free infinitude of
RN({p}).  All of this is `sorry`-free (`force_subOb` uses only `propext`). -/

/-- Replace every atom by the free generator `◯⊥`. -/
def subOb : PLLFormula → PLLFormula
  | .prop _ => Ob
  | .falsePLL => .falsePLL
  | .and a b => .and (subOb a) (subOb b)
  | .or a b => .or (subOb a) (subOb b)
  | .ifThen a b => .ifThen (subOb a) (subOb b)
  | .somehow a => .somehow (subOb a)

theorem subOb_atomFree : ∀ γ, atomFree (subOb γ) = true
  | .prop _ => rfl
  | .falsePLL => rfl
  | .and a b => by
      simp only [subOb, atomFree, Bool.and_eq_true]; exact ⟨subOb_atomFree a, subOb_atomFree b⟩
  | .or a b => by
      simp only [subOb, atomFree, Bool.and_eq_true]; exact ⟨subOb_atomFree a, subOb_atomFree b⟩
  | .ifThen a b => by
      simp only [subOb, atomFree, Bool.and_eq_true]; exact ⟨subOb_atomFree a, subOb_atomFree b⟩
  | .somehow a => by simp only [subOb, atomFree]; exact subOb_atomFree a

/-- Lifted intuitionistic accessibility: base `Ri`, and the new top `f = none`
above everything. -/
def liftRi (P : ConstraintModel) : Option P.W → Option P.W → Prop
  | some w, some v => P.Ri w v
  | some _, none => True
  | none, none => True
  | none, some _ => False

/-- Lifted modal accessibility: diagonal on the base, plus `u ⤳ f` exactly for
`u ∈ U := P.V "p"` — this is what makes `◯⊥` realise `U`. -/
def liftRm (P : ConstraintModel) : Option P.W → Option P.W → Prop
  | some w, some v => w = v
  | some u, none => u ∈ P.V "p"
  | none, none => True
  | none, some _ => False

/-- The lift `P⁺`: adjoin one fallible top `f = none` to the base `P`. -/
def lift (P : ConstraintModel) : ConstraintModel where
  W := Option P.W
  Ri := liftRi P
  Rm := liftRm P
  F := {x | x = none}
  V a x := match x with | some w => w ∈ P.V a | none => True
  refl_i x := by cases x with | none => exact trivial | some w => exact P.refl_i w
  trans_i {x y z} h h' := by
    cases x <;> cases y <;> cases z <;> simp_all [liftRi] <;>
      first | trivial | exact P.trans_i h h'
  refl_m x := by cases x with | none => exact trivial | some w => rfl
  trans_m {x y z} h h' := by
    cases x <;> cases y <;> cases z <;> simp_all [liftRm]
  sub_mi {x y} h := by
    cases x <;> cases y <;> simp_all [liftRi, liftRm]
    exact P.refl_i _
  hered_F {x y} h hw := by cases x <;> cases y <;> simp_all [liftRi]
  hered_V {a x y} h hw := by
    cases x with
    | some w => cases y with
      | some v => exact P.hered_V h hw
      | none => trivial
    | none => cases y with
      | some v => simp [liftRi] at h
      | none => trivial
  full_F {a x} hw := by cases x with | none => trivial | some w => simp_all

/-- `◯⊥` is forced at `some w` iff `w ∈ U` (`U := P.V "p"`, an upset by heredity). -/
theorem force_Ob (P : ConstraintModel) (w : P.W) :
    (lift P).force (some w) Ob ↔ w ∈ P.V "p" := by
  constructor
  · intro h
    obtain ⟨u, hmu, hfu⟩ := h (some w) (P.refl_i w)
    cases u with
    | none => exact hmu
    | some u' => exact absurd (show some u' = none from hfu) (Option.some_ne_none u')
  · intro hw v hv
    cases v with
    | none => exact ⟨none, trivial, rfl⟩
    | some v' => exact ⟨none, P.hered_V (a := "p") hv hw, rfl⟩

/-- **Embedding congruence.**  For IPC `γ`, forcing of `subOb γ` at `some w` in the
lift matches base forcing of `γ` at `w` — provided the base has empty `F` and
constant valuation.  (`◯⊥` behaves as a free generator.) -/
theorem force_subOb (P : ConstraintModel)
    (hF : ∀ w, w ∉ P.F) (hV : ∀ a w, w ∈ P.V a ↔ w ∈ P.V "p") :
    ∀ (γ : PLLFormula), isIPL γ → ∀ w : P.W,
      ((lift P).force (some w) (subOb γ) ↔ P.force w γ) := by
  intro γ
  induction γ with
  | prop a =>
      intro _ w
      calc (lift P).force (some w) (subOb (.prop a))
          ↔ w ∈ P.V "p" := force_Ob P w
        _ ↔ w ∈ P.V a := (hV a w).symm
        _ ↔ P.force w (.prop a) := Iff.rfl
  | falsePLL =>
      intro _ w
      exact ⟨fun h => by simp [lift, subOb, ConstraintModel.force] at h, fun h => absurd h (hF w)⟩
  | and a b iha ihb =>
      intro hip w; simp only [subOb, ConstraintModel.force]; rw [iha hip.1 w, ihb hip.2 w]
  | or a b iha ihb =>
      intro hip w; simp only [subOb, ConstraintModel.force]; rw [iha hip.1 w, ihb hip.2 w]
  | ifThen a b iha ihb =>
      intro hip w
      simp only [subOb, ConstraintModel.force]
      constructor
      · intro h v hv hva
        exact (ihb hip.2 v).mp (h (some v) hv ((iha hip.1 v).mpr hva))
      · intro h v hv hlva
        cases v with
        | none => exact ConstraintModel.force_of_fallible (lift P) rfl
        | some v' => exact (ihb hip.2 v').mpr (h v' hv ((iha hip.1 v').mp hlva))
  | somehow a _ => intro hip _; exact absurd hip (by simp [isIPL])

/-- The disjunctive ladder preserves `isIPL`. -/
theorem disjLadder_isIPL {ρ : ℕ → PLLFormula} (h : ∀ n, isIPL (ρ n)) :
    ∀ n, isIPL (disjLadder ρ n)
  | 0 => h 0
  | (n+1) => ⟨disjLadder_isIPL h n, h (n+1)⟩

/-- `subOb` commutes with the disjunctive ladder. -/
theorem subOb_disjLadder (ρ : ℕ → PLLFormula) :
    ∀ n, disjLadder (fun k => subOb (ρ k)) n = subOb (disjLadder ρ n)
  | 0 => rfl
  | (n+1) => by simp only [disjLadder, subOb]; rw [subOb_disjLadder ρ n]

/-- IPC separation in a base model ⇒ `Le`-failure of the `subOb`-images. -/
theorem not_Le_subOb {γ δ : PLLFormula} (hδ : isIPL δ) (hγ : isIPL γ)
    (P : ConstraintModel) (hF : ∀ w, w ∉ P.F) (hV : ∀ a w, w ∈ P.V a ↔ w ∈ P.V "p")
    (w : P.W) (hd : P.force w δ) (hg : ¬ P.force w γ) :
    ¬ Le (subOb δ) (subOb γ) := by
  intro hle
  apply hg
  have h1 : (lift P).force (some w) (subOb δ) := (force_subOb P hF hV δ hδ w).mpr hd
  exact (force_subOb P hF hV γ hγ w).mp (hle (lift P) (some w) h1)

/-! ### The sole residual: infinitude of one-variable IPC (no `◯`)

After the embedding, the *entire* residual is `◯`-free: an IPC disjunctive ladder
whose every rung strictly escapes the running join, witnessed by base IPC models.
This is exactly the classical infinitude of the one-generated free Heyting algebra
RN({p}) (the Rieger–Nishimura lattice).  It cannot be met by a *single* finite
model — every finite model caps the fragment (checked: ≤ 9 classes for all
height-≤ 8 combs) — so a sound proof needs the unbounded Rieger–Nishimura frame
family + adequacy induction (the crux the mission flags).

**This is now discharged, `sorry`-free.**  `rnModel` is a clean `ℕ`-presentation of
de Jongh's one-variable universal model — the order `w ⊑ v :⟺ v = w ∨ v + 1 < w`,
generator `p` at the single top world `0`.  On it the Rieger–Nishimura ladder
`sLad` (`s₀ = p`, `s₁ = p ∨ ¬p`, `sₙ₊₂ = sₙ₊₁ ∨ (sₙ₊₁ ⊃ sₙ)`) is forced *exactly*
on the initial segment `{0, …, n}` (`rn_staircase`, a two-step induction), so each
`sₙ₊₁` escapes `sₙ` at world `n + 1`.  The rungs `rhoLad` are chosen so that
`disjLadder rhoLad n = sLad n` (`rn_disj_eq`), packaging the ladder as the required
disjunctive ladder. -/
/-- The Rieger–Nishimura staircase order on `ℕ`: `w ⊑ v` iff `v = w ∨ v + 1 < w`.
World `w` sees every world `< w` except `w - 1`, plus itself; worlds `0, 1` are the
two maximal points.  (A clean `ℕ`-presentation of de Jongh's one-variable universal
model.) -/
def rnLe (x y : ℕ) : Prop := y = x ∨ y + 1 < x

/-- The staircase constraint model.  Carrier `ℕ`, `Rᵢ = rnLe`, `Rₘ` the diagonal
(the fragment is `◯`-free), no fallible worlds, generator realised at the single top
world `0` (`V a = {0}` for *every* atom, so the valuation is constant). -/
@[reducible] def rnModel : ConstraintModel where
  W := ℕ
  Ri := rnLe
  Rm := (· = ·)
  F := ∅
  V _ := {x | x = 0}
  refl_i _ := Or.inl rfl
  trans_i {x y z} h1 h2 := by simp only [rnLe] at *; omega
  refl_m _ := rfl
  trans_m {x y z} h1 h2 := h1.trans h2
  sub_mi {x y} h := Or.inl h.symm
  hered_F {x y} _ hw := absurd hw (Set.notMem_empty x)
  hered_V {a x y} h hw := by
    simp only [Set.mem_setOf_eq] at *; simp only [rnLe] at h; omega
  full_F {a x} hw := absurd hw (Set.notMem_empty x)

/-- The Rieger–Nishimura ladder over one variable `p`:
`s₀ = p`, `s₁ = p ∨ ¬p`, `sₙ₊₂ = sₙ₊₁ ∨ (sₙ₊₁ ⊃ sₙ)`. -/
def sLad : ℕ → PLLFormula
  | 0 => prop "p"
  | 1 => (prop "p").or ((prop "p").ifThen falsePLL)
  | (n+2) => (sLad (n+1)).or ((sLad (n+1)).ifThen (sLad n))

/-- The disjunctive-ladder *rungs* whose running join is `sLad`:
`ρ₀ = p`, `ρ₁ = ¬p`, `ρₙ₊₂ = sₙ₊₁ ⊃ sₙ`.  Then `disjLadder rhoLad n = sLad n`. -/
def rhoLad : ℕ → PLLFormula
  | 0 => prop "p"
  | 1 => (prop "p").ifThen falsePLL
  | (n+2) => (sLad (n+1)).ifThen (sLad n)

theorem rn_force_prop (a : String) (w : ℕ) : rnModel.force w (prop a) ↔ w = 0 := Iff.rfl
theorem rn_force_bot (w : ℕ) : rnModel.force w falsePLL ↔ False :=
  ⟨fun h => absurd h (Set.notMem_empty w), False.elim⟩
theorem rn_force_or (w : ℕ) (a b : PLLFormula) :
    rnModel.force w (a.or b) ↔ rnModel.force w a ∨ rnModel.force w b := Iff.rfl
theorem rn_force_imp (w : ℕ) (a b : PLLFormula) :
    rnModel.force w (a.ifThen b) ↔ ∀ v, rnLe w v → rnModel.force v a → rnModel.force v b := Iff.rfl
theorem rn_force_negp (w : ℕ) :
    rnModel.force w ((prop "p").ifThen falsePLL) ↔ ∀ v, rnLe w v → v ≠ 0 := by
  rw [rn_force_imp]
  constructor
  · intro h v hv hv0; exact (rn_force_bot v).mp (h v hv ((rn_force_prop "p" v).mpr hv0))
  · intro h v hv hvp; exact absurd ((rn_force_prop "p" v).mp hvp) (h v hv)

/-- **The staircase.**  `sLad n` is forced in `rnModel` exactly at the worlds `≤ n`:
each new rung reaches exactly one world deeper.  Two-step induction on `n` (the
inductive step for `sₙ₊₂ = sₙ₊₁ ∨ (sₙ₊₁ ⊃ sₙ)` uses that world `k+2` does *not* see
world `k+1`, so the fresh implication is forced there vacuously). -/
theorem rn_staircase : ∀ n, (∀ w : ℕ, rnModel.force w (sLad n) ↔ w ≤ n) ∧
                            (∀ w : ℕ, rnModel.force w (sLad (n+1)) ↔ w ≤ n+1) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun w => ?_, fun w => ?_⟩
    · show rnModel.force w (prop "p") ↔ w ≤ 0
      rw [rn_force_prop]; omega
    · show rnModel.force w ((prop "p").or ((prop "p").ifThen falsePLL)) ↔ w ≤ 1
      rw [rn_force_or, rn_force_prop, rn_force_negp]
      constructor
      · rintro (h | h)
        · omega
        · by_contra hw
          exact (h 0 (by simp only [rnLe]; omega)) rfl
      · intro hw
        rcases Nat.lt_or_ge w 1 with h | h
        · left; omega
        · right; intro v hv; simp only [rnLe] at hv; omega
  | succ k ih =>
    refine ⟨ih.2, fun w => ?_⟩
    show rnModel.force w ((sLad (k+1)).or ((sLad (k+1)).ifThen (sLad k))) ↔ w ≤ k+2
    rw [rn_force_or, rn_force_imp]
    constructor
    · rintro (h | h)
      · have := (ih.2 w).mp h; omega
      · by_contra hw
        have hvle : rnLe w (k+1) := by simp only [rnLe]; omega
        have h1 : rnModel.force (k+1) (sLad (k+1)) := (ih.2 (k+1)).mpr (le_refl _)
        have h2 : rnModel.force (k+1) (sLad k) := h (k+1) hvle h1
        have := (ih.1 (k+1)).mp h2; omega
    · intro hw
      rcases Nat.lt_or_ge w (k+2) with hlt | hge
      · left; exact (ih.2 w).mpr (by omega)
      · have hwe : w = k+2 := by omega
        right
        intro v hv hvs
        have hvle : v ≤ k+1 := (ih.2 v).mp hvs
        have hvk : v ≤ k := by simp only [rnLe] at hv; omega
        exact (ih.1 v).mpr hvk

theorem rn_force_sLad (n w : ℕ) : rnModel.force w (sLad n) ↔ w ≤ n := (rn_staircase n).1 w

/-- `disjLadder rhoLad n` is literally `sLad n`. -/
theorem rn_disj_eq : ∀ n, disjLadder rhoLad n = sLad n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show (disjLadder rhoLad k).or (rhoLad (k+1)) = sLad (k+1)
    rw [ih]; cases k with | zero => rfl | succ m => rfl

theorem rn_sLad_isIPL : ∀ n, isIPL (sLad n) := by
  have H : ∀ n, isIPL (sLad n) ∧ isIPL (sLad (n+1)) := by
    intro n; induction n with
    | zero => exact ⟨by simp [sLad], by simp [sLad]⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show isIPL ((sLad (k+1)).or ((sLad (k+1)).ifThen (sLad k)))
      simp only [isIPL]; exact ⟨ih.2, ih.2, ih.1⟩
  exact fun n => (H n).1

theorem rn_rho_isIPL : ∀ n, isIPL (rhoLad n)
  | 0 => by simp [rhoLad]
  | 1 => by simp [rhoLad]
  | (n+2) => by
      show isIPL ((sLad (n+1)).ifThen (sLad n))
      simp only [isIPL]; exact ⟨rn_sLad_isIPL (n+1), rn_sLad_isIPL n⟩

theorem ipc_escaping :
    ∃ ρ : ℕ → PLLFormula, (∀ n, isIPL (ρ n)) ∧
      (∀ n, ∃ (P : ConstraintModel) (w : P.W),
        (∀ v, v ∉ P.F) ∧ (∀ a v, v ∈ P.V a ↔ v ∈ P.V "p") ∧
        P.force w (disjLadder ρ (n+1)) ∧ ¬ P.force w (disjLadder ρ n)) := by
  refine ⟨rhoLad, rn_rho_isIPL, fun n => ⟨rnModel, n+1, ?_, ?_, ?_, ?_⟩⟩
  · intro v; exact Set.notMem_empty v
  · intro a v; exact Iff.rfl
  · rw [rn_disj_eq]; exact (rn_force_sLad (n+1) (n+1)).mpr (le_refl _)
  · rw [rn_disj_eq, rn_force_sLad]; omega

/-- **The closed escaping rungs** — reduced, `sorry`-free, to `ipc_escaping` via the
`◯⊥`-embedding.  The rungs are `subOb ∘ ρ` for the IPC ladder `ρ`. -/
theorem exists_escaping_rungs :
    ∃ r : ℕ → PLLFormula, (∀ n, atomFree (r n) = true) ∧
      (∀ n, ¬ Le (disjLadder r (n+1)) (disjLadder r n)) := by
  obtain ⟨ρ, hIPL, hesc⟩ := ipc_escaping
  refine ⟨fun k => subOb (ρ k), fun n => subOb_atomFree _, ?_⟩
  intro n
  obtain ⟨P, w, hF, hV, hd, hg⟩ := hesc n
  rw [subOb_disjLadder ρ (n+1), subOb_disjLadder ρ n]
  exact not_Le_subOb (disjLadder_isIPL hIPL (n+1)) (disjLadder_isIPL hIPL n) P hF hV w hd hg

/-- **The closed lax fragment RN(◯,{}) is infinite.**  Its `⊣⊢`-Lindenbaum
quotient (over atom-free `PLL` formulas) has infinitely many classes.  Reduced,
sorry-free, to `exists_escaping_rungs` (the Rieger–Nishimura independence). -/
theorem closed_lax_infinite : Infinite (Quotient closedSetoid) := by
  obtain ⟨r, hAF, hesc⟩ := exists_escaping_rungs
  exact infinite_of_strict_chain (disjLadder r)
    (disjLadder_atomFree hAF) (disjLadder_fwd r) hesc

end LaxInfinite
end PLLND

-- Concrete finite result: fully mechanised, clean axioms.
-- The engine: strict ascending chain ⇒ infinite quotient.  Clean axioms.
-- Forward entailment of the disjunctive ladder: NO axioms at all.
-- The `◯⊥`-as-free-generator embedding: mechanised, only `propext`.
-- IPC-separation ⇒ closed-separation transport: only `propext`.
-- The `◯`-free residual `ipc_escaping`: proved via the infinite staircase model
-- `rnModel` + the RN ladder `sLad` (`rn_staircase`), so the whole file is now
-- `sorry`-free.  `closed_lax_infinite` depends only on the clean axiom set
-- [propext, Classical.choice, Quot.sound] — no `sorryAx`.

#print axioms PLLND.LaxInfinite.closed_lax_infinite
