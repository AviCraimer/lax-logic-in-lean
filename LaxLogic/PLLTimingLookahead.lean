import LaxLogic.PLLTimingRipple

/-!
# Carry-lookahead vs ripple: proof restructuring is circuit speed-up

`PLLTimingRipple.lean` shows the ripple carry has delay `n·δ` — linear in the
width, and *tight* (extraction equals the topological path).  The engineering
fix is the carry-**lookahead** adder, whose delay is `O(log n)`.  This file
mechanises the contrast and pins down what, logically, the speed-up *is*.

## The lookahead principle: an associative fold

The carry-lookahead insight (Brent–Kung and every prefix adder) is that the
block carry is the fold of the per-bit *(generate, propagate)* pairs under the
associative prefix operator

  `(g, p) ∘ (g', p') = (g ∨ (p ∧ g'), p ∧ p')`.

We abstract a `(g, p)` pair as one lax signal `◯gp` (ready when the pair is
stable) and the operator as **one reusable merge cell**

  `∘ : ◯gp ⊃ ◯gp ⊃ ◯gp`,

exactly the shape of the ripple's carry cell.  Because `∘` is associative, the
*same* group pair can be folded in *any* tree shape — and the shape is the only
thing that differs between ripple and lookahead:

* `linFold n`  — the **ripple-shaped** left fold: `∘` nested `n` deep, delay
  `n·δ` (`linReady_bound`, by induction — the same argument as
  `RippleN.ready_bound`);
* `balFold k`  — the **balanced** fold over `2ᵏ` leaves: `∘` in a perfect
  binary tree of *depth* `k`, delay `k·δ` (`balReady_bound`, by induction).

Both are proof terms of the **same sequent** `Γ ⊢ ◯gp` (`Γ = [∘, leaf]`), and
`balFold k` and `linFold (2ᵏ - 1)` use the **same `2ᵏ - 1` merge gates** — the
balanced tree merely re-associates them.  Yet:

  `lookahead_beats_ripple : balReady δ k  <  linReady δ (2ᵏ - 1)`   (`0 < δ`, `2 ≤ k`)

i.e. `k·δ < (2ᵏ - 1)·δ` — the delay drops from linear to logarithmic in the leaf
count with **no extra hardware**.  So *restructuring the derivation to reduce
its `◯`-nesting depth — re-associating the fold into a balanced tree — is the
circuit speed-up.*  Ripple is the maximally-mediated (deepest) proof of the
group carry; lookahead is a shallow proof of the very same `◯gp`.

And the two really do compute the same thing.  Run with the carry pair as the
value layer instead of the trivial one, the folds return the **same group
`(generate, propagate)` pair** for any associative merge (`balGP_eq_linGP`),
instantiated at the actual carry algebra as `lookahead_eq_ripple_gp`; one and
the same evaluation also reproduces the delay bounds (`linGP_delay`,
`balGP_delay`).  So the comparison is between two networks computing one
function at different cost: the speed-up is a re-association of the proof, not
a change in what is proved.

## Belief reading

`◯gp` is "the group carry is believed ready".  The ripple believes it through a
chain of `2ᵏ - 1` mediated inferences; the lookahead believes the *same* fact
through a depth-`k` argument over the same premises.  Evidential depth is what
`◯`'s sequential `+` charges for, and re-associating a proof of equal size into
a shallower one is exactly how the cost is cut.
-/

open PLLFormula

namespace PLLND
namespace Lookahead

/-! ## The associative merge cell and its two fold shapes -/

/-- A `(generate, propagate)` group pair, abstracted as one lax signal:
`◯gp` is ready when the pair is stable. -/
abbrev Ogp := somehow (prop "gp")

/-- The netlist: one reusable prefix-merge cell `∘ : ◯gp ⊃ ◯gp ⊃ ◯gp` and a
leaf pair `◯gp`.  Independent of how deep we fold. -/
abbrev Γ : List PLLFormula := [Ogp.ifThen (Ogp.ifThen Ogp), Ogp]

/-- **The ripple-shaped (linear) fold**: `∘` nested `n` deep to the left.  Same
shape as `RippleN.ripple`; `linFold n : Γ ⊢ ◯gp`. -/
def linFold : ℕ → Tm Γ Ogp
  | 0     => .var (.there .here)                                 -- leaf
  | n + 1 => .app (.app (.var .here) (linFold n)) (.var (.there .here))  -- ∘ (linFold n) leaf

/-- **The balanced (lookahead) fold** over `2ᵏ` leaves: `∘` in a perfect binary
tree of depth `k`.  `balFold k : Γ ⊢ ◯gp` — the *same sequent* as `linFold`. -/
def balFold : ℕ → Tm Γ Ogp
  | 0     => .var (.there .here)                                 -- leaf
  | k + 1 => .app (.app (.var .here) (balFold k)) (balFold k)    -- ∘ (balFold k) (balFold k)

/-- Curry–Howard: both folds are genuine PLL derivations of `◯gp`. -/
example (n : ℕ) : Nonempty (LaxND Γ Ogp) := ⟨(linFold n).toND⟩
example (k : ℕ) : Nonempty (LaxND Γ Ogp) := ⟨(balFold k).toND⟩

/-- The environment: merge cell delay `δ` (a 2-input gate, `σ = max`), leaf pair
ready at `0`. -/
def env (δ : ℕ) : Env (M := ℕ) B Γ :=
  (gate2 δ, ((0, ()), PUnit.unit))

/-- Extracted ready-time of the linear (ripple-shaped) fold. -/
abbrev linReady (δ n : ℕ) : ℕ := (Tm.eval (· + ·) 0 B (linFold n) (env δ)).1

/-- Extracted ready-time of the balanced (lookahead) fold. -/
abbrev balReady (δ k : ℕ) : ℕ := (Tm.eval (· + ·) 0 B (balFold k) (env δ)).1

/-! ## Linear fold: delay `n·δ` (the ripple shape again) -/

theorem linReady_zero (δ : ℕ) : linReady δ 0 = 0 := rfl

theorem linReady_succ (δ n : ℕ) : linReady δ (n + 1) = max (linReady δ n) 0 + δ := rfl

/-- The ripple-shaped fold has delay `n·δ` — linear in the fold depth. -/
theorem linReady_bound (δ n : ℕ) : linReady δ n = n * δ := by
  induction n with
  | zero => simp [linReady_zero]
  | succ n ih => rw [linReady_succ, ih, add_one_mul]; omega

/-! ## Balanced fold: delay `k·δ` (logarithmic in the leaf count) -/

theorem balReady_zero (δ : ℕ) : balReady δ 0 = 0 := rfl

/-- Each level of the balanced tree merges two identical subtrees — `σ = max`
of equal ready-times — and pays one cell delay: `balₖ₊₁ = max balₖ balₖ + δ`. -/
theorem balReady_succ (δ k : ℕ) :
    balReady δ (k + 1) = max (balReady δ k) (balReady δ k) + δ := rfl

/-- **The balanced fold has delay `k·δ`** — depth `k` over `2ᵏ` leaves, so
logarithmic in the leaf count.  By induction on the depth. -/
theorem balReady_bound (δ k : ℕ) : balReady δ k = k * δ := by
  induction k with
  | zero => simp [balReady_zero]
  | succ k ih => rw [balReady_succ, ih, add_one_mul]; omega

/-! ## The speed-up: same gates, re-associated, exponentially less delay -/

/-- `k < 2ᵏ - 1` for `k ≥ 2`: the balanced depth is below the linear length. -/
theorem lt_two_pow_pred (k : ℕ) (hk : 2 ≤ k) : k < 2 ^ k - 1 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
      omega

/-- **Carry-lookahead beats ripple: proof restructuring is speed-up.**  The
balanced fold `balFold k` and the ripple-shaped fold `linFold (2ᵏ - 1)` derive
the *same* `◯gp` from the *same* `2ᵏ - 1` merge cells — the balanced tree only
re-associates them — yet the balanced delay `k·δ` is strictly below the linear
`(2ᵏ - 1)·δ`.  Delay is `◯`-nesting depth; the lookahead is the shallow proof. -/
theorem lookahead_beats_ripple (δ k : ℕ) (hδ : 0 < δ) (hk : 2 ≤ k) :
    balReady δ k < linReady δ (2 ^ k - 1) := by
  rw [balReady_bound, linReady_bound]
  exact mul_lt_mul_of_pos_right (lt_two_pow_pred k hk) hδ

/-! ### Concrete numbers — nominal merge delay `dMERGE = 120 ps`

The prefix merge is a generate/propagate combine of delay comparable to the
full-adder carry cell (`dMERGE = dCARRY = 120 ps`, nominal sky130; illustrative,
not sign-off STA — same discipline as `PLLTiming`). -/

/-- Nominal prefix-merge delay (ps), taken equal to the carry cell. -/
def dMERGE : ℕ := 120

/-- A 32-bit block (`2⁵` leaves) folded the **ripple** way: `31` merges in a
line, `31·120 = 3720 ps`. -/
example : linReady dMERGE (2 ^ 5 - 1) = 3720 := by rw [linReady_bound]; decide

/-- The **same** 32-bit block folded the **lookahead** way: a depth-`5` balanced
tree of the same `31` merges, `5·120 = 600 ps`. -/
example : balReady dMERGE 5 = 600 := by rw [balReady_bound]; decide

/-- The lookahead is `6.2×` faster than the ripple on a 32-bit block, using the
same hardware — kernel-checked. -/
example : balReady dMERGE 5 < linReady dMERGE (2 ^ 5 - 1) :=
  lookahead_beats_ripple dMERGE 5 (by decide) (by norm_num)

/-! ## The two folds compute the same group carry

The delay theorems above run the extractor with a *trivial* value layer
(`B = fun _ => Unit`): they see the timing and discard the data.  Nothing forces
that choice --- `Tm.eval` is parametric in the realiser layer --- so we now run
the **same two proof terms** with the carry pair itself as the value layer, and
prove the folds agree.  This is what licenses the re-association: `balFold k`
and `linFold (2ᵏ - 1)` do not merely inhabit the same sequent, they compute the
same group `(generate, propagate)` pair, so `lookahead_beats_ripple` compares
two networks computing the *same function*.  The leaf counts already match
(`2ᵏ` each); associativity of the merge does the rest, and is used exactly once
(`linGP_append`). -/

section Value
variable {A : Type}

/-- A 2-input cell carrying a delay **and** a value: the output is ready at
`max` of the inputs plus `δ`, and its value is `f` of the input values.  The
delay component is exactly `gate2`'s. -/
def gate2v {x y z : String} (δ : ℕ) (f : A → A → A) :
    sem (M := ℕ) (fun _ => A)
      ((somehow (prop x)).ifThen ((somehow (prop y)).ifThen (somehow (prop z)))) :=
  fun p q => (max p.1 q.1 + δ, f p.2 q.2)

/-- The environment with a non-trivial value layer: merge cell `f` of delay `δ`,
and a leaf pair of value `a` ready at `0`. -/
def envV (δ : ℕ) (f : A → A → A) (a : A) : Env (M := ℕ) (fun _ => A) Γ :=
  (gate2v δ f, ((0, a), PUnit.unit))

/-- The group pair computed by the ripple-shaped fold. -/
abbrev linGP (δ : ℕ) (f : A → A → A) (a : A) (n : ℕ) : A :=
  (Tm.eval (· + ·) 0 (fun _ => A) (linFold n) (envV δ f a)).2

/-- The group pair computed by the balanced (lookahead) fold. -/
abbrev balGP (δ : ℕ) (f : A → A → A) (a : A) (k : ℕ) : A :=
  (Tm.eval (· + ·) 0 (fun _ => A) (balFold k) (envV δ f a)).2

variable (δ : ℕ) (f : A → A → A) (a : A)

theorem linGP_zero : linGP δ f a 0 = a := rfl

theorem linGP_succ (n : ℕ) : linGP δ f a (n + 1) = f (linGP δ f a n) a := rfl

theorem balGP_zero : balGP δ f a 0 = a := rfl

theorem balGP_succ (k : ℕ) :
    balGP δ f a (k + 1) = f (balGP δ f a k) (balGP δ f a k) := rfl

/-- Concatenating two ripple-shaped folds gives a longer ripple-shaped fold.
**This is the only place associativity is used.** -/
theorem linGP_append (hf : ∀ x y z : A, f (f x y) z = f x (f y z)) (m n : ℕ) :
    f (linGP δ f a m) (linGP δ f a n) = linGP δ f a (m + n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h1 : linGP δ f a (n + 1) = f (linGP δ f a n) a := rfl
      have h2 : linGP δ f a (m + (n + 1) + 1) = f (linGP δ f a (m + n + 1)) a := rfl
      rw [h1, h2, ← ih]
      exact (hf _ _ _).symm

/-- **The two folds compute the same group carry.**  For *any* associative merge,
the balanced fold of depth `k` and the ripple-shaped fold of length `2ᵏ - 1` ---
which combine the same `2ᵏ` leaf pairs --- produce the same value.  Re-association
is therefore sound: the lookahead computes what the ripple computes, faster. -/
theorem balGP_eq_linGP (hf : ∀ x y z : A, f (f x y) z = f x (f y z)) (k : ℕ) :
    balGP δ f a k = linGP δ f a (2 ^ k - 1) := by
  induction k with
  | zero =>
      have h0 : (2 : ℕ) ^ 0 - 1 = 0 := by norm_num
      rw [h0]
      exact (balGP_zero δ f a).trans (linGP_zero δ f a).symm
  | succ k ih =>
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have hpos : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
      have hidx : (2 ^ k - 1) + (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by omega
      have hb : balGP δ f a (k + 1) = f (balGP δ f a k) (balGP δ f a k) := rfl
      rw [hb, ih, linGP_append δ f a hf, hidx]

/-- The value layer does not disturb the timing: the very evaluation that
produces the group pair reproduces the linear delay bound. -/
theorem linGP_delay (n : ℕ) :
    (Tm.eval (· + ·) 0 (fun _ => A) (linFold n) (envV δ f a)).1 = linReady δ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : (Tm.eval (· + ·) 0 (fun _ => A) (linFold (n + 1)) (envV δ f a)).1
             = max (Tm.eval (· + ·) 0 (fun _ => A) (linFold n) (envV δ f a)).1 0 + δ := rfl
      rw [h, ih, ← linReady_succ]

/-- Likewise for the balanced fold: one evaluation yields both the group pair
and the logarithmic delay bound. -/
theorem balGP_delay (k : ℕ) :
    (Tm.eval (· + ·) 0 (fun _ => A) (balFold k) (envV δ f a)).1 = balReady δ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h : (Tm.eval (· + ·) 0 (fun _ => A) (balFold (k + 1)) (envV δ f a)).1
             = max (Tm.eval (· + ·) 0 (fun _ => A) (balFold k) (envV δ f a)).1
                   (Tm.eval (· + ·) 0 (fun _ => A) (balFold k) (envV δ f a)).1 + δ := rfl
      rw [h, ih, ← balReady_succ]

end Value

/-! ### The concrete carry algebra -/

/-- A carry `(generate, propagate)` pair. -/
abbrev GP := Bool × Bool

/-- The carry-merge (prefix) operator
`(g, p) ∘ (g', p') = (g ∨ (p ∧ g'), p ∧ p')`. -/
def gpMerge (u v : GP) : GP := (u.1 || (u.2 && v.1), u.2 && v.2)

/-- The carry merge is associative --- the algebraic fact every prefix adder
exploits.  By case analysis on the six bits, so **axiom-free**. -/
theorem gpMerge_assoc :
    ∀ x y z : GP, gpMerge (gpMerge x y) z = gpMerge x (gpMerge y z) := by
  rintro ⟨g₁, p₁⟩ ⟨g₂, p₂⟩ ⟨g₃, p₃⟩
  cases g₁ <;> cases p₁ <;> cases g₂ <;> cases p₂ <;> cases g₃ <;> cases p₃ <;> rfl

/-- **Lookahead and ripple compute the same carry.**  At the actual carry
algebra: the depth-`k` balanced fold and the length-`2ᵏ - 1` ripple fold of the
same leaf pair produce the same group `(generate, propagate)` pair.  Together
with `lookahead_beats_ripple` --- which is strictly faster --- this says the two
networks compute the *same function* at different cost, so the speed-up is a
re-association of the proof and not a change of what is proved. -/
theorem lookahead_eq_ripple_gp (δ : ℕ) (a : GP) (k : ℕ) :
    balGP δ gpMerge a k = linGP δ gpMerge a (2 ^ k - 1) :=
  balGP_eq_linGP δ gpMerge a gpMerge_assoc k

/-! ## Axiom audits — measured and pinned on creation (2026-07-20)

The `_zero`/`_succ` recurrences are `rfl` (the extractor reads the delay off the
proof term), hence axiom-free.  The linear/balanced bounds go through
`omega`/`Nat` lemmas (`propext, Quot.sound`); the depth inequality and the
speed-up theorem use `Nat.le_induction` and ordered-algebra lemmas, so also draw
`Classical.choice` — the clean-classical tier, still sound. -/

/-- info: 'PLLND.Lookahead.linReady_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms linReady_zero

/-- info: 'PLLND.Lookahead.linReady_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms linReady_succ

/-- info: 'PLLND.Lookahead.linReady_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms linReady_bound

/-- info: 'PLLND.Lookahead.balReady_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms balReady_zero

/-- info: 'PLLND.Lookahead.balReady_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms balReady_succ

/-- info: 'PLLND.Lookahead.balReady_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms balReady_bound

/--
info: 'PLLND.Lookahead.lt_two_pow_pred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lt_two_pow_pred

/--
info: 'PLLND.Lookahead.lookahead_beats_ripple' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lookahead_beats_ripple

/-! The agreement results.  The mathematical core is axiom-free: the
re-association step (`linGP_append`), the associativity of the carry merge, and
the two delay-agreement lemmas.  Only the `2ᵏ` bookkeeping in `balGP_eq_linGP`
(and hence its instance) reaches the clean-classical tier. -/

/-- info: 'PLLND.Lookahead.linGP_append' does not depend on any axioms -/
#guard_msgs in
#print axioms linGP_append

/--
info: 'PLLND.Lookahead.balGP_eq_linGP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms balGP_eq_linGP

/-- info: 'PLLND.Lookahead.linGP_delay' does not depend on any axioms -/
#guard_msgs in
#print axioms linGP_delay

/-- info: 'PLLND.Lookahead.balGP_delay' does not depend on any axioms -/
#guard_msgs in
#print axioms balGP_delay

/-- info: 'PLLND.Lookahead.gpMerge_assoc' does not depend on any axioms -/
#guard_msgs in
#print axioms gpMerge_assoc

/--
info: 'PLLND.Lookahead.lookahead_eq_ripple_gp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lookahead_eq_ripple_gp

end Lookahead
end PLLND
