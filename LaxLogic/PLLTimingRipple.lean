import LaxLogic.PLLTimingAdder

/-!
# The n-bit ripple-carry adder: linear carry delay, by induction

`PLLTimingAdder.lean` treats the carry-**skip** adder at a fixed width and
shows its longest topological path is a *false* path (`skip_beats_topological`:
extraction `<` topological).  This file completes the picture with the
carry-**ripple** adder at *every* width `n` — the textbook opposite case: the
carry genuinely ripples, so the longest path *is* sensitisable and extraction
is tight.

Two things come out of the parametric treatment that a fixed width cannot show.

* **The n-bit ripple is one carry cell iterated n times.**  With a single
  reusable full-adder carry hypothesis `g : ◯c ⊃ ◯p ⊃ ◯c`, the width-`n`
  carry-out proof term is literally `g` applied `n` times to the carry-in
  (`ripple`).  Its extracted delay is `n·δ`, proved by **induction on `n`**
  (`ready_bound`) — the first non-fixed-width timing theorem in the library.
  Each induction step is one carry cell: a `σ = max` merge of the previous
  carry with the propagate line, then the cell delay.  So *the critical-path
  length is the nesting depth of the carry cell in the proof term.*

* **Ripple is timing-tight; skip is not.**  For the ripple the extracted bound
  *equals* the topological longest path (`ripple_tight`, `=`); for the skip
  adder it is *strictly below* it (`skip_beats_topological`, `<`).  The two
  adders bracket the general fact that proof-term extraction is always `≤`
  topological STA, with equality exactly when the longest path is
  sensitisable.  The ripple has a unique carry path — no false path to
  discard — so extraction cannot improve on topology.

## Belief reading

`◯c` reads "the carry is believed ready, on the evidence of a settling
schedule".  The ripple adder believes its top carry only through a *chain* of
`n` mediated inferences — `◯c` from `◯c` from `…` — and the cost is additive:
`◯`'s sequential law is `+`, so mediated belief of depth `n` costs `n·δ`
(`ready_bound`).  A carry-lookahead adder proves the *same* `◯c` by a shallow,
parallel argument (depth `O(log n)`), hence a smaller delay: restructuring the
derivation to reduce `◯`-nesting depth is circuit speed-up.  The ripple is the
maximally mediated — deepest, slowest — proof of the carry-out.
-/

open PLLFormula

namespace PLLND
namespace RippleN

/-! ## The width-parametric carry chain -/

abbrev Oc := somehow (prop "c")
abbrev Op := somehow (prop "p")

/-- The netlist, **independent of the width `n`**: one reusable full-adder
carry cell `◯c ⊃ ◯p ⊃ ◯c`, the propagate line `◯p`, and the carry-in `◯c`. -/
abbrev Γ : List PLLFormula := [Oc.ifThen (Op.ifThen Oc), Op, Oc]

/-- **The n-bit ripple carry chain as a proof term**: the single carry cell
applied `n` times to the carry-in.  `ripple n : Γ ⊢ ◯c`. -/
def ripple : ℕ → Tm Γ Oc
  | 0     => .var (.there (.there .here))                                 -- carry-in
  | n + 1 => .app (.app (.var .here) (ripple n)) (.var (.there .here))    -- g (ripple n) p

/-- Curry–Howard certificate: every width is a genuine PLL derivation of the
carry-out from the carry cell, the propagate line and the carry-in. -/
example (n : ℕ) : Nonempty (LaxND Γ Oc) := ⟨(ripple n).toND⟩

/-- The environment: carry cell delay `δ` (a 2-input gate, so `σ = max`),
carry-in ready at `tc`, propagate ready at `tp`. -/
def env (δ tc tp : ℕ) : Env (M := ℕ) B Γ :=
  (gate2 δ, ((tp, ()), ((tc, ()), PUnit.unit)))

/-- The extracted ready-time of the width-`n` carry-out. -/
abbrev ready (δ tc tp n : ℕ) : ℕ :=
  (Tm.eval (· + ·) 0 B (ripple n) (env δ tc tp)).1

/-! ## Linear delay by induction -/

/-- Base: the width-`0` carry-out *is* the carry-in. -/
theorem ready_zero (δ tc tp : ℕ) : ready δ tc tp 0 = tc := rfl

/-- **The carry recurrence, read off the proof term by `rfl`.**  Each further
cell merges the previous carry with the propagate line (`σ = max`) and pays the
cell delay: `readyₙ₊₁ = max readyₙ tp + δ`. -/
theorem ready_succ (δ tc tp n : ℕ) :
    ready δ tc tp (n + 1) = max (ready δ tc tp n) tp + δ := rfl

/-- **Linear carry delay, by induction on the width.**  With carry-in and
propagate ready at `0`, the `n`-bit ripple carry-out settles at `n·δ`.  Each
induction step is one carry cell in the proof term — critical-path length is
carry-cell nesting depth. -/
theorem ready_bound (δ n : ℕ) : ready δ 0 0 n = n * δ := by
  induction n with
  | zero => simp [ready_zero]
  | succ n ih => rw [ready_succ, ih, add_one_mul]; omega

/-! ## Tightness: extraction = topological (contrast with the skip false path) -/

/-- The **topological longest carry path** of the `n`-bit ripple: the unique
chain through all `n` carry cells, `n·δ`.  There is only one carry path, so it
is trivially sensitisable. -/
def dTopoRipple (δ n : ℕ) : ℕ := n * δ

/-- **The ripple carry chain is timing-tight: extraction *equals* topological.**
Contrast `skip_beats_topological` (strict `<`): the carry-skip adder's longest
path is *false*, so extraction beats topology; the ripple's carry path is
unique and sensitisable, so extraction *matches* topology.  The two adders
bracket the general fact — extraction `≤` topological STA, equality iff the
longest path is sensitisable. -/
theorem ripple_tight (δ n : ℕ) : ready δ 0 0 n = dTopoRipple δ n :=
  ready_bound δ n

/-- **Delay is monotone (indeed linear) in the width.**  More adder bits ⟹ an
at-least-as-long carry delay — the linear blow-up that motivates carry-skip and
carry-lookahead. -/
theorem ready_mono (δ : ℕ) {n m : ℕ} (h : n ≤ m) :
    ready δ 0 0 n ≤ ready δ 0 0 m := by
  rw [ready_bound, ready_bound]; gcongr

/-! ### Concrete numbers — nominal sky130 carry delay `dCARRY = 120 ps` -/

/-- An 8-bit ripple carry settles at `960 ps` (`= 8·120`). -/
example : ready dCARRY 0 0 8 = 960 := by rw [ready_bound]; decide

/-- A 32-bit ripple carry settles at `3840 ps` (`= 32·120`) — nearly 4 ns of
pure carry propagation, the classic reason wide ripple adders are avoided. -/
example : ready dCARRY 0 0 32 = 3840 := by rw [ready_bound]; decide

/-! ## Axiom audits — measured and pinned on creation (2026-07-20)

The recurrence and base case are `rfl` (the extractor reads the delay straight
off the proof term), hence axiom-free.  The linear bound, tightness and
monotonicity go through `omega`/`gcongr`/`Nat` lemmas, so carry only
`propext, Quot.sound` — no `Classical.choice`. -/

/-- info: 'PLLND.RippleN.ready_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms ready_zero

/-- info: 'PLLND.RippleN.ready_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms ready_succ

/-- info: 'PLLND.RippleN.ready_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ready_bound

/-- info: 'PLLND.RippleN.ripple_tight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ripple_tight

/-- info: 'PLLND.RippleN.ready_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ready_mono

end RippleN
end PLLND
