/-!
# `omega` drops hypotheses of the form `P → False` — repro and fix

Found while proving `memC_imp` (`wip/rnClass.lean`, 2026-08-02): several
`omega` calls failed on states that were plainly linear.  The precise
quirk, isolated below and checked on BOTH `v4.31.0` (this repo's
toolchain) and `v4.32.1` (newest installed):

* `h : ¬ (w ≤ a)`            — consumed by `omega`;
* `h : w ≤ a → False`        — the *definitionally equal* spelling is
                                **silently dropped** (the reported
                                "possible counterexample" constraint
                                list does not contain `h` at all);
* `h : w ≤ a → w ≤ 3`        — genuine implications between linear
                                atoms ARE consumed;
* implications in the GOAL    — consumed.

So `omega`'s fact collector matches the `Not` constant syntactically
and does not recognise its unfolding.  The `→ False` shape arises
naturally whenever `simp only [someDef]` unfolds a `Prop`-valued
function with a `False` branch — exactly what `memC` does on the `bot`
code.

**Fix**: normalise with `imp_false : (a → False) ↔ ¬a` first.  The
`omega!` macro below does this; the examples pin both the failure and
the fix, so a toolchain that repairs the quirk upstream will flag the
`fail_if_success` line here.
-/

/-- `omega`, after rewriting every `P → False` hypothesis to `¬P`
(which plain `omega` recognises; the unfolded spelling it drops). -/
macro "omega!" : tactic =>
  `(tactic| ((try simp only [imp_false] at *); all_goals omega))

-- The `¬` spelling: plain `omega` consumes it.
example (a w : Nat) (h : ¬ (w ≤ a)) : a + 1 ≤ w := by omega

-- The `→ False` spelling: plain `omega` FAILS (hypothesis dropped) …
example (a w : Nat) (h : w ≤ a → False) : a + 1 ≤ w := by
  fail_if_success omega
  omega!

-- … while genuine implications between atoms are fine without help.
example (a w : Nat) (h : w ≤ a → w ≤ 3) (h2 : w ≤ a) : w ≤ 3 := by omega

-- The shape that bit `memC_imp`: an unfolded `Prop` function with a
-- `False` branch, under a conjunction of guards.
example (a w : Nat) (h0 : (w + 1 ≤ a ∨ w = a + 1) → False)
    (h1 : w ≤ a + 1) : w = a ∨ w ≤ a - 1 ∨ a = 0 := by
  fail_if_success omega
  omega!
