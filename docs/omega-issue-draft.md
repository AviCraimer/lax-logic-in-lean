# Draft issue for leanprover/lean4

*Prepared 2026-08-03, root cause sharpened same day. Not yet filed.
Suggested title below; body follows the lean4 bug-report template. The MWE
is self-contained (no imports, ASCII-only) and was verified with the bare
`lean` binary in an empty directory — no lake, no project, `_root_.False` —
so it is not an environment, loading, or notation artifact. The failure is
also pinned in this repo (`wip/omegaFix.lean`) with `fail_if_success`, so a
repaired toolchain will announce itself.*

---

**Title:** `omega` does not recognise `False` hypotheses — so `p → False` (the unfolding of `¬p`) and `_ ∨ False` are silently dropped

### Prerequisites

- [x] Reproduces on the latest stable release (4.32.2), bare `lean` binary,
  no imports, ASCII spellings, `_root_.False`.
- [x] Searched open and closed issues; found no report of this. Closest
  related: #3848 (`omega` recognises atoms syntactically rather than up to
  definitional equality) — same flavour, different site.
- [x] Minimised; root cause localised (see below).

### Description

`omega`'s fact collector has no case for `False`. Three user-visible
failures follow, the third being how we met it:

1. A hypothesis `h : False` does not close the goal ("No usable
   constraints found").
2. A disjunction with a `False` disjunct, e.g. `h : w ≤ a ∨ False`, is
   dropped wholesale — although a disjunction of two arithmetic atoms is
   case-split fine.
3. A hypothesis `h : p → False` — the *definition* of `¬p` — is silently
   dropped, although the spelling `h : ¬p` is consumed. Mechanism: the
   frontend (`MetaProblem.addFact` in
   `src/Lean/Elab/Tactic/Omega/Frontend.lean`) matches `Not` syntactically,
   so the unfolded spelling misses that arm; the implication arm then
   converts `p → q` to `¬p ∨ q` via `Decidable.not_or_of_imp`, which for
   `q = False` produces exactly the disjunction shape of (2), and the fact
   vanishes.

In all three cases the drop is silent: the "possible counterexample"
constraint list simply omits the hypothesis, so the failure reads as
incompleteness of the decision procedure rather than a parsing gap.

### Steps to reproduce

```lean
-- (1) a False hypothesis is not used
example (h : False) : (1 : Nat) = 2 := by omega
-- error: omega could not prove the goal: No usable constraints found. …

-- (2) a disjunction with a False disjunct is dropped …
example (a w : Nat) (h : w ≤ a ∨ False) (h2 : a + 1 ≤ w) : False := by omega
-- error: possible counterexample list contains only h2

-- … although disjunctions of arithmetic atoms are fine
example (a w : Nat) (h : w ≤ a ∨ w = a + 1) (h2 : a + 2 ≤ w) : False := by omega

-- (3) hence the definitional unfolding of ¬ is dropped …
example (a w : Nat) (h : w ≤ a → False) : a + 1 ≤ w := by omega
-- error: possible counterexample list omits h entirely

-- … although the Not spelling works
example (a w : Nat) (h : ¬ (w ≤ a)) : a + 1 ≤ w := by omega

-- and implications between atoms work (so (3) is not "implications unsupported")
example (a w : Nat) (h : w ≤ a → w ≤ 3) (h2 : w ≤ a) : w ≤ 3 := by omega
```

Sanity checks performed: the hypothesis in (3) is genuinely well-typed and
usable (`fun h hw => h hw` closes the manual version in the same file);
the behaviour is identical with ASCII `->`/`<=` and with `_root_.False`.

Error at (3):

```
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  c ≥ 0
  b ≥ 0
  b - c ≥ 0
where
 b := ↑a
 c := ↑w
```

### Expected behavior

`False` should be treated as the trivially unsatisfiable constraint: a
`False` hypothesis (or disjunct) closes that branch immediately. One arm
for `False` in the fact collector fixes all three shapes at once, since
(3) already reduces to (2) through the existing implication handling.
Failing that, an "unrecognised hypothesis" diagnostic instead of a silent
drop.

### Actual behavior

The hypothesis is ignored with no diagnostic, and the tactic fails.

### Where this bites in practice

The `p → False` spelling arises whenever `simp only [someDef]` unfolds a
`Prop`-valued function with a `False` branch. In our development
(a mechanised classification over Kripke truth sets), a membership
predicate `memC : Code → Nat → Prop` has `memC .bot w = False`, so
hypotheses `memC c t → memC d t` routinely unfold to `⋯ → False`, and a
page of `omega`-driven case analysis failed for no visible reason. Since
`Not` is *defined* as `a → False`, users have no reason to expect the two
spellings to behave differently.

Workaround we use:

```lean
macro "omega!" : tactic =>
  `(tactic| ((try simp only [imp_false] at *); all_goals omega))
```

### Versions

Reproduced identically on:

- `Lean (version 4.31.0, arm64-apple-darwin24.6.0, commit 68218e876d2a, Release)`
- `Lean (version 4.32.1, arm64-apple-darwin24.6.0, commit f054605aea4b, Release)`
- `Lean (version 4.32.2, arm64-apple-darwin24.6.0, commit f3b06c705e6c, Release)` (latest stable at time of writing)

macOS 15 (Darwin 24.6.0), Apple Silicon.

### Impact

Low severity (the workaround is a one-lemma `simp` normalisation) but
confusing to diagnose, because the failure mode is a *silent* drop: the
counterexample report looks like genuine incompleteness. Related in theme
to #3848 (`omega` matching syntactically where users expect definitional
transparency).
