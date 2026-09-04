# Lean proof lessons (for me)

*Recurring mistakes I made and how to avoid them. Written after a bad
batch-debugging session on `wip/G4conf.lean` (2026-07-21).*

## 0. The meta-lesson: work interactively, one goal at a time

The single biggest error: I wrote a ~150-line proof **blind**, then ran
`lake env lean` on the whole thing and tried to fix a dozen errors at
once. That is not how the proof gets done. The right loop:

1. Write the statement and the skeleton with `sorry` in every hole.
2. Run `lake env lean <file>` — **the error output IS the infoview**.
   `unsolved goals`, `type mismatch`, and `declaration uses sorry`
   messages show me the exact proof state at each hole.
3. Fill **one** hole. Re-run. Read the new state. Repeat.
4. Only widen scope once a case is green.

I can see and use the proof state directly (via the error/goal output,
`#check`, `#print`, `set_option pp.all true`, `trace_state`). Humans do
Lean this way through the infoview; I should too. Never batch-write a
long proof and hope.

## 1. Leverage existing theorems — only *new* content needs new proof

For an **extension** logic (base + one new rule), only the new rule
needs a new soundness/whatever case. The shared rules are already sound
**for the general model class**, hence *a fortiori* for any subclass
defined by an extra predicate. Concretely here: `MutuallyConfluent` is a
`Prop` on `ConstraintModel` (not a new structure), so every soundness
fact about arbitrary constraint models applies to confluent ones for
free. Don't re-prove the 17 shared rules; prove the 1 new one.

Corollary: before writing a proof, grep for an existing theorem that
does 90% of it (`g4c_iff_nd`, `derivU_iff_confluent_valid`,
`soundness_valid`, …) and route through it.

## 2. Metavariable pinning in closed terms

When a closed term's type is inferred *late* (e.g. a `LaxND [] φ` axiom
fed to a helper whose `φ` is implicit), any `by simp` membership
subgoals inside it run **while `φ` is still a metavariable** and fail
with goals like `⊢ ?m = B`. Fixes:

- Pin the top type: `thmU (φ := A.ifThen (B.ifThen (A.and B))) (…)`.
- Pin **eliminator** implicits the conclusion doesn't determine:
  `.andElim1 (ψ := B) …`, `.andElim2 (φ := A) …`,
  `.orElim (φ := A) (ψ := B) …`, `.impElim (φ := A) …`,
  `.laxElim (φ := A) …`. (Intro rules usually need no pin — the
  conclusion fixes both parts.)

## 3. `List.mem_cons_self` arity is toolchain-dependent

`List.mem_cons_self _ _` broke ("function expected"). Use the
arity-independent head-membership proof instead:

    List.mem_cons.mpr (.inl rfl)     -- proves  x ∈ x :: l

For tail membership: `List.mem_cons_of_mem _ h`.

## 4. `intro <indices>; induction d` leaves STALE index variables

If `d : Fam n Γ C` and I do `intro n Γ C d; induction d`, the intro'd
`Γ`, `C` stay in scope but each case gets its **own fresh** `Γ✝`, `C✝`.
Writing `have h : DerivU Γ _ := …` then pins the **stale** `Γ`, and it
mismatches `h : Γ✝.Perm …`. Options, cleanest first:

- Put the indices as **theorem binders**, not `intro`s, and let
  `induction d` generalise them.
- In each case, `rename_i Γ Δ A B …` to name the case's own variables,
  then write types explicitly.
- Or avoid naming the context entirely: infer it from a hypothesis
  (`permMem h …` yields membership in the case's `Γ`, no ascription).

Note the tension: stripping *all* ascriptions can then break inference
for things like `DerivU.rename`, whose target context is otherwise
undetermined. So prefer **`rename_i` + explicit** over blind stripping.

## 5. `induction … with | ctor h ih` hides constructor implicits

The explicit args (`h`, premises) and the IH get names; the *implicit*
binders (`Δ A B …`) become inaccessible `✝` names. Use `rename_i` (in
binder order, minus the family indices) to bring them into scope when a
case needs them by name.

## 6. Recipe that would have worked

For "soundness of base+distL":

    theorem sound {n Γ C} (d : G4hf n Γ C) : DerivU Γ C := by
      induction d with
      | init h => sorry
      | …       => sorry
      | distL h ih₁ ih₂ => sorry

Run, read the `init` goal, fill it, re-run, next case. Fill the 17
shared cases with the routine ND translation (`mp`/`cut`/`unit`/
`orElim`), and `distL` with `DerivU.dist` + `orElim`. Then
`derivU_iff_confluent_valid.mp` finishes soundness. One goal at a time.
