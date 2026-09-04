# What the belief session changed for the UI programme

2026-07-18 · written for the session reinvestigating uniform
interpolation, as a companion to `PROGRESS.md` (whose §2–3 record the
oracle and its inefficiencies as of 2026-07-15). Everything below is on
`main` and builds; audit statuses are stated per item. Nothing here
touches the mathematics of the one-variable descent — it is about the
instruments the descent work now has available.

## 1. The oracle is now two-sided

The probe's oracle discipline was one-sided: `PLLND.search` returning
`true` is kernel-grade (a genuine derivation exists), but `false` meant
only "not found within fuel" — a certified *no* needed the exponential
`decide`, in practice unusable. Two additions change this.

**Positive side, fuel-free.** `G4cTm.find` (`PLLG4Term.lean`) is
backward search for a Type-valued proof-term calculus mirroring the
repaired terminating calculus: no fuel parameter (loop-checked on
canonical keys), and success returns a *term*, checked by `G4cTm.sound`
and translatable to every other calculus in the library. It solved the
G4iLL gap sequent instantly. For the probe this replaces fuel
hand-tuning, and a returned term is a reusable certificate rather than
a transient `true`.

**Negative side, certified.** `CounterEmit.emit` (`PLLCountermodelEmit
.lean`) proposes a finite constraint countermodel from a failed search;
the verified checker `FinCM.checkB` certifies it; `not_provable_of_check`
(audits `[propext, Quot.sound]`) turns the certificate into
`¬ Nonempty (LaxND Γ C)`. A wrong proposal can only fail to certify —
the emitter is outside the trusted story. So "search returned false"
can now be upgraded, at model-emission cost, to a machine-checked
underivability theorem. `derivable_iff_no_realP_refutation`
(`PLLRealCompleteness.lean`, same audit) is the machine-checked
statement that this dichotomy is total.

Practical shape for the UI work: keep the cheap one-sided oracle in
inner loops exactly as PROGRESS.md prescribes, and spend the certified
*no* at checkpoints — in particular on candidate refutations of the two
named holes. If itpE-stabilisation (H2) fails past threshold at some
configuration, that failure is a specific underivable sequent, and
`emit` on it yields a checked countermodel: the counterexample hunt and
the proof effort now terminate in the same currency.

## 2. Countermodels are readable now

`emitMin` (checker-gated world deletion) and `emitMinClean`
(checker-gated attribute deletion) cut emitted models to minimal ones:
the 20-world ∨-distribution model becomes the three-world split model
of F&M Fig. 3 (pinned as a build-time guard), and ◯p ⊬ p becomes two
worlds. `PLLDiagram.lean` renders any `FinCM` to TikZ/SVG;
`CounterEmit.describe` prints worlds as belief states, and
`CounterEmit.profile` reports which formulas a world forces. The
one-variable interpolants live in a five-class state space
({⊥, ⊤, ◯⊥, ¬◯⊥, ◯(¬◯⊥ ⊃ ◯¬¬◯⊥)} per PROGRESS.md §1.2), so any
semantic separation among candidates will be witnessed by very small
models — and they will arrive as pictures, not 20-world blobs.

## 3. A mechanised finite canonical model, constructively

`PLLFinComp.lean` has the finitised canonical construction over a
subformula closure: decidable consistency of world-triples
(`cons_iff_check`), a computable Lindenbaum fold, the truth lemma, and
countermodel enumeration (`canonFinCM`, `emitter_completeness`), all at
`[propext, Quot.sound]`. Two uses for UI:

* **A semantic route is now attemptable.** Ghilardi-style uniform
  interpolation — bisimulation quantifiers over finite models — needs
  exactly this infrastructure: finite models over a closure, a truth
  lemma, decidable model checking. Whether the method survives the
  ∀∃ ◯-clause and fallible worlds is genuinely open; but the base camp
  is built and audited, which was not true when the syntactic route was
  chosen.
* **Refutation is complete, not just sound.** By
  `emitter_completeness`, if a candidate entailment fails at all, a
  countermodel over the relevant closure exists and the enumeration
  finds it. A refutation search that comes back empty is therefore
  evidence of a different quality than a fuel timeout. (Cost is
  exponential in the closure — checkpoint use only.)

## 4. The calculus substrate, and a caution carried over

The published terminating calculus is incomplete for PLL
(machine-checked counterexample; `docs/iemhoff-note.md`), so any
interpolant-table induction run over it inherits the gap. The repaired
retention calculus is complete, cut-admissible, and terminating, and
its decider `G4sh.dec` is computable and audits `[propext,
Quot.sound]` — probe guards over it can be `#guard`/`decide` rather
than classical. The retention rules re-expose principal formulas in
premises; that is the same phenomenon the descent bookkeeping meets as
budget-gated clauses that do not grow Γ (PROGRESS.md §1.3's honest
flag), and any termination argument for a table recursion should reuse
the repaired calculus's measure rather than the published one.

## 5. Odds and ends

* Toolchain `v4.31.0` is adopted on `main`: native evaluation is ~22×
  the old interpreter, and the segfault that dogged `laxrun` is gone.
  The X9-style deep probes are cheaper than they were when PROGRESS.md
  §2 was written.
* PROGRESS.md §2's item 4 ("the fast memoised searcher decides the
  wrong calculus") is half-answered: `G4cTm.find` decides the right
  calculus fuel-free. Porting HashMap memoisation onto it (rather than
  onto the Bool-valued search) would memoise *terms*, which compose
  across calls; still unimplemented — a task, not a result.
* Speculative, flagged as such: the evidence layer's table algebra
  (`Tbl`, `PLLEvidence.lean`) builds total lookup gadgets whose
  applications are checked at build time; interpolant tables indexed by
  sequents have the same shape, and the pattern may transfer.
* `RN(◯,∅)` is infinite (`PLLLaxInfinite.lean`, machine-checked), so
  "enumerate the p-free lattice and take the strongest consequence"
  remains closed as a route; tables-with-stabilisation and bisimulation
  quantifiers are the two live ones.
