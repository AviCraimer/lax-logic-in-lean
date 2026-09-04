# Proof search and countermodel search: a user's manual

*For a logician who knows PLL but not this codebase.*

This document describes one job: settling a single sequent `Γ ⊢ C` of
propositional lax logic, and turning the answer into a Lean theorem.  Every
Lean snippet below was compiled against the tree this file sits in, and every
output shown is that compilation's own.

The quickest route is §2, four commands that take a sequent and print a
verdict, the evidence for it, and a paste-ready theorem recording it.  §§3–6
describe the functions behind the commands, for use inside programs.

Modules: `LaxLogic/PLLSearchCmd.lean` (the commands),
`LaxLogic/PLLSearch.lean` (the staged procedure and the API),
`LaxLogic/PLLSearchConf.lean` (PCLL),
`LaxLogic/PLLSearchNoFall.lean` (PCLL + `¬◯⊥`), `LaxLogic/PLLG4Term.lean` (the proof
searcher), `LaxLogic/PLLCountermodelEmit.lean` (the verified countermodel
checker and the simplifier), `LaxLogic/PLLDiagram.lean` +
`LaxLogic/PLLDiagramCmd.lean` (pictures),
`LaxLogic/PLLSearchEx.lean` (worked examples).

## 0. Which command do I want?

| you want | in PLL | in PCLL |
|---|---|---|
| a verdict either way | `#search Γ ⊢ C` | see §5 |
| a countermodel | `#refute Γ ⊢ C` | **`#refuteConf Γ ⊢ C`** |
| a proof | `#search Γ ⊢ C` | §5.1: add `distF` instances, then `#search` |
| a picture of a countermodel | `#draw Γ ⊢ C to "f.svg"` | `#draw … with (RNC.confluentConfig)` |

The one trap worth stating twice: **a countermodel found by `#refute` refutes
PCLL only if it is mutually confluent**, and most of the interesting ones are
not.  Every refutation report says which case it is in, on its `scope` line.
Use `#refuteConf` whenever the claim is about PCLL — it filters by confluence
during the search, so it cannot hand you an unusable model.

---

## 1. Vocabulary

Terms used throughout, each fixed here.

**PLL.**  Fairtlough–Mendler propositional lax logic: intuitionistic
propositional logic with a modality `◯` satisfying `A ⊃ ◯A`, `◯◯A ⊃ ◯A` and
`(A ⊃ ◯B) ⊃ (◯A ⊃ ◯B)`.  In Lean: formulas are `PLLFormula`
(`.prop`, `.falsePLL`, `.and`, `.or`, `.ifThen`, `.somehow` for `◯`;
`truePLL` abbreviates `⊥ ⊃ ⊥`); derivability from a list of hypotheses is
`LaxND Γ C`.

**PCLL.**  PLL plus the distribution scheme `◯(A ∨ B) ⊃ (◯A ∨ ◯B)`.  See §5.

**PCLL + `¬◯⊥`.**  PCLL plus the single axiom `¬◯⊥` — the *infallible*
system: it is sound and complete for confluent models with no fallible
worlds.  See §6.

**Sequent.**  A pair of a hypothesis list `Γ : List PLLFormula` and a
conclusion `C : PLLFormula`, written `Γ ⊢ C`.

**G4iLL″.**  The contraction-free sequent calculus for PLL used by the
searcher (`G4c` in Lean; sixteen rules).  It repairs Iemhoff's G4iLL, which
is incomplete for PLL.  It is equivalent to `LaxND` (`G4c.equiv_nd`).

**Proof term.**  An element of the inductive type `G4cTm Γ C`: a G4iLL″
derivation carried as data rather than as a proposition.  Because it is a
Lean term, Lean's kernel typechecks it; nothing about the program that
produced it needs to be trusted.

**Constraint model.**  The Kripke semantics for PLL (`ConstraintModel`): a
set of worlds with a preorder `Rᵢ` (intuitionistic accessibility), a
sub-preorder `Rₘ ⊆ Rᵢ` (constraint accessibility), a set `F` of *fallible*
worlds, and a hereditary valuation that is total on `F`.  Forcing is the
usual intuitionistic clauses, with

- `w ⊩ ⊥` iff `w ∈ F`, and
- `w ⊩ ◯A` iff for every `v` with `Rᵢ w v` there is `u` with `Rₘ v u` and
  `u ⊩ A`.

**`FinCM`.**  A finite constraint model as concrete data:
`⟨n, ri, rm, fall, val⟩`, with worlds `0, …, n-1`, the relations as lists of
pairs (reflexive pairs implicit), `fall` the fallible worlds, `val` the true
`(world, atom)` pairs.

**Certificate.**  A piece of data whose *type* records the fact one wants,
so that accepting it is a kernel typecheck rather than an act of trust.
Two kinds appear here: a proof term `G4cTm Γ C` (positive), and a pair
`(M, w)` together with a proof of `FinCM.checkB M w Γ C = true` (negative).
`checkB` is a Boolean function that verifies `M` is a well-formed constraint
model, `w` is a world of it, every formula of `Γ` is forced at `w`, and `C`
is not.

**Witness.**  A certified countermodel as a dependent triple:
`Witness Γ C = (M : FinCM) × (w : Nat) ×' (FinCM.checkB M w Γ C = true)`.
`WitnessConf Γ C` (§5) additionally carries `RNC.confB M = true`.

**Answer, Verdict, Reason.**  `Answer Γ C` has three constructors
(`.proved t`, `.refuted M w h`, `.unknown`).  `Verdict Γ C` is the same with
the third constructor carrying a `Reason`: `budgetExhausted b`,
`closureTooBig size cap`, or `allStagesMissed`, saying which bound bit.
`Verdict.toAnswer` forgets it.  `Answer.toDecision` and `Verdict.toDecision`
convert either into a `Decision Γ C`: `Nonempty (LaxND Γ C)`,
`¬ Nonempty (LaxND Γ C)`, or `dontKnow`.

**Discover-then-pin.**  The working discipline of this repository.  Search
code is *untrusted*: it is `partial`, may be wrong, and never reduces inside
a proof.  It is used only to *discover* a certificate; the certificate is
then *pinned*: written into the file as a Lean theorem whose proof is the
certificate, rechecked by the kernel, and audited with `#print axioms`.
`Witness.snippet` and `G4cTm.snippet` emit that theorem as text, so the
pinning step is a copy rather than a transcription.

**Node budget.**  A cap on the total number of sequents the proof searcher
visits.  It is global to the whole search tree, not per branch: a failed
branch hands its remaining budget to the next alternative.  Exhausting the
budget yields "unknown", never "underivable".

**Countermodel-first.**  The staging policy of `Search.settle`: look for a
small countermodel *before* running proof search, because checking a
proposed countermodel is cheap while a failing proof search is not.

**Battery.**  The fixed list of small frames (at most four worlds) that the
countermodel stage decorates with valuations and tests.  It is deliberately
incomplete: a cheap first filter.

**Closure emitter.**  The second countermodel stage (`CounterEmit.emit`):
it builds a candidate model out of the prime deductively-closed subsets of
the subformula closure of the sequent.  It is complete over that closure but
exponential, so it is run only when the closure is small.

**Simplification.**  Deleting from a countermodel — worlds, relation pairs,
valuation pairs, fallible flags — for as long as the verified checker still
certifies what is left (`CounterEmit.simplify`).  Both stages above propose
models far larger than the refutation needs, so this is on by default
(`Config.simplify`); §3 has the details.

**Scope of a countermodel.**  Which logic it refutes.  Every finite
countermodel refutes PLL; it refutes PCLL as well exactly when it is
mutually confluent (§5).  The `scope` line of a refutation report states
which of the two, having tested `RNC.confB` on the model returned.

**Trust.**  Three theorems, and nothing else, are kernel-checked guarantees:

1. `PLLND.Search.proved_sound : G4cTm Γ C → Nonempty (LaxND Γ C)`;
2. `FinCM.not_provable_of_check : FinCM.checkB M w Γ C = true →
   ¬ Nonempty (LaxND Γ C)` (Kripke soundness);
3. for PCLL, `PLLND.RNC.not_derivU_of_checkConf` (§5).

Everything that *produces* a certificate is untrusted: the backward searcher,
the fast vector evaluator that screens candidate models, the frame decoration
enumeration, the emitter, the simplifier, the `Config.accept` filter, the
renderers and the snippet emitters.  Each is `partial` or heuristic, and
every candidate it proposes passes through `checkB` or through Lean's
typechecker before it is returned.  A bug in the search can therefore lose
answers; it cannot manufacture one.  No component uses `native_decide`, so a
pinned certificate audits as `[propext, Quot.sound]`.

Two consequences worth stating plainly.

- **A failed search proves nothing.**  A searcher returning `none` is not a
  completeness oracle.  It means only that this program did not find a
  derivation.  Underivability comes from a countermodel, never from a
  failure.
- **Search results do not reduce in the kernel.**  The searchers are
  `partial`, so `settle {} Γ C` is opaque to `rfl` and to the `decide`
  tactic.  Discovery happens at elaboration time (`#eval`, `#guard`,
  `#search`); pinning happens by writing the found certificate into the
  source.

---

## 2. Asking about a sequent: `#search`, `#refute`, `#refuteConf`, `#draw`

Four commands cover the everyday use of the toolkit.  Each takes a sequent
and prints a block: the sequent in the usual notation, the verdict, the
evidence, and Lean source for the theorem that records the finding.

`LaxLogic/PLLSearchDemo.lean` is a runnable companion to §§2–7 of this
document: open it in VS Code, put the cursor on a command, and the info view
shows that command's output.  Every example there is wrapped in
`#guard_msgs_show`, which checks the output against the docstring above it
*and* leaves it on screen — so what is *typed* and what is *printed* are
separated mechanically, the build fails if the printed text drifts, and the
file can still be stepped through.  (Plain `#guard_msgs` deletes the messages
it checks, which makes a file of `#guard_msgs`-wrapped commands show nothing
at all in the info view.  `LaxLogic/GuardMsgsShow.lean` is the fifteen-line
module that fixes that.)

### Setup

```
lake build LaxLogic           # build the library
lake env lean MyFile.lean     # elaborate a file, running its #eval and #guard
```

A file of your own needs two lines:

```lean
import LaxLogic.PLLSearchCmd
open PLLFormula PLLND PLLND.Search
```

Import `LaxLogic.PLLDiagramCmd` instead of `LaxLogic.PLLSearchCmd` to get
`#draw` (§6) as well; it re-exports everything above.

`PLLFormula` has a `Repr` instance printing `⊃`, `∧`, `∨`, `◯`, so formulas
display in the usual notation.  Each command elaborates to an `#eval`, so its
output appears in the editor's info view, or on the console under
`lake env lean`.

### `#search Γ ⊢ C`

`#search` runs the two-sided procedure: it looks for a countermodel and for a
proof, and reports whichever it finds.

```lean
def unitSeq : PLLFormula := (prop "p").ifThen (prop "p").somehow

#search [] ⊢ unitSeq
```

```
sequent  ⊢ p ⊃ (◯p)
verdict  PROVED   (→R (◯R init))

proof term (G4iLL″):
  (→R (◯R init))

pin it:
theorem found :
    Nonempty (LaxND [] ((PLLFormula.prop "p").ifThen ((PLLFormula.prop "p").somehow))) :=
  PLLND.Search.proved_sound
    (.impR (.laxR (.init (by decide))))

#print axioms found
```

The verdict is one of three words.  `PROVED` is followed by the G4iLL″ rule
tree that was found; `REFUTED` by a one-line description of the countermodel;
`UNKNOWN` by the reason, which names the parameter to change (§3).  The block
under `pin it:` is Lean source, discussed below.

### `#refute Γ ⊢ C`

`#refute` runs the countermodel engines only, skipping proof search.  Use it
when you expect the sequent to be underivable: a failing proof search is the
expensive case, and there is nothing to gain by running it.

```lean
def escSeq : PLLFormula := ((prop "p").somehow).ifThen (prop "p")

#refute [] ⊢ escSeq
```

```
sequent  ⊢ (◯p) ⊃ p
verdict  REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 0
scope    PLL and PCLL: the model is mutually confluent, so it also
         refutes ConfluentU.DerivU (RNC.not_derivU_of_checkConf)

countermodel:
2 worlds, refuting world 0
  *w0  ⊑> {1}  ⊳ {1}  ⊩ —
   w1  ⊑> {}   ⊳ {}   ⊩ p

pin it:
theorem underivable :
    ¬ Nonempty (LaxND [] (((PLLFormula.prop "p").somehow).ifThen (PLLFormula.prop "p"))) :=
  FinCM.not_provable_of_check
    (M := ⟨2, [(0, 1)], [(0, 1)], [], [(1, "p")]⟩) (w := 0) (by decide)

#print axioms underivable
```

When nothing is found the command prints `NO COUNTERMODEL FOUND`.  That is an
absence of information rather than a claim: both negative engines are
incomplete, so the sequent may well be underivable all the same.

### The scope line

Between the verdict and the model, every refutation report says how far the
model reaches:

```
scope    PLL and PCLL: the model is mutually confluent, so it also
         refutes ConfluentU.DerivU (RNC.not_derivU_of_checkConf)
```

or

```
scope    PLL only: the model is NOT mutually confluent, so it refutes
         LaxND and says nothing about PCLL — use #refuteConf there
```

This is `RNC.confB` run on the model that was returned, not a guess.  The
distinction is invisible in the picture and costs nothing to state, and using
a non-confluent model against a PCLL claim is simply a wrong proof; §5 is the
long version.

### Reading the model picture

One line per world:

- `*` marks the refuting world;
- `⊑>` lists the **cover** successors of `Rᵢ`, that is the transitive
  reduction, so an edge implied by two others is not repeated;
- `⊳` lists the `Rₘ` successors;
- `⊩` lists the atoms forced there, `—` if none, or `⊥ (fallible)` for a
  fallible world, which forces everything.

So the model above has a root `w0` forcing no atom, above it a world `w1`
forcing `p`, and `Rₘ` carrying `w0` to `w1`.  The two `Rᵢ`-successors of `w0`
are `w0` and `w1`, and each reaches `w1` by `Rₘ`, where `p` holds — so
`w0 ⊩ ◯p`; but `w0 ⊮ p`.

What is printed is the *simplified* model (§3): the battery's own proposal
here had a fallible ceiling instead of a `p`-world, and a fallible world
forces everything, which is a distracting thing to have to reason past when a
single atom does the job.

### `#refuteConf Γ ⊢ C`

`#refuteConf` is the PCLL version of `#refute`.  A finite countermodel
refutes PCLL only if it is *mutually confluent*, so this command accepts only
confluent models and prints a theorem about PCLL derivability
(`ConfluentU.DerivU`) rather than about `LaxND`.  §5 gives the details.

```lean
#refuteConf [(prop "p").somehow] ⊢ (prop "p")
```

```
sequent  ◯p ⊢ p  (PCLL)
verdict  REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 0
scope    PLL and PCLL: the model is mutually confluent, so it also
         refutes ConfluentU.DerivU (RNC.not_derivU_of_checkConf)

countermodel:
2 worlds, refuting world 0
  *w0  ⊑> {1}  ⊳ {1}  ⊩ —
   w1  ⊑> {}   ⊳ {}   ⊩ p

pin it:
theorem underivable_pcll :
    ¬ ConfluentU.DerivU [((PLLFormula.prop "p").somehow)] (PLLFormula.prop "p") :=
  PLLND.RNC.not_derivU_of_checkConf
    (M := ⟨2, [(0, 1)], [(0, 1)], [], [(1, "p")]⟩) (w := 0) (by decide) (by decide)

#print axioms underivable_pcll
```

### Pinning what was found

The block under `pin it:` is ordinary Lean source.  Paste it into your file
and rename the theorem; the kernel rechecks it, and the `#print axioms` line
that comes with it reports the audit.  Nothing of the search survives the
paste: a pinned positive theorem contains only a proof term, and a pinned
negative theorem only the model.

```lean
theorem unit_derivable :
    Nonempty (LaxND [] ((PLLFormula.prop "p").ifThen ((PLLFormula.prop "p").somehow))) :=
  PLLND.Search.proved_sound
    (.impR (.laxR (.init (by decide))))

#print axioms unit_derivable
-- 'unit_derivable' depends on axioms: [propext, Quot.sound]

theorem esc_underivable :
    ¬ Nonempty (LaxND [] (((PLLFormula.prop "p").somehow).ifThen (PLLFormula.prop "p"))) :=
  FinCM.not_provable_of_check
    (M := ⟨2, [(0, 1)], [(0, 1)], [], [(1, "p")]⟩) (w := 0) (by decide)

#print axioms esc_underivable
-- 'esc_underivable' depends on axioms: [propext, Quot.sound]
```

The `by decide` in the negative theorem is a kernel evaluation of `checkB` on
concrete data, and the `by decide`s in the positive one discharge
list-membership side conditions of the rules.  `by simp` would also discharge
those, but it pulls `Classical.choice` into the theorem's axiom set, so the
emitted snippets use `by decide`.

### Changing the search parameters

Each command accepts a configuration after `with`:

```lean
#search [] ⊢ unitSeq with { findBudget := none }
```

Without one, the commands run `Search.budgetedConfig`, which caps proof
search at 200000 visited sequents.  §3 lists the other fields.

---

## 3. The functions behind the commands

The commands display what the API returns.  In a program one calls the API
directly, most often to sweep a family of sequents.

### The staged procedure

`Search.settle cfg Γ C : Answer Γ C` runs, in order:

1. the battery: a certified countermodel from a small frame, cheap;
2. `G4cTm.find`, giving a proof term, capped at `cfg.findBudget` when that is
   set;
3. the closure emitter, if the subformula closure is no larger than
   `cfg.emitClosureCap`;
4. `.unknown`.

A countermodel from stage 1 or 3 is simplified before it is returned, unless
`cfg.simplify` is `false`.

`Search.settleWhy` is the same procedure returning `Verdict Γ C`, whose
`.unknown` carries the reason.

The two countermodel stages are fed a PLL-normalised copy of the sequent, cut
down by the Heyting laws for `⊥` and `⊤` together with `◯⊤ ≡ ⊤` and
`◯◯ ≡ ◯`, which makes the untrusted enumeration cheaper.  Both certificates,
and the proof term, are always about the sequent as you wrote it.

### Two argument orders

`settle`, `settleWhy` and `refute?` take the configuration first, so the
defaults must be written out as `{}`.  `verdict`, `verdictWhy`,
`countermodel` and `proof` take `Γ` and `C` first and default the
configuration; a non-default one goes in by name.

```lean
#eval (verdict [] escSeq).summary
-- "REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 0"

#eval (match settle {} [] escSeq with
       | .proved _      => "PROVED"
       | .refuted _ _ _ => "REFUTED"
       | .unknown       => "UNKNOWN")
-- "REFUTED"

#eval (verdict [] escSeq (cfg := { findBudget := none })).summary
-- "REFUTED  2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 0"
```

The two orders differ in one default.  The sequent-first wrappers and all
four commands use `Search.budgetedConfig`, which sets
`findBudget := some 200000`; `settle {} Γ C` runs with no budget at all.
Both orders simplify, since `Config.simplify` defaults to `true` either way.

`Search.countermodel Γ C` and `Search.refute? cfg Γ C` are the two orders of
the negative engines alone, returning `Option (Witness Γ C)`.  "Negative
engines alone" describes the function, not its second stage: the closure
emitter begins by running proof search itself, because building an
exponential model for a provable sequent is worse than searching for the
proof.  That search obeys `cfg.findBudget` like any other, and a budget
cutoff makes the emitter decline rather than build (`CounterEmit.emit`).
`Search.proof Γ C` and `Search.prove? Γ C` are the positive engine alone
(§4).  `Search.decide` is an alias for `settle`; under `open PLLND.Search` it
shadows `Decidable.decide`, so prefer `settle`.

### Why an answer is `unknown`

`verdictWhy` and `settleWhy` return a `Reason`, and `Reason.describe` names
the parameter to change.

```lean
#eval (verdictWhy [] unitSeq (cfg := { findBudget := some 2 })).summary
-- "UNKNOWN  positive stage truncated: the node budget of 2 ran out
--  (raise Config.findBudget, or set it to none)"

#eval (verdictWhy [] (prop "p") (cfg := { frames := [], emitClosureCap := 0 })).summary
-- "UNKNOWN  emit stage skipped: subformula closure has 2 formulas, cap is 0
--  (raise Config.emitClosureCap)"

#eval (verdictWhy [] unitSeq).reason?
-- none        -- there is a verdict, so there is no reason
```

The third reason, `allStagesMissed`, means the battery, the proof search and
the emitter all ran to completion and none produced a certificate.  Widen
`Config.frames` or `Config.comboCap`.

### Configuration

`Config` has six fields, all with defaults, so `({} : Config)` is the
standard search.

| field | default | effect |
|---|---|---|
| `frames` | `defaultFrames` | the frames the battery decorates |
| `comboCap` | `200000` | skip a frame whose decoration count exceeds this |
| `emitClosureCap` | `12` | skip the emitter above this closure size |
| `findBudget` | `none` | cap on sequents visited by proof search |
| `accept` | accept all | extra test on candidate models, before `checkB` |
| `simplify` | `true` | cut a countermodel down before returning it |

To widen the battery, prepend your own frames to `defaultFrames`.  A `Frame`
is `⟨n, ri, rm, fall⟩`: the number of worlds, the strict part of `Rᵢ`
(transitively closed), the relation `Rₘ`, and the fallible worlds.

```lean
def myCfg : Search.Config :=
  { frames := ⟨5, [(0,1),(1,2),(2,3),(3,4),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)],
                  [(0,1)], [4]⟩ :: defaultFrames }
```

A wider battery changes which sequents get an answer, not usually what the
answer looks like: a hit on a five-world frame is simplified back down to the
worlds the refutation uses, often the same two a default frame would have
given.  Pass `simplify := false` to see which frame actually fired.

`Config.accept : FinCM → Bool` is an untrusted pre-filter on candidate
models, applied before the verified gate in both refutation stages, and on
each intermediate model inside the simplifier.  PCLL sets it to `RNC.confB`
(§5).

### Budgets and cost

Successes are cheap on both sides.  A provable sequent of ordinary size costs
between a handful and a few hundred visited nodes: `⊢ p ⊃ ◯p` costs 3,
`⊢ (p ∧ ◯q) ⊃ ◯(p ∧ q)` costs 18, and the awkward
`◯((◯p ⊃ r) ⊃ ◯p), ◯p ⊃ r ⊢ r` costs 136.  The expensive case is a sequent
that is underivable *and* escapes both countermodel stages: proof search must
then exhaust its search space, which is finite but exponential.

Three families of underivable sequents against an unreachable atom, with `k`
premises, cost this many nodes:

| family | k=1 | k=2 | k=3 | k=4 | k=5 | k=6 |
|---|---:|---:|---:|---:|---:|---:|
| `◯aᵢ ⊃ b` (k of them) together with `◯cᵢ` (k of them) | 11 | 109 | 637 | 2801 | 10411 | 34693 |
| chained `◯aᵢ ⊃ ◯aᵢ₊₁` together with `◯a₀` | 34 | 596 | 7125 | 67608 | 544671 | >3·10⁶ |
| `(pᵢ ⊃ q) ⊃ pᵢ` (Peirce shapes) | 7 | 49 | 277 | 1345 | 5921 | 24409 |

so about ×3.3, ×9 and ×4.2 per extra premise.  The chained family takes 26
seconds at `k=5` and over three minutes at `k=6`.

Throughput is 7,000–21,000 nodes per second, falling as contexts grow, so the
default budget of 200000 nodes bounds a grinding search at roughly 10 to 30
seconds.  Lower it for sweeps; set `findBudget := none` when you are willing
to wait for a sequent that may take minutes.

### Simplifying the model

Neither proposer aims for a small model.  The battery decorates whichever
fixed frame fits first, so it returns all of that frame; the closure emitter
builds one world per prime deductively-closed subset of the subformula
closure, so a two-atom sequent gets twenty worlds and two hundred `Rᵢ` pairs.
What the refutation *uses* is usually a handful of worlds.

`Config.simplify` (on by default) closes that gap.  `CounterEmit.simplify`
alternates two greedy passes to a joint fixpoint:

- `minimise` deletes a world whenever the model without it still checks;
- `clean` deletes a fallible flag, a valuation pair or a non-reflexive
  relation pair whenever the model without it still checks.

Every deletion is gated by the *verified* `FinCM.checkB` on the original
sequent, so the result is a certificate exactly as the input was — the
simplifier is untrusted like everything else that proposes, and its output is
re-checked rather than believed.  Deletions are also gated by
`Config.accept`, which is what keeps a confluence-filtered PCLL search
confluent: mutual confluence is *not* inherited by submodels, so a simplifier
blind to it could quietly hand back a model that no longer refutes PCLL.

The effect on the `∨`-distribution countermodel, which is the standard
example because it is the one people read:

```lean
#eval (countermodel [premise] goal { simplify := false }).map (·.summary)
-- some "20 worlds, refuting world 4, |Rᵢ| = 198, |Rₘ| = 101, fallible 1"

#eval IO.println ((countermodel [premise] goal).map (·.render) |>.getD "")
-- 3 worlds, refuting world 0
--   *w0  ⊑> {1,2}  ⊳ {2}  ⊩ —
--    w1  ⊑> {}     ⊳ {}   ⊩ p
--    w2  ⊑> {}     ⊳ {}   ⊩ q
```

The three-world model is Fairtlough–Mendler Fig. 3, recovered by deletion:
the root sees a `p`-world along `Rᵢ` and reaches a `q`-world along `Rₘ`, so it
forces `◯(p ∨ q)` and neither `◯p` nor `◯q`.  The pinning snippet shrinks with
the model — from several thousand characters of pair lists to one line — which
matters, because that snippet is what gets pasted into a file and kept.

Cost is a few hundred `checkB` calls on models of this size, under a
millisecond.  Set `simplify := false` to see what a stage actually proposed:
useful when the question is about the *search*, not about the sequent.

`CounterEmit.minimise`, `clean` and `simplify` are also callable directly on
a `FinCM`, and `Witness.simplify` on a witness.

### Rendering a model

`Search.renderCM M w?` produces the picture described in §2;
`Witness.render` applies it to a witness.  `Search.summaryCM M w` and
`Witness.summary` give the one-line form.

```lean
#eval (countermodel [] escSeq).map (·.summary)
-- some "2 worlds, refuting world 0, |Rᵢ| = 1, |Rₘ| = 1, fallible 0"

#eval IO.println ((countermodel [] escSeq).map (·.render) |>.getD "")
-- 2 worlds, refuting world 0
--   *w0  ⊑> {1}  ⊳ {1}  ⊩ —
--    w1  ⊑> {}   ⊳ {}   ⊩ p
```

The renderer earns its keep on unsimplified models, which reach twenty
worlds: `repr` on such a `FinCM` prints several screens of raw pair lists.

`Witness.snippet name wit` returns the pinning theorem as a string, which is
what `#refute` prints:

```lean
#eval IO.println ((countermodel [] escSeq).map (·.snippet "esc_underivable") |>.getD "")
```

Its parts are available separately: `Search.srcOf` renders a formula as Lean
source, `srcOfCtx` a hypothesis list, `srcOfCM` a `FinCM`.

For a picture rather than text, see §6.

---

## 4. Proof terms

The positive engine is `G4cTm.find Γ C : Option (G4cTm Γ C)`, backward search
in G4iLL″ with no fuel parameter.  It always terminates: the search is
loop-checked against the canonical form of the sequent (hypotheses
deduplicated and sorted), and along any branch the context grows only by
subformulas of the end-sequent, so keys must repeat.  `Search.proof Γ C`
is the same search under the budget of `budgetedConfig`; `Search.prove?` is
the unbudgeted form.

`G4cTm.pretty` renders a found term as its rule tree, and `G4cTm.snippet` as
the pinning source.

```lean
#eval (proof [] unitSeq).map (·.pretty)
-- some "(→R (◯R init))"

#guard (proof [] unitSeq).isSome

#eval IO.println ((proof [] unitSeq).map (·.snippet "unit_derivable") |>.getD "")
-- theorem unit_derivable :
--     Nonempty (LaxND [] ((PLLFormula.prop "p").ifThen ((PLLFormula.prop "p").somehow))) :=
--   PLLND.Search.proved_sound
--     (.impR (.laxR (.init (by decide))))
--
-- #print axioms unit_derivable
```

`#guard` fails the build if the search stops finding the proof, so it is the
cheap way to keep a discovery under regression control.

### Node counts

`G4cTm.findBounded budget Γ C` returns the result paired with the *remaining*
budget.  The three readings are:

- `(some t, _)`: a proof term, as trustworthy as `find`'s;
- `(none, k+1)`: the space was exhausted with budget to spare, so this is the
  same certificate-free `none` that `find` gives;
- `(none, 0)`: the budget ran out, and nothing at all is known.  This is the
  case `Reason.budgetExhausted` reports.

Because `budget - remaining` is the number of nodes visited, `findBounded`
also serves as the profiler for choosing budgets.

```lean
#eval 100000 - (G4cTm.findBounded 100000 [] unitSeq).2
-- 3
```

`Search.prove?Bounded budget Γ C` is the same with the remainder discarded.

### Transcribing a term by hand

If you write out a rule tree yourself instead of using `snippet`, the
implicit arguments of the left rules, saying which formula of the context is
being decomposed, sometimes need to be supplied by name, as in
`.orL (A := prop "p") (B := prop "q") (by decide) …`.  The rule names printed
by `pretty` map to constructors as: `→R` `.impR`, `◯R` `.laxR`, `◯L`
`.laxL`, `∧R` `.andR`, `∨R₁/∨R₂` `.orR1/.orR2`, `∧L` `.andL`, `∨L` `.orL`,
`→Lₐₜ` `.impLProp`, `→L∧` `.impLAnd`, `→L∨` `.impLOr`, `→L→` `.impLImp`,
`→L◯` `.impLLax`, `→L◯◯` `.impLLaxLax`, `init` `.init`, `⊥L` `.botL`.

---

## 5. PCLL

PCLL is PLL plus `◯(A ∨ B) ⊃ (◯A ∨ ◯B)`.  In Lean the scheme instance is
`ConfluentU.distF A B`, and derivability is

```
DerivU Γ φ  :=  ∃ L, (every member of L is an instance of distF) ∧
                     Nonempty (LaxND (L ++ Γ) φ)
```

that is, natural deduction from `Γ` together with finitely many instances of
the scheme.  `DerivU` is sound and complete for *mutually confluent*
constraint models, those satisfying `Rₘ x w → Rᵢ x v → ∃ u, Rᵢ w u ∧ Rₘ v u`
(`derivU_iff_confluent_valid`).  Everything in this section lives in
`LaxLogic/PLLSearchConf.lean`, namespace `PLLND.RNC`.

### Proving in PCLL

Choose the distribution instances by hand, typically one per `∨`-subformula
of the sequent, search for a PLL proof of `instances ++ Γ ⊢ C`, and convert
with

```
RNC.derivU_of_proved ps : Nonempty (LaxND (ps.map distF ++ Γ) C) → DerivU Γ C
```

The conversion is valid whatever instances were used, so choosing them badly
costs a failed search and nothing else.

```lean
def premise : PLLFormula := ((prop "p").or (prop "q")).somehow
def goal    : PLLFormula := ((prop "p").somehow).or ((prop "q").somehow)
def inst    : PLLFormula := ConfluentU.distF (prop "p") (prop "q")

#eval (proof [inst, premise] goal).map (·.pretty)
-- some "(→L◯◯ (◯R (∨L (∨R₁ init) (∨R₂ init))) (∨L (∨R₁ (◯L (◯R init))) (∨R₂ (◯L (◯R init)))))"
```

Pin the PLL half from the snippet that `#search [inst, premise] ⊢ goal`
prints, then apply the bridge:

```lean
-- dist_pll is the pinned theorem, Nonempty (LaxND [inst, premise] goal).
theorem dist_pcll : ConfluentU.DerivU [premise] goal :=
  RNC.derivU_of_proved [(prop "p", prop "q")] dist_pll

#print axioms dist_pcll
-- 'dist_pcll' depends on axioms: [propext, Quot.sound]
```

### Refuting in PCLL

A `FinCM` refutes `DerivU` only if it is mutually confluent.  `RNC.confB M :
Bool` decides this, and

```
RNC.not_derivU_of_checkConf : confB M = true → FinCM.checkB M w Γ C = true →
                              ¬ ConfluentU.DerivU Γ C
```

is the certificate theorem.  Both hypotheses discharge by `decide`.

A countermodel returned by `Search.refute?` is *not* automatically a PCLL
refutation: much of `defaultFrames` happens to be mutually confluent, but not
all of it, and the emitter produces non-confluent models freely.  Rather than
test `confB` afterwards, use `RNC.refuteConf?`, `RNC.countermodelConf`, or
the `#refuteConf` command of §2.  These set `Config.accept := confB`, so
non-confluent candidates are skipped *during* the search rather than stopping
it, and they return a `RNC.WitnessConf Γ C`, which carries both facts.
`RNC.refutedU_sound` turns such a witness into `¬ ConfluentU.DerivU Γ C` in
one application, and `WitnessConf.snippet` writes the pinned theorem.

Setting `accept` also protects the *simplifier*, which matters more than it
looks.  Mutual confluence is not inherited by submodels — deleting a world
can destroy it — so a simplifier that gated only on `checkB` could take a
confluent model in and hand a non-confluent one back, still certified against
PLL and now useless against PCLL.  `Config.accept` is threaded through every
deletion, so a witness from `refuteConf?` is confluent after simplification
because each intermediate model was.  The same argument applies to any other
property you filter by, which is why `accept` is the mechanism rather than a
post-hoc test.

When the answer is about PLL only, nothing needs checking by hand either: a
report from `#refute` or `#search` names its scope explicitly (§2).

The distribution axiom itself illustrates the difference.  PLL refutes
`◯(p ∨ q) ⊢ ◯p ∨ ◯q` and PCLL proves it, so every PLL countermodel to it must
be non-confluent, and the confluence-filtered search correctly finds none.

```lean
#eval (RNC.refuteConf? {} [premise] goal).isSome   -- false
#eval (refute? {} [premise] goal).isSome           -- true
```

Pinned PCLL certificates in the house style are in `wip/rncCert.lean`
(negative) and `wip/rncCertPos.lean` (positive), and `wip/rnc_probe.lean`
holds the RNC(◯,{}) matrix.  Those files need `lake build wipshared` first.

---

## 6. Pictures

The text picture of §2 stops being a picture at about six worlds.
`LaxLogic/PLLDiagram.lean` draws a `FinCM` properly — as SVG for the screen,
as TikZ for a paper — and `LaxLogic/PLLDiagramCmd.lean` wires it to the
search as one command:

```lean
import LaxLogic.PLLDiagramCmd
open PLLFormula PLLND PLLND.Search

#draw [premise] ⊢ goal to "docs/figures/demo-ordist.svg"
```

```
sequent  ◯(p ∨ q) ⊢ (◯p) ∨ (◯q)
verdict  REFUTED  3 worlds, refuting world 0, |Rᵢ| = 5, |Rₘ| = 4, fallible 0
scope    PLL only: the model is NOT mutually confluent, so it refutes
         LaxND and says nothing about PCLL — use #refuteConf there
drawing  docs/figures/demo-ordist.svg
```

`#draw` runs the same search as `#refute` — same staging, same
simplification, same certificate, same scope line — and writes the model it
found.  Open the file in VS Code and it previews as an image.  Paths are
relative to the package root, where `lake build` elaborates.  A configuration
goes after `with`, as for the other commands; `with (RNC.confluentConfig)`
draws only mutually confluent models.

The drawing conventions:

- a **circle** per world, labelled with the atoms it forces (`∅` for none);
- a **solid arrow** for a cover step that is also in `Rₘ` (a constraint
  step), a **dashed grey arrow** for one that is `Rᵢ`-only (an information
  step, along which promises lapse);
- a **thin plain line** joining `Rᵢ`-equivalent worlds;
- a **dark disc** for a fallible world, and a **red ring** on the refuting
  world.

Same transitive reduction and same `Rₘ` reading as `renderCM`, so the picture
and the text never disagree.

Below the command are the pieces, for a figure that wants curating:

| function | gives |
|---|---|
| `Diagram.svgOf M w?` | SVG string, automatic layout, labels from the valuation |
| `Diagram.tikzOf M w?` | the same drawing as TikZ, for a paper |
| `Diagram.writeSvg path M w?` | `svgOf`, written to a file |
| `Diagram.toSvg M pos labels refut w h` | full control: your own layout, labels and canvas |
| `Diagram.toTikz M pos labels refut` | the same, in TikZ |
| `Diagram.autoPos M` | the layered layout `svgOf` uses, as a `Nat → Int × Int` |

The committed paper figures (`docs/figures/demoM`, `obsM`, `ordist20`,
`ordist3clean`) are curated in exactly that way, by `Diagram.regen` at the
foot of `PLLDiagram.lean`; `#eval regen` rewrites them when the module is
elaborated.  `#draw` writes its file at elaboration time too, and both are
deterministic, so a drawing committed under `docs/figures/` stays
byte-identical across rebuilds.
## 7. PCLL + `¬◯⊥`

Adding to PCLL the single axiom `¬◯⊥` gives the *infallible* system, in
`LaxLogic/PLLNoFall.lean`, namespace `PLLND.NoFall`:

```
DerivUNoFall Γ φ  :=  DerivU (¬◯⊥ :: Γ) φ
```

Adding one formula (not a scheme) as an axiom is the same as adding it as a
persistent hypothesis, because every rule of the calculus carries its context
unchanged; the formula is `NoFall.nobot`.  The system is sound and complete
for mutually confluent models **with no fallible worlds**
(`derivUNoFall_iff_infallible_valid`) — hence the Lean name.  It is a proper
extension of PCLL (`pcll_not_nobot`), and it collapses the variable-free
fragment: every variable-free formula is derivable or inconsistent
(`varfree_dichotomy`), whereas PLL and PCLL have infinitely many
non-interderivable variable-free formulas.

### `#searchNF` and `#refuteNF`

The command pair of `LaxLogic/PLLSearchNoFall.lean` works like `#search` and
`#refuteConf`:

* `#searchNF Γ ⊢ C` tries a countermodel first — accepted only if mutually
  confluent **and** infallible (`RNC.confB` and `NoFall.infB`) — then runs
  the proof searcher on the extended context `¬◯⊥ :: Γ`;
* `#refuteNF Γ ⊢ C` runs only the countermodel engines, with the same double
  filter.

The showcase of the difference: `◯⊥ ⊢ ⊥` is PLL-refutable (a fallible top
forces `◯⊥` without `⊥`), but the infallible system proves it.

```lean
#refute   [(falsePLL).somehow] ⊢ falsePLL   -- REFUTED, by a fallible model
#searchNF [(falsePLL).somehow] ⊢ falsePLL   -- PROVED
```

The trap of §5 has an exact analogue, and the same resolution: a countermodel
found by `#refute` or `#refuteConf` refutes `DerivUNoFall` only if it also
has no fallible worlds, which is what `#refuteNF` enforces by construction.

### Pinning

The printed snippets use two certificate theorems:

* positive — `NoFall.derivUNoFall_of_nd`, applied to a PLL proof term over
  `¬◯⊥ :: Γ`.  As with PCLL, the searcher does not use the distribution
  scheme on its own; add `ConfluentU.distF` instances to the context and pin
  through `derivUNoFall_of_proved` when distribution is needed.
* negative — `NoFall.not_derivUNoFall_of_check`, with three `by decide` side
  conditions (confluence, infallibility, the checked sequent).  Note the
  checked context is `Γ` itself: the axiom needs no checking, because every
  infallible model forces `¬◯⊥` everywhere (`NoFall.force_nobot`).

`LaxLogic/PLLSearchDemo.lean` §6 runs all of this with pinned outputs.

---

## 8. Command-line tools

The `lakefile.toml` declares a number of `lean_exe` targets, most of them
one-off probes.  Two are representative.

```
lake build oracle2 && lake exe oracle2
```

runs a fixed ten-sequent benchmark through the staged procedure and prints,
per sequent, the verdict, a summary of any countermodel, and the time.  It is
a smoke test that the toolchain and the staging are healthy.  Its staging is
its own copy (`wip/oracle2.lean`), so the models it prints are the stages'
raw proposals: it does not go through `Config.simplify`, and a model there
will often be bigger than the same sequent's model here.

```
lake build rncprobe && lake exe rncprobe
```

runs the PCLL probe of §5 over a fixed dictionary of formulas, printing a
two-sided entailment matrix and the induced quotient.  It takes arguments
(`c`, `r`, `p`) selecting sub-phases; with none it runs the whole matrix,
which is slow.

`scripts/laxrun.sh help` lists a separate CLI (`timing`, `search`, `quant`,
`zoo`), which drives the fuelled decider of `PLLG4Dec.lean` over named
instances rather than the searcher described here.

---

## 9. Failure modes

- **`UNKNOWN` and you want to know why.**  Use `verdictWhy` or `settleWhy`
  rather than `verdict` or `settle`: the `Reason` names the parameter
  (`budgetExhausted`, `closureTooBig`, `allStagesMissed`).
- **`.unknown` on a sequent you believe underivable.**  If the reason is
  `allStagesMissed`, the battery missed it: add a frame to `Config.frames`,
  or raise `Config.comboCap`.  If it is `closureTooBig`, raise
  `Config.emitClosureCap`.
- **A run that will not return.**  Use the sequent-first wrappers or the
  commands, which budget the positive stage by default, or set
  `Config.findBudget` explicitly.  There is no interrupt: the searcher is a
  pure function.
- **`decide` or `rfl` failing on a search result inside a proof.**  Expected:
  the searchers are `partial`.  Discover with `#eval`, `#guard` or the
  commands, then pin the certificate.
- **A transcribed proof term that will not elaborate.**  Supply the implicit
  formula arguments of the left rule by name, or use `G4cTm.snippet`, which
  does it for you (§4).
- **A pinned countermodel that `by decide` rejects.**  The model was copied
  against the wrong sequent, or a relation list is not transitively closed:
  `checkB` includes the well-formedness check.
- **A PCLL claim resting on a PLL countermodel.**  Use `RNC.refuteConf?` or
  `#refuteConf`, not `refute?`; see §5.  The `scope` line of a `#refute`
  report says outright when what it found is no use for PCLL, so the way into
  this mistake is to read past it.
- **`PLLND.Search.decide` shadowing `Decidable.decide`.**  Use `settle`, the
  same function under its other name.
- **A model that looks too small, or a world you expected and cannot find.**
  Simplification deleted it: nothing survives that the refutation does not
  use, and a world carrying an unused promise is exactly the kind of thing
  that goes.  Re-run with `simplify := false` to see the stage's own
  proposal — for the *provenance* of a world (which belief set it came from)
  the raw emitted model is the one to look at, since simplification discards
  that history.  `CounterEmit.describe Γ C` prints it.
- **A file of `#guard_msgs`-wrapped commands showing nothing in the info
  view.**  Expected: `#guard_msgs` deletes the messages it has checked, so
  the only output left in such a file is that of the commands not wrapped —
  which is why the info view seems to jump to the end of the file and show
  one stale-looking block.  Use `#guard_msgs_show`
  (`LaxLogic/GuardMsgsShow.lean`), which checks *and* displays.

---

## 10. Pinning a found proof: `#pinsrc`

The refutation side of this tool has always produced *theorems*: a countermodel
is data, `FinCM.checkB M w Γ C = true` is a cheap kernel computation, and
`FinCM.not_provable_of_check` turns it into `¬ G4c Γ C`.  Every refutation in
this development is pinned that way.

The positive side did not, and the reason was purely mechanical.
`Verdict.proved` carries a **typed** term `t : G4cTm Γ C` — so Lean's
typechecker has already checked a derivation the moment the searcher builds one
— but there was no way to get `t` into a source file.  Running the searcher
inside the kernel is not an option: it is deliberately kernel-opaque.

`LaxLogic/PLLSearchPin.lean` supplies the missing step.

    #pinsrc Γ ⊢ C
    #pinsrc Γ ⊢ C with cfg

prints, on success,

    PROVED  (n nodes, rule tree …)
    paste as the proof term:
    (.impR (.laxR (.init (.head _))))

and on failure the same `Reason` diagnostics as `#search`.  Paste the term as

    theorem my_fact : G4c Γ C := (<term> : G4cTm Γ C).toG4c

and the kernel re-elaborates and re-checks it from scratch.  Nothing about the
search is trusted.

**Why the output is short.**  The emitter prints **no formulas at all**.  Every
index is recovered by unification: the conclusion's `Γ` and `C` come from the
ascription, and each side formula is pinned down by the *membership proof*,
emitted structurally as a `.tail _ (… (.head _))` chain pointing at a position
in `Γ`.  Unifying (say) `A.and B` with the formula at that position determines
`A` and `B`.  So the emitted term is proportional to the **derivation**, not to
the formulas in the sequent — which matters here, because the sequents this
development cares about have quantifier tables in them, formulas of weight in
the hundreds.

The chain is computed from the member's position in `Γ` rather than by recursion
on the membership proof: `List.Mem` is `Prop`-valued, so a `String`-valued
function cannot eliminate it.

**Worked examples** are in `wip/jumpPinned.lean`, which pins three facts that
`wip/jumpprobe.lean` and `wip/sealprobe2.lean` had only as probe output: the
descent to budget `0` at two atom jump goals, and the `◯⊥` collapse at a boxed
one (57 nodes).


## 11. Running probes under a wall-clock cap

`Config.findBudget` bounds a *single* search. Nothing bounds a *run*. A probe
with 84 cells of which 40 never close sits at 100% CPU until killed by hand.
Between 2026-07-30 and 2026-08-02 two probes from an abandoned line of work ran
for three days that way, alongside six others.

So probes are launched through the wrapper, never directly:

```bash
scripts/probe <seconds> <exe-name> > wip/<exe>_out.txt
```

It runs the executable, arms a killer at the cap, and returns. Partial output is
the normal outcome and is fine — every probe flushes after each line, so whatever
reached the file is intact and usable. The wrapper appends a line saying the cap
was hit, so a truncated run is never mistaken for a completed one.

Choosing the cap: a probe whose cells mostly close wants 60–300s; a sweep over a
space where most cells are expected to resist wants 300–900s and should be read
as a sample, not a survey. Anything that would need longer than that is asking
the wrong question — the productive move has always been a smaller cell (see the
`#pinsrc` discipline in §10) rather than a bigger budget.

Before ending a working session, check nothing survived:

```bash
ps -eo pid,etime,args | grep '.lake/build/bin/' | grep -v grep
```
