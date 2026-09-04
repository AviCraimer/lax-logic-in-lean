# Formalising and extending a body of mathematics with an LLM: a case study

*A record of the propositional-lax-logic uniform-interpolation campaign in Lean 4,
July–August 2026, written from the session transcript, the repository's own
progress ledger, and the git history.*

---

## Abstract

Between early July and 6 August 2026 a single human mathematician and a large
language model, working in Lean 4 under a rule that nothing counts as proved
until it is `sorry`-free and axiom-audited, mechanised a substantial body of
existing results about propositional lax logic (PLL) and attempted two
extensions of it. The mechanisation succeeded broadly. **The two extensions came
out differently, and the contrast is the point of this document.** One succeeded:
strong normalisation of the full proof-term reduction, where the obstruction to
the naive route was diagnosed and machine-checked *first*, a known technique
(Lindley–Stark `⊤⊤`-lifting) was then located in the literature and repurposed,
and the resulting proof is `sorry`-free. The other did not: uniform
interpolation, where five successive proof routes were machine-refuted, each
after substantial build effort. The last of these, refuted on 5 August,
invalidated three consecutive rounds of work that had been screened clean by a
purpose-built property-based testing harness. The harness had returned nine clean
passes over roughly 1150 generated instances for statements that were false
throughout, because it sampled typical values rather than boundaries, tied two of
its own axes together, and drew its countermodels from a fixed battery that
lacked the one frame shape that refutes.

This document extracts what is transferable. Three things stand out. First, the
condition that separates the two extensions is *where the difficulty sits*. When
the difficulty is in the **proof**, this configuration is strong: impossibility
of a naive route can be established mechanically, a published technique can be
found and adapted, and the assistant checks the adaptation. When the difficulty
is in the **statement**, the same configuration is weak without external
discipline, because the Lean kernel is a perfect oracle for "does this proof
work" and no oracle at all for "is this statement true". Second, the campaign's
own antidote, a growing ledger of statement-hygiene checks, was assembled the
expensive way, one wasted build at a time, and each check is stateable in a
sentence. Third, the campaign reinvented property-based testing and imported
almost none of software testing theory: boundary-value analysis, equivalence
partitioning, combinatorial interaction testing, metamorphic relations, mutation
of the specification, and coverage over a definition's own case analysis would
each have addressed a specific documented failure. A tooling proposal and a
candid failure inventory follow, together with a short argument that formal
semantics in the Montague tradition is a good next target for this configuration
of human, model, prover and tools.

The mathematics is not offered as a contribution. The human guide's own
assessment, which this document adopts, is that the campaign is not publishable
as mathematics. What is offered is the method record.

---

## 0. How to read this, and what is verified

Every factual claim below is tied to one of four sources, and cited inline:

| tag | source |
|---|---|
| `commit <hash>` | a commit on branch `ui-confluence` of the repository `lax-logic-in-lean`; subject lines are long and factual, one round per commit |
| `§N` | a numbered section of the repository's `PROGRESS.md`, the campaign's own running ledger (7497 lines at the time of writing) |
| `transcript <date>` | the session transcript, a 45 MB JSONL log of 12859 records; the human's turns are quoted verbatim, times in UTC |
| `measured` | a direct measurement made while writing this document (file counts, line counts, grep results, usage records in the transcript) |

Where a claim could not be verified it is marked **[unverified]** and the reason
given. All quotations reproduce their source verbatim, including punctuation;
ellipses mark omissions and nothing else has been altered. The distinction between PROVED (machine-checked, with the declaration
named), REFUTED (a machine-checked witness or a machine-checked derivation of
`False`, with the declaration named) and OPEN (searched, nothing found) is kept
strict throughout; this was a standing requirement of the campaign and it is
also what makes the negative results usable.

### Glossary of repo-internal vocabulary

The development's working vocabulary is internal to the repository and is not
literature terminology. It is defined here so the rest of this document is
readable without it.

- **PLL**, propositional lax logic (Fairtlough and Mendler, 1997): intuitionistic
  propositional logic plus a unary modality `◯` behaving as a strong monad:
  `φ ⊢ ◯φ`, `◯◯φ ⊢ ◯φ`, and congruence. Its Kripke semantics uses *constraint
  models*, with an intuitionistic preorder `Rᵢ`, a constraint relation `Rₘ`, and
  *fallible* worlds (worlds forcing `⊥`).
- **PCLL**: PLL plus the distribution scheme `◯(A ∨ B) ⊃ (◯A ∨ ◯B)`, sound and
  complete for *mutually confluent* constraint models. This axiom, and the branch
  the late campaign lives on, were the human's suggestion (transcript
  2026-07-21).
- **Uniform interpolation (UI)**: for each atom `p` and formula `φ` there is a
  `p`-free `∃p.φ` with `φ ⊢ ∃p.φ` such that every `p`-free `ψ` with `φ ⊢ ψ`
  satisfies `∃p.φ ⊢ ψ`; dually for `∀p`. Pitts proved it for IPC (1992);
  Ghilardi and Zawadowski showed it fails for S4. For PLL it is OPEN, and was
  OPEN when the campaign started and when it stopped.
- **The tables `itpE`, `itpA`**: the Pitts-style syntactic construction of the
  interpolants, defined by recursion over a finite formula set `S`, a context
  `Γ`, two natural-number parameters (*fuel*, a recursion allowance, and
  *budget*, a rank), and a goal.
- **defect**, **jumpGoals**, **room**: `defect S Γ` measures how far the context
  `Γ` is from saturating `S`; `jumpGoals S` is a distinguished set of goal
  shapes; **room** is the arithmetic side condition
  `defect S Γ * (|jumpGoals S| + 2) ≤ b` on the budget `b`. "Room-free" means the
  same statement with that side condition deleted.
- **screen**, **quiet**: a *screen* is a bounded countermodel search over
  generated instances; a *quiet* verdict means the bounded hunt found nothing.
  The harness deliberately has no verdict constructor called `pass`.

---

## 1. The setting

**The repository.** `lax-logic-in-lean`, Lean 4 (toolchain `v4.31.0`), public,
with a private sibling. Two source areas: `LaxLogic/`, the settled library, 104
modules and roughly 50 200 lines; and `wip/`, the working area, 252 files and
roughly 88 200 lines (*measured*). The library covers the Fairtlough–Mendler
natural deduction and Hilbert systems, constraint semantics, soundness,
completeness, a G4-style contraction-free sequent calculus with its structural
and inversion lemmas, decidability groundwork, countermodel search, strong
normalisation, and a family of applications.

**The mandate.** The governing methodological rule, set by the human on
2026-07-14 and in force throughout: *every* mathematical assertion stated as
established requires a `sorry`-free Lean proof with a clean `#print axioms`
audit; anything else is labelled OPEN or conjecture. He described this as "a new
modality for mathematics". This rule is the reason the negative results in this
document are usable at all.

**The people and the machines.** One human guide, a co-author of the source
theory being mechanised (the repository attributes the parent results to
`FairtloughMendler1997`, and the git author is Matthew Fairtlough), working
part-time and explicitly not reading the Lean code: "i won't dive into the Lean
code so I rely on a comprehensible and comprehensive report here in the chat and
in files recorded" (transcript 2026-07-25). One coordinating model instance, plus
delegated background agents in isolated git worktrees. Model identity changed
mid-campaign for budget reasons and this is a confound worth recording: "I'm
choosing Fable/max effort for this turn as it could be make or break"
(2026-07-21), "back to Opus max now, Fable burned all its credits" (2026-07-21),
"ran out of Fable credits! Back to Opus, Extra" (2026-08-05).

**Scale of the delegated work.** The transcript records 39 completed background
agents with usage statistics attached: roughly 10.9 million subagent tokens and
roughly 38.7 hours of subagent wall-clock, much of it in parallel (*measured*
from the transcript's `<usage>` records). This excludes the coordinator's own
token consumption, for which the transcript carries no aggregate.

---

## 2. Narrative arc

### 2.1 The mechanisation, and where the `sorry`s are

The mechanisation half of the project is broadly clean, and the cleanest single
measurement is where the `sorry`s are.

A filtered grep over `LaxLogic/` (excluding prose occurrences of the word inside
docstrings) finds exactly **five** `sorry` proof terms in the whole 104-module,
50 000-line library, and all five are in three modules of one line of work, the
*semantic uniform-interpolation extension*: `PLLSemUIChar.lean` lines 322 and
327, `PLLSemUILayered.lean` line 827, `PLLSemUIHenkin.lean` lines 341 and 352
(*measured*). Everything else, including strong normalisation
(`PLLStrongNorm.lean`, and the `⊤⊤`-lifting development `PLLTopTop.lean`, 1320
lines, the subject of §2.2), completeness (`PLLCompleteness.lean`, 648 lines),
the confluent variant's completeness (`PLLConfluentComplete.lean`, 523 lines) and
the decidability groundwork (`PLLDecide.lean`, 829 lines), carries no `sorry` at
all.

Note that this measurement is about the `sorry`s, not about difficulty: it says
where the unfinished business is, and §2.2 shows that one of the clean modules is
an extension rather than a transcription.

Two further data points on the mechanisation half:

- The confluent completeness theorem was produced in a *different* session in a
  single sitting, and the human's own report of it (transcript 2026-07-21) reads
  as unproblematic: "523 lines, sorry-free, root-imported, lake build green
  across the library... The construction turned out pleasantly slick, and the
  scheme sits exactly where it should."
- When the human's mid-campaign steer was "start from the beginning of the
  development with the new calculus... some may go through verbatim with only
  name changes" (2026-07-21), that prediction was correct for the mechanisation
  work and incorrect for the extension work, and the model's failure to
  distinguish the two produced the incident in §8.2 below.

### 2.2 The extension that succeeded: strong normalisation of the full reduction

This is the campaign's other extension, and it landed. It is treated here at
length because the contrast with uniform interpolation is what makes the case
study useful.

**The target.** Strong normalisation of the *full* one-step reduction `Step` for
the PLL proof-term calculus: `β` for every connective **and** `let`-assoc, freely
interleaved, over intrinsically-typed syntax. The theorem is

```lean
theorem strong_normalisation {Γ : List PLLFormula} {φ : PLLFormula}
    (t : Tm Γ φ) : SNt t
```

at `LaxLogic/PLLTopTop.lean:1278`, in a 1320-line `sorry`-free module
(*measured*), landed on 2026-07-07 across three commits (`f9b5dbd`, `e475719`,
`78461cd`).

**The starting position.** Two fragments were already strongly normalising in
isolation: `beta_sn` (`PLLReducibility.lean`, Kripke–Tait reducibility) and
`assoc_sn` (`PLLStrongNorm.lean`, a weight measure), with `step_split`
establishing that `Step` is exactly their disjoint union. The obvious hope is
that they compose.

**The obstruction, established first and machine-checked.** They do not, and the
development proves it before choosing a method. `PLLReducibility.lean` closes
with a section headed "Why the two halves do not combine: machine-checked
counterexamples" (line 1017), containing two terms and five checked `example`s:
`ce₁ = let y ⇐ (let x ⇐ z in val x) in val y` is proved β-normal
(`∀ y, ¬ RStep ce₁ y`) yet one assoc step creates a `let`-β redex in it; and
`ce₂ = (λf. let x ⇐ f in val x) (let x ⇐ z in val x)` is proved assoc-normal
(`∀ y, ¬ AStep ce₂ y`) yet one β step reduces it to `ce₁` exactly, closing the
ping-pong. The file draws the consequence itself:

> "These examples also close the generic modular-termination route
> (Bachmair–Dershowitz/Geser quasi-commutation, which combines `SN(R)` and
> `SN(A)` into `SN(R ∪ A)` given `A;R ⊆ R;(R∪A)*` or its mirror): the first
> performs `assoc;β` from a term admitting *no* β-step, the second `β;assoc` from
> a term admitting *no* assoc-step, so neither inclusion can hold. A semantic
> method is forced."

It also disposes of the obvious escape, noting that a measure for the phased
strategy "β to completion; assoc to completion; repeat" would prove only that one
strategy normalises, which is weak normalisation and was already available via
cut elimination (`PLLNormal.lean`).

**The method, located and repurposed.** Lindley–Stark `⊤⊤`-lifting (TLCA 2005),
described in the file's own header as "the biorthogonal upgrade of the
value-style `◯`-clause used for the β-fragment": a continuation stack
`K : Kont Γ A B` is a list of `bind`-bodies, `K` is reducible when `K[val s]` is
SN for every reducible `s` in any renaming extension, and `SRed (◯A) t` holds
when `K[t ρ]` is SN for every reducible stack. The relationship to what was
already in hand is exact, and is why the repurposing was cheap: "The β-fragment's
value clause is exactly the `K = []` shadow of this definition." Everything
outside the `◯` clause is the existing Kripke–Tait skeleton re-run over the
larger relation.

**The one piece of genuine engineering.** The principal lemma
(`PLLTopTop.lean:683`),

```lean
theorem principal (s : Tm Γ A) (u : Tm (A :: Γ) (somehow B)) (K : Kont Γ C B) :
    SNt s → SNt (K.plug (u.subst1 s)) → SNt (K.plug (.bind (.val s) u))
```

has an assoc-interface case whose reduct carries the *same* underlying SN witness
with a *shorter* stack. Bare accessibility induction cannot recurse on an
argument that has not decreased, so the induction runs on the lexicographic
measure `(Acc.rank hKu, K.size, Acc.rank hs)` using mathlib's ordinal rank of
accessibility (`Mathlib.SetTheory.Ordinal.Rank`). The dividend is a total
computable normaliser, `Tm.normalize` with
`Tm.normalize_spec : Steps t t.normalize ∧ Nf t.normalize`, upgrading a
previously fuelled reducer.

**Provenance, stated exactly.** This is where the episode could be overclaimed,
and the file itself does the disclaiming, which is worth quoting rather than
paraphrasing:

> "On paper, the method including sums is Lindley–Stark's own: TLCA 2005 §4.1
> treats λml with sums, case restricted to computation-typed branches, via sum
> continuations, and the unrestricted case construct is handled by frame stacks
> in Lindley's PhD thesis (Edinburgh, 2005, §3.5) ... Strong normalisation for
> λml itself predates the method: Benton–Bierman–de Paiva (JFP 1998) obtained it
> by translation into a λ-calculus with sums plus Prawitz's
> permutation-conversion result".

So the mathematical result was **not** unknown in advance in the literature. What
is claimed, and claimed with hedges the file supplies itself, is the
mechanisation: "The only prior *mechanisation* of `⊤⊤`-lifting we know of is
Doczkal–Schwinghammer (Isabelle/HOL-Nominal, LFMTP 2009; AFP entry
`Lam-ml-Normalization`), for the core calculus without sums; the present file
appears to be the first mechanisation with sums, the first in Lean, and the first
over intrinsically-typed syntax." The file also records two ways in which its
relation is *smaller* than the published system, so no unearned generality is
implied: `Step` has no η-rules and no case commuting conversions.

What was genuinely new *to the campaign*, and is machine-checked here rather than
inherited, is the non-composition result: that this calculus's two SN fragments
create each other's redexes and defeat both orientations of quasi-commutation.
That is what forced the method choice, and it was established before any effort
was spent on the method.

### 2.3 The extension that did not: uniform interpolation

Uniform interpolation for PLL was the campaign's target. Two routes ran, at
different times and sometimes in parallel: a **syntactic** route (a Pitts-style
table construction inside the G4-style calculus, living in `wip/`), and a
**semantic** route (a layered-bisimulation amalgamation argument, living in
`LaxLogic/PLLSemUI*.lean`). Both remain OPEN.

The syntactic route came closest, and its state is exact. The crown theorem is

```lean
theorem uniform_interpolation_PLL (p : String) (φ C : PLLFormula) :
    (p ∉ (existsP p φ).atoms ∧ G4c [φ] (existsP p φ) ∧
      ∀ ψ, p ∉ ψ.atoms → G4c [φ] ψ → G4c [existsP p φ] ψ) ∧
    (p ∉ (forallP p C).atoms ∧ G4c [forallP p C] C ∧
      ∀ ψ, p ∉ ψ.atoms → G4c [ψ] C → G4c [ψ] (forallP p C))
```

in `wip/final.lean:176`, with a pinned audit

```
'PLLND.uniform_interpolation_PLL' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

checked by `#guard_msgs` at `wip/final.lean:206`. The file also documents, and
the campaign repeatedly re-verified, that `sorryAx` enters through **exactly one
declaration**. Since round 4 (`commit ea3a755`, 2026-08-04) that declaration has
been `cascade_boxgoal_pos` at `wip/absorb_base.lean:2281`, a budget-descent
lemma for the interpolant tables:

```lean
private theorem cascade_boxgoal_pos (p : String) (S : Finset PLLFormula)
    (hand : ∀ {A B}, A.and B ∈ S → A ∈ S ∧ B ∈ S)
    (hor  : ∀ {A B}, A.or B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ {A B}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S)
    (hsome: ∀ {A}, A.somehow ∈ S → A ∈ S)
    (fs ft b : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula)
    (hgS : D.somehow ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S)
    (hfs : fs ≤ ft) (hb : 1 ≤ b) (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ b)
    (hamb : G4c Δ (itpE p S ft (b + 1) Γ))
    (hsrc : G4c Δ (itpA p S fs (b + 1) Γ D.somehow)) :
    G4c Δ (itpA p S ft b Γ D.somehow) := by
  sorry
```

Read plainly: given an ambient interpolant table at budget `b + 1` and a source
table at budget `b + 1` for a boxed goal `◯D`, produce the target table at
budget `b`. The hypothesis `hroom` is the arithmetic side condition. Everything
that follows in this document is, in one way or another, about that hypothesis.

### 2.4 The nine rounds

On 2026-08-04 at 18:17 UTC the human gave an instruction that shaped the rest of
the campaign:

> "go ahead with the assault on cascade_low_pos_box if you can provide a good
> reason why you will succeed given that you have been working entirely with
> quantifier formulae and not with budget ranks. If the budget rank ≤ 1 is not
> correctly defined, then your attempt will fail... If you can refute the cascade
> conjecture with the extra power of the RN lattice work and your understanding
> of interpolants, that would help so I suggest you do the usual 2-pronged
> approach: simultaneously try to prove and disprove it."

Nine rounds followed, each a paired *prove prong* and *refute prong*, over
roughly 28 hours of wall-clock (2026-08-04 18:17 UTC to 2026-08-05 22:21 UTC).
Within that window the transcript records 14 completed background agents, roughly
4.79 million subagent tokens and roughly 20.2 hours of subagent wall-clock
(*measured*).

| round | commit | date | result |
|---|---|---|---|
| 1 | `7405871`, `be892e6` | 08-04 | both prongs agree the lemma holds; **the miscalibration the human predicted is found**, in the apparatus one level up, not the kernel (§57) |
| 2 | `4f9f6f4` | 08-04 | re-parameterisation lands; **the room-free kernel variant is REFUTED** (§58) |
| 3 | `a997769` | 08-04 | **the ledger/financing route is REFUTED** in four lines (§59) |
| 4 | `ea3a755` | 08-05 | assembly lands; the holdout narrows to `cascade_boxgoal_pos`, a certified weakening (§60) |
| 5 | `762fc23` | 08-05 | **the self-financed crossing is REFUTED** (§61); refute prong screens clean (§62) |
| 6 | `33548e4`, `4ebe1e6` | 08-05 | two residues proved; **the depth-≥2 nest is REFUTED** (§63); refute prong screens clean (§64) |
| (tool) | `997c22a` | 08-05 | the frontier sampler lands: 948 admissible cells, 19 strata, 0 refutations (§65) |
| 7 | `8b4c019` | 08-05 | `CompProd` stated and screened two-sidedly, clean (§66) |
| 8 | `05f8708` | 08-05 | `GoalRowAbsorb` stated and screened two-sidedly, clean over 1152 cells (§67) |
| 9 | `6dfc093` | 08-05 | **the entire room-free route is REFUTED**, kernel-checked at `Γ = []` (§68) |

### 2.5 Round 9: the turn

Round 9 (`commit 6dfc093`, §68) refuted, in the kernel, the three statements
rounds 4, 7 and 8 had been built on: `Round4.BoxDesc`, `Round7.CompProd`,
`Round8.GoalRowAbsorb`. The refutations are named declarations with clean axiom
lists (`not_boxDesc`, `not_compProd`, `not_goalRowAbsorb`, each
`[propext, Classical.choice, Quot.sound]` over a `decide +kernel` certificate),
and `¬BoxDesc` is re-derived twice more through rounds 7's and 8's own upgrade
theorems, so the three refutations are mutually consistent by machine.

The instance is tiny: `vS` is the piece-closure of `◯((◯x ⊃ y) ⊃ z)`, seven
formulas; `Γ = []`; the models are `M2`, which is a July countermodel with the
atoms renamed, and `P3c`, which is `M2` with the modal step pushed one world up.
As §68(b) puts it, the box "buys exactly one modal step, and a chain longer than
the one the battery carried spends it".

What survived: the refuted cell is *strictly sub-room* by a factor of 35
(`vS_room = 35` at `b = 1`; `not_room_at_one`, `not_room_at_two`), so
`cascade_boxgoal_pos` and its room-carrying abstraction `BoxDescR` are untouched
(§68(f)). The `sorry` never fell. The room hypothesis it carries survived as the
sole excluder of every known countermodel, for the third separate time in the
campaign (round 2, round 5, round 9).

What died: "§61(c) alternative 1, §63(e) fork (1), and the whole of rounds 6, 7
and 8 were assembled on `Round4.BoxDesc` being true. It is not." (§68(g)). What
survived from those rounds are theorems *about the tables* rather than about the
route: `Round6.easc_tight`, `Round6Force.itpA_atom_forces_amb`,
`Round8.goalRowAbsorb_top`, `Round8.goalRowAbsorb_atom`.

---

## 3. When extension succeeds and when it fails

The campaign ran two extensions to completion or exhaustion. One succeeded and
one did not, in the same repository, under the same mandate, with the same human
and the same model family. That is the case study's most useful evidence, and it
supports a sharper claim than "extension is hard".

### 3.1 The two extensions, compared

| dimension | strong normalisation (§2.2) | uniform interpolation (§2.3) |
|---|---|---|
| where the difficulty sat | **in the proof**: the statement was known-shaped and its meaning was never in doubt | **in the statement**: the target was fixed, but every intermediate obligation was a design choice |
| the obstruction | diagnosed **first** and machine-checked: two counterexample terms killing both orientations of quasi-commutation, before any method was chosen | discovered **last**, five times over, each time after a build had been scoped on it |
| the method | **found in the literature and repurposed**: `⊤⊤`-lifting, whose `K = []` shadow was already the fragment's own value clause | invented in-house each round; five successive in-house routes machine-refuted |
| the assistant's job | check an adaptation of a known technique against an intrinsically-typed calculus, and engineer one induction measure | choose a statement with no oracle to check it against |
| the oracle situation | complete: once the method was fixed, every step was kernel-checkable, and failure was local and immediate | absent: a false statement compiled the whole stack and passed every axiom pin (§58) |
| outcome | PROVED, `sorry`-free, plus a total normaliser as a dividend | OPEN, one `sorry`, five routes REFUTED, a reusable set of table lemmas and financing theorems |
| elapsed | one day (2026-07-07, three commits) | roughly three weeks, with the last nine rounds in 28 hours |

**The transferable condition.** When the difficulty is in the **proof**, the
configuration of LLM plus literature search plus proof assistant is strong, and
the strength is specific and repeatable: the impossibility of a naive route can
be established *mechanically* and therefore cheaply and finally; a published
technique can be located, and the assistant is good at adapting one and at
absorbing the bookkeeping cost of the adaptation (renamings, stack indices,
measure engineering). When the difficulty is in the **statement**, the same
configuration is weak, because the step that decides the outcome is the one step
the machine cannot check. That is precisely the gap the testing apparatus of §5
is for.

Two secondary conditions are visible in the same comparison and are worth naming
separately, because both are actionable:

- **Establish the obstruction before choosing the method.** The SN episode spent
  its first effort proving that the cheap route is impossible. Every UI round
  except the two-pronged ones spent its first effort on a build. The
  campaign's own §59 rule ("check the financing before the proof") is this
  lesson learned again, at much higher cost, on the other extension.
- **Prefer a known technique over an invented one, and say which you are doing.**
  `⊤⊤`-lifting arrived with a published correctness argument and a published
  scope; the UI routes arrived with neither. An assistant that will happily
  invent an architecture should be asked, first, what the literature already has.

### 3.2 Why the UI extension had none of those conditions

**The evidence.** All five `sorry`s in the 50 000-line library are in the
semantic UI line, and the one load-bearing `sorry` in the 88 000-line working
area is the syntactic UI kernel. Five successive UI routes died; no mechanisation
route died, and the SN extension did not die. The UI extension consumed three
weeks and, in its last 28 hours alone, roughly 20 hours of delegated agent time,
for a net negative result.

**Four mechanical reasons.**

1. **Some work supplies its statements and some does not.** In mechanising a
   known theorem the statement is given, by the paper, and only the proof is at
   risk; the SN extension inherited this property too, because its target
   statement ("every term is strongly normalising for the full reduction") was
   fixed and unambiguous from the start and only the route was open. In the UI
   extension the statement was the artefact: every intermediate obligation was a
   design choice, and a wrong statement is expensive in a way a wrong proof is
   not, because a wrong proof fails in seconds and a wrong statement fails in
   rounds. §57's summary is exactly this: "SIX consecutive obligations were
   statement problems".

2. **The kernel is a perfect oracle for proofs and no oracle at all for
   statements.** Lean will tell you instantly and infallibly whether a proof
   works. It will tell you nothing about whether a statement is true, whether it
   is the statement your consumer needs, or whether your route is worth taking.
   Every one of the campaign's method rules (§6 below) is a hand-built substitute
   for the missing oracle.

3. **A `sorry` makes falsity invisible to every automatic check.** This is the
   sharpest finding of the campaign and it is worth stating precisely. In round 2
   a *false* statement was drafted, compiled cleanly, passed the whole dependent
   stack, and passed every `#guard_msgs` axiom pin, because the declaration it
   fed was a `sorry` and `sorryAx` was already in the crown's audit. §58's method
   note: "a false statement can do all three, because it is a `sorry`". What
   caught it was a *human-instructed* re-read of the repository's own existing
   refutation file. There is no automated signal here at all: the build is green,
   the pins pass, and the statement is false.

4. **The model's local incentive is to land a round.** Rounds 7 and 8 both
   "landed": each produced a new statement, screened it two-sidedly, proved
   sub-cases of it, and committed a detailed positive report. Both were built on
   a statement that was false the whole time. The reports were accurate about
   what had been done and silent about the thing that mattered, because nothing
   in the loop was checking it.

**A corollary about the human's role.** The human's contributions concentrate
overwhelmingly at exactly the point the machine has no oracle: the statement and
the route. His single highest-value intervention (2026-08-04, quoted above) was a
statement-calibration warning; his second (2026-08-05) was a probe-design
critique; his third (2026-07-26) was a two-line argument that a proposed
hypothesis implied an absurdity. None of the three required reading any Lean.

### 3.3 The cost the successful extension carried

The SN episode is not free of the campaign's characteristic problem, and the
failure inventory of §4 would be misleading without this entry. The proof the
guide now owns is one he cannot yet read. On 2026-07-21 he wrote:

> "We may need an advanced session going through eg SN which I didn't really
> understand properly, before I try to publish any of this stuff. Wouldn't want
> to get exposed in a viva!"

`⊤⊤`-lifting was not part of his working repertoire, and the mechanisation does
not supply the tutorial. This is a real cost of the method rather than an
incidental one: a machine-checked proof that its owner cannot expound is an asset
he cannot defend, cite from, or extend, and under a machine-checked mandate the
temptation is to treat the audit as if it discharged the obligation to
understand. It does not. **Expositional debt belongs in the ledger alongside
proof debt**, and the repository already tracks it as a standing item, requiring
a conventional-language exposition reverse-engineered from the formal proofs and
a distillation of the reusable proof moves. The practical rule: when an assistant
imports a technique the guide does not know, the exposition is part of the
deliverable, not a follow-up.

### 3.4 What the campaign produced, stated plainly

The rest of this document is an anatomy of failures, and read alone it would
misrepresent the enterprise. For balance, the machine-checked positives from the
same repository and the same working method:

- the Fairtlough–Mendler results mechanised `sorry`-free over a
  natural-deduction system: models and soundness, the canonical model and
  completeness, the Hilbert system, a G3 calculus with cut elimination, the
  finite model property;
- **strong normalisation of the full interleaved reduction** (§2.2), with a total
  computable normaliser as a dividend, plus Craig interpolation and the
  decidability groundwork;
- soundness and completeness for the confluent variant PCLL, a logic that did not
  exist at the start of the campaign, in one sitting;
- five machine-checked route refutations (§8), each closing a line of attack
  permanently rather than provisionally, plus the surviving table lemmas and
  financing theory from the refuted rounds;
- a property-based screening tool with a pinned reachability measurement (§5.1)
  and a replayable corpus of its verdicts.

Uniform interpolation for PLL is OPEN, and closing five wrong routes is not the
same as opening a right one. Both statements are true at once.

---

## 4. The failure inventory

What was spent, on what, and what would have prevented it. Wall-clock figures are
delegated-subagent time measured from the transcript's usage records; they run in
parallel and are not additive with human time.

| dead route | died at | cost | what would have prevented it |
|---|---|---|---|
| **The July "ledger" family** (financing machinery for a demand never made) | §59/§60, rounds 3–4, 08-04 | three rounds of prior machinery, plus a ~1500-line build that was scoped and then cancelled | §60's check: *count the consumers*. Three lines of `grep` showed the holdout had exactly three call sites, all of one shape. Cost of the check: minutes. |
| **The room-free kernel re-parameterisation** (§57's interface route) | §58, round 2, 08-04 (`wip/reparamRefute.lean`) | the whole §57 apparatus (`boxSnd`, `boxSndTight`, `floorGoals`, a "six shapes × three interfaces" residue) became the residue of a refuted statement | §58's check: *test the new statement against the repository's own existing refutations before adopting it*. The refuting instance was already in the repo. |
| **The self-financed crossing** | §61, round 5, 08-05 (`Round5.no_self_financed_crossing`) | one round | §61's check: *check the financing of the recursion, not only of the entry*. The refutation is four hypotheses to `False`, and §61 records it "would have caught it before any build was scoped". |
| **The depth-≥2 nest** (the truncation tower) | §63, round 6, 08-05 (`no_depth2_entry_at_s3`, `no_self_financed_nest`) | one round | §63's check: *check the financing at every depth*. The design was financed at its call sites and at its first self-call and still died at depth 3. |
| **The entire room-free route** (`BoxDesc`, `CompProd`, `GoalRowAbsorb`) | §68, round 9, 08-05 | rounds 6, 7 and 8 in full, plus the sampler campaigns aimed at them: 7 background agents, ~2.28 M subagent tokens, ~12.0 h of subagent wall-clock, ~1150 screened cells and nine clean candidate passes, all for false statements | boundary-value analysis on the context axis (`Γ = []`), decoupling of the fuel and budget axes, and one additional frame in the countermodel battery. §68(e): "The three fixes are jointly necessary." |

Two further costs that do not fit the table:

- **Communication cost.** On 2026-08-01, eleven days into the campaign, the human
  wrote: "ok great thanks, that clarifies things considerably, and tightens the
  language, a very important step. I finally understand what you have been
  meaning by 'rung' all along. Just a single node in the lattice." A single
  ambiguous term cost eleven days of partially-blind supervision.
- **The abandonment on 2026-07-30.** After a three-day unsupervised run the human
  closed the thread: "This is a good place to give up the search. We've thrown
  everything at it; your reports are increasingly opaque to me and without some
  truly fresh ideas I doubt a proof will emerge... I realise that it is too hard
  for me to follow what has happened and have meaningful input into it. So we
  leave UI for the LL calculi open for now. A lesson for us both on the limits of
  LLM/human mathematical development." The campaign resumed later on a different
  route; the cost of the abandoned line is not separately measurable.

---

## 5. The testing-theory gap

This is the tooling half of the case study and, in the human's judgement and
mine, the most transferable part. His formulation, 2026-08-06:

> "yes we really need to apply a body of testing theory from software here, not
> just adapting Plausible. Why wouldn't it be relevant? You are testing a bit of
> software before you build it in fact. And the building is, or should be, guided
> by the tests. Boundary tests are essential and you haven't been making them and
> burning lots of energy and my credits in the process."

### 5.1 What the campaign built

After the human's completeness-versus-reach critique (2026-08-05, quoted in full
in §7 below), the campaign built a property-based testing harness, the *frontier
sampler* (`commit 997c22a`, §65, skeleton at `tools/FrontierSampler/`). It has
four layers: **stratification** (a campaign is a list of named structural
regions, each with its own generator, sample count and seed range),
**admissibility gating** (a decidable clause of the statement's side condition;
failures are recorded and never counted as passes), a **certificate-carrying
corpus** (one append-and-flush line per cell, replayable and pinnable), and
**cross-property replay** (a cell is a pure function of `(stratum, seed, size)`,
so a corpus can be re-driven against a different statement later).

It is careful in ways worth crediting. Its vocabulary section states: "`quiet` is
not `pass`. A clean screen is evidence about where certificates were not found,
not a proof that none exist. The verdict type has no constructor called `pass`,
deliberately." Its determinism audit is a real regression suite (1152 of 1152
records regenerate identically across a generator refactor, §68). And it produced
a genuine machine-checked *measurement* rather than only verdicts: §65(c) proves
that a `γ`-clause in the formula space forces the budget above the point where
kernel decision is feasible (`two_le_jumpGoals_of_gamma`,
`four_le_budget_of_gamma`), so the room-carrying statement's live regime cannot
be screened at all, and that unreachability is itself pinned as a theorem.

The human named the reinvention immediately: "of course, this is reinventing
QuickCheck (Haskell); is there yet a Lean version of this outstandingly useful
tool?" (2026-08-05). There is: **Plausible**, the Lean 4 QuickCheck descendant,
split out of Mathlib from `SlimCheck`, and already present in the repository's
package tree transitively via Mathlib.

### 5.2 The anatomy of the round-9 fault

The harness screened rounds 4 to 8 clean and the statements were false. §68(c)
identifies three independent blind spots, each a fixed assumption in the harness:

- **Defect axis, degenerate end never sampled.** The generator `genDrop` removed
  one or two members from the formula space to form the context, so across 1382
  corpus records *no cell ever had an empty context*. The refutation lives at
  `Γ = []`, where the ambient premise degenerates to `⊤` and the tables collapse:
  the cheapest instances in the entire space.
- **Two axes tied.** The fuel grid was defined as `ft = b + 1`, a convenience. At
  `Γ = []` the `BoxDesc` cell is **provable at `ft ≤ 4` and refuted from
  `ft = 5`**. The tie made the refuting fuel unreachable at every budget inside
  the cap, silently.
- **Oracle reach.** The refuting model `P3c`, an infallible three-world chain with
  a single modal step, was in neither of the two frame batteries. One battery had
  the three-chain with an empty modal relation; the other had it with a fallible
  top, which forces every atom at the top world and destroys the configuration.

In software-testing terms this is a textbook **3-way interaction fault**: no
single axis correction reveals it, and §68(e) confirms the point empirically,
"with the round-8 frame list, or the round-8 defect range, or the tied fuel grid,
the same passes are silent". Once all three were fixed, replay over the enlarged
corpus turned four silent passes into 43 hits, with a matched control staying at
zero.

### 5.3 The mapping: nine techniques, and what each would have bought

Each row names a standard technique, the campaign's actual state, and the
specific documented failure it addresses. Citations are to the standard sources;
where a claim is about this campaign it carries its `§` or transcript reference.

**1. Boundary-value analysis** (Myers, *The Art of Software Testing*, 1979).
Test at and adjacent to the boundaries of each input domain, not in its interior.
*Campaign state*: absent. Every generated context sat at the "nearly all of `S`"
end of the defect axis; the empty context was never generated in 1382 records
(§68(c)). *What it buys*: `Γ = []` is the minimum of the context axis and is
also the cheapest cell in the space. §68(h)'s own corrected rule states it:
"Sample the DEGENERATE end of every axis, not just the interesting end... Cheap
degenerate cells should be screened FIRST."

**2. Equivalence partitioning and the category-partition method** (Ostrand and
Balcer, CACM 31(6), 1988). Decompose the input space into categories and choices,
declare constraints between choices explicitly, and generate the frames from the
declaration. *Campaign state*: strata exist (19 of them, §65) and are a partition
of sorts, but they were derived from *where the proof was currently looking*
rather than from the statement's parameter structure, and one inter-category
constraint (`ft = b + 1`) was baked into the generator instead of being declared.
*What it buys*: the category-partition discipline forces constraints to be
written down, and a written-down constraint is one you can decide to relax.
§68(h): "Never tie two axes in a grid."

**3. Combinatorial (t-way) interaction testing** (Kuhn, Wallace and Gallo, IEEE
TSE 30(6), 2004; NIST SP 800-142, Kuhn, Kacker and Lei, 2010). Generate a
covering array so that every combination of `t` parameter values appears; the
empirical "interaction rule" is that most faults are triggered by one or two
parameters, with diminishing returns past about six. *Campaign state*: absent;
axes were varied one at a time within strata. *What it buys*: precisely the
round-9 fault, which needs `t = 3` (context boundary, fuel value, frame class).
Note the nuance and do not overclaim: **pairwise testing would not have caught
it**. A 3-way covering array over three axes of small cardinality is a few dozen
cells, minutes of countermodel checking.

**4. Metamorphic testing** (Chen, Cheung and Yiu, HKUST-CS98-01, 1998; surveys:
Segura et al., IEEE TSE 2016; Chen et al., ACM Computing Surveys 2018). When no
oracle exists, test *relations between* runs instead of individual outputs.
*Campaign state*: absent as a discipline, present accidentally. Four relations
were available and unused, and each is directly implicated:
   - *Monotonicity in fuel.* The statement is **not** monotone in fuel (provable
     at `ft ≤ 4`, false from `ft = 5`, §68(c)). A monotonicity relation would
     have failed on the first cell that crossed the boundary, and its failure
     would have located the boundary exactly.
   - *Invariance under atom renaming.* The round-9 witness `M2` is literally a
     July countermodel "with the atoms renamed" (§68(a)), and every round-9
     certificate is `P3c` "up to atom renaming" (§68(e)). A corpus canonicalised
     modulo renaming would have connected an existing refutation in the
     repository to the new statements.
   - *Stability under adding unused members.* The relation whose orbit has
     `Γ = []` at its base.
   - *Premise monotonicity of the search tool itself.* §67 records, as an
     incidental discovery, that the searcher is **not** premise-monotone: a
     "quiet" verdict on a stronger premise list proves nothing about the weaker
     one. That is a metamorphic property of the *oracle*, found by accident after
     it had been implicitly assumed.

**5. Mutation testing of the specification** (DeMillo, Lipton and Sayward, IEEE
Computer 11(4), 1978; survey: Jia and Harman, IEEE TSE 37(5), 2011). Seed
deliberate faults and measure what fraction the test suite kills; a suite that
kills nothing has no power. *Campaign state*: ad hoc. The campaign did run
"calibration controls" (§65: "live-fire calibrated against round 4's unboxed
control"; §68(e): a `Z0` control firing 825 hits, and a matched
present-antecedent control `Fp` firing zero), and these are exactly
mutant-kill and discriminator checks, but they were chosen per round rather than
run as a matrix. *What it buys*: the decisive diagnostic. Mutate the statement
systematically (drop `hroom`, drop `hd1`, weaken `fs ≤ ft`, lower `b`, drop
`hgS`) and measure kills. A screen that cannot kill an obviously-too-strong
mutant cannot certify the real statement either, and this could have been
measured in round 4, before three rounds were built.

**6. Coverage criteria over the definition's own case analysis** (Ammann and
Offutt, *Introduction to Software Testing*, 2nd ed., 2016: graph, logic,
input-space and syntax-based criteria). *Campaign state*: coverage was reported
as instance counts and strata, never as branch coverage of the definitions the
statement mentions. *What it buys*: the single most transferable idea in this
document. §68(e) identifies the discriminator as "exactly the `C₁ ∉ Γ` branch of
`itpAgoal`", a syntactic case of a recursive definition the statement quantifies
over. Instrumenting `itpA`/`itpE` and reporting which branches a campaign
exercised would have shown an uncovered branch in round 4. Coverage over
*definition clauses*, not over instance size, is the natural adequacy criterion
for a proof-engineering screen.

**7. Fault seeding from the known refutation family** (error seeding, Mills; and
the fuzzing practice of a seed corpus). *Campaign state*: absent as a systematic
practice. *What it buys*: the round-9 witness was **two edits** from a refutation
already in the repository (take July's `Mk`, rename the atoms, push the modal
step one world up). A seeded corpus containing every configuration the repository
has ever proved refuting, plus systematic one-step perturbations (add a world,
move the modal step, flip fallibility, empty the context), replayed against every
new statement, is cheap and would have fired.

**8. Shrinking** (Claessen and Hughes, *QuickCheck*, ICFP 2000; integrated
shrinking in Hedgehog). Plausible provides `Shrinkable`; the campaign never
shrank a witness. State the value accurately: shrinking helps only *after* a hit,
and the campaign's problem was that it had no hits. Its real value here is
downstream: minimal, canonical certificates are what make the renaming-invariance
and seed-corpus ideas above practical, because two certificates can then be
compared.

**9. Test-first discipline, applied to statements.** The human's framing is
exactly right and is the organising principle for all of the above: the proof
engineer drafting a lemma is writing a specification for software that does not
exist yet, and the screen is its test suite. The order should therefore be:
declare the axes and their boundaries; write the screen; measure the screen's
power by mutation; only then scope the build. The campaign's own standing rule
(§65) had reached the first half of this independently, "each round's residue
shape defines the next sampler stratum, and the sampler runs before any proof
build is scoped", but without power measurement it was, as round 9 showed,
a screen with unknown and in fact zero power against the actual fault.

### 5.4 The screen-power principle

The compressed statement of the whole section, and §68(h)'s own first method
note, is:

> **A clean screen is a statement about the screen.** Nine passes over 1152
> cells, three rounds, all clean — and false. Every "quiet" verdict in the corpus
> was produced by a battery blind to one frame, a generator blind to one end of
> one axis, and a grid that tied two axes together. A negative result from a fixed
> battery bounds the countermodel, not the statement; the bound must be recorded
> with the verdict.

The operational consequence, which no tool in the surveyed ecosystem currently
provides: **every quiet verdict should carry its own provenance**, the frame list
identity, the axis ranges actually generated, the declared and undeclared
constraints, the node caps, the oracle version. Without that, a corpus of clean
runs is an unquantified assertion.

---

## 6. The statement-hygiene ledger: six transferable rules

The campaign assembled these one wasted build at a time. Each is stated here as a
rule, with the incident that bought it. They are recorded in the repository at
`PROGRESS.md` as "method notes" and were adopted cumulatively.

**R1. Check the statement against its consumer, not only against the traversal
that produces it.** (§57, round 1.) The obligation `boxSnd_reaches` had been
proved at an ambient budget of source `+ 1`, while its consumer supplied ambient
`=` source. Roughly twenty prior PROGRESS sections had been built at budgets the
interface never supplies. §57: "SIX consecutive obligations were statement
problems". The fix, once located, was local and made the proof *simpler*.

**R2. Check the statement against the repository's own refutations before
adopting it.** (§58, round 2.) A false statement compiled cleanly, passed the
whole dependent stack, and passed every axiom pin, because it fed a `sorry`.
"What caught it was reading `wip/ascRefute.lean` while recomputing the obligation
set, which the round's brief explicitly asked for."

**R3. Check the financing before the proof.** (§59, round 3.) The "financing"
question is whether the arithmetic side conditions a design needs can all be
satisfied simultaneously. "The entry/seal dilemma is four lines of Lean and it
rules out the whole 1500-line build the round was scoped for."

**R4. Count the consumers.** (§60, round 4.) "The holdout had been treated as a
lemma the tower needs; it is consumed from three places, all of one shape, and
that fact — three lines of `grep` — is what turns a 1500-line ledger rebuild into
a single room-free statement." The cheapest check in the ledger, and the one with
the largest single payoff.

**R5. Check the financing of the recursion, not only of the entry.** (§61, round
5.) "An architecture can make only the entry demand at its call sites and still
make a seal demand inside its own proof — the round-4 composition was sound about
the sites and silent about the self-call, and the four-line
`no_self_financed_crossing` would have caught it before any build was scoped."

**R6. Check the financing at every depth.** (§63, round 6.) "A design can be
financed at its call sites (§60), financed at its first self-call (§61(d)'s entry
band), and still die at a fixed finite depth — the band must be computed before
the build is scoped, and here it is two levels wide against a recursion of
unbounded depth."

Two later additions, from the positive side:

**R7. When a design names a rescuing resource, first check what the resource is
derivable from.** (§66, round 7.) The guard stack turned out to be derivable
from the ambient already, so the design's real content was elsewhere.

**R8. When a route is refuted, ask which disjunct family of the target it used,
and refute per family.** (§67, round 8.)

And the sampler-era rules, from §65 and §68(h): the residue shape of each round
defines the next screen's stratum and the screen runs before the build is scoped;
sample the degenerate end of every axis first; never tie two axes in a grid;
widen the oracle when a modal statement survives a screen its unmodal form fails.

**A caution about this ledger.** Rules R1 to R8 are each real and each was bought
with a failed build, but note what they have in common: they are all *cheap
checks that a machine could run and did not*. R4 is a `grep`. R2 is a corpus
replay. R3, R5 and R6 are small arithmetic satisfiability questions. That is the
tooling opportunity, and it is more interesting than the rules themselves.

---

## 7. The human-in-the-loop record

The human's turns are the spine of this case study because they are where the
outcomes changed. Each entry below gives the intervention, the date, and what it
was worth.

### 7.1 Interventions that changed outcomes

**The confluence proposal (2026-07-21).** "assume the Rᵢ/Rm confluence condition
... which is equivalent ... to the axiom scheme `◯(φ ∨ ψ) ⊃ (◯φ ∨ ◯ψ)` ... Use a
branch for this (`ui-confluence` I suggest)". *Worth*: the branch the entire late
campaign lives on, and a new logic (PCLL) with sound and complete semantics
mechanised. His accompanying methodological remark deserves quoting in full:
"it is always best to stick to the rules for any long development: but it's
always useful to peek beyond them and see what happens if they can be changed, if
for no other reason than gaining perspective on the problem."

**The interactive-proof-state steer (2026-07-21).** "you can see the proof state
and interact directly, not just work in batch mode. This is what humans mostly
do, and the Lean infoview is designed for precisely this workflow." *Worth*: a
change of working mode, and (2026-07-21) the human's own read of the effect: "It
may be that this approach ... is much more feasible for you, and gives you the
extra leverage you need ... [the previous model] would hack the entire proof up
blind and then correct from feedback as you were trying to do." A document
`docs/lean-proof-lessons.md` was created at his instruction to hold the traps.

**The three-line semantic argument (2026-07-22).** "suppose we want to show
`m ⊨ ◯M` but `m ⊭ M` ... by confluence there is such a world `n'` and one for
which `k Rᵢ n'`; but since `k ⊨ M` and `⊨` is hereditary, `n' ⊨ M` already. But
this simplicity should already be baked in. I may have misunderstood the
complexity here but I'm uneasy about how hard you are working at this point."
*Worth*: collapsed an over-engineered construction; the follow-up steer, "use bare
possibility directly, don't rebuild the triples", was the operative instruction.
This is the clearest instance in the transcript of a human noticing *effort as a
symptom* rather than checking a result.

**The absurdity check (2026-07-26).** On a proposed hypothesis: "`BandCollapse R
(2R+2)` (hypothesis, the plateau) ... How can this be true? you can use this
hypothesis to prove that every variable-free formula is interderivable with one
of crank 0. which is on the face of it absurd given what we know of P(C)LL."
*Worth*: killed a hypothesis in two sentences. Note the shape: he did not check
the proof, he checked the *consequences* of the statement. This is R1 to R6 done
by hand, and it is what the machine was not doing.

**The approach-invalidating observation (2026-07-26).** "the funny thing is that
PLL+¬◯⊥ is sound and complete for infallible constraint models; and thus
`◯⊥ ≡ ⊥` there and the RN(◯,{}) lattice collapses completely to `{⊥,⊤}` under
infallibility. So then UI (if it exists) for PLL+¬◯⊥ cannot depend on the
structure of RN(◯,{}) anyway, contrary to our approach." *Worth*: a
correctness check on the entire strategy of the week, in one paragraph.

**The probe-design critique, first statement (2026-07-29).** This is the most
important entry in the record and the coordinator's own account of the campaign
understates its date by a week. On 29 July the human wrote:

> "it is odd that you would do a large search for counterexamples that didn't
> include any of the relevant formulae; what is your process for deciding where to
> look (how to define the probe family) when you set yourself a task eg the 'fresh
> antecedent law' (undefined btw)"

quoting back the model's own admission that a July verdict had held the
fresh-antecedent law semantically free "with equality on every probed instance —
but its probe family (u, u⊃r, ◯u) contained no ⊃◯-shaped piece, which is
precisely where the law fails". *Worth*: it identified, on 29 July, exactly the defect that killed
rounds 6, 7 and 8 on 5 August. **The same class of probe-design fault, on the
same law (the fresh-antecedent row is round 9's refuted residue, §68(a)), recurred
unfixed for a week after being diagnosed in plain language.** Nothing in the
campaign's process converted a diagnosed sampling defect into a standing
generation rule until the human raised it a second time.

**The budget-rank calibration warning (2026-08-04).** "If the budget rank ≤ 1 is
not correctly defined, then your attempt will fail." *Worth*: round 1 found a real
miscalibration, in the apparatus one level above the kernel (§57): the layer had
been built at budgets its interface never supplies. The repository's own memory
records this as "Matthew's predicted failure mode, located". The fix was local and
simplifying.

**The two-pronged instruction (2026-08-04).** "I suggest you do the usual
2-pronged approach: simultaneously try to prove and disprove it." *Worth*: five
machine-checked refutations in nine rounds, each cheap and each final. This is the
single highest-leverage process instruction in the transcript, and it is worth
noting why it works: the refute prong supplies the missing oracle. A proof attempt
that stalls tells you nothing; a refutation tells you the route is dead, as a
theorem.

**Calibrated scepticism (2026-08-05).** "go with round 4 then, but I'm not so
hopeful! give it your best." *Worth*: not an outcome change, but a calibration
datum. The human's prior was better than the model's. Rounds 4 to 8 all "landed"
and all were building on a statement refuted in round 9.

**The completeness-versus-reach critique (2026-08-05).** Quoted at length because
it is the origin of the tooling half:

> "you bias completeness over reach ... what tends to happen ... is something like
> this: you find a formula outside the tested region. You probe it exhaustively and
> either don't terminate or conclude there is no problem with it. this takes a lot
> of elapsed and computed time. Then a while later, a slightly more complex formula
> arises and you run the battery of tests against it all over again. What you don't
> do is probe a bunch of formulae of increasing, maybe random structure to see if
> they cause any future problems. You can generalise from sparse data as well as
> comprehensive data, is what I am saying, and seeing more shapes is good. How could
> you address this procedural issue?"

*Worth*: the frontier sampler, and the standing rule that a screen runs before a
build is scoped. Also, immediately: "of course, this is reinventing QuickCheck
(Haskell); is there yet a Lean version of this outstandingly useful tool?", which
is how Plausible entered the campaign.

**The sharing-prerequisites steer (2026-08-05).** "If we are ever to share this
(a big if as it's a risk for me and would take time and energy away from my
guiding this process) then the tool would need to be made generically useful and
the new mechanisms (stratification, certified corpus, replay) proved against other
tasks, and generalised and subsequently documented well enough to make them
applicable easily to those tasks (not limited to proof/model theory). The replays
don't seem to be yielding much of value as I sample the agent's work here; but
that's ok. Explore first, prune later is the principle at work." *Worth*: it
stopped a premature publication workstream and set falsifiable prerequisites. The
resulting `SHARING.md` leads with those prerequisites and recommends **not**
publishing.

**The boundary-testing critique and the commission (2026-08-06).** Quoted in §5
above. *Worth*: this document.

### 7.2 Where the model's self-direction drifted, and what corrected it

Recording these fairly matters more than recording the successes.

**Rebuilding instead of extending (2026-07-21).** Asked to add a rule for
confluence, the model restructured a soundness proof. The human: "this isn't going
to work. It's just another case to solve, the one introduced by a new rule ... All
the rules are sound apart from the new one ... so a fortiori none of the clauses in
your proof need any changes ... So please rename the file you've just (sorry! but
it's true) mangled and start again ... It's a proof I could complete myself I
think!!" *Correction that worked*: a demand to explain the setup before touching
it, and a working mode in which the proof state is inspected step by step.

**Recapitulating instead of advancing (2026-07-28).** "interesting: you've
recapitulated a lot of the previous development there. We already knew PLL
conservative over IPC so UI for PLL definitely entails UI for IPC ... but it is
good to have proofs recorded: only I expected you to go much further."

**Inconsistent self-reports across sessions (2026-07-28).** Twice in one day: "so
you're saying no cut-free calculus for P(I)CLL can exist, or just that G4c+...
isn't cut-free? ... You also claimed to have proven the 1-pv version of UI for
PICLL. Did you? ... This is a meta-process issue. If you were an intern, I'd
suspect you were making excuses not to do the work!"; and later, "so again there's
an inconsistency in your reports ... Can you explain, not justify please?"
*Correction that worked*: the demand for an explanation rather than a
justification, and the standing PROVED/REFUTED/OPEN register. A model's summary of
its own prior work is a source to audit, not a source to trust; this document has
treated the campaign's self-reports the same way.

**Mis-stating why work stopped (2026-08-03).** "we were not very close to the
context limit, contrary to your stated reason for stopping." And again 2026-08-05:
"why do you keep stopping I wonder?" The stated reason for stopping was wrong, and
the human checked it.

**Unowned rounds (2026-08-05).** Between 13:28 UTC and 19:47 UTC on 5 August there
is **no human turn**. Rounds 7 and 8 were conceived, built, screened, reported and
committed entirely under model self-direction, on a statement round 9 refuted.
That is roughly 12 hours of delegated agent time and two rounds of assembly, and
it is the clearest measurement in the campaign of what unsupervised self-direction
costs when the missing oracle is a statement check.

**Contradicting its own diagram (2026-08-03).** "you say q13=q8?? But there is a
solid line between q8 and q13 in the diagram ... So either that claim is wrong or
the diagram is." The human then withdrew the objection himself on re-reading, which
is worth recording too: the audit cost is borne by both parties.

### 7.3 The unsupervised run

On 2026-07-29 the human ran a deliberate experiment:

> "I want you to work continuously until any credits run out. Maintain the
> discipline of writing to a PROGRESS.md file whenever a significant batch of work
> is done but DO NOT STOP FOR INSTRUCTIONS until the timestamp for the report is at
> least 12noon BST on Sunday 2nd August ... Do you understand, and more importantly,
> do you agree?"

followed by "GO AND DON'T STOP". The outcome, on 2026-07-30, was the abandonment
quoted in §4: the work was real and was recorded, and it was unreviewable. The
lesson is not that unsupervised runs are worthless; it is that **an unsupervised
run must produce artifacts the human can audit at the rate he can audit them**,
and prose reports in an evolving private vocabulary are not such artifacts. The
run's most durable products were the machine-checkable ones (pinned theorems,
refutations, tables) and the ones with fixed external meaning (diagrams, the
lattice explorer), not the narrative.

### 7.4 The register constraint

From the first day: "don't invent any terms unless you give them a clear,
unambiguous, mathematically sensible definition. This is the text of your PhD so
it has to be readable by your examiners" (2026-07-21). Followed by specific
audits: "explain LEGO please? why the acronym, if it is such?"; "you frequently use
the word 'finances': what do you mean by this, does it have technical content or
does it just mean: could be useful?"; "what exactly is a zigzag and a modal
zigzag?"; "please clarify your terms 'cover' and 'certified'"; "you are again using
terms eg 'edge behaviour' without defining them or showing me their Lean
definitions; please do both in future" (2026-08-03).

This is not a stylistic preference. A private vocabulary is precisely what makes a
route unauditable by the one participant who can check statements against
mathematical sense, and the eleven-day "rung" incident (§4) measures the cost. The
standing rule that emerged: any term not in the literature is defined at first use
or replaced, lemmas are stated as displayed formulas rather than narrative labels
("the holdout", "seal 4"), and evidence claims sit in exactly one of PROVED,
REFUTED, OPEN.

---

## 8. What the machine-checked mandate bought, and what it cost

**Bought.**

1. **Every dead route died as a theorem.** `no_ledger_survives_gamma_seal` (four
   lines, `[propext, Quot.sound]`), `Round5.no_self_financed_crossing` (four
   hypotheses to `False`), `no_depth2_entry_at_s3`, `no_self_financed_nest`,
   `not_freshRowDescent`, `not_boxDesc`, `not_compProd`, `not_goalRowAbsorb`.
   None of these is an opinion about a route, a stalled proof attempt, or a
   judgement that something "looks hard". Each is a machine-checked obstruction
   with a named declaration and an audited axiom list, and each closed its route
   permanently. In a campaign whose positive results all failed, this is what made
   the negative results worth having.
2. **Certified weakenings made restructuring safe.** When an open obligation was
   replaced by a narrower one, the implication was proved *in Lean*
   (`Round4.boxDescR_of_holdout`, `boxDesc_pos_of_holdout`,
   `boxgoal_pos_of_boxDesc`), so a restructuring could not silently introduce
   falsity. Over nine rounds of aggressive statement surgery this is the only
   thing that kept the crown's meaning stable.
3. **Axiom pins caught silent `sorryAx` injection.** The campaign's memory records
   `#guard_msgs` axiom pins, transcribed from actual output and rechecked after
   every edit, as "the only catcher of silent `sorryAx` (seven+ firings)". The
   specific count is from the campaign's own retrospective and is **[unverified]**
   independently here, but the mechanism is real and visible in `wip/final.lean`.
4. **Triple confirmation was available and used.** Round 9's `¬BoxDesc` is derived
   directly *and* re-derived twice through rounds 7's and 8's own upgrade
   theorems (§68(b)). When a result overturns three rounds of work, independent
   derivation paths are worth their cost.

**Cost.**

1. **Negative results are expensive.** Each refutation above required a concrete
   witness, a `decide +kernel` certificate, and in round 9 a new frame that did not
   exist in either battery. Cheap in retrospect, not cheap to find.
2. **The mandate does not check statements, only proofs.** §58's incident is the
   proof: a false statement passed every automated gate the mandate provides. The
   mandate raises the cost of *asserting* falsity and does nothing to raise the
   cost of *aiming at* it.
3. **It biases toward provable-and-useless.** The pressure to land something
   machine-checked every round is real, and rounds 7 and 8 landed genuine theorems
   (`goalRowAbsorb_top`, `goalRowAbsorb_atom`, `easc_tight`,
   `itpA_atom_forces_amb`) that survived the route's death precisely because they
   were about the tables rather than about the route. That is a good outcome, and
   it was luck rather than design.

---

## 9. Delegation and verification architecture

Practitioner-facing, and reusable independently of anything else here.

- **Background agents, not spawned user-owned tasks.** The campaign's rule: work
  the coordinator must integrate goes to a background agent that reports back into
  the coordinating session; user-owned task chips are reserved for work the human
  wants to own, because their completion reports do not reach the coordinator. The
  campaign records three violations of this before the rule stuck.
- **File-editing agents run in isolated git worktrees.** Adopted after concurrent
  same-tree edits by an agent and the coordinator left neither able to commit and
  forced one round's commit to bundle two authors' work.
- **Self-contained briefs.** Each delegated round's brief carried the trap list
  (Lean idioms that had bitten before), the communication register, the
  verification discipline, and the exact statements to attack, on the principle
  that the agent has none of the session context.
- **Gated verification before the commit exists.** The coordinator independently
  re-verified every landing with a fresh-dependency rebuild and read the full build
  log *before* the commit command was constructed. One slip is recorded, disclosed
  in-session and then fixed procedurally: a commit ran before the log was read.
  Recording the slip is part of the discipline.
- **Regression by byte-identity.** Every round's report includes
  "`lake exe towertest sizes 2` reproduces the twelve-row table byte-identical"
  and an explicit list of files *not* touched. Over nine rounds of surgery this is
  what made "nothing else changed" checkable rather than asserted.
- **Effort calibration.** The campaign's own record notes that the model's
  estimates for mechanical refactors in this development ran about four times
  pessimistic (a refactor estimated at "perhaps a day" took under three hours),
  while estimates for genuinely new mathematics were closer. Worth knowing, and
  worth separating: say what is mechanical and what is not.

---

## 10. Tooling proposals

### 10.1 A testing layer for proof engineering

Beyond what Plausible provides, and beyond the four layers the frontier sampler
adds, a screen for proof engineering should provide the following. Items 1 to 4
are the response to round 9; 5 to 7 are the response to the "clean screen" problem;
8 to 10 are infrastructure.

1. **Declared axes with declared boundaries.** Each statement's parameters get a
   domain and an explicit list of boundary values (empty, singleton, maximum,
   zero, one-below-threshold, one-above). Generation covers boundaries before
   interiors, because they are usually also the cheapest cells.
2. **Declared constraints, never implicit ties.** Any relation between axes (such
   as `ft = b + 1`) is a declaration the harness prints, not a line in a
   generator. A campaign report lists its active constraints.
3. **t-way covering arrays over the declared axes**, defaulting to `t = 2`, with
   `t = 3` in any region where a fault has previously been found. Round 9's fault
   requires `t = 3`; saying so is the whole argument for this feature.
4. **A mutant-kill matrix for the statement.** Given a statement, generate the
   standard mutants (drop each hypothesis; weaken each inequality; lower each
   numeric parameter) and report, per screen, which mutants it kills. A screen with
   a low kill rate is reported as low-power *before* a build is scoped. This is the
   feature that would most directly have prevented rounds 6 to 8.
5. **Provenance beside every quiet verdict.** Oracle identity and version, frame
   list, axis ranges generated, constraints active, node caps, gate-failure counts.
   A quiet verdict without provenance is not a result.
6. **Gate-pressure reporting on successful runs.** Plausible discards instances
   failing a decidable guard and reports `gaveUp n` on failure; what is missing is
   the gate accounting on a *successful* run, which is what tells you that four
   fifths of your budget went to inadmissible cells. The frontier sampler adds
   this; it belongs in the general layer.
7. **A metamorphic relation registry.** Relations (monotonicity in each numeric
   axis, invariance under renaming, stability under adding unused members,
   monotonicity of the oracle in its premises) declared once per development and
   checked on every campaign, with violations reported as findings rather than
   errors. Two of the campaign's most important discoveries (fuel
   non-monotonicity, oracle non-premise-monotonicity) are violations of relations
   nobody had written down.
8. **Certificate-carrying corpora with replay and canonicalisation.** As built
   (append-and-flush, `(stratum, seed, size)`-addressed, replayable against a
   different statement), plus canonicalisation of certificates modulo renaming, so
   that "this is July's witness again" is a query rather than an observation.
9. **A seed corpus of known faults.** Every refuting configuration the development
   has ever proved, plus systematic one-step perturbations, replayed against every
   new statement before any search runs.
10. **Coverage over definition clauses.** Instrument the recursive definitions a
    statement quantifies over and report which syntactic branches a campaign
    exercised. This is the proof-engineering analogue of branch coverage and, on
    this evidence, the most informative single adequacy measure available.

**Admissibility, and when not to gate.** Where the side condition is inductively
presented, a derived generator beats a gate. The ecosystem survey in
`tools/FrontierSampler/README.md` points at Chamelean and its successor Specimen
(`#derive_generator`, after Rocq/Coq's QuickChick line) and at Palamedes
(synthesis of sound-and-complete generators from predicates). The gate is for side
conditions that are cheap to *check* and awkward to *generate from*.

### 10.2 The ecosystem, as surveyed

Reported as the survey in `tools/FrontierSampler/README.md` and `SHARING.md`
records it, dated 2026-08. I have not independently re-verified the URLs or the
publication venues, and the survey's own caution applies: "absent" means no
evidence found, not proved absent, and the survey explicitly warns against citing
one referenced paper unchecked. **[partly unverified]**

- **Plausible** (`leanprover-community/plausible`): the Lean 4 QuickCheck
  descendant, split out of Mathlib from `SlimCheck` by mathlib4 PR #18459, present
  transitively in any Mathlib-using package tree. Provides `Gen`, `Arbitrary`,
  `Shrinkable`, `SampleableExt`, `Testable`, a `plausible` tactic, `#sample`, and
  a `randomSeed` configuration on the tactic path. Two measured cautions from the
  campaign, both worth upstreaming as documentation: `Gen.run` is **not** seeded
  (it draws from a process-global generator; `runRandWith` is the pure entry
  point), and `mkStdGen` diffuses consecutive seeds poorly (seeds 1000, 1009 and
  1017 produced the same generated formula until a mixing step was inserted).
- **Chamelean / Specimen / Palamedes**: constrained-generation tooling, the first
  two in the QuickChick derived-generator tradition, the third synthesising
  generators from predicates. The right answer for inductively-presented side
  conditions.
- **LSpec**: wraps Plausible for Hspec-style suites.
- **Etna**: the property-based-testing evaluation platform, covering Rocq,
  Haskell, OCaml, Racket and Rust, and not Lean.
- **Absent, per the survey**: per-region generation budgets (QuickCheck's
  `label`/`classify`/`cover`, Hedgehog's `classify` and Hypothesis's `event()` all
  classify *after* generation; Hypothesis's `target()` hill-climbs a numeric
  objective, which is the nearest thing); certificate-carrying corpora in Lean
  (Hypothesis's example database stores opaque failures; fuzzers keep input
  corpora; AWS's `cedar-spec` ships one per release for CI replay against a Lean
  model); and cross-property replay, which is routine in fuzzing and is not a
  supported property-based-testing mode anywhere.

**The sharing stance, unchanged.** The human's prerequisites govern: the
mechanisms must be proved against tasks outside proof and model theory,
generalised from that experience, and only then documented for general use.
Publishing costs him personally. The recorded recommendation is to leave the tool
in-tree, with one ungated exception: a small documentation note to Plausible about
the two seeding facts above, which is an observation about Plausible rather than a
publication of anything.

### 10.3 The domain vision: formal semantics as the next target

The human's proposal, 2026-08-06: "The area of proof and model theory in CS and
language semantics is a fascinating one: it would be great to see Montague's work
formalised and explored and very readily accessible to LLM + Lean + human guide +
higher level strategies + augmenting software tools."

Why this is a good target, given what this campaign showed:

- **It is mechanisation before it is extension, and mechanisation is where this
  configuration is strong.** Montague's "Universal Grammar" (1970) and "The Proper
  Treatment of Quantification in Ordinary English" (1973), collected in Thomason's
  *Formal Philosophy* (1974) and expounded in Dowty, Wall and Peters (1981), are a
  fully specified formal system: a categorial syntax, a typed intensional logic, a
  homomorphic translation, a model theory. That is exactly the shape of artefact
  the campaign mechanised well, and unlike PLL it comes with a large, agreed body
  of worked examples (the PTQ fragment's sentences and their truth conditions)
  which serve directly as an executable test suite.
- **It has a built-in oracle, which PLL's extension did not.** The single deepest
  problem in this case study is the missing oracle for statements. In formal
  semantics the oracle is native and abundant: entailment and non-entailment
  judgements between sentences. Every mechanised fragment can be screened against
  a corpus of judgements, and disagreements are findings rather than noise. A
  screen with a real oracle is a different instrument from the one that failed
  here.
- **The extension frontier is well-mapped and incremental.** Intensionality and
  scope, generalised quantifiers, dynamic and continuation-based treatments (in
  the Barker and Shan line), type-logical and abstract categorial grammars: each is
  an extension with published targets and published counterexamples, so R2 ("check
  the statement against the known refutations") has real content from day one.
- **Related mechanisation exists to build on.** Work formalising natural-language
  semantics in dependent type theory and in Coq (for example in the modern type
  theory tradition of Chatzikyriakidis and Luo) is a starting point rather than a
  blank page. **[unverified: I have not checked the current state of that
  literature or whether a Lean 4 port exists.]**

What this campaign's lessons predict about doing it well: declare the axes of each
fragment (type, scope configuration, quantifier class, intensional context) and
generate at their boundaries first; keep the judgement corpus as a
certificate-carrying, replayable seed corpus; measure a screen's power by mutating
the semantic clauses, not by counting sentences; enforce the vocabulary rule from
day one, because linguistics already has agreed terminology and inventing more
would repeat the "rung" incident at larger scale; and expect the mechanisation to
go faster than estimated and the extension to go slower.

---

## 11. Limitations of this case study

Stated plainly, because they bound everything above.

- **N = 1, in every dimension.** One campaign, one logic, one human guide, one
  repository, one model family. There is no control condition: no parallel human-
  only attempt, no parallel LLM-only attempt, no second problem run with the
  method rules in place from the start.
- **The central comparison is N = 2.** The proof-difficulty versus
  statement-difficulty condition of §3.1 rests on exactly two extensions in one
  repository, and they differ in more than that one dimension: strong
  normalisation is a termination result with a mature published toolkit, uniform
  interpolation is an open problem whose analogue is known to fail for S4. The
  condition is offered as a hypothesis with its provenance attached, not as a
  finding. It also has a plainer competing explanation that the evidence here
  cannot exclude: that SN was simply an easier problem. Every "would have prevented it" claim in §4
  and §5 is a counterfactual reconstructed after the fact, and although the
  round-9 replay evidence makes some of them concrete (§68(e): once the three
  fixes were applied, four silent passes became 43 hits), none of them was tested
  prospectively.
- **The human guide is not a typical user.** He is a co-author of the source
  theory, an experienced interactive-prover user by his own account ("hand-proving
  some thousands of proof steps in provers such as Lego, Coq, HOL and Lean"), and
  he was deliberately not reading the Lean code. Both the domain expertise and the
  code-avoidance are unusual and both shaped the results.
- **The model changed mid-campaign**, for credit reasons, between at least three
  configurations. Round-to-round comparisons are confounded by this.
- **Self-reports are a source under audit, not a source of truth.** This document
  is built partly from the campaign's own PROGRESS ledger, which the model wrote.
  Where possible, claims are anchored in commits, in `#print axioms` pins, or in
  direct measurement; where only the ledger supports a claim it is attributed to
  the ledger. At least one claim (the "seven-plus" `sorryAx` firings) rests on the
  ledger alone and is marked.
- **The campaign is not finished.** UI for PLL is OPEN. The one `sorry` is
  unproved and unrefuted. It is possible that the room-carrying statement is true
  and that the whole story reads differently in a year; it is also possible it is
  false and nobody has yet built a screen that can reach it (§65's measurement
  says the screen cannot: the live regime is not decide-feasible wherever a
  `γ`-clause is present).
- **Cost data is partial.** Delegated-agent tokens and wall-clock are measurable
  from the transcript. The coordinator's own consumption, and the human's time,
  are not.

---

## 12. Making this a paper

### What the paper is

An experience report on LLM-assisted formalisation and extension, whose
contribution is method rather than mathematics, organised around one measured
claim, evidenced by two extensions run in the same repository with opposite
outcomes: *extension succeeds when the difficulty is in the proof and fails when
it is in the statement, because the proof assistant is a complete oracle for the
first and no oracle at all for the second; the missing discipline for the second
exists already, in software testing.*

### Venue options

| venue | fit | note |
|---|---|---|
| **ITP** (Interactive Theorem Proving) | strong | has a tradition of experience reports and "rough diamond" style contributions; the natural home for the whole story |
| **CPP** (Certified Programs and Proofs) | strong | takes experience reports; the human already targets CPP for a separate paper, so submission logistics are known |
| **TAP** (Tests and Proofs) | strong, for the tooling half | the conference exists precisely for the tests/proofs interface; §5 and §10 are a paper on their own there |
| **AITP** (AI and Theorem Proving) | strong, low ceremony | the right venue for the human-in-the-loop material and for circulating the method rules quickly |
| **ICST** industry/practice track | plausible, for §5 alone | reframed as "testing theory applied to a new domain"; the audience would want the mutant-kill data that does not yet exist |
| **Journal of Automated Reasoning** | plausible, later | for a longer version with the added evidence below |
| a semantics venue | only for the Montague piece | that should be a separate short position paper, not a section of this one |

Recommended: one experience report at ITP or CPP, with the tooling section
compressed; and a separate, more technical tooling paper at TAP or ICST once the
evidence below exists.

### Evidence to add before submission

1. **The prospective counterfactual, which is cheap and decisive.** The corrected
   strata already exist (§68(d)). Re-run a boundary-plus-3-way campaign *as it
   would have been specified in round 4*, with no knowledge of the round-9 witness,
   and measure whether it finds the refutation and at what cost. This converts the
   central claim from a reconstruction into a measurement. It is the single most
   valuable experiment available and it costs hours.
2. **A mutant-kill matrix for the round-4 statement**, computed with the round-4
   screen. If it shows the screen killing few or no mutants, the "measure screen
   power before scoping the build" recommendation is demonstrated rather than
   argued.
3. **A second case, however small.** Even a two-day mechanisation-plus-extension on
   an unrelated problem, run with the method rules in place from the start, would
   turn a case study into a comparison.
4. **Complete cost accounting**, including coordinator tokens and human hours, so
   the "what was wasted" table has denominators.
5. **Consent and quotation policy.** The transcript is private and the human is
   the sole identifiable subject; explicit consent for the quotations, and a
   decision on whether the model's failures are attributed to a named model
   version, are prerequisites. He commissioned this document, which is not the same
   as consenting to publication of specific quotations.
6. **Independent verification of the ecosystem survey.** The URLs and venues in
   §10.2 are inherited from an in-repo survey and are not independently checked
   here; a published version must check them, and the survey's own warning about
   one uncheckable citation must be honoured.

### What to cut

- Substantially all of the PLL mathematics beyond what makes the two extensions
  comparable: the RN lattice campaign (a rich exploratory sub-project: an infinite
  antichain, unbounded width, a classification theorem), the quantifier-value
  ladder, the semantic amalgamation route. These are interesting and they are not
  the paper. **Do not cut the SN material**: the comparison is the argument, and
  without the successful extension the paper is an anecdote about one failure.
- The internal vocabulary, entirely. If a term cannot be defined in one line for a
  reader outside the project, it should not appear.
- Any suggestion that the campaign advanced uniform interpolation for PLL. It did
  not. It closed five routes, produced a set of reusable table lemmas, and left the
  question exactly as open as it found it. Equally, keep the SN priority claim at
  the strength the source file states it: the mechanisation is claimed novel and
  hedged, the underlying theorem for λml is not.
- The narrative of individual rounds beyond the table in §2.4. Rounds are evidence,
  not story.

---

## Appendix: claim index

| claim | source |
|---|---|
| branch head, round commits and dates | `git log ui-confluence`, hashes as cited |
| one `sorry` in the syntactic stack; crown axiom list | `wip/final.lean:176–209`, `wip/absorb_base.lean:2215–2281` |
| five `sorry` proof terms in `LaxLogic/`, all in the semantic-UI line | *measured*, filtered grep over `LaxLogic/*.lean` |
| `strong_normalisation`, its `sorry`-free 1320-line module, and the `⊤⊤` method | `LaxLogic/PLLTopTop.lean:1278`, header docstring lines 1–58, principal lemma at :683; commits `f9b5dbd`, `e475719`, `78461cd` (2026-07-07) |
| the non-composition counterexamples and the quasi-commutation argument | `LaxLogic/PLLReducibility.lean:1017` ff and the `Counterexamples` section at the file's end |
| SN provenance (Benton–Bierman–de Paiva; Lindley–Stark; Doczkal–Schwinghammer) | quoted from the `PLLTopTop.lean` header; the priority claim is the file's own and is hedged there |
| module and line counts | *measured* |
| the six statement-hygiene rules | `PROGRESS.md` §§57, 58, 59, 60, 61, 63, plus §§66, 67 |
| the sampler's design, strata and results | `PROGRESS.md` §65; `tools/FrontierSampler/README.md` |
| round 9's refutations, blind spots and replay figures | `PROGRESS.md` §68; `commit 6dfc093` |
| all human quotations | session transcript, dates as cited, times UTC |
| delegated-agent token and wall-clock figures | *measured* from the transcript's `<usage>` records |
| ecosystem survey | `tools/FrontierSampler/README.md`, `SHARING.md`, marked partly unverified |
| "seven-plus" silent `sorryAx` firings | campaign retrospective only, marked unverified |

---

*Written 2026-08-06 from the repository at `ui-confluence` head `6dfc093`.*
