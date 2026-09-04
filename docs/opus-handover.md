# Handover instructions for delegated proof agents (Opus-grade)

*A **strategical** — following M. Fairtlough's coinage: a strategy for
combining and manipulating strategies. The individual strategies below
(§2) are proof-work moves; the strategical (§3) is the policy for
choosing, sequencing, and escalating them. Refined from the runs of
2026-07-12, in which an Opus agent produced the sorry-free
`uniform_interpolation_IPC` (2,654 lines, first-attempt clean kernel
audit) from a brief built this way.*

Audience: a capable but non-frontier model (Opus, sometimes Sonnet)
receiving a self-contained brief for Lean 4 proof work in this
repository. Everything here is also a checklist for whoever *writes*
that brief.

---

## 1. The governing principle: define "done" as a machine-checkable artifact

Every brief names one **acceptance test** that the compiler, not the
agent, adjudicates — typically a pinned axiom audit:

```lean
/-- info: 'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Foo.bar
```

A passing build then *is* the result; the agent's prose report is
commentary. Corollary: the orchestrator independently re-runs the
acceptance test before committing anything. Never accept a claim that
has a checkable form unchecked.

## 2. The strategy inventory

### S1 — Top-down decomposition by sorry-extraction (the default)

Work **top-down from the target theorem**, not bottom-up from
imagined lemmas. Where a step resists:

1. Leave `sorry` at the stuck point and make the file compile.
2. Read the goal state at the sorry; **freeze it as a named lemma**
   whose hypotheses are exactly the facts in scope that the step
   appears to need (the *constraint extraction*).
3. Replace the `sorry` with `exact that_lemma …` — the elaborator now
   enforces that the extracted statement is *sufficient*.
4. Prune hypotheses one at a time until the proof of the consumer
   breaks — this establishes *necessity* and yields the weakest
   workable statement.
5. Normalize and unify the extracted lemmas across sorry sites (on
   this project, six extraction sites repeatedly collapsed to two or
   three genuinely distinct lemmas).
6. Recurse on each extracted lemma; adjudicate it (S3) before proving.

This converts proof search into *lemma-statement design* while the
file compiles at every step, and it localizes all risk into displayed,
testable statements. The entire stabilization interface of the UI
development was produced this way.

### S2 — Clone-and-thread under statement freeze

To prove a *variant* of an existing large proof (extra hypothesis, new
invariant, restricted fragment): **never edit the original**. Clone it
append-only under a new name, add the hypothesis, recompile, and let
the error list enumerate exactly the sites the new hypothesis must be
threaded through or discharged at. Patch only those. Evidence: the
~990-line `itp_stab_aux_bf` clone needed real work at a few dozen
enumerated sites and nowhere else; the four ◯-flavoured obligations
died wholesale from the new hypothesis rather than site-by-site — the
compiler found that simplification, not the planner.

### S3 — Adjudicate before proving

Every candidate lemma is tested before any proof attempt, using
whichever oracle applies:

- **finite-algebra evaluation** (Heyting algebras + nuclei; sound for
  the logic) for refutation of general laws — compare *sequent* forms,
  size-gate every evaluation;
- **decidable instances / bounded search with a soundness
  certificate** for per-instance claims;
- the repository's `laxrun` CLI for the packaged harnesses.

Report every claim in exactly one register: **PROVED** (machine-
checked, where) / **REFUTED** (witness, where) / **OPEN** (searched
what space, found nothing). A refutation is a success: it is cheaper
than a failed proof campaign by orders of magnitude.

### S4 — Map, then execute (scout/executor split)

For work inside large existing proofs, a **scout pass** first produces
the seam map: the dependency spine to the target with `file:line` for
every link, the count and location of sites needing surgery, the
interface deltas of any alternative route (shifted constants, extra
hypotheses), and what is mechanical vs bespoke. The scout runs under a
**no-new-mathematics rule**: if the plan turns out to need an unproved
fact, *stop-and-report is a successful outcome* — the report names the
missing fact precisely, and that becomes the next brief. The executor
then runs against the map. (The IPC crown took exactly one
scout-stop + one executor run.)

### S5 — Separate the bespoke core from the mechanical tail

Identify up front which deliverable pieces are bespoke mathematics and
which are mechanical (clones with N site-swaps, wrapper corollaries,
audit lines). Do the bespoke core first; the tail is then low-risk
volume, and an honest partial that lands the core is worth banking.

## 3. The strategical: combining the strategies

- **Sequence**: scout (S4) → adjudicate statements (S3) → bespoke core
  by S1/S2 → mechanical tail (S5) → acceptance test (§1) →
  orchestrator verifies independently and commits. Commit at every
  green intermediate state (append-only makes this safe) — partial
  work is *banked*, never stranded.
- **Escalation ladder**: Sonnet for transcription, sweeps, tooling,
  and inventory-grade triage; Opus for mapped proof engineering and
  human-facing write-ups; the frontier model only for unmapped
  problems (finding the map, designing statements against a hostile
  search space). Calibration from 2026-07-12: the mapped IPC job cost
  ~330k Opus tokens in 53 minutes against a ~500–800k frontier
  estimate — mapping first bought a ~3× saving. A structured partial
  from a cheaper model converts an expensive restart into a cheap
  *completion pass*; always prefer resuming a partial to restarting.
- **Failure conversion**: a stalled or dead agent is resumed from its
  transcript with a state-aware continuation brief, not respawned
  cold. An agent that stops without acting gets one direct "execute
  now, tools not narration" nudge.
- **Pre-authorized decisions**: the brief lists the judgment calls the
  agent may take alone (e.g. "if the shifted constant cannot be
  absorbed, weakening the new lemma's threshold is acceptable — take
  the strongest provable form and note it") and the calls it must
  stop-and-report instead (any new unproved mathematical fact). This
  is what makes a weaker model safe on real proofs: the discretion
  boundary is explicit.

## 4. The brief template (checklist for the orchestrator)

A brief that follows this template is what made the 2026-07-12 runs
land. In order:

1. **Mission** in one paragraph, with the acceptance test verbatim.
2. **State**: the dependency spine with `file:line` anchors; site
   counts; interface deltas of the intended route. Anchors beat
   prose — the agent greps, it does not read whole files.
3. **Hard rules**: append-only; statement freeze on all existing
   lemmas; which files may be touched; no `sorry` in new material;
   no git (the orchestrator commits); no new mathematics beyond the
   named facts (else stop-and-report).
4. **Pre-authorized decisions** and their bounds (§3).
5. **Build recipe** with measured iteration cost (here: the wip chain
   script, ~133 s full, ~8 s for the biggest single file after the
   v4.31 toolchain bump — iteration is nearly free; say so, it changes
   the agent's economics). *Tell the agent to verify import order and
   private-name visibility from the files rather than trusting the
   brief* — briefs have gotten both wrong.
6. **Discipline**: output discipline (grep + line-range reads ≤150,
   incremental appends ≤200 lines, short messages — protects the
   output-token cap); synchronous finish (no background children, no
   monitors); a timebox with the instruction that *an honest partial
   fully reported beats a complete run never reported*.
7. **Report spec**: what the final message must contain (statements
   as landed, the audit line verbatim, per-file compile times, every
   deviation taken).

## 5. Repository quick facts for briefs

- Toolchain `leanprover/lean4:v4.31.0` + Mathlib `v4.31.0`; library
  `lake build` ~2 min cold, seconds warm.
- wip proof chain: `scripts/build_wip_chain.sh` (order: absorb_base →
  adequacy → packaging → indiff → spaceindiff → final; oleans default
  `.lake/wipdeps`, override with `WIPDEPS`).
- CLI harnesses: `scripts/laxrun.sh {help,timing,search,quant,zoo}`
  (native binary).
- Audit idiom: `#guard_msgs in #print axioms <thm>` pinned in-file.
- House rules that never relax: `LaxLogic/*.lean` sorry-free; `wip/`
  may carry sorries by design; explicit-refspec pushes only; every
  `gh pr` command carries `--repo fairflow/lax-logic-in-lean`; agents
  never push to `main`; nothing is ever sent to anyone external —
  drafts only, Matthew sends.
