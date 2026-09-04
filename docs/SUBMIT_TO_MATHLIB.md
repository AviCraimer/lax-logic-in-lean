# Formal-Verification PR Playbook — for Claude Fable 5

**Status:** DRAFT / INTERNAL. Do not publish to any public forum, and do not
contact any paper author, until the human operator gives explicit go-ahead.
(See "Courtesy / disclosure hold" at the end.)

**Prepared from:** the "Rethlas+Archon Solved A Conjecture with Formal
Verification" thread on the Lean Zulip and the artefacts it links to.

---

## 0. What this document is (and what it is NOT)

The source material documents a **repeatable pipeline for producing a
machine-checked Lean 4 result and having it independently verified**, plus a
**benchmark-submission process** for putting a verified result on a public
leaderboard.

It does **not** document the process for merging a contribution into the
`leanprover-community/mathlib4` repository. In fact the paper explicitly notes
that the generated code is stylistically far from mathlib conventions (naming,
`have`-heavy structure, un-generalised auxiliary lemmas) and that aligning it
for upstream contribution "would require non-trivial human effort." Treat a
real mathlib PR as a **separate, later** step that this pipeline feeds into,
not something the pipeline performs.

**Relevance to our own work (modal / Lax / computational logic):** none of the
sources touch modal logic or the Studia Logica result you have in mind. The
methodological hook that *is* transferable is the verification philosophy: a
formal kernel check catches errors "even within the rigorous peer-review
processes of top journals," and the informal verifier is specifically told to
scrutinise skipped steps and *apparently unused hypotheses* — exactly the
failure mode of a broken hand proof. That is the legitimate bridge to our
Studia Logica question; anything stronger needs a human to assert.

---

## 1. Actors / architecture (the "two-agent" model)

- **Rethlas** — informal reasoning agent. Two sub-agents (generation +
  verification) in a loop. Equipped with reasoning "skills" (build toy
  examples, build counterexamples, search results, decompose into subgoals,
  direct/recursive proving, identify key failures) and a semantic theorem
  search engine (**Matlas**, over arXiv statements).
- **Archon** — formalisation agent. Dual sub-agents: a **Plan Agent** (fresh
  context, decomposes + guides) and a **Lean Agent** (executes formalisation in
  a constrained scope). Tools: **LeanSearch** (Mathlib retrieval), Lean LSP MCP
  (compiler diagnostics), web search, persistent memory, and a **Review Agent**
  at session boundaries to detect multi-session stalls.
- **Comparator** — the trusted external verifier (see Stage 5).

For our own agent, the mapping is: Fable-5-as-Rethlas produces an informal
proof/refutation; Fable-5-as-Archon formalises it; Comparator is the neutral
referee.

---

## 2. Stage-by-stage pipeline

### Stage A — Frame the target as a single formal statement
- Pin down one top-level theorem. In the reference project everything reduces
  to one declaration (`main_theorem`) living in a short, self-contained
  `Challenge.lean` whose only job is to state the claim (proof body = `sorry`).
- Principle: *a reviewer should be able to trust the statement by reading one
  file, and trust the proof by running one command.* Design for that.

### Stage B — Informal proof / refutation (Rethlas role)
- Broad search → focused search → generate 2–4 attack plans → attempt them →
  on failure, extract "key failures" and regenerate.
- Capture the informal argument as a Markdown blueprint that lists every cited
  theorem and every logical step (the repo keeps this as
  `INFORMAL_RAW_OUTPUT.md`, with a human-polished PDF alongside).
- Run the informal **verification** sub-agent: check each step, flag hand-wavy
  jumps, and test whether "unused" hypotheses hide an omitted argument.
  *(This is the step most relevant to auditing a suspect published proof.)*

### Stage C — Scaffolding (Archon role, phase 1)
- Split the blueprint into modules, write theorem signatures, drop `sorry` at
  each obligation. Topic-based file layout (see the reference repo's
  `Anderson/…` tree: `Basic.lean` for definitions, one folder per major
  external result, `Main.lean` for final assembly).

### Stage D — Proving (Archon role, phase 2)
- Lean Agent discharges `sorry`s; when stuck it returns diagnostics to the Plan
  Agent, which re-strategises. Independent obligations can be proved in
  parallel.
- Use LeanSearch first to decide *whether a lemma already exists in Mathlib*
  before formalising from scratch. Where Mathlib lacks infrastructure, look for
  an alternative route (the project famously swapped a Krull-domain argument for
  a Kaplansky-criterion one).

### Stage E — Verification & polish (Archon role, phase 3)
- Confirm the whole project builds and that there is **no** `sorry`, no stray
  `axiom`, and no other escape hatch.
- Quality pass: extract reusable lemmas, reduce proof size. (Note the known
  limitation: output tends to be verbose and off-convention — budget human
  cleanup if upstreaming.)

### Stage F — Independent verification with Comparator (the "proof-checking framework")
This is the crux the thread is really about. Comparator gives three guarantees:
the submitted proof proves *exactly* the `Challenge.lean` statement; it uses
only permitted axioms (`propext`, `Quot.sound`, `Classical.choice`); and it is
accepted by the Lean kernel.

Setup (versions must match the project's `lean-toolchain`):
1. Install Lean via `elan`, matching the repo toolchain.
2. Build the three external tools, each checked out to the **pinned commit**
   (not `@main`, not a tag): `landrun` (sandbox), `lean4export` (olean → text
   exporter), `comparator` (verifier).
3. `lake exe cache get`, put the binaries on `PATH`.
4. Run: `lake env comparator config.json`.
- Optional stronger assurance: enable the **nanoda** kernel (independent Rust
  reimplementation) via `"enable_nanoda": true` for a two-kernel cross-check.
- Common gotcha: an `incompatible header` error on `Challenge.olean` means a
  toolchain/olean mismatch or a stale `.lake` artefact — **not** a proof
  problem. Rebuild the tools at the pinned commit and clear `.lake/build`.

### Stage G — Package the repo for review
- Root files: `Challenge.lean` (statement), the proof folder, `config.json`
  (pre-set for Comparator), informal blueprint, and a `README` that tells a
  verifier the two-step "read one file / run one command" protocol.

### Stage H — Optional: submit to the lean-eval benchmark leaderboard
This is a *separate* public-scoring route (not mathlib), if we ever want a
neutral, logged verification of record:
- **Author path** (adding a new problem): put the statement in a shared
  `LeanEval/…` module tagged `@[eval_problem]`; add a one-file-per-problem TOML
  manifest under `manifests/problems/<id>.toml` (keys: `id`, `title`, `test`,
  `module`, `holes`, `submitter`, + optional `source`/`notes`/
  `informal_solution`); validate with
  `lake exe lean-eval validate-manifest` and `check-problem-build`; open a PR
  (CI regenerates the `generated/` workspaces).
- **Solver path** (proving an existing problem): `lake exe lean-eval
  start-problem <id>`, write only `Submission.lean` (+ `Submission/…`), never
  edit `Challenge.lean`/`Solution.lean`/`config`, run `lake test` locally
  (needs landrun + lean4export + comparator on PATH), then open a **submission
  issue** on `leanprover/lean-eval-submissions`. Results are recorded, sticky,
  and the source tarball is retained age-encrypted in a private audit repo —
  **submitting agrees to that retention**, so treat it as an explicit consent
  step requiring human sign-off.

---

## 3. Cost / effort reference points (for planning)
- Reference project: ~19–20k lines of Lean across ~42–44 files, ~80 hours agent
  runtime; compute via 3× Claude Code Max seats, ~70% of each weekly quota
  (headline budget $600; effective usage ~$105).
- Only human intervention reported: downloading paywalled reference PDFs and
  dropping them in the project directory. No mathematical judgement required
  from the operator during the run.
- Human-guidance ablation: supplying a Markdown proof blueprint at a stuck point
  cut time to completion by ~70% — so a good informal blueprint is high-leverage.

---

## 4. Verification / trust checklist (copy into any PR description)
- [ ] `Challenge.lean` states the intended claim and nothing weaker.
- [ ] Whole project builds; zero `sorry`, zero non-standard `axiom`, no escape
      hatches.
- [ ] Comparator run passes (`lake env comparator config.json`).
- [ ] (Optional) nanoda second-kernel cross-check passes.
- [ ] External tool commits are the pinned SHAs; toolchain matches.
- [ ] Human has read and signed off on the top-level statement's semantics.

---

## 5. Links & references
**Zulip thread**
- Topic: https://leanprover.zulipchat.com/#narrow/channel/583339-AI-authored-projects/topic/Rethlas.2BArchon.20Solved.20A.20Conjecture.20with.20Formal.20Verification/with/608266318
- Kevin Buzzard's message in-thread: confirms Comparator is easy to run on the
  repo and that he independently ran it — "Lean default kernel accepts the
  solution."

**Paper**
- arXiv (v2, revised 30 May 2026): https://arxiv.org/abs/2604.03789
- Blog (full main text): https://frenzymath.com/blog/conjecture/

**Code**
- Formalization results: https://github.com/frenzymath/Anderson-Conjecture
- Rethlas (informal agent): https://github.com/frenzymath/Rethlas
- Archon (formal agent): https://github.com/frenzymath/Archon

**Verification / benchmark infrastructure**
- lean-eval (problem set + comparator integration): https://github.com/leanprover/lean-eval
- lean-eval-submissions (submission pipeline + results store): https://github.com/leanprover/lean-eval-submissions
- Comparator: https://github.com/leanprover/comparator
- lean4export: https://github.com/leanprover/lean4export
- landrun: https://github.com/Zouuup/landrun
- nanoda (independent kernel): https://github.com/ammkrn/nanoda_lib

**Underlying mathematics (for the reference project, not our topic)**
- D. D. Anderson, Problem 8a, in Cahen–Fontana–Frisch–Glaz (eds.), *Open
  Problems in Commutative Ring Theory*, Springer 2014:
  https://link.springer.com/chapter/10.1007/978-1-4939-0925-4_20

---

## Courtesy / disclosure hold
If this pipeline is later pointed at the suspected-broken Studia Logica proof:
the formal refutation and any statement of "the published proof is flawed" must
be shown to the paper's author privately **before** any public posting (Zulip,
arXiv, mathlib, leaderboard, or otherwise). Nothing goes public in any forum
until the human operator confirms the author has been notified.