# Note for the next session — the dangling threads

*Written 2026-08-07 at Matthew's request, at the end of a session that had
grown beyond reasonable bounds. It is a **note to whoever opens the next
session**, human or model: what is live, what is shelved, what is decided,
what is waiting on a decision that is Matthew's to make.*

**Companion documents.** `HANDOFF.md` (repo root) is the standing handover —
project, invariants, pitfalls, verification commands; §10 there points here.
`docs/calculus-map.md` is the **summary of results**: which of the seven proof
systems each result belongs to, and whose it is (ours vs Fairtlough–Mendler
1997). Read the calculus map before asserting provenance about anything below.


**Added 2026-08-17 — FRJ◯ thread (PAUSED).** Fiorentini–Ferrari FRJ(G) + ◯
on branch `claude/frj-redevelopment-69005f`: ◯-free completeness PROVED
(`FRJ/Minimal.lean`, `frj_iff_not_IPL`); the ◯-case paused at the
conditional `completeness_of_supply` — the two supply kernels are OPEN and
were never extensionally attacked.  See the final § of `HANDOFF.md`
(2026-08-17) and, on the branch, `docs/frj-w4.md`.  First moves if resumed:
extensional attack on the supply statements; the TOCL 2020 §6 organisation
read at source.

---

## 0. Repo state

* Branch `main`, at `925bc10` (`ui-confluence` was merged into `main` on
  2026-08-06 — there is no live feature branch).
* `lake build` green. The `#guard_msgs` blocks are the golden tests.
* **Sorries, complete list.** In `LaxLogic/`: five, all in the semantic-UI
  extension line — `PLLSemUIChar.lean:322,327`, `PLLSemUILayered.lean:827`,
  `PLLSemUIHenkin.lean:341,352`. In `wip/`: one that matters,
  `cascade_boxgoal_pos` at `wip/absorb_base.lean:2281` (the UI tower's
  kernel), plus two routine ones in `wip/G4conf.lean:285,292`.
* `uniform_interpolation_IPC` is **sorry-free**. The crown
  `uniform_interpolation_PLL` (`wip/final.lean`) still carries `sorryAx`
  through that one kernel — it is a statement, not a theorem.
* `wip/` holds ~350 files and wants pruning at some point. Not urgent; nothing
  there is on the main build path except through the `wipshared` glob in
  `lakefile.toml`.

Verification, before changing anything:

```bash
cd /Users/matthew/Lean/Sources/lax-logic-in-lean && lake build
```

---

## 1. Uniform interpolation for PLL — **shelved**, with one live idea

**Where it stopped.** Nine rounds of assault (PROGRESS §§57–68) ended on
2026-08-06 in a definitive negative: the *room-free* route is **REFUTED**,
kernel-checked at `Γ = []`. `BoxDesc` (round 4), `CompProd` (round 7) and
`GoalRowAbsorb` (round 8) each fall directly, and `¬BoxDesc` is re-derived
twice more through rounds 7's and 8's own upgrade theorems — triple-confirmed
by independent paths (`wip/round9pin.lean`).

What survives is the *room-carrying* statement `cascade_boxgoal_pos`, whose
hypothesis is

> `defect S Γ * ((jumpGoals S).card + 2) ≤ b`  ("the room")

and the refutation is strictly **sub-room** (`vS_room = 35`, refuted at
`b = 1`), so it is untouched. That is the **third** time the room has turned
out to be the sole excluder of every known countermodel.

**Why it is shelved rather than continuing.** §65's measurement, now a
theorem (`wip/frontier_pin.lean`): a γ-clause forces `J ≥ 2`, hence room ≥ 4,
hence fuel ≥ 5, hence interpolant tables of 10⁵–10⁶ nodes — past what
`checkB` can decide. So the surviving statement's live regime **cannot be
screened**, in either direction. It has to be *built*, and that is a large
ledger-carrying construction with no external evidence available while it is
built. Combined with the round-9 lesson (three independent screen blind spots
— see `probe-strategy-reach-vs-completeness` in memory), stopping was right.

**The live idea (Matthew, 2026-08-07): go at the confluent class, and look
for failure modes there.** Two observations, held apart because they cut
opposite ways:

* **It may simplify.** On mutually confluent models the `∀∃` clause for `◯`
  collapses to bare possibility — `w ⊩ ◯φ ⟺ ∃u, Rₘ w u ∧ u ⊩ φ` — so `◯`
  becomes an ordinary diamond and the promise bookkeeping that *was* the wall
  (need `2d`, have `2d−1`) plausibly evaporates. The full argument is
  `docs/confluent-ui-plan.md` §3, with the one new obligation named there:
  the amalgamated model must itself be confluent (`amalgam_confluent`).
* **It may harden.** Adding an axiom means more sequents to interpolate — but
  also more interpolants available to do it with. Which effect dominates is
  not known and, as Matthew put it, there is no way to know without trying.

**Caveat for whoever picks it up — read this before writing any calculus.**
The obvious calculus for the job was already tried and partly refuted. `G4cf`
= `G4c` + an analytic `distL` rule (`wip/G4conf.lean`), and
`wip/g4confGap.lean` **kernel-refutes** both its completeness-without-cut and
its cut admissibility (`g4cf_complete_refuted`, `[propext, Quot.sound]`): a
`NoObOr` invariant collapses `G4cf` to `G4c` on the cut-necessity sequent's
cone. Soundness there is sorry-free; the two remaining sorries are routine.
So the confluent attack is not "port the calculus and go" — either it runs
semantically (the amalgamation route, where the promise financing is the
thing that dissolves), or it needs a genuinely different calculus.

**Suggested first move, if resumed**: *refute* before building. Hunt failure
modes of the interpolant construction restricted to confluent models, where
the model check is cheaper and the countermodel emitter still works. A
confluent counterexample would settle the question negatively at a fraction
of the cost of the positive build; no counterexample would be the first real
evidence for the dissolved-wall claim.

---

## 2. Testing: the frontier sampler, catpart, and what a testing layer should be

Three separate objects, one theme — the session's methodological finding is
that **the failures were statement failures, and statement failures are a
testing problem, not a proving problem**.

**(a) The frontier sampler** — `wip/frontier.lean`, `wip/frontierCore.lean`,
`wip/frontier_pin.lean`, corpus at `wip/frontier_corpus.txt`; generic core
extracted to `tools/FrontierSampler/`. Built 2026-08-05 in answer to
Matthew's critique that I bias completeness over reach. 948 admissible cells
over 19 strata, constructive generation, countermodel-only triage. Its real
yield was a **measurement that became a theorem** (the γ-clause infeasibility
above), not a refutation.
*Decision recorded in `tools/FrontierSampler/SHARING.md`: **do not publish**.*
Matthew's prerequisite governs — the mechanisms must earn their keep on a
task outside proof and model theory first. Leave it in-tree.

**(b) catpart** — Matthew's own 1990s Sheffield category-partition tool, in
SML. **It runs again**, byte-identical output after ~30 years, under SML/NJ
110.99.9: `tools/catpart-ref/` + `BUILD.md`; the archaeology is
`docs/catpart-archaeology.md`; a Lean 4 port is *designed but not built* in
`docs/catpart-lean-design.md`. Three edits to `catpart0.2.lex` were all it
needed (`String.str`, `List.foldr`, `#"0"` — the SML basis moved under it).

**(c) The layer that does not exist.** Plausible is Lean's QuickCheck
descendant (in-repo via mathlib) and covers random generation only. Absent in
Lean, and wanted here: boundary-value generation, category-partition
selection, admissibility gating, mutant-kill matrices, metamorphic relations,
certificate corpora, coverage over *clause branches* of a definition. Round
9's fault needed a 3-way interaction (empty context × untied fuel × missing
frame), so pairwise would not have caught it — but branch coverage over the
`itpA`/`itpE` clauses would have, and fault seeding was one edit away.
*Standing rule adopted*: each round's residue shape defines the next sampler
stratum, and it runs **before** any proof build is scoped.

**Open decisions** (Matthew's): whether the Lean catpart port gets built;
whether the testing layer is developed as a thing in its own right or stays a
by-product; whether either is ever published.

---

## 3. The report on this development — successes, failures, and failure modes

`docs/llm-formalisation-case-study.md` (13,608 words) + a one-page outline.
Commissioned 2026-08-06. Matthew's view, verbatim in substance: *the work is
not publishable except as a case study in how to, and how not to, work with
an LLM on formalising a body of mathematics and trying to extend it.*

The central measurement, independently verified: **5 real sorries in 104
modules / 50,238 lines, all five in the semantic-UI extension line**.
Mechanising established results (strong normalisation, completeness,
decidability) is clean; *extending* is where it goes off track. §2.2 records
the counter-case, where extension **succeeded** — full strong normalisation
of the interleaved reduction via Lindley–Stark `⊤⊤`-lifting, 1,320 lines
sorry-free, after five machine-checked counterexamples proved the two
fragments do not compose and thereby forced a semantic method.

The thesis is therefore not "extension is hard" but the **condition**: when
the difficulty is in the *proof* (obstruction machine-checkable, technique
locatable), the LLM + Lean + guide configuration is strong; when the
difficulty is in the *statement*, it is weak without external testing
discipline.

Evidence gaps are stated in the document and are real: N = 1 everywhere, no
prospective counterfactual, no mutant-kill data, and a consent/quotation
policy would be needed before any of the human-in-the-loop record is
published. **Open decision**: whether this becomes a paper, and if so where.

---

## 4. The `omega` / `⊥` issue, and the Zulip post

Two different things that keep getting bundled.

**(a) The `omega` bug** — `docs/omega-issue-draft.md`, prepared 2026-08-03,
**not yet filed**. `omega`'s fact collector has no case for `False`, so a
hypothesis `h : False` does not close the goal, `_ ∨ False` is dropped
wholesale, and — how we met it — `p → False`, the *unfolding* of `¬p`, is
silently dropped although `¬p` is consumed. Root cause localised to
`MetaProblem.addFact` in `Lean/Elab/Tactic/Omega/Frontend.lean`. MWE verified
with the bare `lean` binary, no imports, on 4.31.0 / 4.32.1 / 4.32.2; pinned
here with `fail_if_success` in `wip/omegaFix.lean`, so a repaired toolchain
will announce itself. Workaround in use: `omega!`.
*Next action: file it at `leanprover/lean4`.* It is ready; it needs an
account and a decision to post, both Matthew's.

**(b) The Zulip post** is a *publication* question, not a bug report, and it
is gated. The only ungated piece is a small note to **Plausible**: `Gen.run`
draws from the process-global `stdGenRef` (so runs are not replayable) and
`mkStdGen` diffuses consecutive seeds poorly — measured here, seeds 1000,
1009 and 1017 produced the same formula — plus a pure `Gen.runWithSeed`.
An hour's work, useful to everyone, commits nobody to anything else.

---

## 5. The belief paper — runs in a parallel session

`docs/belief-paper-draft.md` (+ `belief-applications-draft.md`,
`belief-paper-selection.md`, `belief.bib`). PLL as the logic of idealised
evidential belief, with an argument for constructivism. Target: CPP 2027,
due 10 September 2026.

**What this session generated for it and has not yet been copied across** —
Matthew's framing: *the space between the total sceptic and the total
believer is vast, even in the closed fragment, and only through
constructivity*:

* the ladder of logics with **exact cardinalities** of the closed fragment —
  PLL infinite, PLL + linearity exactly **6**, PLL + excluded middle exactly
  **4**, PLL + `¬◯⊥` exactly **2** (`wip/linear.lean`, `wip/classical.lean`,
  `varfree_exactly_six`, `varfree_exactly_four`);
* the collapse of RN(◯,{}) under `¬◯⊥`, which is what makes the point sharp;
* the strict `◯`-depth hierarchy (`wip/depth*.lean`);
* the visibility results (`wip/visible.lean`).

**Coordination note**: that session and this one both edit `docs/`. Whoever
resumes should check `git log` before writing there.

---

## 6. Michael, and the Q○.K work

The conversation with Michael Mendler has taken over the last few days. It
lives in the **private** sibling repository `~/Lean/Sources/qkcd` — never
mirror its content into this public repo; migration is one-way, outward only.
State: tag `qok-proposition2`, every numbered result of the AiML draft
machine-checked, including the `(UI○)` correction that made Proposition 2
possible. The formalisation report went to Michael by real mail on
2026-08-05. `docs/QOK-WALKTHROUGH.md` and `docs/QOK-IMPLEMENTATION-REPORT.md`
there were updated today.

Nothing is owed *from* this repo to that thread. It is listed here so the
next session knows where the attention has been.

---

## 7. What this session actually produced about RN(◯,{}) — the new mathematics

Recorded because it is the part Matthew called a definite gain, and it is
scattered across `wip/`.

* **Visibility** (`wip/visible.lean`, 787 lines). `Visible a` := `a` closed,
  proper, and join-prime; join-primality is exactly the relative disjunction
  property, and a visible element names a point of the Esakia dual. **PROVED**
  visible: `⊤`, `t1`, `t2`, `t4`, `t6`, and the first gap. **REFUTED** for the
  whole odd-rung family (`not_joinPrime_rnSub_odd`). The engine is a Harrop
  lemma for PLL: `Harrop(◯A)` for *arbitrary* `A`, because `laxL`'s conclusion
  succedent must be `◯`-shaped — so a boxed hypothesis can never help produce
  a disjunction.
* **The `◯`-depth hierarchy is strict** (`wip/depth*.lean`). `D₀ = {⊥,⊤}`,
  `D₁` = the ladder, `D_{n+1}` = the Heyting algebra generated by
  `D_n ∪ ◯D_n`. Collapse at depth 2 is **REFUTED**; `◯g₁` has class depth
  exactly 3. The PCLL conjecture falls with it.
* **The ladder of logics** (`wip/linear.lean`, `wip/classical.lean`,
  `wip/schemeext.lean`) — cardinalities above; and **linearity, not K, is
  what forces `∨`-distribution** (`dist_of_lin`, `K_does_not_force_dist`).
  Also `nucleus_eq_closed`: on a Boolean algebra every nucleus is closed,
  `j x = x ⊔ j ⊥` — false for Heyting, which is why the classical rung is
  four elements and not two.
* **The converse of K fails** (`wip/converseK.lean`, added today):
  `◯A ⊃ ◯B ⊬ ◯(A ⊃ B)`, two pinned countermodels — one infallible and
  **linear** (so linearity does not force it), one with a fallible world (the
  F&M `PLL_C` character shape). `[propext, Quot.sound]`.
* **The explorer** — `docs/rn-explorer.html` (v12): the ladder, the families,
  the gap antichain, the descending chain with no floor, the visible points
  marked and graded. Open it with `open docs/rn-explorer.html`; **not** via an
  artifact link — the frame runtime blocks its downloads and printing.
* **The proof-state player** — `tools/proofstates/`, so a proof can be
  *watched* rather than only read:
  `lake exe pstates LaxLogic/PLLTopTop.lean --decl principal --html out.html`.
  Built in answer to a request Matthew has now made more than once.

---

## 8. Standing constraints — do not rediscover these

* **Delivery.** Matthew cannot open paths into a worktree, and often not into
  the repo either, from the session UI. Static documents (`.md`, `.pdf`) →
  **publish as an Artifact** and give the URL. Dynamic HTML → give a shell
  command (`open <path>`) or serve it locally; artifact links do not work for
  those. Short content → inline it in full.
* **The machine-checked mandate.** Every theoretical claim that will stand in
  a paper must be Lean-checked, sorry-free, with a pinned `#print axioms`.
  Anything else is OPEN or a conjecture, and must be labelled so.
* **Never remove a worktree to tidy up** (vetoed 2026-07-20 — it kills live
  agent sessions).
* **Browser**: the Claude-desktop browser tools time out here. Use
  claude-in-chrome (Comet), which rewrites `file://`, so serve local pages
  with `python3 -m http.server`.
* **Delegation**: file-editing subagents must run with `isolation: worktree`;
  subagents do not commit or push — the coordinator integrates.
* **Search memory before treating a project-history finding as new.** The
  recurring failure is not forgetting but re-deriving without checking.

---

## 9. If you want a ranked list

1. **File the `omega` issue.** Ready, cheap, unblocked by anything.
2. **The Plausible note.** An hour, ungated, useful to strangers.
3. **Copy the RN results into the belief paper.** The deadline is real
   (10 Sep 2026) and the material is proved and sitting in `wip/`.
4. **Decide about the case study.** It is written; what is missing is a
   decision and a consent policy, not more words.
5. **The confluent UI probe** — refute-first, per §1. This is the only item
   that is research rather than tidying, and the only one where the answer is
   unknown.
6. Prune `wip/`. Last, and only when nothing else wants attention.

---

## 10. LJF UI proved — the state as of 2026-08-09 evening

**The landmark**: uniform interpolation for LJF is machine-checked and
unconditional at `7aefbdc` (= tag `ljf-ui-v1`): `interp` computes both Pitts
quantifiers by one well-founded recursion; `eSound`, `aSound`, `eMinF`,
`aMinF`, `satE2`, `satA2`, `dykAnt` sorry-free, axioms pinned. Scope
discipline: this is UI for **LJF**; IPC awaits focalization completeness
(running on branch `ljf-focalization`, delegated); PLL awaits the lax flag +
`circL` (Matthew 2026-08-09: ◯R is subsumed by the lax judgment, so `circL`
is the only rule with content — but the lax phase is untested).

**Branches**: `ljf-simp-1` = simplification round 1 (this branch; may
overwrite files with compiling code). `ljf-focalization` = Deriv → LJF bridge.
Tag `ljf-ui-v1` marks the revert point.

**Rule 1 (archive, don't discard)**: when simp round 1 deletes superseded
proofs (the eMin/aMin/qAssemble layer, the pre-unification Tp/Up families),
move them verbatim into `Archive/` with a header note saying what superseded
them and when, for future archaeologists. Files from this round stay in place
until then.

**Rule 4 (metrics)**: measured on `ljf-simp-1` (LJF.lean has zero imports,
so `lake build LaxLogic.LJF` is exactly the file's elaboration time):
baseline 6,636 lines / 15 min 53.7 s → after rounds A+B+C+C2 **4,462
lines / 13 min 52.0 s** (−33% lines, −13% compile), zero statement
changes, all pins passing. Full log: `docs/ljf-simp-round1.md`. Round D
(the eliminator unification) is designed there and queued as the next
session's opening move.

**The post-simp sweep (Matthew's Note, 2026-08-09)** — standing checklist:

1. *Calculus fidelity.* Concern: the proof detoured so far through admissible
   machinery that it was "effectively proving the result using a different
   calculus". Kernel of truth: the effective working system is LJF + its
   admissible-rule toolkit (routeStab, simStab, dykCommute, …). Defence:
   every toolkit lemma concludes with genuine LJF constructors, so the
   theorem is about LJF proper. The simp-round side-by-side table
   (docs/ljf-simplification-pass.md §3) is the instrument: for each clause,
   record whether the induction runs on raw rules or on toolkit lemmas, and
   whether Pitts/Dyckhoff make the corresponding move on paper (they do —
   their "admissibility of weakening/inversion" citations are the same
   moves, unmechanised).
2. *Comparison against the shorter proofs.* Two in-repo comparators:
   `IPCFocused.lean` (545 lines, ∃-side only, over the shared PLLFormula
   stack — Matthew's 2026-08-08 control experiment) and the fuel/height route
   (`PLLG4UI` 1856 + `PLLG4UIAdq` 1113 + `PLLG4UITrunc` 4036 — adequacy by
   height induction, no sequent termination order). Question: what did the
   zero-import LJF rebuild buy — both quantifiers, both minimality
   directions, and a reusable termination order; at what cost in lines; and
   could the short file have been completed to the full theorem without
   growing into the long one?
3. *omega defect, second exhibit.* §9 item 1's omega filing gains the
   goal-only-pow-atom positivity drop from the termination fight (unsat
   systems reported satisfiable); file both together, with the `Prod.Lex`
   printer deception (error printer shows reduced first components while the
   tactic faces the raw pair) as a separate usability issue.
