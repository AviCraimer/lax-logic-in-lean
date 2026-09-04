# HANDOFF — lax-logic-in-lean (fairflow/lax-logic-in-lean)

**Last updated:** 2026-08-17 by Fable 5 — FRJ◯ retrospective appended (final §); previous update 2026-08-07 (§10 supersedes §§2 and 7 where they conflict)
**Repo state:** `main` @ 925bc10 — `lake build` clean, every `#guard_msgs` audit green; no live feature branch (`ui-confluence` merged 2026-08-06)
**Deployed:** n/a (library). Merged: `main` @ PR #5 (the summit theorems). **PR #6 OPEN** (commentary + comment sweep) — awaiting Matthew's personal prose review; do not merge it yourself.

**Start here:**
* **`docs/calculus-map.md`** — the summary of results: which of the seven proof
  systems each result belongs to, what is proved about it, and whose it is
  (ours vs Fairtlough–Mendler 1997). Read it before asserting provenance.
* **`docs/next-session.md`** — the live threads as of 2026-08-07, one section
  each, with the next action and who decides. Read it before starting work.

## 1. What this project is (3 sentences max)

A Lean 4 mechanisation of Fairtlough–Mendler Propositional Lax Logic (I&C 1997): natural deduction (`LaxND`), an intrinsically-typed term calculus (`Tm`) with kernel-checked strong normalisation, a cut-free G3 sequent calculus (`SC`), a **machine-checked refutation of the completeness of Iemhoff's G4iLL** (`PLLG4Gap.lean`), and the repaired calculus **G4iLL″** proven complete with cut, contraction and weakening all admissible: `G4c = SC = LaxND = Tm` (`PLLG4HComp.lean`, audits pinned). The owner is Matthew Fairtlough, co-creator of PLL; he reviews prose personally and merges PRs (or explicitly authorises you to). Current targets: **decidability** (F&M Thm 2.8) via a termination discipline for G4iLL″, then **uniform interpolation** (open again — our refutation voided the published proof).

## 2. Current state

- **What works** (all kernel-checked, `#guard_msgs`-audited):
  - The gap: `PLLG4Gap.lean` — separating sequent SC-derivable / G4-refuted (`[propext]` only), two-copy variant axiom-free ⟹ contraction inadmissible. `PLLG4Tower.lean` — Howe's original sequent G4-underivable; naive tower needs only 2 copies.
  - The calculus: `PLLG4H.lean` (G4h/G4c, three retention repairs, height-indexed) with `toSC`, `ofG4p`.
  - The ladder: hp exchange/weakening (`PLLG4H`), master inversion + `impR_inv` (`PLLG4HInv`), `andR_inv` (`PLLG4HCut`), rule lifters + identity + MP (`PLLG4HAdm`), `weak_Imp` + `impLImp_dup` (`PLLG4HStr`), **contraction cut-free** (`PLLG4HCtr.G4c.contract`), `exfalso_adm` + `cut_atom` + **`cut`** + **`selfAbsorb`** (`PLLG4HCut`), **`completeness`** + `equiv_sc/nd/tm` (`PLLG4HComp`).
  - Side artifacts: `KleeneBrouwer.lean` (constructive KB well-foundedness, ZERO axioms), `PLLRun.lean` (normalizer demos, `pll_g4c` tactic — the earlier `pll_g4` was retired 2026-07-17: it ran the incomplete naive calculus under `native_decide`), `docs/annotated/` (infoview-snapshot proof readings), `docs/surveys/` (4 research briefings), `docs/commentary.md` (the human story, PR #6).
- **What is in progress:**
  - PR #6 review (Matthew).  Termination design: route sketched in `docs/g4p-ladder.md` final section + the memory file — set contexts (licensed by admissible contraction) + subformula closure ⟹ finite search space ⟹ history/loop-check termination.
  - Note to Iemhoff: not yet drafted.
- **What is broken / known-bad (cosmetic only):**
  - `PLLDecide.lean` / `PLLTopTop.lean` carry stale "chunk" labels; `PLLTopTop.lean:1191` has an unused-variable lint. Both flagged in PR #6, deliberately untouched.
  - `PLLG4.lean`'s "Howe smoke test" is a historically mis-bracketed sequent (docstring now explains; kept as archaeology).
  - `G4p ≟ G4c` equivalence unproven and retired (only `ofG4p` needed).

## 3. Verification commands (run these FIRST, before changing anything)

```bash
cd /Users/matthew/Lean/Sources/lax-logic-in-lean/.claude/worktrees/g4ill   # the working worktree
lake build            # expect: "Build completed successfully."; known cosmetic warnings in PLLSequent/PLLTopTop
lake env lean LaxLogic/PLLG4HComp.lean   # expect: silence — the summit audits are inside
```

- The `#guard_msgs` blocks ARE the golden tests: they pin decider verdicts (`PLLG4Gap`, `PLLG4Tower`) and axiom sets (`[propext, Classical.choice, Quot.sound]` for the summit; `[propext]` for the refutation; **no axioms** for `KleeneBrouwer.wellFounded_kb`). A guard failing means your change is wrong.
- Single-file iteration: `lake env lean LaxLogic/<file>.lean` (build dependencies first if oleans are missing: `lake build LaxLogic.<Dep>`).
- Git flow: work on `worktree-g4ill` (this worktree; the repo root checkout sits on `FablePLL`), push, `gh pr create --repo fairflow/lax-logic-in-lean --base main`; **Matthew merges** unless he says "accept pr". Never commit without a green compile of every touched file.

## 4. Decisions and rationale (DO NOT RE-LITIGATE)

| Decision | Rationale | Rejected alternatives and why |
|---|---|---|
| `SC` (G3, membership-keeping) is ground truth; everything is measured against it | Proven equivalent to `LaxND`/`Tm` (`cutElimination`, `curry_howard`) | Trusting G4iLL: refuted, kernel-checked |
| Three **retention** repairs (laxL keeps box; both `◯→` rules keep full first-premise context) | Each forced by a machine-found countermodel (rev 3: `j=id, φ:=p, ψ:=p∧q, E:=q`); they are what make contraction cut-free and `selfAbsorb` structural | "Optimising" premises back to consuming form re-opens the gap |
| Height index (`G4h n Γ C`) + Perm-hypothesis rule style + additive rules | hp-transports (perm/weaken/invert) are measure-invisible for the (weight, height-sum) inductions; exchange is one line per rule | Multiplicative contexts: pushes contraction into every case. `Prop`-only: cut's transports break |
| "Contraction-free" claims use the weak/strong distinction: G4iLL″ is a **localization** theorem (all needed contraction lives in the ◯-rules), NOT a refutation of strong Howe | Matthew's correction, 2026-07-09 evening — the retention rules absorb contraction | Claiming Howe refuted: wrong, the strong (reductive) form is open and *supported* by our evidence |
| UI waits on **termination**, not completeness (we have completeness) | Pitts's method needs both; Iemhoff had termination without completeness — we hold the dual | Running Pitts now: repeats her error shape. Trusting literature that "PLL-UI is settled": refuted here — correct any agent that reports it |

Longer log: `docs/g4p-ladder.md` is the design history (this repo's DECISIONS.md-equivalent — document reality, don't rename).

## 5. Invariants — things that must remain true

- **No `sorry` is ever committed.** No axioms beyond `[propext, Classical.choice, Quot.sound]` in the G4h tower; `PLLG4Gap`'s refutation stays `[propext]`-only; `KleeneBrouwer` stays axiom-free.
- `lake build` green (including every `#guard_msgs`) before every commit; guards are frozen — a failing guard indicts the change.
- `PLLTerms/PLLTopTop/PLLSequent/PLLNDCore` are **frozen** (proven, load-bearing): comment edits at most, recompile after.
- New G4h lemmas declare their height discipline: height-preserving (`G4h n → G4h n`) or bumping (`→ G4c`) — never hide a bump behind `Exists.imp`.
- The three lax rules keep their retention shapes exactly (see §4 row 2).
- Machine-check any claim adjacent to the Iemhoff refutation before writing it in prose.

## 6. Pitfalls already hit (don't rediscover these)

- **Symptom:** type mismatch `C✝`/`Γ✝` vs your named variable in `have`-ascriptions inside `induction` cases (bit us TWICE: 8 errors, then 4) → **Cause:** `induction` generalises the target's indices; the outer names go stale → **Fix:** bind case-locals in `@`-patterns (`E₀`, `Γ₀`) and ascribe with those.
- **Symptom:** rule lifter/`Exists.imp` won't typecheck across a height bump → **Cause:** `Exists.imp` maps same-index only → **Fix:** `obtain ⟨n, h⟩ := d; exact ⟨n+1, .rule …⟩`.
- **Symptom:** `induction d` fails "index is not a variable" (e.g. goal formula `falsePLL`, `A.somehow`) → **Fix:** the eq-trick (`G4h n Γ G → G = ◯A → …`); conversely `cases d` handles non-variable indices and auto-dismisses impossible constructors.
- **Symptom:** `injection e with e₁ e₂` errors "too many identifiers" → **Cause:** outer constructors CLASH (e.g. `and` vs `ifThen`), injection closes the goal itself → **Fix:** outer-clash `cases e`; same-outer `injection e with …` then `cases` the clashing component.
- **Symptom:** `omega` can't see weight facts → **Fix:** `simp only [PLLFormula.weight] at hA` first.
- **Symptom:** doc-comment before `#guard_msgs` → parse error → **Fix:** plain `--` comment there.
- **Symptom:** Edit tool refuses a file you created via heredoc → **Fix:** Read it once first.
- **Symptom:** a failing script step didn't stop the git commit after it → **Cause:** separate command lines don't short-circuit like `&&` → **Fix:** guard commits with `if lake env lean <file>; then git commit …; fi`.
- **Symptom:** your `git add -A` commits a background agent's half-written files (shared worktree) → **Fix:** `git status` before staging when agents run; scope the add.

## 7. Next actions (each sized for ONE session; tracker = THIS list — no beads; mirror to `gh issue` if a queue is wanted)

1. [x] **Termination A** — done 2026-07-10 (`PLLG4Space.lean`, PR #7).
2. [x] **Termination B** — done 2026-07-10 (`PLLG4Set.lean`, PR #7): fully *cumulative* set calculus (design refinement: nothing erased, `impLBot` vanishes, `weaken_subset` replaces all structural plumbing).
3. [x] **Termination C** — done 2026-07-10 (`PLLG4Dec.lean`, PR #7): fuel-structural visited-set search; `search_complete` via minimal heights + the visited-invariant; `instance decidablePLL : Decidable (Nonempty (Tm Γ φ))` — **F&M Thm 2.8 decidability, mechanised**. Note: `#eval` guards use tiny sequents (the gap sequent's space is astronomically large — the instance is total but exponential; fuel is computed arithmetically, never the powerset).
4. [ ] *(Fable session)* **Uniform interpolation**: Pitts `∃p/∀p` over the terminating search; adequacy from `completeness`. (Session task #9.)
5. [ ] **Multiplicity-3 hunt**: decider sweep for a sequent needing 3 copies (strong-Howe dichotomy); record either outcome in `PLLG4Tower.lean`. — *Done when:* a pinned witness or a documented negative sweep.
6. [ ] **Draft `docs/note-to-iemhoff.md`** from `docs/commentary.md` + `docs/g4ill-gap-review.md`: the gap, the repair, the offer. Matthew edits and sends personally. — *Done when:* draft committed; NOT sent.
7. [ ] **`TACTICS.md` + `LaxLogic/Tactics/`** per the handoff convention's Lean extra: package the recurring moves (perm plumbing `push2/pushL/rot3`, cross-splits, hp-transport idioms) with worked examples. — *Done when:* file exists, one tactic family extracted and used somewhere.
8. [ ] *(Matthew)* Review & merge PR #6.
9. [ ] **Mathlib PR prep**: `KleeneBrouwer` (zero-axiom) as the first candidate; check mathlib conventions, draft the PR. — *Done when:* branch ready for Matthew's go.
10. [ ] *(Fable sessions)* Session tasks #7 (Pfenning–Davies judgmental PLL) and #8 (G4iK□/G4iKD□ audit via the counterexample methodology).

## 8. Out of scope / deferred (so the model doesn't wander)

- Do NOT re-open the `G4p` ladder (superseded; only `ofG4p` matters) or refactor frozen proof files for style.
- Do NOT "fix" `PLLDecide.lean`'s semantics — it decides **G4-original** (the incomplete calculus), which is exactly its job in the refutation; it does NOT decide PLL.
- Do NOT claim strong Howe refuted, or that PLL-UI is settled (either way), anywhere.
- Do NOT contact Iemhoff or anyone externally; drafts only, Matthew sends.
- Multimodal lax logic (`◯₁ ⊔ ◯₂`, joins of nuclei at the term level) is the *successor project*, not this repo's scope.
- The zombie background-task chips in the session UI are harmless orphans; ignore or stop them, don't investigate.

## 9. Update — 2026-07-12: uniform interpolation paused

- **Stopped** (Matthew, budget): mechanising uniform interpolation for PLL over `G4c` is paused — not a dead end, see below.
- **State:** the whole development compiles down to one unproved lemma, `cascade_low_pos_box` (`wip/absorb_base.lean`) — the sole `sorry` anywhere in the UI work, and it concerns ◯-involving goals specifically; the ◯-free fragment is already unconditional, giving uniform interpolation for plain IPC with no gap.
- **Search:** three rounds of semantic countermodel search this week (`wip/refute3.lean`, `wip/refute4.lean`; the full 34-pair finite-algebra test collection, ~454 configurations at the lemma's own threshold) found zero counterexamples; current `∃p`/`∀p` definitions need no revision on present evidence.
- **Write-up:** `docs/ui-attempts-table.md` (this session) — plain-English attempt-by-attempt table for readers outside the project; `docs/iemhoff-note.md` (drafted in parallel) — the human-readable note on G4iLL's incompleteness and the two flaws located in Iemhoff's own printed uniform-interpolation proof (`wip/g4ill_ui.lean`).
- **Toolchain:** bumped to `leanprover/lean4:v4.31.0`.
- **Late addendum, same day:** `uniform_interpolation_IPC` landed sorry-free (box-free crown, pinned audit `[propext, Classical.choice, Quot.sound]`) — proved by an Opus agent from a mapped brief; the two missing facts and the method are recorded in `docs/opus-handover.md`, the handover strategical for delegated proof agents.

## 10. Update — 2026-08-07: uniform interpolation SHELVED; the threads are in `docs/next-session.md`

**Where the record is.** Two documents govern, and both are newer than
everything above:

| document | what it is |
|---|---|
| **`docs/calculus-map.md`** | **the summary of results** — the seven proof systems (`LaxND`, `SC`, `G3iLL`, `G4iLL`, `G4h`/`G4c`, `DerivU`, `DerivUNoFall`), what each is, what is proved about it here, what depends on it, and the provenance summary (ours vs F&M 1997). It ends with a "which system is a given result really about?" table. Written because the calculi had been confused in conversation more than once. |
| **`docs/next-session.md`** | **the live threads**, 2026-08-07: shelved UI and the confluent idea; the testing layer (frontier sampler, catpart, what is missing); the case study; the `omega`/`⊥` issue and the Zulip question; the belief paper; the Q○.K thread; the new RN(◯,{}) mathematics; the standing constraints. |

**State, superseding §2.** `main` @ 925bc10, `lake build` green. Sorries:
five in `LaxLogic/` (all in the semantic-UI extension line —
`PLLSemUIChar.lean:322,327`, `PLLSemUILayered.lean:827`,
`PLLSemUIHenkin.lean:341,352`), one that matters in `wip/`
(`cascade_boxgoal_pos`, `wip/absorb_base.lean:2281`), two routine ones in
`wip/G4conf.lean`. `uniform_interpolation_IPC` is sorry-free;
`uniform_interpolation_PLL` still carries `sorryAx`.

**The UI campaign's verdict (PROGRESS §§57–68, rounds 1–9).** The *room-free*
route is REFUTED, kernel-checked at `Γ = []`: `BoxDesc`, `CompProd` and
`GoalRowAbsorb` each fall, and `¬BoxDesc` is re-derived twice more through
rounds 7's and 8's own upgrade theorems. The refuted cell is strictly
sub-room, so the room-carrying `cascade_boxgoal_pos` survives — the room is
the sole countermodel excluder for the third time. §65 then proved that the
surviving statement's live regime is **not decide-feasible** wherever a
γ-clause is present, so it cannot be screened in either direction: it has to
be built. That is why the campaign is shelved rather than continued.

**Status of §7's list.** Items 1–3 done (2026-07-10). Item 4 (uniform
interpolation) — shelved, as above. Item 6 (note to Iemhoff) — drafted as
`docs/iemhoff-note.md`, still not sent, still Matthew's to send. Items 5, 7,
9, 10 untouched. Item 8 (PR #6) still Matthew's.

**Two new invariants for §5.** (i) A *false statement* compiles the whole
stack and passes every axiom pin, because it is a `sorry` — check statements
against the repo's own refutations before believing a clean build. (ii) A
clean screen is a statement about the screen: screen the **degenerate end** of
every axis first (round 9's fault needed empty context × untied fuel ×
missing frame simultaneously, and no sweep had ever emptied a context).


---

## 2026-08-17 — FRJ◯ (forward refutation with ◯): campaign PAUSED, retrospective

New since §10, all on branch `claude/frj-redevelopment-69005f` (NOT merged;
worktree hello-8a60f1): a mechanisation of Fiorentini–Ferrari FRJ(G)
(TOCL 21(3) 2020) extended to PLL's ◯.  The ◯-FREE completeness is PROVED
there (`FRJ/Minimal.lean`: `frj_iff_not_IPL` — `Provable G ↔ ¬ IPL G` for
circ-free `G`, the paper's Thm 6.2(i)+3.1).  The ◯-extension's completeness
campaign was paused 2026-08-17: the approach was not converging.

- PROVED (`FRJ/Saturate.lean`, pins `[propext, Quot.sound]`, guards in
  `FRJ/Audit.lean`): `completeness_of_supply : PledgeSupply K G →
  CircSupply K G → ¬K.valid G → Provable G` (conditional statement (A));
  `provable_root_countermodel` ((B) forward, unconditional);
  `completeness_of_discrete` (discrete models — these collapse to a single
  classical world, ◯ transparent, so this is only the classical shadow);
  `completeness_via_closure` (the ◯-free case re-derived through the new
  organisation — a consistency check, no new territory).
- REFUTED: the paper's triple-induction structure extended to ◯
  (`minMod`-as-recursion; measure dichotomy, branch `docs/frj-w4.md` §9).
- OPEN: unconditional (A); BOTH supply kernels as statements — never
  extensionally attacked (first move if resumed).  Candidate cheap
  extension: an erasure-transfer lemma for ◯-inessential countermodels
  (`Rm = id`), reducing that class to the proved ◯-free completeness.

Method lessons (banked in memory + branch HANDOFF): a lemma-statement
introduced by interface refinement owes the standing extensional attack
BEFORE the next analysis window; two isomorphic residues = change tack;
an in-window-unreachable goal hook drives grinding.

Full trail: branch HANDOFF.md (ten dated §§), branch `docs/frj-w4.md`
§§8–13, engine `wip/frj_sat.lean` (corpus 28 pass / 5 control-ok /
0 unresolved).
