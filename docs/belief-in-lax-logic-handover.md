# Handover — writing *Belief in Lax Logic* with Matthew

**For:** the next Opus session that will help Matthew Fairtlough draft the paper
**From:** the session of 2026-07-14 (revised same day: all results merged to
`main` + `origin/main`; machine-checked mandate added as the governing rule).
**Status:** paper not yet started; this is the brief. No code task is pending.
All the mechanised results and this brief are on `main` (see §7) — **work from
`main`; no git worktree is involved.**

---

## 0. Before anything else — three ground rules

**(a) Every mathematical claim in the paper is machine-checked in Lean.**
This is the method, and it is not optional. *Belief in Lax Logic* is a
**machine-checked mathematics paper**: every result it states as established —
every lemma, theorem, corollary, and worked example — must be backed by a
`sorry`-free, axiom-audited Lean proof (`#print axioms` showing only the
ordinary axioms `propext` / `Classical.choice` / `Quot.sound`) **before** it
stands in the text as proved. A claim without a Lean proof is a **conjecture**,
and the paper must say so — mark it `OPEN` or `to mechanise`, never assert it.
The order of work is therefore **mechanise first, write second**: when in doubt,
prove it in Lean, then describe it.

Scope of the rule. "Theoretical work" = any *mathematical* assertion (a
definition's properties, a lemma, a computation, a counterexample, an example
algebra). It does **not** cover motivation, history, philosophical argument, or
related-work discussion — that prose is written normally. The rule has exactly
two escapes: (i) Matthew explicitly exempts a specific item ("this one we state
without mechanising"); (ii) it is non-mathematical prose. Matthew's own words
for this: *"This is a new modality for mathematics and as far as possible we
will follow it."* Take that literally. (The resonance is real and worth a line
in the paper's methodology note: the paper is *about* a modality — verified,
lax truth — and its method *is* one, working throughout under the modality
"machine-checked".)

Practical consequence (UPDATED 2026-07-18): the original §3b to-mechanise
ledger is now CLOSED except for "more worked examples" — see the §3b status
update. The Boolean-collapse hinge and its companions are mechanised and in
the library.

**(b) Whose paper this is.** Matthew Fairtlough is the *Fairtlough* of
Fairtlough–Mendler. This is his logic and his paper. You are an assistant: you
draft, you formalise claims, you compute examples, you check the literature, you
pressure-test arguments. You are **not a byline co-author** — do not offer to
be one, and say so plainly if authorship comes up. Within that role, be a real
collaborator: if something Matthew proposes is wrong, say it is wrong and show
why. He explicitly values `PROVED` / `REFUTED` / `OPEN` kept apart and honest
reporting over agreement — the prior thread turned on machine-*refuting* a
shortcut he had hoped would work, and he was glad of it.

**(c) Register — the one hard stylistic rule.** Use **standard proof-theoretic
and modal-logic language only.** No invented vocabulary. A previous thread was
*stopped* over home-made jargon ("fuel", "seals", "the zoo", "the cascade",
"ambient budget", …) that Matthew could not and would not follow. Write lemmas
as **displayed formulas**, name notions by their standard names (nucleus,
closure operator, Heyting algebra, Kripke model, forcing, …), and if you must
coin a term, define it once on first use as a displayed definition and never
drape prose over it. When in doubt, write the formula, not a metaphor for it.

---

## 1. The paper in one paragraph

*Belief in Lax Logic* argues that Propositional Lax Logic (PLL) is a legitimate
**logic of belief** — read `◯M` as "M is believed" — and, on the way, gives an
argument for constructive logic. The engine is a contrast the mechanised
results make precise: **classically, belief is degenerate** (every believer is
"the truths, plus one fixed dogma"), whereas **constructively, belief is rich
and evidential** (a proof of `◯M` carries the grounds for believing M). Since
evidential belief — belief whose grounds you can demand — is non-trivial *only*
intuitionistically, wanting belief to be more than prejudice is itself a reason
to work constructively. The argument does not presuppose constructivism; it
earns it from a pre-theoretic desideratum about belief.

---

## 2. The argument, distilled

Read `◯M` as "M is believed", equivalently "M holds subject to the believer's
grounds". A believer is a **nucleus** `j` on the algebra of propositions: an
inflationary, idempotent, meet-preserving closure operator. This is exactly what
PLL's `◯` is, so the belief reading is not an analogy — it is the intended
algebra with a doxastic gloss.

**(A) Classical belief is degenerate.**
On a Boolean algebra every nucleus is *closed*:
> `j(x) = x ∨ a`,  where `a = j(0)` fixed;  equivalently  `◯M ⟺ M ∨ a`.
(The finitary proof uses only `x ∨ ¬x = 1`.) So a classical believer believes
exactly the truths, plus one fixed proposition `a` (a "dogma") and its
consequences — a one-parameter family `c_a`, one believer per proposition. The
extremes are Matthew's two kinds:
> `a = ⊥` : the **total sceptic** — `◯M ⟺ M`, believes only truths (`j = id`).
> `a = ⊤` : the **totally credulous** — `◯M ⟺ ⊤`, believes everything.
Classically a believer can be *nothing but* truth-plus-a-prejudice. No
conditional belief, no evidential structure. Belief is boring.
*(Status: MACHINE-CHECKED 2026-07-16 — `BeliefCollapse.lean` +
`BeliefBooleanIso.lean` (`N(B) ≃o B`); see the §3b status update.)*

**(B) Constructive belief is rich.**
Off Boolean, nuclei are no longer all closed. Standard families reappear as
genuinely distinct notions:
> **closed**  `c_a(x) = x ∨ a`      — dogmatic belief;
> **open**    `u_a(x) = a → x`      — *hypothetical* belief ("I would believe M given a");
> **double-negation-like** `(x → a) → a`.
On a Boolean algebra the open family collapses into the closed one —
`a → x = x ∨ ¬a`, i.e. `u_a = c_{¬a}` — so hypothetical belief is *invisible*
classically. Intuitionistically it is a separate thing, and the space of
believers is large: the free lax structure on no generators (the closed
`◯`-fragment) is **infinite** (machine-checked, §3). The constructive believer
simply has more available attitudes than the classical one can express.

**(C) Belief is evidential — the constraint reading, made exact.**
F&M's own reading of `◯M` is "M holds up to constraints". The
context-completeness theorem (machine-checked, §3) makes this a completeness
statement:
> `PLL ⊢ φ`  ⟺  for every standard constraint `C`,  `IPL ⊢ φ^C`.
Doxastic gloss: the constraint `C` is the believer's **grounds**; `φ^C` is what
`φ` amounts to once those grounds are discharged. A proof of `◯M` is a proof
carrying a constraint (a body of evidence) under which M holds — so Matthew's
slogan
> *"a proof of `◯M` contains the evidence for believing M"*
is exact, not metaphorical. The strong-monad structure (`unitC`/`bindC`, the
C_I/C_M/C_S combinators of the Curry paper) are the **operations on evidence**:
believe a truth (unit), chain grounds (multiplication / `bindC`), combine
grounds for a conjunction (strength). This is the BHK / propositions-as-types
reading applied to a belief modality.

**(D) The argument for constructivism.**
Evidential belief — belief you can demand the grounds of — is non-degenerate
*only* intuitionistically, because classically it collapses to "truth ∨ dogma",
with no evidence anywhere in the picture. So if you want belief to be more than
prejudice, you are pushed into constructive logic — not by fiat but because that
is the only setting in which the modality has room to carry content. A reason to
be a constructivist that does not presuppose constructivism. This is, I think,
the paper's real engine; give it its own section.

**(E) The idealisation to own up front.**
The unit `M ⊢ ◯M` makes the believer believe *every* truth — logical omniscience
over the true, belief as a closure operator on truth. This is exactly what makes
`◯` a nucleus, so it is not a bug to hide but a scope to declare: this is a logic
of **idealised, truth-closed, evidential** belief. The interest is the evidential
and constructive structure, not resource-bounded or fallible-about-truth belief.
A referee reaches for this first — put it in the introduction, not the rebuttal.

Two further doxastic facts worth a subsection each:
- **Full introspection.** `◯◯M ⊣⊢ ◯M` (unit gives `◯M ⊢ ◯◯M`, multiplication
  the converse). Believing-that-you-believe coincides with believing; the lax
  believer is transparently introspective (both the `4`/positive-introspection
  direction and its converse).
- **No consistency axiom.** PLL does **not** have `¬◯⊥` (the doxastic `D`).
  `◯⊥` is a genuine, non-trivial element — the free generator of the closed
  fragment, `◯⊥ ≠ ⊤`. By monotonicity `◯⊥ ⊢ ◯M` for all M, so a believer who
  "believes the absurd" believes everything (credulous collapse *at the
  `◯`-level*), yet `◯⊥` does not make everything *true*. The inconsistency is
  quarantined — a clean contrast with KD45 belief; develop it carefully.

---

## 3. The machine-checked ledger

### 3a. Already proved — `sorry`-free, axiom-audited (cite freely)

All of the following live on `main` (merge commit `c9e98b6`, pushed to
`origin/main`), in the main checkout, files `wip/context_completeness.lean` and
`wip/lax_infinite.lean`. Re-run `#print axioms <name>` under the Lean toolchain
(v4.31.0) before leaning hard on any statement in print — that audit *is* the
standard of "proved" under rule 0(a).

Axiom key: **clean** = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`
— the ordinary axioms of classical Lean, i.e. an honest proof.

| Result | Lean name / location | Statement (as mechanised) | Axioms |
|---|---|---|---|
| **Context completeness** (F&M Curry Thm 6) — *"belief = provability under a constraint"* | `PLLND.Ctx.thm6`, `wip/context_completeness.lean:651` | `Nonempty (LaxND [] φ) ↔ ∀ C : StdCtx, Nonempty (LaxND [] (subC C φ))` | clean |
| **Constructive belief is infinite** — the closed `◯`-fragment `RN(◯,{})` | `PLLND.LaxInfinite.closed_lax_infinite`, `wip/lax_infinite.lean:616` | `Infinite (Quotient closedSetoid)` | clean |
| **The constraint algebra 𝕊 is Boolean** | `PLLND.Ctx.thm2_boolean_algebra`, `wip/context_completeness.lean:1588` | 𝕊 a bounded distributive lattice with complements (`BooleanAlgebra CQuot`) | clean |
| **No finite set of constraints suffices** (F&M Cor 10) | `PLLND.Ctx.corollary10`, `wip/context_completeness.lean:981` | no finite `𝔻 ⊆ StdCtx` is complete for PLL | clean |
| supporting: `◯⊥` is a free Heyting generator | `force_subOb`, `lax_infinite.lean:393` | `p ↦ ◯⊥` embeds the Rieger–Nishimura lattice | `propext` |
| supporting: RN ladder staircase invariant | `rn_staircase`, `lax_infinite.lean:521` | de Jongh one-variable universal model | clean |

These anchor §2(C) (`thm6`, + `lemma7` at `context_completeness.lean:546`) and
§2(B)'s "infinite" (`closed_lax_infinite`). Recorded sharp finding: chain/comb
Kripke models provably cap the one-variable fragment at ≤ 5–9 classes, so an
*infinite* model is genuinely required — the constructive richness is real.

### 3b. STATUS UPDATE 2026-07-18: items 1–4 are DONE, item 5 partial

The 2026-07-16 mechanisation sweep closed this ledger; everything is
promoted into the library (`LaxLogic/Belief*.lean`, root-imported, checked
by `lake build`), indexed in `docs/belief-mechanisation-index.md`. Current
truth, verified against the library 2026-07-18:

1. **The Boolean collapse — DONE.** Every nucleus on a Boolean algebra is
   closed, plus the sharp iso `N(B) ≃o B` (`BeliefCollapse.lean`,
   `BeliefBooleanIso.lean`).
2. **Open = closed on a Boolean algebra — DONE, and sharper.**
   `openNucleus_eq_closedNucleus` (on any `BooleanAlgebra`); the converse
   `em_of_openNucleus_eq_closedNucleus` (collapse at `a` ⟹ excluded middle
   at `a` — so the separation is *exact*, `open = closed ⇔ EM at a`); and
   the explicit non-Boolean witness `open_ne_closed_Fin3`
   (`BeliefOpenClosed.lean`).
3. **Full introspection — DONE.** `◯◯M ⊣⊢ ◯M`, plus logical omniscience
   `Γ ⊢ M ⇒ ◯Γ ⊢ ◯M` (`BeliefIdealisation.lean`; normality of `◯` in
   `BeliefNormality.lean` — note the earlier "not normal" claim was wrong,
   `◯` validates K).
4. **`◯⊥` facts — DONE.** `⊬ ¬◯⊥`, `⊬ ◯⊥`, and the credulous collapse
   (`BeliefFalsum.lean`).
5. **Worked examples — PARTIAL; more wanted (Matthew, 2026-07-18).**
   `BeliefExamples.lean` has: the 3-chain's complete nucleus enumeration
   (`chain3_card = 4`, sceptic/credulous/closed/open all exhibited,
   `chain3_open_ne_closed`) with clean axioms; `chain4_card = 8` and
   `boolean22_card = 4` via `native_decide` (`ofReduceBool` flagged in the
   index, per policy). STILL WANTED: a small **non-linear non-Boolean**
   Heyting algebra with its full believer menagerie side by side (the
   pentagon-free 5-element HA is the natural pick), RN truncations, and
   ideally clean-axiom (`decide`, not `native_decide`) versions of the
   4-chain/2×2 counts.

Everything here may be cited as established (rule 0(a) satisfied); the
axiom audits are in the mechanisation index.

---

## 4. Literature — the backbone, and the prior art you must engage

**The classical-collapse backbone.** See `docs/nuclei-noncomplete-lit.md`
(verified citations):
- On any Boolean algebra `B`, every nucleus is closed, `j(x) = x ∨ j(0)`, so
  `N(B) ≅ B`. Elementary; Beazer–Macnab territory. **Matthew already knows
  this** — do not re-derive it to him as news (the previous session over-sold it
  as a surprise and was corrected). Its role is the stated hinge of §2(A),
  carrying a citation *and its own mechanisation* (§3b item 1).
- Off Boolean and off *complete*: for a non-complete Heyting algebra, the nuclei
  `N(H)` form in general only a bounded meet-semilattice — both `∨` and `→` on
  `N(H)` are extremal-fixpoint constructions needing completeness (Erné 2022);
  `N(H)` is a frame iff `H` is complete. Consequence: be careful with any
  "algebra of believers" claim over RN or 𝕊 — it need not itself be a Heyting
  algebra. (This killed a tempting "assembly tower over RN" line; see
  `docs/assembly-tower-lit.md`.)
- Macnab 1981 ("Modal operators on Heyting algebras", *Algebra Universalis* 12)
  is the right primary source for nuclei on a possibly-incomplete Heyting
  algebra. It stayed **paywalled** — only reached second-hand via Erné 2022.
  Getting it is the one open literature errand.

**Prior art the paper MUST position against (verify details — do not assert from
memory).** This is the biggest gap in the current thinking and your most
valuable early contribution:
- **Justification logic** (Artemov): `t : F`, "`t` is evidence/justification for
  `F`". Matthew's slogan "a proof of `◯M` is the evidence for M" is squarely this
  territory. Is PLL's `◯` a *forgetful* justification modality `∃t. t : M`?
  Could be a section or a related-work paragraph. **Verify.**
- **Intuitionistic epistemic logic** (Artemov & Protopopescu, 2016, *Review of
  Symbolic Logic*): an intuitionistic `K` with co-reflection `A → KA` and
  *without* `KA → A`, motivated verificationally (a proof is a verification).
  Very likely the **closest published neighbour**; the paper must say clearly
  how PLL's belief reading relates — complementary, a special case, or genuinely
  different (PLL predates it by ~20 years, from a type-theoretic / hardware-
  verification motivation, not an epistemic one). **Read it early; verify the
  exact axioms.** It may reshape the paper's positioning.
- **Doxastic logic** (Hintikka; KD45): the classical baseline the paper
  contrasts against. §2(E)'s "no `D` axiom, full introspection" is the precise
  comparison.
- **BHK / propositions-as-types**; **Goldblatt 1981** ("Grothendieck topology as
  geometric modality") and the nucleus-as-modality literature — the algebraic
  lineage of `◯`.

---

## 5. A proposed skeleton (a starting point, not a cage)

1. **Introduction** — PLL and its history (Curry's problem, hardware
   verification, the `◯` modality); the belief reading; the thesis; the
   idealisation declared up front (§2E); **a methodology note stating every
   result is Lean-verified** (rule 0(a)); contributions.
2. **Lax logic recalled** — syntax; the three `◯`-laws (unit, multiplication,
   strength); nucleus semantics; constraint semantics. Precise statements lifted
   from the codebase.
3. **Belief as a nucleus** — `◯M` = "M is believed"; believer = nucleus;
   truth-closure; the unit as "believe every truth".
4. **Classical belief is degenerate** — `N(B) ≅ B` (§3b-1); `◯M ⟺ M ∨ a`; the
   `c_a` spectrum; sceptic and credulous extremes; contrast with KD45 (no `D`,
   `◯⊥` non-trivial, full introspection — §3b-3,4).
5. **Constructive belief is rich** — open vs closed nuclei (§3b-2); hypothetical
   belief `a → (−)` invisible classically; the infinite closed fragment
   (machine-checked, §3a); **worked examples on small Heyting algebras**
   (§3b-5), machine-computed.
6. **Belief is evidential** — constraint semantics; Theorem 6 (§3a); constraint
   as grounds; `λ`-terms as evidence operations; "a proof of `◯M` contains the
   evidence".
7. **The argument for constructivism** — evidential belief is non-degenerate
   only intuitionistically; the desideratum-to-constructivism move (§2D).
8. **Related work** — justification logic; intuitionistic epistemic logic;
   doxastic logic; BHK; geometric-modality/nucleus lineage.
9. **Limitations and further work** — truth-closure idealisation; resource-
   bounded / fallible belief; multi-agent; *belief about belief* and the
   assembly tower `N(N(…))` as a speculative meta-belief structure (flag as
   open — the tower over RN is genuinely open and delicate; do not overclaim).
10. **Conclusion.**

---

## 6. Pitfalls — what NOT to claim

- **Do not** state any §3b item as proved before its Lean proof exists and its
  `#print axioms` is clean. In particular do not call the Boolean collapse
  machine-checked until §3b-1 is done.
- **Do not** claim an "assembly tower over RN" is a Heyting algebra, or that RN's
  tower height is known. Off-frame `N(RN)` may fail both `∨` and `→`; the height
  is **open** (`assembly-tower-lit.md`, `nucleus-assembly-direction` memory).
- **Do not** conflate "believes everything" (`◯M` for all M, the credulous
  `a = ⊤` / `◯⊥`) with "everything is true" (`⊤`). The distinction is a feature
  (§2E).
- **Do not** assert the justification-logic or Artemov–Protopopescu details from
  this document — verify against the primary sources before print.
- **Do not** overstate the belief model: it is truth-closed and logically
  omniscient over truths. Say so.

---

## 7. Logistics

- **Working location: `main`, in the main checkout at
  `/Users/matthew/Lean/Sources/lax-logic-in-lean/`.** Everything is here and on
  `origin/main` (fairflow) at `53548f7`; the old `g4ill` worktree is no longer
  needed and should be ignored. Result files: `wip/context_completeness.lean`,
  `wip/lax_infinite.lean`. New mechanisations (§3b) go in `wip/` alongside them
  (or in a dedicated `wip/belief_*.lean`), imported into the paper as they land.
- **This handover:** `docs/belief-in-lax-logic-handover.md` (on `main`).
- **Toolchain:** Lean v4.31.0 + Mathlib v4.31.0 (see `toolchain-bump-v431`
  memory). `#print axioms <name>` is the honest-proof check and the gate of rule
  0(a); run it before citing anything.
- **The Curry paper (source for §6 / Theorem 6):** F&M, "On the Logical Content
  of Computational Type Theory: A Solution to Curry's Problem", TYPES 2000,
  LNCS 2277, pp. 63–78. Durable copy:
  `https://ncatlab.org/nlab/files/MendlerComputationalTypeTheory.pdf`.
- **Git discipline:** origin sync is the norm (push/pull `origin main:main` with
  explicit refspecs — never a bare `git push`; `upstream` is AviCraimer's parent
  repo and must never receive a push — see `git-remote-traps` memory). Commit
  when Matthew asks.

---

## 8. Pointers

- **Memory** (`…/memory/`): `communication-register` (the register rule — read
  it), `curry-problem-paper` (Theorem 6 provenance),
  `nucleus-assembly-direction` (the collapse, off-frame results, tower),
  `ui-route-status`, `toolchain-bump-v431`, `git-remote-traps`.
- **Docs** (`docs/`, all on `main`): `nuclei-noncomplete-lit.md` (collapse +
  off-frame backbone for §4/§2A), `assembly-tower-lit.md` (§9 further-work),
  `opus-handover.md` (the *previous*, proof-effort handover — different purpose,
  but shows house style and the register in action).
- **Codebase (`main`):** `wip/context_completeness.lean` (the Curry paper,
  ~1745 lines, source of §6), `wip/lax_infinite.lean` (~634 lines, source of
  §5's "infinite"). `PLLCompleteness.lean` is the F&M-1997 Kripke completeness
  the Curry work builds on; `PLLNDCore.lean`/`PLLND` hold the core `◯`-laws you
  will cite for §3b-3,4.

**First move, suggested:** read the `communication-register` memory and
`nuclei-noncomplete-lit.md`; skim `thm6` and `closed_lax_infinite` on `main`;
then do the two highest-value things in parallel — (i) mechanise §3b-1 (the
Boolean collapse), the hinge the whole classical-degeneracy argument rests on,
and (ii) read Artemov–Protopopescu IEL and report to Matthew where PLL belief
sits relative to it. Settle both before any section prose is written.

---

# ADDENDUM (2026-07-18) — post-drill state, successor project, queued tasks

*Added at Matthew's request at the close of the long g4ill/UI session, so a
fresh session starts with this instead of a degraded compaction chain. The
original brief above is kept intact; where it disagrees with this addendum,
the addendum wins.*

## A1. Headline result since the brief: the completeness chain is choice-free

The mechanised completeness theorem (and the whole decidability chain) has
been **finitised: it no longer uses the axiom of choice**. Commit `2d38c2c`
"drill the Classical.choice floor — decidability and completeness chain now
`[propext, Quot.sound]`". Methodological point Matthew wants kept: surgery
of this kind — re-founding a completeness proof choice-free — is not
feasible by hand through the conventional review process; the Lean+AI
combination did it "without a lot of fuss". This belongs in the paper's
methodology note (§0(a) of the brief) as a first-class exhibit.

Current library facts a fresh session should NOT re-derive (see the
`belief-paper` memory for the full ledger): `LaxLogic/` has zero sorries;
decidability (F&M Thm 2.8) IS mechanised (`decidablePLL`/`decidableG4c`);
G3 sequent calculus with cut-elimination + disjunction property; the
Belief* mechanisations promoted into the library; Route B realisability
with the separation triptych; the ⊩ᵖ adequacy+fullness theorem choice-free.

## A2. Terminology guard: Theorem 2.8 vs UI

**F&M Theorem 2.8 = DECIDABILITY of PLL — not uniform interpolation.** It
has LANDED (mechanised, clean axioms, via the repaired calculus G4c).
**UI (uniform interpolation)** = the Pitts-style ∀p/∃p quantifiers = the
separate, still-open thread whose sole gap is one lemma (task #9; see A4).
The successor-project nomination below was originally conditioned "once
Theorem 2.8 lands" — that condition is **already met**.

## A3. Nominated successor project: multi-nucleus lax logic with a join modality

Extracted from the nuclei/model-completions/monads survey
(`docs/surveys/nuclei-model-completions-monads.md`, sections (d), (e) and
the synthesis — read them verbatim when starting):

* **The gap (verified negative, §(d)):** there is no published term
  calculus for the JOIN of two lax modalities — "◯₁ ⊔ ◯₂ as a quotiented
  alternating bind-tower" exists nowhere: the literature offers either
  categorical answers (Beck distributive laws + no-go theorems;
  coproducts of monads: Kelly, Hyland–Plotkin–Power, Ghani–Uustalu) or
  algebraic-effects answers, never a lax-modal proof theory.
* **What it would look like (§(e)):** two nuclei j₁, j₂, each with its own
  I/M/S/Ext rule pack; the join ◯ = j₁∨j₂ = least nucleus above both;
  proof-theoretically the closure of the two rule-sets under alternating
  nesting. In the F&M Boolean constraint algebra this closure is FINITE
  and explicit (TYPES-2000 Def. 1: ⊓ᵢⱼ[K₁ᵢ∧K₂ⱼ, L₁ᵢ∨L₂ⱼ]); over a general
  frame of nuclei it is the transfinite reflection tamed by
  Escardó–Pataraia induction (choice-free — Lean-friendly). Natural
  substrates: adjoint logic (◯ = UF), Mendler–Scheele multimodal CK,
  and Valliappan *Lax Modal Lambda Calculi* (CSL 2026) — check whether it
  treats multiple ◯s before claiming novelty.
* **Why this repo:** the constraint-context machinery (Thm 6), the G4c
  calculus + decider + proof-term emitter + countermodel emitter, and the
  nuclei/assembly groundwork are exactly the toolkit the construction
  needs. **"Multi-nucleus lax logic with an explicit join modality" is
  unclaimed territory for which this repo is unusually well-armed** —
  Matthew nominates it as the successor project. One theorem, three faces
  (survey synthesis): model completion of nuclear HAs (open, coherence the
  hinge) ⟺ joins in N(H) (Escardó) ⟺ coproducts of idempotent monads —
  "coherence is the model-theoretic name for 'the join-iteration doesn't
  terminate finitely'".

## A4. UI thread — current true state (refresh of task #9)

Proof effort RESUMED 2026-07-15 (the "STOPPED 2026-07-12" note is stale).
State: the sole `sorry` of the UI development (`cascade_low_pos_box`) is
reduced, sorry-free, to the one-variable semantic residual
`descent_forcing`; the Lean development `wip/onevar_descent_dev.lean`
compiles with exactly two named holes — (H1) the mechanical clause walk,
(H2) `itpE_stab`, the ∃-side stabilisation past the threshold. The X9
counterexample candidate is DEAD (stabilises at budget 2 against
threshold 16; 5-class state space; oracle-sound). New proof-relevant law,
two lines from the ◯-unit: truncation absorption
`orAll (others ++ [◯(E ⊃ orAll others)]) ≡ ◯(E ⊃ orAll others)` — first
mechanisation target. Full detail: `PROGRESS.md` (repo root) and the
`onevar-descent-probe` memory.

## A5. New tooling to exploit (built 2026-07-17, on main)

* **Fast decider from G4c** — same algorithm as the verified one, much
  more efficient (`prove`, `PLLG4Term.lean`: loop-checked, fuel-free;
  gap sequent instant vs >6.5 min for the verified decider).
* **Proof-term emitter** (`G4cTm`): searcher untrusted, kernel checks the
  emitted term — "if we can build a term, Lean can check it".
* **Countermodel emitter** (`PLLCountermodelEmit.lean`): checker-gated
  FinCM certificates, choice-free; minimisation + TikZ/SVG export.
  Fine-tuning in progress; emitter completeness OPEN.

**Queued study:** assess what this tooling changes about the previously
exhausting proof/countermodel searches, then REVISIT UI at 1 and 2
propositional variables with it (the 2-pv probe — each quantifier one
variable — is designed and ready on the `wip/slick_probe.lean` harness).

## A6. Queued task: the bibliography

Build a LARGE BibTeX bibliography for the Belief paper (now drafted at
`docs/belief-paper-draft.md`, currently very light on references), then
prune. Sources to mine: every reference already cited across
`docs/*-lit.md`, `docs/surveys/`, `docs/iel-justification-lit.md`,
`docs/realisability-modal-lit.md`, the F&M corpus, and the belief-thread
memories. Inclusion bias: **any item with a formal development (Lean, Coq,
Agda) is a candidate** (e.g. Férée–van der Giessen–van Gool–Shillito's
mechanised UI, iSL work). Deliverable: `docs/belief.bib` + a short note
mapping bib keys → paper sections. Second-order goal (Matthew): hunt
HIDDEN CONNECTIONS inside this body — Lean+AI is the instrument; flag
candidates rather than silently dropping them.

## A7. Fresh-session start list

1. Read this addendum, the `belief-paper` + `machine-checked-mandate` +
   `onevar-descent-probe` memories, `PROGRESS.md`.
2. Esakia duality tutorial for Matthew: `docs/esakia-duality-tutorial.md`
   (written 2026-07-18; Johnstone's *Stone Spaces* has Priestley §II.4 but
   not Esakia duality by name).
3. Then, per Matthew's priorities: (a) bibliography (A6, delegable);
   (b) tooling-potential study + UI revisit at 1–2 pvs (A5/A4);
   (c) the successor project (A3) awaits its moment.

## A8 (added 2026-07-18, late). The semantic route to UI — opened, and compressed to one target

`LaxLogic/PLLSemUI.lean` (compiles; two intended sorries) +
`docs/semantic-ui-route.md` (the plan). PROVED today: A-bisimulation for
constraint models (zigzag for BOTH relations, matching fallibility),
forcing invariance, and the full Pitts universal-property layer — any
p-free formula meeting the semantic spec `IsSemEx`/`IsSemAll` IS the
uniform interpolant (`semEx_upper/adjunction`, `semAll_lower/adjunction`,
via choice-free completeness). UI for PLL is thereby equivalent to
DEFINABILITY alone (`semEx_definable`/`semAll_definable`, the Ghilardi
step) — no cascade, no thresholds. Engine: the finite canonical model
(triples; the Θ-promises are the ◯-part of the world descriptions).
Hazards: the ∀∃ ◯-clause under amalgamation (S4-shaped risk; full
heredity is the counter-pressure) and fallible worlds (likely absorbers).
Start at ONE variable with the computation harnesses + two-sided oracle.
Realisability connections recorded in the doc: truth is
bisimulation-invariant, evidence is not (κ-naming); ∀p as p-UNIFORM
evidence (the ⊩ᵘ/⊩ᵖ axis transposed from futures to atoms — candidate
new Belief-paper section); the Thm-6 transfer route is blocked by
Corollary 10 (recorded dead-end with reason).
