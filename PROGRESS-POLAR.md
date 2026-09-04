# PROGRESS — the polarised UI campaign

2026-08-08 · live log, updated in place as work continues. The previous
campaign's log is `PROGRESS.md` (§§1–90, shelved 2026-08-07); this file is the
new campaign only. Companion documents: `docs/lax-logic-interpolation-handoff.md`
(the programme), `docs/lax-interpolation-candidates-strategy.md` (the candidate
method), `docs/ui-two-routes.md` (the routes and their state).

Verification: `lake build` (the focused stack is on the library root).

---

## §1. What is built (all sorry-free, on the root, 2026-08-08 morning)

| file | content | audit |
|---|---|---|
| `LaxLogic/PLLJudgmental.lean` | two-judgment PLL, sound + complete, `equiv_nd`, `equiv_lax` | none at all |
| `LaxLogic/PLLPolar.lean` | polarised syntax, `circ : Pos → Neg`, roundtrip, `phase` | `[propext]` |
| `LaxLogic/PLLFocused.lean` | focused calculus, four judgments with the `JD` flag; **soundness** | clean |
| `LaxLogic/PLLCandidate.lean` | `Cand p` — the 13 closure clauses read off the rules | (definition) |

Findings along the way, each in its file's header or commit:

* `CircInvert` is free — `circE` with the identity continuation (monad law).
* At `.lax`, ⊃-right would be the converse of K (refuted `wip/converseK.lean`);
  `impR`/`andR` are `.tru`-only. Found by the soundness proof, not inspection.
* `circL` is the only rule that reads the flag — the entanglement is confined.
* Candidates must be indexed over **inversion sequents**: over stable sequents
  the join clause is not even statable (no `⊔` on `List Neg`).
* The contraction-count is `cl_circL`, guarded, `.lax`-only — the strategy
  document's "cheap early test" comes out positive.
* The load sits on **`cl_orL`**, the one clause `∨` contributes. Third
  independent arrival at ∨ (after the ∃p/∀p split and the ∨-free finiteness).

## §2. The attack on `cl_orL` — plan (2026-08-08, midday)

The candidate semantics to try first, because it is the one the ∃p argument
already suggests: for a fixed `p`-free "budget" of hypotheses,

    C_θ Γ Ω j N  :=  the p-free content of (Γ; Ω ⊢ N at j) is entailed by θ

made precise as: every p-free consequence of the sequent is a consequence of θ.
The join clause for C_θ is then exactly the statement that the p-free
consequences of a disjunction are the intersection of the branches' p-free
consequences — which is TRUE and easy (∨-left). The place it can fail is not
the join itself but **extremality**: whether among the satisfying θ there is a
least one (the ∃p of the sequent), and that is the directedness question of
`docs/ui-two-routes.md` §1 again, now in candidate form.

So the attack decomposes:

1. define the p-free consequence relation of an inversion sequent;
2. prove the 7 unconditional clauses for `C_θ` (expect: routine, ∨-left included);
3. prove the 6 guarded clauses (expect: `cl_circL` needs the lax phase — the
   place to watch);
4. extremality: the least θ. This is where directedness lives and where the
   outcome (theorem vs impossibility) will be decided.

Status: starting.

---

*(append below as progress happens; do not rewrite above)*

## §3. The join clause FELL — all thirteen clauses hold (2026-08-08, afternoon)

`LaxLogic/PLLCandOr.lean`, on the root, sorry-free, `lake build` 8668 green.

**The result.** For any budget `θ`, the consequence candidate

    Cθ θ Γ Ω j N := Nonempty (LaxND (θ :: ⌜Γ⌝ ++ ⌜Ω⌝) (wrap j ⌜N⌝))

satisfies **all thirteen closure clauses**, assembled as `candOf p θ : Cand p`.
In particular:

* `cθ_orL` — **the join clause, the one the difficulty was traced to, is
  ∨-elimination**. A theorem, `[p,C,Q]`.
* `cθ_circL` — the contraction clause holds by `laxElim` **with the
  ◯-hypothesis retained**: `Q` enters `Ω` while `◯Q` stays in `Γ`. The
  retention discipline of the G4c repairs reappears as a fact about the
  candidate, not a rule design. Choice-free `[p,Q]`.
* `cθ_strengthen` — budgets are closed under strengthening, `[propext]` only.

**Two corrections found by discharging** (the strategy document's discipline
working as intended): `cl_impL` and `cl_andL` as first extracted were
trivially satisfiable — the continuation had lost its new hypothesis. Fixed in
`PLLCandidate.lean` (`N :: Γ` resp. `M :: Γ` in the continuation; `cl_andL'`
added for the second projection).

**What this means.** Candidacy is CHEAP — every budget is a candidate, and
p-freeness was not even needed for the closure clauses. So the closure clauses
do NOT carry the difficulty of uniform interpolation; the entire content has
moved into **extremality**, stated precisely as `ExtremalBudget p Γ Ω j N`:

    a p-free θ with Cθ θ (the sequent), entailed by every p-free θ' whose
    candidate also accepts the sequent — the WEAKEST p-free budget.

Uniform interpolation IS the inhabitation of `ExtremalBudget` for every
sequent. This is the ∃p/∀p asymmetry of `docs/ui-two-routes.md` §1, reached a
second way; the directedness criterion is what inhabitation will need.

**Assessment, plainly.** The candidate method did what its document promised —
each mis-stated clause was caught by attempting its discharge, and the load was
localised — but the localisation's lesson is that closure was never the hard
part for THIS candidate family. The hard part is extremality, and for that the
finite ∨-free fragment (`neg_exactly_four`, the eight-element algebra) is the
natural place to try inhabitation first: at ZERO variables `ExtremalBudget`
should be computable outright.

Next: inhabit `ExtremalBudget` in the closed fragment (p not occurring at
all — the degenerate sanity case), then at one variable over the ∨-free
fragment, where L_p is finite and the candidate set can be enumerated.

## §4. THE CONVERGENCE THEOREM — extremality IS ∀p, machine-checked (2026-08-08)

`extremal_iff_forallp` + `cθ_iff_entails` (`PLLCandOr.lean`, pinned clean):
acceptance curries — `Cθ θ S ↔ θ ⊢ ⌜S⌝` — so the extremal budget of a sequent
is precisely **the greatest p-free formula entailing the sequent formula**,
i.e. the propositional quantifier **∀p ⌜S⌝**. The candidate route, run to
completion, lands exactly on the object the algebraic route (ui-two-routes §1)
identified as the hard half. ∃p never appears: the closure clauses absorbed it.
Also `extremalOfPFree`: when ⌜S⌝ is itself p-free it is its own extremal
budget (minimality not even needing the competitor's p-freeness).

**The reduction, now proved rather than suspected.** UI for PLL ⟺ for every
sequent formula φ, the set T = {ψ p-free : ψ ⊢ φ} has a greatest element.
T is an IDEAL — downward closed, and ∨-closed (ψ₁ ⊢ φ, ψ₂ ⊢ φ ⟹ ψ₁∨ψ₂ ⊢ φ).
So the question is PRINCIPALITY of these ideals, and failure requires an
infinite strictly ascending chain of p-free formulas below φ.

**The refutation hunt this licenses.** At ONE variable, "p-free" = CLOSED, and
the repository already has a mechanised infinite strictly ascending chain in
RN(◯,{}): the boxed odd rungs `chainF k = ◯t(2k+1)`, `chain_step_strict`
(wip/chainStrict.lean, 2026-08-02). So UI for PLL FAILS iff some one-variable
φ(p) has its closed lower ideal generated by such a chain — a φ that every
`chainF k` entails, while every closed θ ⊢ φ sits below some `chainF k`.
That is a concrete, finite-to-state hunt, and it is exactly where Matthew's
1-pv instinct pointed. In IPC Pitts guarantees every such ideal is principal;
◯ is the only new ingredient, and the chain that could break principality is
made of ◯'s.

Next: the hunt for that φ — or the proof that no such φ exists, which would be
the 1-pv base case of UI. Either outcome is the paper.

## §5. Ascending vs descending — the two dual hunts (2026-08-08, Matthew's question)

Matthew: previously we looked for infinite DESCENDING chains; §4 asks for
ASCENDING. What changed? Answer: the quantifier. Nothing else.

    ∃p φ = least element of the FILTER  S = {ψ p-free : φ ⊢ ψ}  (∧-closed)
           fails ⟺ descending coinitial chain, no floor
    ∀p φ = greatest element of the IDEAL T = {ψ p-free : ψ ⊢ φ}  (∨-closed)
           fails ⟺ ascending cofinal chain, no cap

Chains are wlog in both directions: T ∨-closed ⟹ (countable) non-principality
⟺ a strictly ascending cofinal chain exists; dually for S via ∧.

The earlier exploration (Gmeet descending, gap_no_glb, the floorless chain of
next-session §7) is ∃p-side ammunition. The convergence theorem landed the
candidate route on ∀p, whose chain is chainF (ascending, chain_step_strict).

SCOPE, honestly: full UI needs BOTH quantifiers. The ∨-free local-finiteness
argument freed ∃p within the ∨-free fragment only; for full PLL at 1 pv
(p-free = closed, closed fragment infinite) ∃p is NOT settled and the
descending chain is its threat. Two hunts, each with its chain mechanised:

  ∀p hunt: φ(p) with ∀k chainF k ⊢ φ, and every closed θ ⊢ φ below some chainF k.
  ∃p hunt: φ(p) with ∀n φ ⊢ Gmeet n, and every closed consequence above some Gmeet n.

The ∃p hunt inherits the old campaign's floor machinery (wip/floor.lean,
wip/floorRefute.lean, the Gmeet family) and is likely the cheaper start.

## §6. Second-order candidates, the least candidate, and the armed hunts (2026-08-08 evening)

**Matthew's structural point, and its proof.** He asked whether candidates must
be strictly second-order. YES — and `extremal_iff_forallp` is now the proof:
any FORMULA-indexed candidate family collapses to ∀p, chains and all. So the
convergence theorem is re-read as: first-order candidates buy nothing. The
chains are refutation-only instruments; the positive route must go through
predicates on sequents.

**The least candidate exists, for free** (`LaxLogic/PLLCandLeast.lean`):
`LC p` is the inductive predicate whose CONSTRUCTORS are the thirteen clauses
— a least fixed point, no extremal formula needed. `LC.toCand` (it is a
candidate), `LC.initial` (contained in every candidate — NO AXIOMS AT ALL),
`LC.le_budget` (via initiality, LC-membership makes the sequent derivable from
every budget — LC marks the sequents whose p-content is irrelevant).
UI = DEFINABILITY of this second-order object by a formula, per antecedent.
Refuting definability = the chains; proving it = the phase recursion, which is
the next build.

**The refutation criteria, kernel-checked, generic**
(`LaxLogic/PLLUIChains.lean`, [propext] only): `no_least_consequence` (∃p) and
`no_greatest_antecedent` (∀p), generic in the chain AND in the p-free class.
The unused-variable linter found the chain's monotonicity hypotheses were
unnecessary — strictness and trapping suffice — so the criteria are stronger
than the prose that proposed them.

**The hunts, armed** (`wip/hunts.lean`, in wipshared):

    no_existsP_of_trap : φ below every Gmeet n + closed consequences trapped
                         above the chain ⟹ NO post-interpolant
    no_forallP_of_trap : every chainF k below φ + closed antecedents trapped
                         below the chain ⟹ NO pre-interpolant

New mechanised inputs both hunts needed:
* `Gmeet_strict : Gmeet n ⊬ Gmeet (n+1)` — strict descent of the gap meets,
  proved from the cmE edged lift (gap_forced/gap_fails); a fact the floor
  campaign never pinned.
* `varFree_rnSub/chainF/gap/Gmeet` — closedness of all chain members, via the
  substitution lemma `varFree_embed` (embed = substP pv ◯⊥).

Each hunt is now exactly TWO obligations about a witness φ. Next: candidate
witnesses. The trapping condition is the hard half in both; the natural first
φ's are GZ-style limit formulas over the respective chains.

## §7. BOTH HUNTS ARE VACUOUS — no witness can exist, either side (2026-08-08 night)

Instruction was: start the ∃p hunt. The first step of a refutation hunt is to
check a witness COULD exist. It cannot — on either side — and the reason was
already in the repository, proved by the shelved campaign for a different
purpose. Two new theorems in `wip/hunts.lean` make it explicit:

    existsP_trap_unsatisfiable : ¬ ∃ φ, (∀n, φ ⊢ Gmeet n)
                                        ∧ (closed consequences trapped)
    forallP_trap_unsatisfiable : ¬ ∃ φ, (∀k, chainF k ⊢ φ)
                                        ∧ (closed antecedents trapped)

**∃p side.** `collapse` (wip/collapse.lean) — every gap-entailing φ entails
some rung — yields `post_interp_exists`: every such φ has a CLOSED consequence
ψ which itself entails every gap. That ψ breaks the trap immediately: the trap
demands `Gmeet n ⊢ ψ` for some n, while ψ ⊢ Gmeet(n+1) always, giving
`Gmeet n ⊢ Gmeet (n+1)` against `Gmeet_strict`.

**∀p side, the mirror.** `c_chain_bound_is_theorem` (wip/rungbound.lean) — a
formula entailed by every chainF k is an outright THEOREM. Then ⊤ is a closed
antecedent, and the trap would demand `⊤ ⊢ chainF k`, i.e. chainF k a theorem;
`chainF_not_theorem` (new, one line from chain_step_strict) forbids it.

**What this means, precisely.** These do NOT refute uniform interpolation, and
do not prove it. They kill the two chains as REFUTATION INSTRUMENTS: the
mechanised ascending and descending chains of RN(◯,{}) cannot be the shape of
a counterexample, because anything sitting at their limit collapses onto a
closed formula (a rung, or ⊤) which is then trapped by construction. The
chain criteria of `PLLUIChains.lean` remain correct and generic — they simply
have no instance here.

**Duplication check, honestly.** `existsP_trap_unsatisfiable` is the same fact
as `post_interp_schema_vacuous` and `forallP_trap_unsatisfiable` the same as
`pre_interp_schema_vacuous`, both already in the repo. What is new is only the
routing: they are now stated as unsatisfiability of the CANDIDATE-METHOD trap
hypotheses, which is what connects them to `PLLCandLeast.LC`. Had I searched
the repo before arming the hunts, §6 would have been written differently — the
memory rule "search before treating a finding as new" applies to my own
instruments, not just to results.

**Where this leaves the programme.** The negative prong is closed for these
chains; a counterexample would need a genuinely different escaping family, and
the two collapse theorems constrain what that could look like (its limit must
avoid collapsing onto a closed formula — which is exactly what both collapse
theorems say cannot happen for gap-entailing or chain-entailed formulas). So
the weight shifts to the POSITIVE prong: the phase recursion over PLLFocused,
verified against LC by initiality. That is the next build.

## §8. The IPC control experiment — and the gap it found (2026-08-08 night)

Matthew's test: build the polarised/focused apparatus with the lax rules
omitted, same names throughout, and see whether the proposed UI proof runs.

`LaxLogic/IPCFocused.lean`, namespace `IPC`, sorry-free, on the root.
Calculus named **`LJF`** (Liang–Miller); the PLL version is **`LJF◯`** = LJF +
`◯` + the second judgment. Differences are exactly: no `circ`, no `JD` flag,
no `circR`/`circL`, and `impR`/`andR` unrestricted.

**PROVED outright** — `∃p` side, all four left-inversion clauses, each named
for its rule as in `Cand`: `cl_fls`, `cl_downL`, `cl_atomL`, `cl_orL` (the join
clause, four lines, exactly as `cθ_orL` was in PLL). Plus soundness of all four
judgments, and `exInterp_of_stable` assembling the whole inversion phase as a
terminating recursion on `sizeΩ`.

**THE GAP THE EXPERIMENT FOUND.** `StableInterp` was stated as a leaf of the
recursion. It is not. At a stable sequent the only way to use `Q ⊃ N ∈ Γ` is
`LFoc.impL`, whose first premise is `Stab Γ Q` — a GOAL-directed subproblem
(Dyckhoff's case). So computing the p-free content of an ANTECEDENT needs the
p-free content of a GOAL:

    ∃p and ∀p are MUTUALLY RECURSIVE, and the structure as built was incomplete.

This was invisible while only inversion clauses were in view — every one of
them goes through with `ExInterp` alone — and would have been carried into the
PLL development unnoticed. That is precisely what the control was for, and it
is the first time this campaign's structure has been caught being wrong rather
than merely incomplete.

**The missing half added**: `AllInterp` (∀p at a goal), with
`allInterp_pfree` (axiom-free) and `allInterp_and` (`[propext]` only) proved.

**Where the difficulty localises, sharply**: the IMPLICATION clause of ∀p. The
obvious candidate `(∃p Q) ⊃ (∀p N)` is sound but NOT minimal — from p-free ψ
with ψ ⊢ Q ⊃ N one cannot recover Q from ∃p Q, which is weaker. Repairing that
IS Dyckhoff's weight argument, i.e. the whole of Pitts. Left as the explicit
hypothesis `ImpInterp`.

**No back door.** I was about to discharge `StableInterp` by lifting `existsP`
out of `wip/final.lean` (whose IPC crown is genuinely sorry-free). Matthew
stopped it, correctly: that would supply the formula from Pitts' recursion
rather than from these clauses, making the machinery decorative. The
construction here emerges from the proof — `ExInterp`/`AllInterp` are Σ-types
whose `fml` field the clauses build.

**Consequence for PLL**: `circL` is the only stable-phase rule IPC lacks. So
the entire difference between the two logics, for UI purposes, is one rule of
one phase — sitting on top of a core difficulty (the ∀p implication clause)
that both logics share and neither has here.

## §9 — The pure development: LJF from the ground up (2026-08-08, late)

Direction change on Matthew's instruction, stated back and confirmed: the
technique is under test, so **nothing is borrowed from any other calculus** —
no `Deriv`, no `G4c`, no substitution lemmas, no completeness. `LaxLogic/LJF.lean`
imports nothing at all, not even Mathlib. Cut is **not** used anywhere and is
not planned to be: identity expansion plus per-clause invertibility carry the
property proofs (cut-admissibility remains available as a corollary-grade
extra, per Matthew's expectation).

### Landed, sorry-free, `lake build` green (commits e8bcd3f, 6b9696f)

1. **The calculus.** `LJF` = canonical-polarity Liang–Miller: `Stab`/`RFocus`/
   `LFoc`/`Inv`, weakening as one traversal, identity expansion as the mutual
   pair `posRestore`/`idNegK` (continuation-passing, no cut).

2. **The weight, solved for.** `atom = ⊥ = 1`; `∨`, `⊃`, `↓` cost +1; `∧`
   costs +3; `↑` costs 0. Contexts measured by `Σ 3^w`. Each clause of the
   recursion contributes an inequality and this assignment satisfies all of
   them — the costs differ from Dyckhoff's because the shifts change the
   clause set. The exponential base does the multiset-order work: one
   hypothesis of weight w is only ever replaced by ≤ 2 of weight ≤ w−1,
   and 2·3^(w−1) < 3^w.

3. **The interpolant as a total function.** `interp p todo done goal` computes
   BOTH quantifiers in one recursion — `goal = none` is ∃p (strongest p-free
   consequence of the context), `goal = some G` is ∀p (weakest p-free missing
   hypothesis). Eleven processing clauses, fire-saturation of parked atom
   implications, then the saturated aggregate whose three irreducible shapes
   are exactly G4ip's: atoms, `a ⊃ N` with `a` absent, and the Dyckhoff
   implication `↓(Q′ ⊃ N′) ⊃ N`, whose clause is the mutual ∃p/∀p recursion.
   Termination: single Nat measure `2·sum3 todo + sum3 done + goalW goal` —
   the factor 2 makes parking strict; no lexicographic order.

4. **p-freeness.** `interp_pfree`, by the functional-induction principle Lean
   derives from the weighted recursion, all 22 cases.

### The remaining contract (recorded at the end of LJF.lean)

E1/A1 (soundness of both modes) and E2/A2 (minimality of both modes), with
the internal toolkit: hypothesis-simulation traversal + branch extraction.
The expected mountain is the E2/A2 case for the Dyckhoff implication — the
focused `(A⊃B)⊃C` argument. If it resists, it is carried as an explicit
hypothesis.

### What the weights are FOR (Matthew's question, answered in full in the
file header of Part 2 and in the session report)

Uniformity forces the interpolant to be defined by recursion on the sequent,
not on a derivation. The clauses transform rather than decompose (currying
preserves naive size; the ∨-antecedent clause duplicates N; goal inversion
grows the context), so no naive measure survives; the weight is the solution
of the clause-inequality system, and the exponential sum is a Nat-valued
stand-in for the Dershowitz–Manna multiset order. Necessity: a loop-checker
could give termination of search but yields no formula — the interpolant is
built BY the recursion, so its existence needs structural well-foundedness.
And it buys predicativity: the interpolation candidate is a least fixed
point; Girard-style candidates take such fixed points impredicatively, while
the weight reaches this one by well-founded recursion.

## §10 — The four properties (2026-08-09)

All on `main`, `lake build` green, sorry-free, axioms pinned at
`[propext, Classical.choice, Quot.sound]`, file still imports nothing.

* **E1 `eSound` : Γ ⊢ ∃p(Γ)** — PROVED unconditionally (db733d4).
* **A1 `aSound` : ∀p(Γ⇒G), Γ ⊢ G** — PROVED unconditionally (db733d4).
* **E2 `eMin`** — PROVED modulo `SatE2` (3448020): every processing clause
  discharged by its inverse transformation (a `simulate` instance per
  clause); the saturated case is the explicit hypothesis.
* **A2 `aMin`** — PROVED modulo `SatA2`, same shape.

Two structural discoveries, both forced by the minimality induction *before
writing its Lean*, both now in the definition of `interp` (da31337 and the
following commit):

1. **The E-guards.** The ∀p clause for an implication goal must be
   `⋀_b (↓E(Γ+b) ⊃ A(Γ+b ⇒ N))`, and likewise the ∀p clause for a context
   disjunction — the unguarded forms would demand `E(Γ) ⊢ E(Γ+b)`, which is
   false. Soundness still closes because `eSound` supplies the guard.
2. **eMin/aMin are not mutual.** The E/A coupling lives entirely in the
   E-guards of `interp` and in the saturated case; each minimality function
   recurses only into itself.

The cut-free toolkit that carries all of it: `routeStab` (CPS re-targeting —
shift release, disjunction routing, ex falso in one traversal), `simulate`,
`extract`/`invBranches`, `stableFire`/`upMerge`, `resSim` (the focused
`(A⊃B)⊃C ⊢ B⊃C`), the inverse transformations `inv*`.

**OPEN**: `SatE2`/`SatA2` — minimality at saturated contexts, the inner
induction over derivations (the heart of Pitts). That is the whole distance
between here and unconditional UI for LJF; then LJF-completeness bridges to
IPC, and `circL` is the only new rule for PLL.

## §11 — The saturated case, opened (2026-08-09, second session)

Review findings (all repaired on `main`): SatE2/SatA2 were FALSE as stated
(parkedness missing — counterexample `done = [↑q ∧ ↑q]`); the ∀p clause for
an implication goal AND the ∀p clause for a context disjunction both need
E-guards (`⋀_b (↓E(Γ+b) ⊃ …)`); the four properties' induction is a plain
predicative WF-recursion — the second-order candidates apparatus is
scaffolding, not load-bearing, exactly as expected for a non-impredicative
target.

The inner induction (Pitts' hard lemma) is DESIGNED AND WRITTEN, one
statement isolated:

* `DykAnt` — the Dyckhoff antecedent dispatch — is the SINGLE remaining
  hypothesis; one statement serves both modes.
* The p-fire elimination needs NO extra hypothesis: `init` on `↑p` is
  refuted by saturation + parkedness + p-free kept side; nested p-fires
  shortcut to their own premise; every other fire composes the outer
  `p ⊃ M` package with the inner fire's body into a genuine derivation
  over the fired context, handed to eMinF at smaller measure.
* Everything on `main` compiles: the dispatch helpers (fireClean,
  atomAssemble/qAssemble/dykAssemble, interpE_eq), saturation facts,
  ΩOk-invariant machinery, dec_fireT/dec_dykT.
* Branch `claude/inner-induction`: the full 8-def mutual
  {eMinF, TInv, TStab, TRF, TLF, TpElim, TpLF, TpInv} — all dispatches
  type-correct; 8 termination obligations remain, all in the aggregate
  arm's tactic block (two shapes, both provable by the context lemmas —
  suspected decreasing_by attachment issue; diagnose fresh next session).

Literature (docs/second-order-pll-survey.md, full survey): **Iemhoff 2024
(arXiv:2209.08976) already proves UI for PLL** — claim discipline is now
"explicit machine-checked construction", not "first proof". Second-order
PLL does not exist; recommended name PLL2; Aczel's Russell–Prawitz
modality is the near-miss (J ⊢ ◯ strictly).

## §12 — SatE2 PROVED modulo DykAnt (2026-08-09, 08:09)

`satE2_of_dyk : DykAnt p → SatE2 p` — on `main` (892deec), sorry-free,
axioms pinned. The three termination diagnoses that unblocked the 8-def
mutual are recorded in commit 07debf6 for reuse on the A-side:
(1) align lexicographic first components SYNTACTICALLY (0 + n is not
defeq to n); (2) never `cases` an atom equality inside a dispatch —
generalise the p-fire family over both atoms with a = p, b = p
hypotheses; (3) prefer an offset first component (μ+1, 0) to a sizeOf
tie-break across defs.

REMAINING for unconditional UI-for-LJF: (i) DykAnt — the Dyckhoff
antecedent dispatch (X-to-residual commute with branch bookkeeping);
(ii) the A-side mirror (aMinF + U-components: attack emissions instead
of conjunct fires; goal-clauses already discharge through aMin);
(iii) LJF-completeness for the bridge to IPC-as-Deriv.

Correction to §11's survey note: Iemhoff 2024's UI-for-PLL proof rests
on her G4iLL, which this repo REFUTED as incomplete (machine-checked
counterexample, 2026-07-08, wip; unsent letter in repo). UI for PLL
remains OPEN — this campaign is the third serious attempt, and the
claim discipline is back to "first proof, machine-checked".

## §13 — The Dyckhoff commute PROVED (2026-08-09, third session stretch)

Commit 24d41b6 + this: on branch `claude/inner-induction`, all green.

* **The E-res conjunct** (third definition change forced by the (ii)
  induction): the ∃p Dyckhoff conjunct is now the PAIR
  `(↓A([res],rest ⇒ Q'⊃N') ⊃ E([N],rest)) ∧ E([res],rest)` — without the
  second component the dispatch needs minimality at its own station (a
  measure-climbing call); with it, it projects. Full cascade repaired.
* **`negOfDownStab`** — shift release into a plain derivation, by
  recursion on the formula (mirror of upMerge), via the CPS release
  `relStab/relLF/relInv`.
* **`dykCommute`** — PROVED: a mixed-context stable proof of the
  antecedent `↓(Q'⊃N')` becomes a derivation over the residual station;
  X-uses are manufactured from the residual because the branch of Q' in
  context closes the released implication (extract). Focused Dyckhoff.

**DykAnt is now mechanical**: dykAntC := (E-res-conjunct-projection via
simHyp) ∘ aMinF([res],rest) ∘ dykCommute. It needs aMinF — i.e. the
A-side — so the final assembly is ONE mega-mutual: the E-components
(moved in, dyk-parameter replaced by the in-mutual dykAntC) + aMinF +
the U-components (attack emissions; goal-clauses discharge through
aMinF + the guards; p-fires mirror TpElim; atom-parts use the satE
already available as the E-components are in the same mutual).
Measures: the established lexicographic pattern; dykAntC's first
component sits in the dec_dyk1 slack. All three termination diagnoses
of §12 apply verbatim.

## §14 — UNIFORM INTERPOLATION FOR LJF: PROVED (2026-08-09)

The mega-mutual landed. All four characteristic properties plus the
saturated cases and the Dyckhoff dispatch are machine-checked,
unconditionally, sorry-free, axioms [propext, Classical.choice,
Quot.sound]:

  eSound  aSound  eMinF  aMinF  satE2  satA2  dykAnt

The final week's structure: dykCommute (the focused Dyckhoff commute) +
aMinF at the residual station + projection of the E-res conjunct
discharged DykAnt; the A-side traversal (UEntry/UStab/URF/ULF/UInvG +
the UpElim p-fire family) emits attack disjuncts where the E-side fired
conjuncts; the p-fire elimination needed no extra hypothesis in either
mode. The termination war ended with the Prod.Lex display-deception
diagnosis and term-level monotone chains (defeq-unification replacing
omega atom-sharing). Full account and the simplification/tools pass:
docs/ljf-simplification-pass.md.

Remaining: focalization completeness (→ UI for IPC); then circL + the
lax judgment through every layer (→ UI for PLL, the open prize).
