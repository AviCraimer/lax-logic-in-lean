# The uniformity endgame: from height-fuel to Γ-only fuel

*Status map written 2026-07-10 evening, after P4a landed.  This is the
design record for the final layer of the uniform-interpolation
mechanisation: what is proved, what remains, and the two candidate
routes for the last step, with the failure analysis that selects
between them.*

## What is proved (all in the build graph, audits pinned)

| Layer | Statement | File |
|---|---|---|
| Quantifiers v2 | `interE p fuel Γ`, `interA p fuel Γ C` — Pitts/Iemhoff/UIML clause tables adapted to retention | `PLLG4UI.lean` |
| p-freeness | `p ∉ atoms (interE/interA …)` | `PLLG4UI.lean` |
| E1/A1 | `Γ ⊢ interE`, `interA, Γ ⊢ C` (every fuel) | `PLLG4UI.lean` |
| Fuel monotonicity | `interE_{f+1} ⊢ interE_f`, `interA_f ⊢ interA_{f+1}` + multi-step | `PLLG4UI.lean` |
| **Adequacy (P4a)** | for height-`n` derivations of `Γ ∪ Δ ⊢ C`, Δ p-free, any `fuel > n`: `(p∉C → interE, Δ ⊢ C) ∧ (interE, Δ ⊢ interA)` | `PLLG4UIAdq.lean` |
| Set-congruence | set-equal contexts give ⊣⊢ quantifiers | `PLLG4UIStab.lean` |
| Lax fixpoint lemma | `◯((α ∨ ◯(α∧β)) ∧ β) ⊣⊢ ◯(α∧β)` — pure monad, no Löb | `PLLG4UIStab.lean` |

The missing layer is **uniformity**: the packaged interpolant must sit
at a fuel computed from Γ (resp. Γ, C) alone, while P4a's fuel grows
with the derivation.  Equivalently: the *stabilization* directions

    SE: interE p H(Γ) Γ ⊢ interE p f Γ          (f ≥ H(Γ))
    SA: interA p f Γ C ⊢ interA p H(Γ) Γ C       (f ≥ H(Γ), modulo an
                                                  interE-ambient)

with `H(Γ) := defect(Γ) + O(1)`, `defect` = space formulas not yet in
the context set (the decider's own budget).

## The E-side closes; the analysis

SE has a clean proof by the **whole-context strategy**: derive each
clause of `interE_{f+1}` from the *entire* `interE_H` (not from its
corresponding clause):

* grown-context clauses — project `interE_H`'s own clause one level
  down, then compose fuel-monotonicity with the defect-descent
  induction hypothesis (strictly smaller defect);
* same-set clauses — set-congruence collapses them onto the state
  itself, closed by the inner induction on `f`;
* **guarded clauses need no guard analysis at all**: an implication
  whose consequent is derivable from the ambient conjunction is
  derivable outright (weakening) — and the consequent always is, by
  the two bullets above.  The ◯-clauses close the same way through
  `laxR`/`box_mono`.

## The A-side wall: the offset cascade

SA resists the same strategy.  Mapping a source disjunct of
`interA_f` onto the target disjunct of `interA_H` requires rebuilding
the target's **guard components** `interE_{H-1}(Γ') ⇢ interA_{H-1}(Γ', G)`.
For *grown* Γ′ the defect-descent pays as always.  For *same-set* Γ′
the required component sits at level `H−1` — **one below the
threshold** — and every attempt to lower a level-`f` fact to level
`H−1` regenerates the same demand one level lower: an off-by-one
cascade that terminates only when the state descends (defect grows),
which same-set positions by definition never do.  Three session-hours
of invariant surgery (target-level quantification, threshold shifts
`H+1`, `H+2`, mono-first detours, adequacy sandwiches) all reproduce
the cascade; we record this as strong evidence that **SA is not
provable by disjunct-to-disjunct mapping over the v2 definition**, and
that this is the precise shadow of the termination failure that broke
Iemhoff's original proof: the same-set guard is the reset-without-
growth case wearing a different hat.

## The two closing routes

**Route T (truncation — recommended, the GL/UIML playbook).**  Change
the definition once more (v3): make the quantifier recursion
*well-founded* on ⟨defect, goal-weight⟩ by omitting same-set clause
recursions (retention makes the omitted premise the conclusion's own
sequent — the adequacy proof already skips those steps without
touching any clause, so P4a transfers almost verbatim), and replacing
the one genuinely self-referential piece — the ◯-goal disjunct
`◯(E ⇢ A(Γ ⇒ ◯D))` — by its **one-step-unfolded truncation**
`◯(E ⇢ ⋁(other disjuncts))`, exactly Bílková's `N`-device.  Fuel
disappears entirely; uniformity is definitional.  New obligations:
(a) soundness/p-freeness/adequacy re-runs (mechanical; the P4a case
analysis carries over, with the Δ-side `laxL` commute now consuming
the N-disjunct); (b) the **N-redundancy lemma** — the truncated
disjunct entails the disjunction of the others in the consumers'
context — whose engine is the lax fixpoint lemma just proved
(the collapse is monad multiplication; GL needed the 4-axiom).
This is the identified genuinely-novel lemma; nothing like it is in
the literature for lax logic.

**Route S (cascade-closing, kept as fallback).**  Prove SA directly by
finding an invariant that breaks the off-by-one — e.g. a vector-valued
statement over all goals at a state with a Ruitenburg-style
periodicity argument.  Empirics support it (machine-verified
stabilization at fuel ≈ 3 on every tested instance, both quantifiers,
through fuel 8), but the only known proof technologies are open
research (Litak's Open Problem 1 is the substitution cousin for PLL).

## Also true and worth stating in the paper

* P4a alone already yields **ordinary Craig-style interpolation
  statements per instance** and a *per-derivation* uniform
  interpolant; only the single-formula-for-all-consequences form
  awaits the truncation step.
* The height-inclusive collapse (`n < fuel` is the entire adequacy
  invariant) is a reusable observation for any retention calculus:
  cumulative contexts absorb what termination orders were paying for.
* Empirical stabilization data (probe files in the session scratchpad,
  verified by the kernel decider): every instance stabilizes by fuel 3;
  the movers grow syntactically forever while staying ⊣⊢-constant —
  any mechanisation of Route S must live in the Lindenbaum quotient.

## Route T, second design pass (2026-07-11): the jump system

Working the v3 definition against the rules exposed one more knot the
first pass had underestimated: `impLLax`'s first premise (`Γ ⊢ A` with
`◯A⊃B ∈ Γ` retained) keeps the context **identical** and only jumps
the goal — the retention repair transfers the very payment that made
Iemhoff's recursion terminate.  The GL/iSL mechanisations never face
this: their modal premises always shrink the context weight.  What
falls out:

* **Empirical validation first** (session probes; algebraic
  differencing over Heyting-algebras-with-a-nucleus — sound for PLL,
  linear-time on megaformula values — plus the kernel decider on small
  instances): the *omission law* (same-set clauses dropped) and the
  *N-truncation* match the stabilized v2 values; a jump **budget**
  `b` stabilizes empirically by `b ≈ 2–3`.  The *bare law*
  (`◯(E⇢Z) ⊣⊢ ◯Z` under ambient `E`) validated on most of the battery
  but **flagged a divergence on the gap-theorem context**, which
  prompted the v3.1 repair: keep v2's guarded shapes verbatim and
  make every same-context reference — `E` and `A` alike — pay the
  budget.  **Resolution (later the same night):** the flag was a
  *comparison* artifact — `E`-values descend pointwise toward the
  fixpoint as fuel grows (fuel-mono direction), and v2 simply had not
  converged by fuel 4–5 on that context: the fuel-5→6 step dropped by
  exactly the 40 points separating it from v3.1, while v3.1 was
  already budget-stable at `b = 2`.  So v3.1 computes the limit
  directly.  The guarded v3.1 shapes are kept regardless: the
  adequacy case-map consumes guarded pairs (the IHs deliver exactly
  that shape), and the design principle stands on its own — only
  congruence-grade equivalences may be folded into a quantifier
  definition; ambient-relative ones (the bare law included) belong to
  consumption sites.  Budget-annotation is congruence-grade once
  absorption holds, so it is safe in any polarity.
* **The consumer-side bookkeeping cannot mirror the budget.**  A
  Δ-side decomposition between two Γ-side jumps changes the consumer
  sequent (so no splicing) without touching the quantifier's
  arguments; cumulative Δ-stages are bounded only by Δ's piece
  closure, which uniformity must not mention.  So a refined
  "chain-credit" judgment does not close the gap by itself: the glue
  has to live at the **value level**.
* **The absorption lemma** (the genuinely novel step, replacing the
  first pass's N-redundancy): for `b` at least the jump-goal count,
  `itpA@(b+1) ⊢ itpA@b` (with `itpE` dually) — one-step budget
  stabilization.  Proof design, validated case-by-case: a lazy
  orL-cascade down the source's jump components, keeping the target
  goal un-introduced; a chain of length `> K` must repeat a jump goal
  (pigeonhole — premise-1 chains keep the context fixed, goals range
  over the space's `≤ K` jump goals); at the repeat, the *spliced*
  target chain (length `a < j`) is introduced instead, and the leaf
  hypothesis `A@(b−j+1)(g)` reaches the target component `A@(b−a)(g)`
  by **budget monotonicity** (`b−j+1 ≤ b−a` — the slack `j−a ≥ 1` is
  exactly what the repeat buys); the skipped coefficients are simply
  never used (∧-decrease as projection).  Budget-mono is the easy
  half; the cascade is the hard half; `lax_fixpoint`/`box_guard`
  handle the ◯-goal self-reference separately.

  Intended Lean statement — **corrected 2026-07-11 morning after
  hand-executing the boxed cases**: the *pure* form
  `[itpA@(b+1)] ⊢ itpA@b` is stronger than anything the adequacy
  landing needs, and its γ-box positions demand an E-glue one budget
  below the band at every crossing — an infinite regress (each route
  tried funnels into the pure descent at ◯-shaped jump goals).  The
  landing always holds the ambient `E(Γ)`, and the correct statement
  is **ambient-relative** (`wip/absorb_base.lean`, threshold
  `kcap S := 2·S.card + 4` overcounting the jump states):

      itp_stab : kcap S < b → ∀ fuel,
        (∀ Γ,   G4c [itpE@(b-1)] (itpE@b)) ∧
        (∀ Γ C, G4c [itpE@b, itpA@b Γ C] (itpA@(b-1) Γ C))

  The E-half needs no extra ambient — E is its own.  With ambient E
  the box barrier dissolves: budget-mono (`E@b ⊢ E@(b−1)`, the easy
  direction) matches any lower guard, `box_guard_collapse` opens the
  guarded box against the ◯-shaped target, and `laxL` re-imports the
  ambient at every box crossing, so the inner value lands *in
  context* — which is exactly what the pigeonhole/splice shortcut
  consumes (at a repeated jump state, `itp_budget_mono_le` lifts the
  in-context low-budget value into the spliced target slot).  The
  cascade auxiliary still carries a seen-state list; fresh states
  descend (orL/andL one level, matching target component
  introduced), repeats stop by the mono-splice.  Grown-context and
  goal-decomposition obligations discharge by the fuel-level IH.
  A pure upper band (`itp_absorb_of_base` over a pure base) is being
  ground in parallel as insurance, but the ambient-relative form is
  the mainline: it is what the adequacy case-map's jump landings
  actually consume (their context is `interE@B, Δ`).
* **Adequacy then transfers P4a-style**: fuel > height exactly as
  before (fuel-mono re-proved for v3), with absorption as the new
  `E_step`-analogue gluing jump landings, and one application of the
  syntactic fuel-indifference lemma (`μ = (defect + b)·(W₀+1) + goal
  weight` strictly decreases on every call) converting "every fuel
  above the height" into the fixed, Γ-only packaged formula.  Fuel
  disappears; uniformity is definitional.

### Adequacy case-map: the landings that differ from P4a

Dry-run of all fifteen rules against the v3 clauses; only these
deviate from the P4a proof text (everything else is verbatim modulo
the extra guard-splits):

* `impR`, same-set antecedent (`C₁ ∈ Γ`): the unguarded `A13`
  disjunct lands from the premise IH through **set-congruence**
  (`itp_congr`, the v2 lemma re-proved for v3 — new obligation).
* `laxR`: the basic ◯-disjunct is bare (`◯(A(Γ,D))`) — lands by
  `laxR` + IH directly; simpler than v2 (no guard-click).
* `laxL`, Δ-side box (goal `◯D`): land the **truncation disjunct**
  `◯(⋁others)` — `laxL` the Δ-box, **cut in the IH**, orL: an
  `others`-disjunct closes by `laxR`+`orAll_intro`, the truncation
  disjunct itself closes by *identity* (the monad-multiplication
  move).  Verified against the rules 2026-07-11.
* `impLImp` at a present piece (`B⊃D ∈ Γ, D ∉ Γ`) and `impLLax`
  Γ-side (the jump cases): premise-1's IH arrives at the top budget;
  **absorption** lowers it into the `b−1` component slot; the E-side
  jump conjunct then fires by MP to unlock `E(B::Γ)` for premise-2's
  IH — the P4a `hfire` pattern with absorption as new glue.
* `impLLaxLax` with Γ-side principal and Δ-side witness: land the
  bare γ-disjunct `◯(A@b'(Γ,◯A))` by `laxL` on the Δ-box + cut-in
  IH₁ (+ absorption) + `laxR`-identity; its E-side twin fires by
  self-witnessing MP as in v2 (verified: bare form still
  self-witnesses, since `A1` supplies premise-1 directly).

Consolidated new-obligation list for the v3 tower: `itp_congr`,
absorption (+ its easy half budget-mono), fuel-mono, `E1`/`A1`,
p-freeness, fuel-indifference (packaging only), piece-closure
instantiation of the space `S` (packaging only; use the linear
piece-closure finset, not `enum`, so the budget cap and the measure
stay small).

## The guarded/consumed reshaping of the seals (2026-07-12)

The G4iLL post-mortem (task #13, `wip/g4ill_ui.lean`) produced two
structural facts with a plausible transfer to the cascade holdout:
consumed-form glue (`guardMP`: from `Δ ⊢ X` and `Y,Δ ⊢ C` conclude
`X→Y,Δ ⊢ C`) is admissible in cut-free-incomplete G4iLL exactly where
the retained G3 form fails, and Pitts'/UIML's *guarded* `L4→` clause
`(E(S₁)→A(S₁)) → E(D,Γ∖F)` is in-habitat provable where Iemhoff's
unguarded `∃pS₁` needs cut.  The transfer hypothesis — restate the
four seal crossings of `cascade_low_pos_box` in guarded/consumed
style — was adjudicated on a 34-pair exhaustive-nuclei zoo
(`wip/refute4.lean`) and mechanised where it survived (`box_remap` /
`box_reguard`, `wip/absorb_base.lean`).  Verdict: the analogy breaks
for an identifiable structural reason; the holdout stands, but its
obstruction and its residue are now machine-sharp.

**What a seal crossing can carry is machine-delimited.**  `box_remap`
(proved): from `Δ ⊢ ◯(E ⇢ Z)`, `E′,Δ ⊢ E`, and the inner map
`Z, E′, Δ ⊢ Z′`, conclude `Δ ⊢ ◯(E′ ⇢ Z′)`.  The inner obligation
receives the opened source body, the target guard, and the ENTIRE
outer context — `laxL` retains contexts, so every formula-shaped
resource crosses a seal.  What cannot cross is exactly the meta-level
material: the seen-set continuations, which conclude the outer `R`.
Every "(A)-family" guarded-engine candidate is therefore a
repackaging of the same inner sequent.

**The guard family is ambient-dominated at same-context seals.**  All
guards in reach at a seal sit at the same `Γ` as the ambient, and
budget-mono orders them pointwise (`E@(c+1) ⊢ E@c ⊢ E@(c−1)`), so no
guard-strengthened restatement adds leverage there: Z6 (guarded
descent) tracks Z1 (bare descent) on the zoo, failing at the same
unique point with the same witness.  The surviving guarded-crossing
law, Z2b — re-guarding one budget down with the ambient OUTSIDE the
box — is proved (`box_reguard`); it discharges guard plumbing only,
never the value map.

**The budget floor is a ledger artifact on the A-side — with one
structural false point.**  The bare descent
`E@(c+1) ⊓ A@(c+1)(Γ,g) ≤ A@c(Γ,g)` with only `1 ≤ c` is zoo-TRUE at
every probed configuration and budget `c ≥ 1` — defect 1 and 2,
`J ∈ {1,2,4}`, chained (`S={◯p⊃r,r,◯r⊃s,s}`, floor 12) and
shared-consequent (`S={◯p⊃r,◯p₂⊃r,r}`, floor 6) jump structures,
mostly with zero slack — and zoo-FALSE at exactly (◯-shaped goal,
`c = 0`), where the target table is empty (goal clause and truncation
both b-gated; `orAll [] = ⊥`).  The defect-scaled floor
`defect·(J+2)` is invisible to the semantics.  But the E-mate
genuinely fails low: the floorless ascent `E@c ⊢ E@(c+1)` (Z8) is
zoo-REFUTED at (chained-d2, `c = 1`) — chain3, nucleus `[0,2,2]`,
`v(r)=v(s)=1` — so the mutual-pair decomposition, the only known
proof scheme, is closed below `c = 2` by countermodel, independently
of the seal problem.

**Why the Pitts/guardMP analogy breaks.**  Her guards are
ANTECEDENT-side: weakening carries hypotheses across any commit,
which is exactly why the consumed forms close.  The seal deficit is
SUCCEDENT-side-under-◯: continuations are conclusion-anchored — they
conclude the outer disjunction `R`, strictly weaker than the single
◯-disjunct a seal must produce — and formula-shaped stand-ins fail
(in-context oracles `(value ⇢ R)` fire to the wrong conclusion inside
a seal; the budget-family oracles `⋀_{β≤c}(A@(β+1) ⇢ A@β)` are the
stabilization ladder itself).  Ledger-raising cannot compensate:
entry `… + X` funds seals to `defect·(J+2)+X ≤ c−1` while the raised
holdout needs `J+1+defect·(J+2)+X ≤ c−1` — short by `J+1` for every
`X`.  This is the precise sense in which the seal problem is not a
guardMP-shaped problem.

**The fresh-antecedent seal's missing law is semantically free.**
Z5: `E@(c+1)(Γ) ⊓ E@c(C₁::Γ) = E@(c+1)(C₁::Γ)` for `C₁ ∉ S ∪ Γ`,
with EQUALITY on the zoo at every probed instance
(`C₁ ∈ {u, u⊃r, ◯u}`, at and below the floor, and at the moving-E
d2-chain config where the bare ascent Z8 fails).  A proof would kill
the fourth seal — the one
with no decreasing measure — without the whole-head rebuild; its
γ-conjunct conversions recurse into the A-descent one budget down,
i.e. into the holdout itself: same knot, but now with a zoo-true
target on both ends.

**Residue, sharpened.**  The holdout's conclusion from `1 ≤ c` alone
is TRUE on the zoo; no known decomposition reaches it: value-form
chains burn one budget per jump visit, cannot splice at repeats (the
deep obligation needs a LOWER-budget value; the context holds only
higher ones), and are forced into the (◯-goal, 0) false point; the
continuation form splices but loses its `(J∖seen)+1` allotment at
every seal; the mutual pair fails at `(E, c=1)`.  The mechanism the
semantics uses at `c = 1` is SYNTACTIC starvation — b-gated tables at
saturated/grown contexts collapse to literal `⊥`, killing every pair
disjunct whose partner starves (e.g. `A@1(Γ,p) ⊢ ⊥` at the canonical
config).  The identified future route: starvation-collapse lemmas
(which `(Γ, g, b)` starve) plus a `(defect, budget)`-lex landing map
for the `c = 1` base, meeting the pigeonhole band from below —
cascade_main-scale machinery, recorded not attempted.
