# A contraction-free sequent calculus for Propositional Lax Logic: what the mechanisation found, and what it proves

*Commentary on the `G4H*` development in `lax-logic-in-lean`. Prepared 2026-07-09, worktree `g4ill`.*

## Abstract

This document is the reader's guide to a completed Lean 4 mechanisation
whose subject is the contraction-free proof theory of Propositional Lax
Logic (PLL). The mechanisation set out to close the proof-theoretic half
of Fairtlough–Mendler's decidability theorem (F&M, *Propositional Lax
Logic*, Information and Computation 137(1), 1997, Theorem 2.8) by way of
a terminating Gentzen calculus, taking as its intended vehicle Iemhoff's
G4iLL (*Proof Theory for Lax Logic*, arXiv:2209.08976; de Jongh
Festschrift, Springer 2024) — Dyckhoff's contraction-free G4ip together
with four lax rules.

Three things came out of it, and only the first was planned.

1. **G4iLL is incomplete for PLL.** The kernel-checked separating
   sequent is
   `◯((◯p → r) → ◯p), ◯p → r ⇒ r`.
   It is derivable in the height-indexed G3 calculus (an explicit
   witness) and underivable in G4iLL (an explicit kernel refutation,
   with the axiom audit pinned to `[propext]` — no compiled evaluation
   in the trusted base). With two copies of `◯p → r` it *is*
   G4iLL-derivable (an axiom-free proof term), so contraction is not an
   admissible rule of G4iLL. The shape is exactly the one Howe
   identified (MSCS 11(4), 2001, §5); his conjecture that lax logic has
   no contraction-free calculus survives the refutation that G4iLL was
   taken to be.

2. **The gap is repairable, and the repair is complete and cut-free.**
   Three *retention* repairs to Iemhoff's lax rules — each keeping in a
   premise material the original rule discards — yield a calculus,
   written **G4iLL″** and mechanised as `G4h`/`G4c`, in which every
   structural rule is admissible: height-preserving exchange and
   weakening, admissible contraction *proved before cut and without cut
   anywhere in its proof*, and admissible cut. Completeness against the
   G3 calculus is then a plain structural induction, and the chain
   `G4iLL″ = SC = LaxND = Tm-inhabitation` closes, unconditionally,
   with `#print axioms` reporting only the three standard axioms.

3. **The repair localizes the contraction PLL needs into the modal
   rules, and no further.** The intuitionistic skeleton of G4iLL″ is
   still fully reductive in Dyckhoff's sense — his four ⊃-left rules
   consume their principal and descend in weight. All of the
   duplication that PLL genuinely requires (item 1 shows it requires
   some) is absorbed into the three ◯-rules by their retention
   discipline. G4iLL″ is thus best read not as a counterexample to
   Howe's conjecture but as a *localization theorem*: contraction-freeness
   in the strong (reductive) sense is impossible for the lax rules, and
   G4iLL″ is precisely the calculus that pays that unavoidable cost in
   the smallest place.

Everything below expands these three points, in conventional
proof-theoretic prose, with pointers into the Lean sources by file and
theorem name. The design log (`docs/g4p-ladder.md`) records the same
history as it happened, with the false starts; the review pack
(`docs/g4ill-gap-review.md`) is the referee-facing dossier for the
incompleteness claim; the two annotated readings under `docs/annotated/`
walk two of the theorems at the level of the Lean proof state. This
document is the synthesis those three support.

---

## 1. The problem

PLL is intuitionistic propositional logic with one unary connective,
here written `◯` and read "it is somehow the case that", whose algebraic
semantics is a Heyting algebra equipped with a **nucleus** `j` — a map
that is inflationary (`x ≤ jx`), idempotent (`jjx = jx`), and
meet-preserving (`j(x ∧ y) = jx ∧ jy`) (F&M §3; Goldblatt 1981). The
propositional laws of `◯` are those of a monad: `◯` is a strong monad on
the intuitionistic-proof category, and the two nontrivial rules are the
unit `A ⊢ ◯A` and a Kleisli-style binding.

F&M Theorem 2.8 asserts that PLL is decidable. The standard modern route
to decidability of an intuitionistic (or intuitionistic-modal) logic is a
**terminating** Gentzen calculus: a sequent system whose backward proof
search is bounded, so that exhaustive search is a decision procedure.
Dyckhoff's G4ip is the paradigm for IPC — it replaces the single
context-sharing left-implication rule of G3ip (whose principal formula is
kept, funding contraction and defeating any naive termination measure) by
four rules split on the shape of the implication's antecedent, each of
which *consumes* its principal and yields premises strictly smaller in a
Dershowitz–Manna multiset order on a bespoke weight. G4ip needs no
contraction rule, and contraction is nonetheless admissible.

Iemhoff's G4iLL adds to G4ip four rules governing `◯`:

- `R◯` (unit) and `L◯` (the box-opening left rule, `Γ, ψ ⇒ ◯φ` over
  `Γ, ◯ψ ⇒ ◯φ`), and
- the two rules for an implication with a boxed antecedent, `◯φ → ψ`:
  a "right-nested" rule `R◯→` and a "box-witnessed" rule `L◯→` that
  fires when the context also contains a box `◯χ`.

The mechanisation's point of departure (`LaxLogic/PLLG4.lean`,
`inductive G4`) is a faithful transcription of these rules; the
faithfulness argument — multisets versus the repo's permutation-indexed
lists, empty succedents, `⊥` not an atom, one deliberately added but
harmless `⊥→` rule — is tabulated rule-by-rule in `docs/g4ill-gap-review.md`
§2, and is what licenses transferring underivability verdicts to
Iemhoff's calculus as written.

The plan was: mechanise G4iLL, prove `G4iLL = SC` (`SC` being the repo's
height-indexed G3 calculus, `PLLSequent.lean`, already equipped with a
mechanised cut), verify the Dershowitz–Manna measure, and read off
decidability. The verified decision procedure for `G4` itself
(`LaxLogic/PLLDecide.lean`) was built and works. What failed was the
equivalence.

---

## 2. The discovery: G4iLL is incomplete

### 2.1 The separating sequent

Write `F′ := ◯p → r` and `G′ := F′ → ◯p`. The separating sequent is

> `◯G′, F′ ⇒ r`.

It is **valid** in every nuclear algebra. With `f = ⟦F′⟧ = jp → r`,
`g = ⟦G′⟧ = f → jp`, a four-line computation (`docs/g4ill-gap-review.md`
§5.1) gives `jg ∧ f ≤ r`: inflation and meet-preservation give
`jg ∧ f ≤ j(g ∧ f)`, modus ponens in the algebra gives `g ∧ f ≤ jp` and
hence `j(g ∧ f) ≤ jp`, and `jp ∧ f = jp ∧ (jp → r) ≤ r`. So a sound
complete calculus must derive it. The G3 calculus does
(`PLLG4Gap.lean`, `theorem sep_SC`, kernel-checked).

It is **not** G4iLL-derivable. The argument the verified decider
mechanises is a two-step exhaustion (`docs/g4ill-gap-review.md` §4).
Backward from `◯G′, F′ ⇒ r`, the only applicable instances are the two
lax-implication rules on `F′`:

- `R◯→`, with premises `◯G′ ⇒ p` and `r, ◯G′ ⇒ r`; the first is invalid;
- `L◯→` with box `◯G′`, with premises `G′ ⇒ ◯p` and `r, ◯G′ ⇒ r`; the
  first is invalid.

Both offered subgoals are refuted by a concrete three-element nucleus
countermodel (the 3-chain `0 < m < 1` with `j0 = jm = m`, `j1 = 1`,
`v(p) = v(r) = 0`), which validates the endsequent while refuting both
`◯G′ ⇒ p` and `G′ ⇒ ◯p` (`docs/g4ill-gap-review.md` §5.2). This
countermodel is explanatory, not load-bearing: the machine-checked
verdict is `PLLG4Gap.sep_not_G4`, an explicit inversion proof whose axiom
audit is pinned to `[propext]` — the search tree is small, and the
kernel closes it without the decision procedure. (The `decide … = false`
guard is retained as an independent second witness.)

### 2.2 Why contraction is the culprit — proof-theoretically

The G3 derivation of `◯G′, F′ ⇒ r` uses **one** context occurrence of
`F′` **twice**: once as the outermost implication broken towards `r`, and
once *inside* the `L◯`-opening of `◯G′`, where — with `G′` present — it
delivers `◯p`. G3's context-keeping left rules fund exactly this: the
principal implication survives into the premises, so a single occurrence
can be broken on two sides of a box-opening.

G4iLL's `L◯→` (constructor `impLLaxLax`) keeps the **box** `◯χ` across
its two premises but *consumes the implication*. So the one occurrence of
`F′` cannot be spent twice, and its two would-be spend sites lie on
opposite sides of a box-opening where no single G4 rule can service both.
This is Howe's duplication phenomenon (MSCS 2001, §5) one connective up:
the formula that needs contracting is not an arbitrary antecedent but the
`◯`-antecedent implication itself, straddling the opening. Howe's own
sequent `B ⊃ ((◦A ⊃ C) ⊃ ◦A), ◦B, ◦A ⊃ C ⇒ C` is the same shape with the
box packaged inside `◯G′`; the mechanisation checks Howe's original
sequent underivable too (`PLLG4Tower.lean`, decider-checked, with the
implication `◦A ⊃ C` needing to be doubled before it derives).

### 2.3 The quantitative witness

That contraction is *not admissible* — not merely absent as a rule — is
the sharp form of the failure, and it is machine-checked as an explicit
pair of proof terms (`PLLG4Gap.lean`, `theorem contraction_not_admissible`):
`◯G′, F′, F′ ⇒ r` is derivable (`two_copies_G4`, an axiom-free term, one
copy consumed outside the opening and one inside), while `◯G′, F′ ⇒ r`
is not (`sep_not_G4`). Cut fails likewise (`cut_not_admissible`): `◯p`
interpolates between `◯G′, F′` and `r`, both halves are G4iLL-derivable,
yet the cut cannot be eliminated.

A companion multiplicity experiment (`PLLG4Tower.lean`) records that the
*naive* way to force more contraction does not work: stacking another
boxed antecedent (`◯(F′ → (F′ → ◯p))`) still needs only two copies of
`F′`, because G4's additive branching hands each premise its own copy of
the context — only `F′`-firings nested along a single branch compound,
and antecedent-stacking spreads the uses across sibling branches. Whether
*some* PLL sequent needs multiplicity three is left open and flagged as
mechanically searchable; §7 returns to why the answer matters.

### 2.4 Consequence for the interpolation programme

Iemhoff's PLL uniform-interpolation theorem (her Thm 8.4, obtained via
Cor 8.1) is proved *through* the claimed G4iLL = G3iLL equivalence. With
that equivalence false, the theorem loses its proof. This does not refute
PLL-UI — it reopens it. The Pitts-style route (Pitts, JSL 57(1), 1992)
runs the interpolant construction over a *terminating* calculus with the
right (focused/reductive) rule shapes; G4iLL had them but is incomplete,
and G4iLL″ (below) is complete but, by design, not reductive in the modal
rules. §7 discusses what this leaves open.

---

## 3. Literature forensics

The incompleteness bears on a chain of published results, and the chain
has a referee-patch history worth setting down precisely, because it
determines *which* statement is refuted and how.

The general enabling theorem is "the G4i analogue of a G3i calculus":
for a suitable class of G3-style calculi, the Dyckhoff-style G4 variant
derives the same sequents.

- **arXiv:2011.11847 v1** (Nov 2020), Theorem 1, states the hypothesis as
  closure under **weakening** only. Its modal case exhibits an
  `R→`-instance that silently drops the second copy of `◯φ → ψ`. G4iLL
  satisfies every stated hypothesis of this version (nonflat; G3iLL
  closed under the structural rules; terminating in the weight order),
  yet, as §2 shows, derives strictly less than G3iLL. So the *unpatched*
  theorem is refuted outright.
- **Studia Logica 110:1493–1506 (2022)**, the published version
  (accepted May 2022; the arXiv was never updated), strengthens the
  hypothesis of Theorem 3.4 to closure under weakening **and
  contraction**. G4iLL does *not* satisfy the added hypothesis (§2.3),
  so the published theorem simply does not apply to lax logic. (There is
  a residual concern even in the patched proof — it asserts `Sᵢ ≪ S`
  where the instance's conclusion is the doubled sequent `S⁺` and only
  `S ≪ S⁺` is evident — but that is not needed for the present point.)
- ***Proof Theory for Lax Logic*** — both arXiv:2209.08976 v1 (Sept 2022)
  and the published de Jongh chapter (2024) — cites the theorem in its
  **unpatched** (weakening-only) form, "accepted for publication", and
  proves no contraction admissibility for G4iLL before invoking it as
  Corollary 8.1. So the lax paper inherits the gap: it relies on a
  hypothesis (contraction admissibility) that is false for its calculus,
  under a citation to a version of the general theorem that omits that
  hypothesis.

Two structural remarks explain why the sibling calculi of the same school
are immune. First, van der Giessen–Iemhoff already flagged an analogous
soft spot: arXiv:2011.10383 v2 ("Corrected version at July 14, 2022"),
Remark 1, notes that the direct contraction claim for G4iGL□ "might be
wrong". Second — and this is the load-bearing observation — the
iSL/iGL equivalence proofs are *direct* inductions (a Bílková-style
order), not applications of the general theorem, and their `→SL`/`→GL`
rules **retain** what G4iLL's `L◯→` discards: `→SL` keeps the implication
itself, `→GL` keeps the unboxed context. The counterexample shape needs a
rule that *drops* the principal across a modal step; the strong-Löb rules
do not have one, so they are structurally out of range. This is the same
retention that §4 introduces deliberately for lax.

---

## 4. The repair: three retention revisions

The repair is a sequence of three changes, each *forced* by a specific
case that would not close, and each of the same character: a lax rule is
made to **keep** in a premise something it originally consumed. The
design log `docs/g4p-ladder.md` records them in order, including the
countermodel that forced the third; here is the settled account.

Throughout, weight is Dyckhoff's, extended by `w(◯A) = w(A) + 1`
(`PLLFormula.weight`); `∧` weighs `2` more than its parts, the rest `1`.

### Revision 1 — `L◯→″` keeps its box (= G3's `L◯`)

The box-opening left rule and the box-witnessed implication rule are made
to keep their box in every premise. `laxL` becomes exactly G3iLL's `L◯`
(needs only a membership hypothesis, the box staying put), and `L◯→″`'s
first premise carries the **whole** conclusion context — box *and*
implication — plus the opened witness:

```
Γ, ◯χ, χ ⇒ ◯B                     Γ, ◯χ, ◯φ→ψ, χ ⇒ ◯φ    Γ, ◯χ, ψ ⇒ Δ
-------------- laxL (= G3 L◯)      ------------------------------------- L◯→″
Γ, ◯χ ⇒ ◯B                                   Γ, ◯χ, ◯φ→ψ ⇒ Δ
```

The consequence, checked case by case in the design log, is that the
"boxed hypothesis versus unboxed premise" mismatch that had forced an
auxiliary box-strengthening lemma into every cut case never arises: the
two copies of a duplicated box always travel together into the same
premise. This is the minimal form of the "⊗-insight" that makes the iSL
cut go through, adapted to lax.

### Revision 2 — `R◯→″` keeps its context (= G3's `L⊃` discipline)

Writing the general-contraction case table *in Lean* exposed a case the
paper analysis had missed. A doubled `◯φ → ψ` whose visible copy is fired
by the right-nested rule `R◯→` (whose first premise, in the consuming
form, is `Δ ⇒ φ` — the implication gone) cannot be rebuilt from the
inverted premises `ψ, Γ ⇒ φ` and `ψ, Γ ⇒ E`. This was not an oversight in
the proof search: with `j = id`, `φ := p`, `ψ := p ∧ q`, `E := q`, the
required inference **fails in a Heyting algebra with nucleus** — the rule
shape itself is the obstacle. The fix is the same medicine: give the
first premise the full conclusion context, exactly G3's `L⊃`
premise-1 discipline.

```
Γ, ◯φ→ψ ⇒ φ    Γ, ψ ⇒ Δ
------------------------ R◯→″
Γ, ◯φ→ψ ⇒ Δ
```

The implication is still consumed in every *second* premise — that is the
Dyckhoff residue that keeps the calculus G4-shaped and keeps the
intuitionistic skeleton reductive. Soundness is a weakening of the old
premise, and the soundness translation into `SC` actually *simplifies*
(premise 1 is now G3-shaped on the nose).

### Height-indexing

One cost is structural rather than logical: the principal-left
recursions in cut transport the *other* derivation by weakening, and a
`Prop`-valued structural induction cannot absorb a weakening. So the
judgment carries an explicit **height index** — `G4h n Γ C` with premises
at `n` and conclusion at `n + 1` (the repo's own `SCh`/`SC` pattern) —
and the plumbing lemmas (exchange, weakening, all the inversions) are
proved *height-preserving*, after which contraction and cut run on the
classical lexicographic measures (formula weight, then height sum). The
working judgment is `G4c Γ C := ∃ n, G4h n Γ C`.

The whole package has a one-line description:

> **G4iLL″ = G3iLL + Dyckhoff's implication splitting, with maximal
> retention in the three lax-implication/box rules.**

Termination is unaffected as a deferral: the retained material makes
naive backward search loop even more freely, but decidability was always
a separate discipline (§7).

---

## 5. The admissibility development, lemma by lemma

The files below build the structural metatheory of G4iLL″. Each is a
self-contained port or new result; the module docstrings carry the local
detail, so this section gives the mathematical statement, the proof idea,
and the location.

### 5.1 The calculus and its plumbing — `PLLG4H.lean`

Defines `G4h`/`G4c`; height monotonicity (`succ_mono`, `mono`);
**height-preserving exchange** (`G4h.perm`) and **weakening**
(`G4h.weaken`); the embedding `G4p ⊆ G4c` (`G4c.ofG4p`), which routes the
consuming predecessor calculus — and hence Iemhoff's `G4` and the gap
sequent — into the retaining one by simulating each consuming box rule
with the keeping one plus weakening; and **soundness** `G4c → SC`
(`G4c.toSC`). The soundness proof is where the retention first pays
visibly: because `laxL` and `L◯→″` now match `SC.laxL` verbatim, the
modal cases are *simpler* than for the consuming calculus.

### 5.2 Height-preserving inversions — `PLLG4HInv.lean`

The master inversion `G4h.inv`: if `G4h n Γ C` and `Γ` exposes a
principal `P` invertible to a list `L` (the relation `G4.Inv P L`
enumerates the invertible connectives), then `G4h n (L ++ Δ) C` at the
*same* height. Height preservation is exactly what the cut and
contraction measures will consume — inverting a side premise must cost
nothing. In the principal cases the answering premise sits one height
below and is returned through `succ_mono`; the box-keeping rules make
their traversal cases *shorter* (a membership transport for `laxL`, a
single `cons` for `L◯→″`'s full-context premise). Named corollaries
(`andL_inv`, `orL_inv₁`/`₂`, `impLProp_inv`, `impLBot_inv`,
`impLImp_inv₂`, `impLLax_inv₂`) and, crucially, the two **right**
inversions `impR_inv` and (later, in the cut file) `andR_inv`, which are
what let the cut proof avoid a left-analysis in the implication-shaped
principal cases.

### 5.3 Generalised identity and telescoped modus ponens — `PLLG4HAdm.lean`

Restates each `G4h` constructor at the existential wrapper `G4c` (the
"rule lifters", aligning binary premises' heights with `mono`), then
ports the joint induction of the predecessor's `identity_mpt`:
simultaneously the **generalised identity** `A, Γ ⊢ A` for every formula
`A` (`G4c.identity`) and the **telescoped modus ponens**
`As, curryImp As B, Γ ⊢ B` — the identity by structural recursion on `A`
against a weight bound, the telescope by the shared `curryImp`/`telWeight`
machinery. `identity_mem` and the two-hypothesis `mp` are the corollaries
the cut and completeness proofs actually call. Here too the modal cases
*shrink*: the box-keeping `laxL` needs no permutation surgery, and in the
`◯`-antecedent telescope case the identity premise heads the full context
unswapped.

### 5.4 Spines, weak implication, `L→→`-duplication — `PLLG4HStr.lean`

Three ingredients Dyckhoff–Negri isolate for the intuitionistic
contraction/cut proofs, ported to the lax setting.

- `Spine φ σ` (`φ = ◯ᵏσ`) with `laxR`-lifts: bookkeeping for a goal
  descending a box-tower.
- **`weak_Imp`** (Dyckhoff–Negri, *Structural cut elimination*, Lemma 4.1;
  here for *all* antecedent shapes including `◯`): from `Γ ⇒ D` and
  `Γ, B ⇒ E` conclude `Γ, D → B ⇒ E`. Induction on the first derivation,
  each rule-ending feeding one left rule; the two box endings give
  *shorter* cases than the intuitionistic ones because their premises
  already carry the full context. `weak_Imp` is stated at `G4h` (an
  existential judgment cannot be inducted on) and re-exported at `G4c`.
- **`impLImp_dup`** (Dyckhoff–Negri Lemma 4.2, folded form): a context
  occurrence of `(A → B) → D` may be replaced by `A, B → D, B → D`. Plain
  structural induction; the principal case closes by `impR_inv` and
  `weak_Imp`. This is the engine of the `⊃⊃` case of contraction.

### 5.5 Contraction, cut-free — `PLLG4HCtr.lean`

Two results, and this file is the payoff of the design.

- **`G4h.contract_atom`**: contraction of an *atom*, height-preservingly.
  Atoms are never a left rule's principal (they occur only in `init`'s
  conclusion and `Lp→`'s side condition), so both copies travel into
  every premise and the content is pure permutation bookkeeping. Consumed
  by the cut theorem's `init` case.
- **`G4c.contract`**: full contraction, via `contract_bounded`, with **no
  cut anywhere in the proof**. Outer induction on the *weight* of the
  contracted formula, inner structural induction on the derivation. This
  is the classical Dyckhoff–Negri order — contraction *before* cut —
  restored for a lax calculus, which the incompleteness had appeared to
  put out of reach.

  The case structure: for a principal non-modal formula, invert the
  surviving copy and contract the strictly lighter pieces (`∧`, `∨`, and
  the `p⊃`, `⊥⊃`, `∧⊃`, `∨⊃` implication forms); the `⊃⊃` case runs the
  Dyckhoff–Negri recipe — duplicate the spectator copy into premise 1 via
  `impLImp_dup`, contract the three strictly lighter residues, re-abstract
  with `impR`. **All three modal principal cases close by the inner
  (structural) induction alone**, with no self-absorption lemma, because
  the retention repairs arrange for both copies of a duplicated
  hypothesis to reach the *same* premise: `laxL` and `L◯→″` keep the box,
  so both copies persist unopened into the premise; `R◯→″`'s revision-2
  first premise keeps the implication, so the inner induction contracts it
  directly. The annotated reading `docs/annotated/contraction.md` walks
  this file at the level of the Lean proof state, case by case.

### 5.6 Ex falso and atomic cut — `PLLG4HCut.lean` (first half)

- `exfalso_adm`: from `Γ ⇒ ⊥` conclude `Γ ⇒ E`. No right rule concludes
  `⊥`, so a `⊥`-derivation is a tree of left rules over `botL` leaves;
  rebuild each rule at goal `E`, reusing the goal-independent auxiliary
  premises verbatim. Purely structural.
- **`cut_atom`**: from `Γ ⇒ p` and `p, Γ ⇒ E` conclude `Γ ⇒ E`, by strong
  induction on the height sum. The right derivation is processed rule by
  rule, the cut copy parametric everywhere (atoms are never left-rule
  principals), the left derivation transported into each premise by
  height-preserving inversion. Two places need more: `L→→`'s first
  premise, whose residue `B → D` is not an inversion piece, runs the cut
  at the *enlarged* context and repairs afterwards with `impR_inv`,
  `impLImp_dup`, and the now-closed cut-free contraction (no measure cost:
  the repair makes no recursive calls); and `Lp→` whose side atom *is* the
  cut copy, where the induction **switches sides** and analyses the left
  derivation.

### 5.7 The main cut — `PLLG4HCut.lean` (second half)

**`cut_of_selfAbsorb`**: cut by lexicographic induction on (cut-formula
weight, height sum). The architecture is a right-primary case analysis
on the second derivation, as in `cut_atom`. The height-preserving right
inversions `impR_inv` and `andR_inv` do the essential work: they let the
implication-shaped principal cases (`∧`, `p⊃`, `∧⊃`, `∨⊃`, `⊃⊃`) reduce
to strictly lighter cuts *without* a secondary analysis of the left
derivation. A left-analysis is then needed in only three places:

- `∨`-principal, where there is no right inversion for `∨R`;
- the box cut formula used as a box in a `laxL` of the right derivation,
  where the goal is `◯`-shaped and the `laxL`-rebuild after a left-push is
  therefore legitimate;
- the box cut formula used as the *witness* `hX` of an `L◯→″` of the right
  derivation — the case that had been open the longest. Two keys close it:
  the second premise transports by plain inversion at the *implication*
  (no box crossing), and the missing `Γ ⇒ ◯A₁` is obtained as a
  **boxed-goal** cut of the left derivation against the *synthetic* `laxL`
  packaging of the first premise, run by left-analysis directly against
  that synthetic derivation. What remains after these is one clean
  obligation, isolated as a named proposition:

  ```
  SelfAbsorb : ∀ {Γ l₀ A B E},
    Γ.Perm (◯A → B :: l₀) → G4c Γ ◯A → G4c (B :: l₀) E → G4c Γ E
  ```

  ("an implication whose antecedent-box is derivable *in its own presence*
  may fire") — semantically valid in every nuclear algebra: from
  `f ∧ γ ≤ jA` and `f ∧ jA ≤ B` get `f ∧ γ ≤ B ∧ ⋀l₀ ≤ E`. `SelfAbsorb`
  is the old self-absorption lemma, now isolated to a single spot: this is
  the genuine mutual knot, and the conditional cut theorem pins every
  other obligation as discharged around it.

### 5.8 The summit: `SelfAbsorb` proved outright

`selfAbsorb_aux` proves `SelfAbsorb` by **plain structural induction on
the `◯A`-derivation** — no cut, no measure. The resolution is the exact
mechanism of the repair, read backwards. The two ways a `◯A`-derivation
can end are the two firing shapes of the retained lax rules:

- a `laxR` ending (the box goal was *produced*) feeds `R◯→″`, whose
  revision-2 first premise is the full context, so the subderivation is a
  verbatim firing input;
- a `laxL` ending (a box was *opened*) feeds `L◯→″` with that very box as
  witness — and `L◯→″` is precisely the box-witness rule Iemhoff
  introduced *because of* Howe's duplication, which (revision 1 having
  kept the implication in it) absorbs the opened premise verbatim.

If the implication is itself fired inside the derivation, its own first
premise is again a verbatim firing input. Everything else is a parametric
rebuild with the side derivation transported by height-preserving
inversion at the principal. The lemma that had walled every earlier
attempt turns out to be *exactly* what the two retained rules were shaped
to accept.

Hence, unconditional and each with a pinned axiom audit, no `sorryAx`
(choice-free since the 2026-07-17 axiom-hygiene pass):

- `G4c.selfAbsorb : SelfAbsorb` — audit `[propext]`;
- `G4c.cut : G4c Γ A → G4c (A :: Γ) E → G4c Γ E` — audit
  `[propext, Quot.sound]`.

### 5.9 Completeness and the equivalences — `PLLG4HComp.lean`

**`completeness`** (`SC Γ C → G4c Γ C`) is a plain structural induction on
the height-indexed G3 derivation `SCh`: the right rules and the two
membership-keeping lax rules transfer verbatim; `andL`/`orL` invert the
surviving copy and contract the strictly lighter pieces; `impL` is two
cuts through the in-context modus ponens `mp`. With `toSC` (§5.1) this
gives `G4c = SC`, and the banked equivalences `SC ↔ LaxND ↔ Tm` chain it
to

- `G4c.equiv_sc : G4c = SC`,
- `G4c.equiv_nd : G4c = LaxND` (natural deduction),
- `G4c.equiv_tm : G4c = Tm`-inhabitation (the term calculus),

so G4iLL″ proves **exactly** the PLL sequents. The proof-theoretic half
of F&M Theorem 2.8 is mechanised end to end. The file carries the
`#guard_msgs`-pinned `#print axioms` audits for `selfAbsorb`, `cut`,
`completeness`, and `equiv_tm`, each `[propext, Classical.choice,
Quot.sound]`.

---

## 6. The correct framing — do not overclaim

The temptation is to announce "a contraction-free sequent calculus for
lax logic, refuting Howe". The mechanisation earns a more precise, and
more interesting, statement. The distinction that matters is between two
senses of "contraction-free".

**Weak sense** — the calculus has no contraction *rule*, and contraction
is admissible. Every G3-style system has this once cut is available;
it is not the prize, and it was never in doubt for lax logic.

**Strong sense** — Dyckhoff reductivity: every premise is strictly
smaller than the conclusion in a well-founded order, and *no formula is
used twice* (no principal is retained). This is what makes G4ip a
*terminating* search calculus and what Pitts/Iemhoff-style uniform
interpolation consumes. Iemhoff's G4iLL had the strong property and is
**incomplete** (§2). G4iLL″ is **complete** but does **not** have the
strong property in its lax rules — the three retention repairs each keep a
principal, which is precisely contraction *absorbed into the rules* rather
than eliminated.

So the honest headline is a **localization theorem**:

> The intuitionistic skeleton of a complete contraction-free calculus for
> PLL can be fully reductive — Dyckhoff's four ⊃-left rules consume their
> principal and descend — and **all** the contraction that PLL genuinely
> needs can be confined to the three ◯-rules, where the gap theorem shows
> some of it is unavoidable.

Two corollaries sharpen this and connect it to what is still open.

- **Strong Howe stands, and is supported.** Howe conjectured that no
  contraction-free calculus for lax logic exists. In the weak sense this
  is false (G4iLL″, and indeed G3iLL, refute it). In the strong sense —
  no *reductive* calculus — the gap theorem is direct evidence *for* it:
  the sequent `◯G′, F′ ⇒ r` is derived by a genuine double use of one
  occurrence, and G4iLL″ funds that double use only by a rule that keeps
  the occurrence. Strong Howe remains open, and the mechanisation is
  evidence in its favour.

- **A bounded-duplication dichotomy, decider-searchable.** The
  quantitative edge (§2.3) makes strong Howe *decidable in a bounded
  sense*. If two copies of the offending implication always suffice, then
  "G4iLL + one built-in duplication of the `◯→`-principal" would be both
  complete and fully reductive — refuting strong Howe. If some PLL sequent
  needs three, the bounded-duplication hierarchy is strict and strong Howe
  holds at every level. The naive tower (§2.3) does not decide this — it
  stays at two — but the question is exactly of the form the verified
  decider of `PLLDecide.lean` can attack, one candidate sequent at a time.

---

## 7. What remains

The mechanisation closes the proof-theoretic half of F&M Theorem 2.8 over
a calculus now *known* complete. Four things remain, in rough dependency
order.

1. **Termination / decidability discipline for G4iLL″.** The retained
   material means naive backward search does not terminate; the calculus
   is not Dershowitz–Manna decreasing at `L◯→″`'s and `R◯→″`'s first
   premises. The planned route is orthogonal to the search order: with
   *set* contexts (justified by the now-admissible contraction) and
   subformula closure, the search space is finite, so a history/loop-check
   terminates. Weak termination plus a complete strategy suffices for
   decidability; a Bílková-style order on the cut-free system is the
   fallback. This is a genuinely separate piece of work — the completeness
   result does not deliver it — but it now sits over solid ground.

2. **Uniform interpolation for PLL.** With PLL-UI reopened (§2.4), the
   natural attack is Pitts's method (JSL 57(1), 1992) over the terminating
   *complete* calculus of item 1. The obstruction to a naive transcription
   is precisely §6: the modal rules are not reductive, so the interpolant
   recursion needs care exactly where the duplication lives. Fallbacks:
   bisimulation quantifiers, and the algebraic model-completion route of
   van Gool–Metcalfe–Tsinakis (APAL 168(10), 2017) building on
   Ghilardi–Zawadowski — noting that the model-completion status of the
   variety of *nuclear* Heyting algebras appears genuinely unstudied
   (`docs/surveys/nuclei-model-completions-monads.md`). The iSL precedent
   (Férée–van der Giessen–van Gool–Shillito, IJCAR 2024, mechanised in
   Coq) is the closest worked analogue, and its `→SL` retention is the
   same phenomenon G4iLL″ exhibits.

3. **The note to Iemhoff.** The finding is now a *repair-gift*, not merely
   a refutation: incompleteness of G4iLL, the retention fix, and a
   complete cut-free G4iLL″ with all structural rules admissible. The
   review pack (`docs/g4ill-gap-review.md`) is the dossier; the framing of
   §6 is what keeps the claim exactly as strong as the mechanisation
   supports and no stronger.

4. **Portability.** The retention mechanism is not special to `◯`. A
   Pfenning–Davies judgmental presentation, and constructive `□`/`◇`
   variants, are the natural next targets (the strong-monad observation of
   §1, and the audit of the sibling G4iK□ calculi, are recorded in the
   project memory and `docs/surveys/`).

---

## Appendix: reusable techniques

The mechanisation reuses a small kit of techniques that transfer to any
list-context sequent development in Lean. They are collected here because
they are the parts most likely to be lifted into other files.

**The permutation-hypothesis presentation.** Left rules locate their
principal through a hypothesis `h : Γ.Perm (P :: Δ)` rather than by a
pattern in the conclusion index. Conclusion contexts stay plain
variables — no `++`, no `List.erase`, no multiset quotient near an index —
so `cases`/`induction` never fight the unifier, and exchange is one line
per case (compose the rule's `Perm` with the ambient permutation, premises
untouched). `List.erase` appears in *proof terms* only (via
`List.perm_cons_erase`), never in a type being matched. `PLLG4.lean`'s
header calls this the "slime discipline"; it is what makes the whole ladder
tractable.

**Height-preserving vs height-bumping, and the `Exists.imp` typography.**
An existential judgment `G4c := ∃ n, G4h n` cannot be inducted on, so
every lemma proved *by induction* is stated at `G4h` and re-exported at
`G4c`. Lemmas that must not cost anything in a later measure (exchange,
weakening, every inversion) are proved height-*preserving* on `G4h`;
lemmas that legitimately build a taller derivation bump the index. The
re-export at `G4c` is uniformly `d.imp fun _ h => …` (`Exists.imp`),
which threads the height through without naming it — the recurring
one-liner at the bottom of each `G4h` lemma.

**Weight induction with `≤`-slack.** Contraction and cut are outer
inductions on a formula weight, but the recursive calls land on formulas
whose weight is only known to be `≤` the bound, not `=`. Stating the outer
induction as `∀ w, A.weight ≤ w → …` (rather than `= w`) gives the slack:
the inner call supplies its own `≤ w` from an `omega` on the `simp`-ed
`weight` equation, and the induction is on `w`, not on `A`. This is the
shape of both `contract_bounded` and `cut_of_selfAbsorb`.

**The index-generalisation `E₀` gotcha.** When an inner structural
induction runs *inside* an outer weight induction, the succedent of the
derivation being inducted on must be generalised (it appears in the case
as `E₀`, distinct from the outer `E`), or the induction hypothesis is too
weak to apply after an inversion has changed the goal. Overlooking this
produces an induction hypothesis specialised to the wrong succedent; the
symptom is a case that looks structurally identical to a solved one but
whose `ih` will not unify.

**`#guard_msgs` axiom audits as machine-checked documentation.** Every
headline theorem is followed by

```lean
/-- info: '…' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms …
```

so the axiom base is *re-checked on every build*, not asserted in prose.
A `sorryAx` or an `ofReduceBool` (compiled-evaluation) creeping in would
break the build. The gap file's audits are pinned tighter — `[propext]`
only for the underivability results — which is what certifies that the
incompleteness verdict uses no trusted compiled evaluation. This is the
same discipline the annotated documents quote (`docs/annotated/README.md`).

**The `trace_state` annotation method.** The two annotated readings under
`docs/annotated/` reproduce literal Lean infoview snapshots at chosen
points in the proofs. The method (documented in
`docs/annotated/README.md`): copy the source file verbatim to a scratch
location *outside the repository*, insert `trace_state` (a no-op that
prints the goal), compile the copy with `lake env lean`, and transcribe
the printed blocks — re-anchoring line numbers against the checked-in
source afterwards, since the inserted lines shift them. Nothing about the
method touches the kernel: `trace_state` changes only what is printed,
not what is proved.

---

*Cross-references.* Design log with the false starts and the forcing
countermodels: `docs/g4p-ladder.md`. Referee dossier for the
incompleteness claim: `docs/g4ill-gap-review.md`. Proof-state-level
readings: `docs/annotated/contraction.md`,
`docs/annotated/strong-normalisation.md`, `docs/annotated/README.md`.
Literature surveys underpinning §3 and §7:
`docs/surveys/categorical-modal-proof-theory.md`,
`docs/surveys/nuclei-model-completions-monads.md`,
`docs/surveys/lean-infosphere-2026-07.md`. The predecessor calculi
(historical, still in the build): `PLLG4.lean` (Iemhoff's G4iLL, verbatim),
`PLLG4P.lean` (the single-repair G4iLL′, superseded by G4iLL″).
