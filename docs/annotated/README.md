# Annotated proof documents: conventions

This directory holds annotated readings of two theorems from the
`lax-logic-in-lean` development, prepared for the appendix of the
companion paper: contraction for the repaired G4 calculus
(`contraction.md`, from `LaxLogic/PLLG4HCtr.lean`) and strong
normalisation of the full proof-term reduction via Lindley–Stark
⊤⊤-lifting (`strong-normalisation.md`, from `LaxLogic/PLLTopTop.lean`).
This page records the extraction method, the abbreviation conventions,
and how to read the infoview snapshots reproduced in both documents.

## The extraction method

Every snapshot in these documents is a literal capture of Lean's
infoview — the hypothesis list and goal Lean displays at a chosen
point in a tactic proof — obtained as follows.

1. The target `.lean` file is **copied**, verbatim, to a scratch
   location outside the repository.  The repository's `.lean` files
   are never edited, not even temporarily; every snapshot in these
   documents comes from a disposable copy.
2. The tactic `trace_state` is inserted into the copy at the chosen
   point (immediately after an `intro`, on entry to an induction case,
   after a load-bearing `have`/`obtain`, or immediately before a
   closing `exact`).  `trace_state` is a no-op tactic that prints the
   current goal — hypotheses and all — to stdout in exactly the format
   the infoview renders, and then leaves the proof state untouched.
3. The copy is compiled with `lake env lean <copy>`, run from the
   package root so imports resolve through the ordinary `lake`
   environment.  Each `trace_state` call prints one block; the blocks
   appear in the compiler's elaboration order, which for a single
   `induction … with` is the order the cases are *declared* in the
   match, not necessarily top-to-bottom source order when nested
   inductions interleave.
4. Each block is transcribed into the document essentially unedited,
   then trimmed and abbreviated per the rules below.  Every
   transcribed snapshot is captioned with its anchor, `file.lean:line`,
   where the line number is the line **in the repository file**, not
   in the disposable copy — the two diverge as soon as a
   `trace_state` line is inserted, so anchors were re-derived against
   the checked-in source after extraction.

Nothing about this method touches the kernel: `trace_state` does not
change what is proved, only what is printed while proving it. The
theorem statements and proof terms in the two documents are exactly
what `lake build` accepts from the actual repository files.

## Reading an infoview snapshot

A snapshot looks like this (from `contraction.md`, the `andL`
principal case of `G4c.contract_bounded`, anchored at
`PLLG4HCtr.lean:241` — already trimmed by the elision and
shared-line-grouping rules below, exactly as it appears in that
document, so the reader sees the actual output form rather than an
idealised one):

```
case succ.andL.inl.intro
w : ℕ
ihw : …
n Γ' E : …
n✝ : ℕ
Γ✝ Θ : List PLLFormula
A₁ B₁ E₀ : PLLFormula
h : Γ✝.Perm (A₁.and B₁ :: Θ)
d₁ : G4h n✝ (A₁ :: B₁ :: Θ) E₀
Γ : List PLLFormula
hA : (A₁.and B₁).weight ≤ w + 1
ih : ∀ {Γ}, (A₁ :: B₁ :: Θ).Perm (A₁.and B₁ :: A₁.and B₁ :: Γ) → G4c (A₁.and B₁ :: Γ) E₀
hp : Γ✝.Perm (A₁.and B₁ :: A₁.and B₁ :: Γ)
hΔ : Θ.Perm (A₁.and B₁ :: Γ)
⊢ G4c (A₁.and B₁ :: Γ) E₀
```

Reading conventions:

* **`case` line.** The dotted case name records the full nesting of
  the tactic block that produced the snapshot: `succ` (outer
  induction on the weight bound), `andL` (inner induction, the case
  for the `andL` constructor of `G4h`), `inl.intro` (the `rcases` that
  split on which branch of `cross_split3` fired, and unpacked its
  existential). It is Lean's bookkeeping name, not part of the
  mathematics, and is kept in the transcription only when it helps
  orient the reader among several snapshots from the same theorem.
* **Inaccessible names (`Γ✝`, `n✝`).** Lean marks a hypothesis
  inaccessible — appends a dagger — when its name has gone out of
  scope for direct reference, typically because a later binder
  (`Γ` here) shadows it or because it was introduced by `induction`'s
  automatic naming rather than a user `intro`. Daggered names are
  kept exactly as Lean prints them: they are real, distinct
  hypotheses, and merging them with same-named accessible hypotheses
  would misrepresent the state. `Γ✝` and `Γ` above are genuinely
  different lists (the pre-split context and the split remainder,
  respectively) and both are still in play.
* **Metavariable-style universe/height holes (`n✝`, the `_` in
  `G4h _ …`).** Where the source has `G4h _ (…) …`, Lean has already
  solved the height index from the constructor's indices and simply
  doesn't print it in goal position; in hypothesis position it prints
  the solved value. No information is lost.
* **The goal line (`⊢ …`).** Always the last line of a block. Read
  literally: this is the statement the enclosing `exact`/tactic block
  must close.

## Abbreviation conventions

Snapshots are reproduced **losslessly** except for the following
mechanical trims, each flagged inline where it is used:

* **Long-context elision.** A context list of more than about four
  entries is elided with `…` after the first few, when the elided
  entries are not the ones under discussion in the surrounding prose.
  The full list is always recoverable by recompiling the snapshot's
  anchor.
* **Repeated type ascriptions.** Where Lean prints a block of
  hypotheses on one shared line (`Γ' E : …`), the transcription keeps
  Lean's own grouping.
* **Named abbreviations for long formulas.** When a formula that
  recurs across several snapshots is long enough to hurt readability
  (for example a specific instance of `(A.ifThen B).ifThen D`), the
  prose introduces a short name for it once — e.g. `K := B₁.ifThen D₁`
  — and uses the short name in subsequent prose *and* is explicit
  every time a snapshot itself has been rewritten to use it. Bare
  transcriptions of `trace_state` output are never silently rewritten
  this way; only prose commentary abbreviates, unless a snapshot block
  explicitly says "abbreviated as `K`" in its caption.
* **Nothing about logical content is ever altered.** No hypothesis is
  dropped because it looks redundant, no `Perm` is simplified, no
  metavariable is resolved by hand. If a snapshot looks noisy, that
  noise (permutation bookkeeping, in particular) is itself the content
  the surrounding prose is explaining.

## Why these two theorems

Both documents read a *design decision*, not just a proof. The
calculus underlying both — `G4h`/`G4c`, defined in
`LaxLogic/PLLG4H.lean` — went through three revisions before
contraction and cut separated cleanly for the lax modality; the design
history and the nucleus countermodel that forced the third revision
are in `docs/g4p-ladder.md`. `contraction.md` reads the payoff of that
revision: every modal principal case in `G4c.contract_bounded` closes
by the *inner* (structural) induction alone, with no appeal to a
self-absorption lemma, because the box-keeping rules `laxL` and
`L◯→″` and the context-keeping `R◯→″` arrange for both copies of a
duplicated hypothesis to reach the same premise. `strong-normalisation.md`
reads the term-calculus analogue: `PLLReducibility.lean` proves strong
normalisation of the β-fragment alone by ordinary Tait reducibility,
then exhibits two machine-checked terms showing that the β-fragment
and the `let`-associativity fragment do not compose by any syntactic
argument (each creates redexes of the other); `PLLTopTop.lean`'s
Lindley–Stark ⊤⊤-lifting is the semantic method that is actually
needed, and its "principal lemma" is where the design pays for itself
in the same way contraction's box-keeping rules do.

## Provenance check

Both headline theorems, and their support, were checked against the
kernel's axiom log immediately before writing these documents:

```
#print axioms PLLND.strong_normalisation
#print axioms PLLND.Tm.normalize
#print axioms PLLND.G4c.contract
#print axioms PLLND.G4c.contract_bounded
#print axioms PLLND.G4h.contract_atom
```

all report only `[propext, Classical.choice, Quot.sound]` — the three
standard axioms of a classical Mathlib-based development, no
`sorryAx`. This is the same discipline the brief's `#guard_msgs`/
`#print axioms` convention recommends: a machine-checked one-line
audit, re-run rather than assumed, and quoted alongside the prose it
supports.
