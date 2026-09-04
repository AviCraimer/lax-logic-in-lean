import LaxLogic.PLLSearch

/-!
# Pinning a found proof: from *evidence* to *theorem*

The two-sided oracle already returns a **typed** proof term: `Verdict.proved`
carries `t : G4cTm Γ C`, and `G4cTm.toG4c` turns it into `G4c Γ C`.  So when
the searcher says `PROVED`, Lean's typechecker has already checked a
derivation.  What has been missing is a way to get that derivation into a
*source file*, so that the fact survives as a theorem rather than as a line of
probe output.

Running the searcher inside the kernel is not an option — it is deliberately
kernel-opaque, and `decide` on a hundred-thousand-node search is infeasible.
The refutation side has never had this problem: a countermodel is *data*, and
`FinCM.checkB M w Γ C = true` is a cheap kernel computation, which is why every
refutation in this development is pinned as a theorem.  This file gives the
positive side the same standing.

## How

`G4cTm.toLeanSrc` prints a proof term as Lean source.  The trick that makes the
output short is to emit **no formulas at all**.  Every index of every
constructor is recovered by unification:

* the conclusion's `Γ` and `C` come from the expected type;
* each side formula (`A`, `B`, `D`, `X`, `a`) is determined by the *membership
  proof*, which is emitted structurally as a `.tail _ (… (.head _))` chain
  pointing at a position in `Γ`.  Unifying `A.and B` with the formula at that
  position determines `A` and `B`.

The chain is computed from the member's position in `Γ`, not by recursion on
the membership proof — `List.Mem` is `Prop`-valued, so a `String`-valued
function cannot eliminate it.

Because the emitted term mentions no formulas, its size is proportional to the
*derivation*, not to the (very large) tables that occur in the sequents this
development cares about.

## Use

    #pinsrc Γ ⊢ C                    -- default config
    #pinsrc Γ ⊢ C with cfg           -- explicit config

prints either `PROVED — paste this: …` or the reason no certificate was found.
Paste the term into a file as

    theorem my_fact : G4c Γ C := (<pasted term> : G4cTm Γ C).toG4c

and the kernel checks it.  Nothing about the search is trusted: the pasted term
is re-elaborated and re-checked from scratch.
-/

open PLLFormula

namespace PLLND
namespace G4cTm

/-- The position of `φ` in `Γ`, as a `.tail _ (… (.head _))` membership chain in
Lean source.  `k` is the index. -/
def memChain : Nat → String
  | 0 => "(.head _)"
  | n + 1 => s!"(.tail _ {memChain n})"

/-- Index of the first occurrence of `φ` in `Γ`. -/
def posOf (Γ : List PLLFormula) (φ : PLLFormula) : Nat :=
  Γ.findIdx (fun ψ => decide (ψ = φ))

/-- The membership chain for `φ ∈ Γ`, or a marker if `φ` is somehow absent
(which cannot happen when the argument came from a real derivation).

The marker is a deliberately **unknown identifier** rather than `sorry`: emitted
source is meant to be pasted into a file, and a fallback that elaborated to
`sorry` could turn a broken emission into a silently unsound theorem.  An
unknown identifier fails loudly at elaboration. -/
def memSrc (Γ : List PLLFormula) (φ : PLLFormula) : String :=
  let k := posOf Γ φ
  if k < Γ.length then memChain k else "MEMBER_NOT_FOUND_IN_CONTEXT"

/-- **A proof term as Lean source.**  Emits constructor names and membership
chains only; every formula index is recovered by unification against the
expected type. -/
def toLeanSrc : {Γ : List PLLFormula} → {C : PLLFormula} →
    G4cTm Γ C → String
  | Γ, _, .init (a := a) _ => s!"(.init {memSrc Γ (prop a)})"
  | Γ, _, .botL _ => s!"(.botL {memSrc Γ falsePLL})"
  | _, _, .andR a b => s!"(.andR {toLeanSrc a} {toLeanSrc b})"
  | _, _, .orR1 a => s!"(.orR1 {toLeanSrc a})"
  | _, _, .orR2 a => s!"(.orR2 {toLeanSrc a})"
  | _, _, .impR a => s!"(.impR {toLeanSrc a})"
  | _, _, .laxR a => s!"(.laxR {toLeanSrc a})"
  | Γ, _, .laxL (A := A) _ a => s!"(.laxL {memSrc Γ A.somehow} {toLeanSrc a})"
  | Γ, _, .andL (A := A) (B := B) _ a =>
      s!"(.andL {memSrc Γ (A.and B)} {toLeanSrc a})"
  | Γ, _, .orL (A := A) (B := B) _ a b =>
      s!"(.orL {memSrc Γ (A.or B)} {toLeanSrc a} {toLeanSrc b})"
  | Γ, _, .impLProp (a := q) (B := B) _ _ a =>
      s!"(.impLProp {memSrc Γ ((prop q).ifThen B)} {memSrc Γ (prop q)} \
{toLeanSrc a})"
  | Γ, _, .impLAnd (A := A) (B := B) (D := D) _ a =>
      s!"(.impLAnd {memSrc Γ ((A.and B).ifThen D)} {toLeanSrc a})"
  | Γ, _, .impLOr (A := A) (B := B) (D := D) _ a =>
      s!"(.impLOr {memSrc Γ ((A.or B).ifThen D)} {toLeanSrc a})"
  | Γ, _, .impLImp (A := A) (B := B) (D := D) _ a b =>
      s!"(.impLImp {memSrc Γ ((A.ifThen B).ifThen D)} {toLeanSrc a} \
{toLeanSrc b})"
  | Γ, _, .impLLax (A := A) (B := B) _ a b =>
      s!"(.impLLax {memSrc Γ (A.somehow.ifThen B)} {toLeanSrc a} \
{toLeanSrc b})"
  | Γ, _, .impLLaxLax (A := A) (B := B) (X := X) _ _ a b =>
      s!"(.impLLaxLax {memSrc Γ (A.somehow.ifThen B)} {memSrc Γ X.somehow} \
{toLeanSrc a} {toLeanSrc b})"

/-- Node count of a proof term, for reporting. -/
def size : {Γ : List PLLFormula} → {C : PLLFormula} → G4cTm Γ C → Nat
  | _, _, .init _ => 1
  | _, _, .botL _ => 1
  | _, _, .andR a b => 1 + size a + size b
  | _, _, .orR1 a => 1 + size a
  | _, _, .orR2 a => 1 + size a
  | _, _, .impR a => 1 + size a
  | _, _, .laxR a => 1 + size a
  | _, _, .laxL _ a => 1 + size a
  | _, _, .andL _ a => 1 + size a
  | _, _, .orL _ a b => 1 + size a + size b
  | _, _, .impLProp _ _ a => 1 + size a
  | _, _, .impLAnd _ a => 1 + size a
  | _, _, .impLOr _ a => 1 + size a
  | _, _, .impLImp _ a b => 1 + size a + size b
  | _, _, .impLLax _ a b => 1 + size a + size b
  | _, _, .impLLaxLax _ _ a b => 1 + size a + size b

end G4cTm

namespace Search

/-- Run the oracle and report a pasteable proof term, or why there is none. -/
def pinReport (cfg : Config) (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match settleWhy cfg Γ C with
  | .proved t =>
      s!"PROVED  ({t.size} nodes, rule tree {t.pretty})\n\
paste as the proof term:\n{t.toLeanSrc}"
  | .refuted M w _ =>
      s!"REFUTED — underivable, countermodel {repr M} at world {w}.  \
Nothing to pin on the positive side."
  | .unknown (.budgetExhausted k) =>
      s!"no certificate: the positive stage was cut off at {k} nodes, so \
nothing is known.  Raise Config.findBudget or set it to none."
  | .unknown (.closureTooBig sz cap) =>
      s!"no certificate: subformula closure {sz} exceeds emitClosureCap {cap}."
  | .unknown .allStagesMissed =>
      "no certificate: every stage ran to completion and none produced one."

end Search

end PLLND

/-- Report a pasteable proof term for `Γ ⊢ C` (default configuration). -/
macro "#pinsrc " Γ:term " ⊢ " C:term : command =>
  `(command| #eval IO.println (PLLND.Search.pinReport {} $Γ $C))

/-- Report a pasteable proof term for `Γ ⊢ C` at an explicit configuration. -/
macro "#pinsrc " Γ:term " ⊢ " C:term " with " cfg:term : command =>
  `(command| #eval IO.println (PLLND.Search.pinReport $cfg $Γ $C))
