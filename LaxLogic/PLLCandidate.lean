import LaxLogic.PLLFocused

/-!
# Interpolation candidates, read off the focused rules

`docs/lax-interpolation-candidates-strategy.md`: stop constructing *the* uniform
interpolant; generalise to an **interpolation candidate** in Girard's sense, and
let the closure clauses be **discovered from the rules** — one clause per way of
consuming a formula, sorted by polarity into *unconditional* (asynchronous) and
*guarded* (synchronous).

The document notes the method "cannot be fully stated until the focused calculus
is pinned down, because the closure clauses *literally are* the rules".  It is
now pinned (`LaxLogic/PLLFocused.lean`), so this file states them.

## Over what? — the calculus forces the answer, and it is not the obvious one

Matthew's question. The first attempt indexed candidates over **stable
sequents**, `List Neg → JD → Pos → Prop`, on the grounds that stability is where
choices are made. **That does not work, and the reason is instructive.**

`∨` is positive, so a disjunction lives in the **inversion context** `Ω`, and
`Inv.orL` splits it *before* stability is reached. A stable sequent does not
record `Ω`. So over stable sequents the join clause would have to read

    C Γ₁ j P → C Γ₂ j P → C (Γ₁ ⊔ Γ₂) j P

and there is no `⊔` on `List Neg` — the clause **cannot be stated**. The
indexing is therefore forced to the **inversion sequent**:

    C : List Neg → List Pos → JD → Neg → Prop

which is the only shape in which every clause, the join included, is
expressible. Stable sequents appear as the `Ω = []` case. Not formulae (too
coarse — the flag is invisible), not strategies (too fine — no rule needs a
strategy's internals), and not stable sequents (too narrow — `∨` escapes them).

## The clauses, tagged by the rule that forced them and by polarity

Read off `PLLFocused`. Asynchronous rules (`Inv`) give unconditional clauses;
synchronous rules (`Stab`, `RFocus`, `LFoc`) give guarded ones. The prediction
of the strategy document — that the clauses fall into exactly these two families
along the polarity boundary — is borne out, with two clauses carrying all the
difficulty. They are flagged below.
-/

namespace PLLND
namespace Candidate

open Polar Focused

mutual
/-- `p` does not occur in a positive proposition. -/
def PFreePos (p : String) : Pos → Prop
  | .atom a => a ≠ p
  | .fls    => True
  | .or q r => PFreePos p q ∧ PFreePos p r
  | .down n => PFreeNeg p n
/-- `p` does not occur in a negative proposition. -/
def PFreeNeg (p : String) : Neg → Prop
  | .up q    => PFreePos p q
  | .imp q n => PFreePos p q ∧ PFreeNeg p n
  | .and m n => PFreeNeg p m ∧ PFreeNeg p n
  | .circ q  => PFreePos p q
end

/-- An **interpolation candidate** for the variable `p`: a predicate on
**inversion sequents** closed under the clauses forced by the rules of
`PLLFocused`.

Every field is named for the rule that forced it. The two marked `★` carry the
difficulty; see the discussion after the structure. -/
structure Cand (p : String) where
  /-- The predicate, on inversion sequents. -/
  C : List Neg → List Pos → JD → Neg → Prop

  -- Unconditional clauses — from the asynchronous rules (`Inv`).

  /-- `impR`. Right-inverting `⊃` moves the antecedent into `Ω`. -/
  cl_impR : ∀ {Γ Ω Q N}, C Γ (Q :: Ω) .tru N → C Γ Ω .tru (.imp Q N)
  /-- `andR`. Two premises over the same sequent: closure under **meet**. -/
  cl_andR : ∀ {Γ Ω M N}, C Γ Ω .tru M → C Γ Ω .tru N → C Γ Ω .tru (.and M N)
  /-- `circR`. **The flag-shifting clause.** `◯P` at either flag reduces to `P`
  at `.lax`, so the candidate must transport across the flag change. -/
  cl_circR : ∀ {Γ Ω j P}, C Γ Ω .lax (.up P) → C Γ Ω j (.circ P)
  /-- `orL` ★. Two branches, one conclusion: closure under **join**, and now
  statable because `Ω` is in the index. This is the clause `∨` contributes and
  where the difficulty of the whole problem sits — see below. -/
  cl_orL : ∀ {Γ Ω P Q j N},
      C Γ (P :: Ω) j N → C Γ (Q :: Ω) j N → C Γ (.or P Q :: Ω) j N
  /-- `flsL`. The absurd branch is always in. -/
  cl_fls : ∀ {Γ Ω j N}, C Γ (.fls :: Ω) j N
  /-- `downL`. A shifted negative becomes a stable hypothesis. -/
  cl_downL : ∀ {Γ Ω M j N}, C (M :: Γ) Ω j N → C Γ (.down M :: Ω) j N
  /-- `atomL`. An atom becomes a stable hypothesis. For the **eliminated** atom
  `p` this is the clause that does the work of elimination. -/
  cl_atomL : ∀ {Γ Ω a j N},
      C (.up (.atom a) :: Γ) Ω j N → C Γ (.atom a :: Ω) j N

  -- Guarded clauses — from the synchronous rules, at `Ω = []`.

  /-- `RFocus.init`, guarded: an atom in focus, and `p`-free. -/
  cl_init : ∀ {Γ j a}, Neg.up (Pos.atom a) ∈ Γ → a ≠ p → C Γ [] j (.up (.atom a))
  /-- `RFocus.or1`/`or2`, guarded: each disjunct choice. -/
  cl_orR : ∀ {Γ j P Q}, C Γ [] j (.up P) → C Γ [] j (.up (.or P Q))
  /-- `RFocus.rel`, guarded: release. -/
  cl_rel : ∀ {Γ j N}, C Γ [] j N → C Γ [] j (.up (.down N))
  /-- `LFoc.impL`, guarded and **cross-flag**: the argument premise sits at
  `.tru` while the conclusion sits at `j`; the continuation gains `N` as a
  stable hypothesis. The only place `⊃` meets the flag. (An earlier statement
  of this clause omitted the `N :: Γ` and was trivially satisfiable — caught
  when the discharge attempt made it vacuous.) -/
  cl_impL : ∀ {Γ j Q N P}, .imp Q N ∈ Γ → C Γ [] .tru (.up Q) →
      C (N :: Γ) [] j (.up P) → C Γ [] j (.up P)
  /-- `LFoc.and1`/`and2`, guarded: projection, the continuation gaining the
  chosen conjunct. (Same correction as `cl_impL`.) -/
  cl_andL : ∀ {Γ j M N P}, .and M N ∈ Γ → C (M :: Γ) [] j (.up P) →
      C Γ [] j (.up P)
  cl_andL' : ∀ {Γ j M N P}, .and M N ∈ Γ → C (N :: Γ) [] j (.up P) →
      C Γ [] j (.up P)
  /-- `circL` ★. **Guarded, and at `.lax` only.** Stripping `◯` from a hypothesis
  in the lax phase. The clause into which contraction-tracking goes — see
  below. -/
  cl_circL : ∀ {Γ Q P}, .circ Q ∈ Γ → C Γ [Q] .lax (.up P) → C Γ [] .lax (.up P)

/-! ## What the extraction found

Two observations, both of which the strategy document predicted as tests of
whether the reframing is right.

**1. The contraction-tracking IS a guarded positive-phase clause — `cl_circL`.**
The document's "cheap early test" was: *if the contraction-count turns out to be
a guarded (positive-phase) closure condition, that is strong evidence the whole
reframing is right, and it makes the "same obstruction twice" claim precise.*
It does. And the focused calculus shows why in a sharper form than expected: in
`PLLFocused`, `Stab.lfoc` selects a hypothesis by **membership** and never
removes it, so a hypothesis may be re-focused any number of times and the
context is never consumed. The contraction that `G4` had to count, and that
`G4c` absorbed into its retention rules, is here **not a resource at all** — it
is the number of times `lfoc` picks the same hypothesis, which is a property of
the focusing phase and nothing else. So `cl_circL` is where it goes, guarded by
`.lax`, exactly as predicted.

**2. The difficulty is `cl_orL`, not any modal clause.** The candidate must be
closed under **join** — two branches, one conclusion — and, as the header
records, that clause is the reason the whole candidate has to be indexed over
inversion sequents rather than stable ones: over stable sequents it is not even
expressible. Every modal clause (`cl_circR`, `cl_circL`) is a transport or a
strip, and both are unproblematic. This is the third independent arrival at the
same place: `docs/ui-two-routes.md` §1 found `∃p` free and `∀p` blocked by joins
overshooting; the closed-fragment work found `∨` to be the source of the
infinitude of RN(◯,{}) while the `∨`-free part is finite; and now the candidate
extraction puts the load on the one clause `∨` contributes.

**The recommendation that follows.** Attack `cl_orL` — equivalently the
directedness criterion of `docs/ui-two-routes.md` §1 — and treat the modal
clauses as solved. If `cl_orL` is unsatisfiable the strategy document's
outcome (b) applies and there is an impossibility result; if it is satisfiable
the induction closes. Either is the paper.

**Status.** `Cand` is a definition, not a theorem: nothing here asserts that a
candidate exists, and no field is discharged. What is claimed is only that these
are the clauses the rules of `PLLFocused` force, and that they split along the
polarity boundary as the strategy document predicted. -/

end Candidate
end PLLND
