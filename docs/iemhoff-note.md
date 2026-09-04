# Notes on the uniform-interpolation development for Propositional Lax Logic

*Draft — for M. Fairtlough to review and, if he judges it useful, to send.*

This note records some findings from a machine-checked formalisation, in Lean 4,
of Propositional Lax Logic (PLL) and of the sequent calculi used in your
*Proof Theory for Lax Logic* (arXiv:2209.08976v1; the book chapter of the same
title). The formalisation covers PLL as a natural-deduction/term calculus, the
single-succedent G3-style calculus (here `SC`, your G3iLL) and the
contraction-free calculus `G4` (your G4iLL, transcribed from Fig. 2.3), together
with a verified decision procedure for `G4`-derivability. Everything referred to
below is in the public repository `github.com/fairflow/lax-logic-in-lean`; each
claim names the Lean file and theorem that establishes it, and is marked as
proved (machine-checked), refuted (with an explicit witness), or open.

The formalisation turned up two genuine problems in the G4iLL route to uniform
interpolation, plus one purely local slip in the soundness proof of the
interpolant assignment. It also confirms the positive core: Craig interpolation
for PLL goes through cleanly, and a small repair of G4iLL restores exactly the
calculus your programme needs. None of this is offered as anything other than
the ordinary business of mechanisation, which is good at finding the places
where a paper proof and a machine disagree.

Throughout, ◯ is the lax modality of Fairtlough–Mendler PLL (◯A = "A holds
subject to some constraint"), the strong monad of the logic; it is the modality
your papers write as a circle (rendered `#` in the OCR of the arXiv source,
which I have normalised to ◯ in the quotations below). All sequents are
single-succedent.

---

## 1. The headline findings

1. **G4iLL is not complete for PLL.** There is a sequent that is PLL-derivable
   (and derivable in G3iLL) but not derivable in G4iLL. Hence Corollary 1 of
   arXiv:2209.08976 — G3iLL and G4iLL are equivalent — is false as stated.
2. **Cut and contraction are not admissible in G4iLL.** Both are refuted by
   explicit witnesses. In particular Fact 3 ("G4iLL is a balanced calculus")
   fails, since balancedness requires cut-admissibility.
3. **A separate, local flaw** sits inside the soundness proof of the interpolant
   assignment: Lemma 7, case (DPN) for the L◯ rule, first subcase. The
   derivation given closes the *wrong* sequent.
4. **Craig interpolation for PLL holds** (Maehara's method over the cut-free
   calculus), machine-checked.
5. **A minimally repaired G4iLL exists** — three rules retain their principal
   formulas — and is proved complete for PLL, with cut and contraction
   admissible and equivalent to natural deduction. So the target calculus your
   argument wants does exist; uniform interpolation for PLL itself remains open
   in the formalisation (one lemma outstanding).

---

## 2. G4iLL is incomplete for PLL

Write F′ := ◯p ⊃ r and G′ := F′ ⊃ ◯p = (◯p ⊃ r) ⊃ ◯p. The separating
sequent is ◯G′, F′ ⇒ r.

Proved derivable in G3iLL (`PLLG4Gap.sep_SC`, `LaxLogic/PLLG4Gap.lean`):
bind on ◯G′; a second use of F′ inside the `laxL` box-opening turns G′
into ◯p, so ◯p holds outright, and F′ gives r as the final implication.

Refuted in G4iLL (`PLLG4Gap.sep_not_G4`): a kernel-checked proof term
(axiom audit `propext` only, no choice or quotients, no compiled
evaluation), agreeing with the decision procedure's `false` verdict. The
cause is retention: your L○→ (like R○→) consumes its principal implication, so
its first premise here, G′ ⇒ ◯p, is invalid, and no rule instance keeps
the second copy of F′ the G3 proof needs inside the box — every branch
fails. This is Howe's duplication phenomenon (MSCS 2001) one level up:
the formula needing contraction is the ◯-antecedent implication itself,
straddling a box-opening. A constant-only variant, F = ◯⊥ ⊃ ⊥,
G = F ⊃ ◯⊥, separates the calculi the same way, so this is not about the
atom p.

Packaged: `PLLG4Gap.sc_but_not_G4` proves `SC` derives ◯G′, F′ ⇒ r while
`G4` does not.

**Consequence.** Corollary 1 — "G3iLL and G4iLL are equivalent and the
structural rules are admissible in both" — is refuted: the general
theorem it invokes (Theorem 1 of *The G4i analogue of a G3i calculus*,
arXiv:2011.11847) fails in exactly its modal case, since the premises
S_i here carry an extra copy of ◯φ→ψ, so S_i ≪ S fails and the copy
cannot be dropped. Fact 3 ("G4iLL is balanced") rests on Fact 2 and
Corollary 1; Theorem 5 — the interpolation engine of *Uniform
interpolation and the existence of sequent calculi* (APAL 2019) — needs a
balanced calculus, so the Theorem 5 → 6 chain ("PLL has uniform
interpolation") is not established as given.

---

## 3. Cut and contraction are not admissible in G4iLL

Both fail on the same family, each an explicit derivation pair plus the
underivability of §2.

**Cut.** Refuted (`PLLG4Gap.cut_not_admissible`) on cut formula ◯p:
`cut_left_G4` derives ◯G′, F′ ⇒ ◯p and `cut_right_G4` derives ◯p, ◯G′,
F′ ⇒ r, both G4iLL-derivable, but cutting them gives the underivable
sequent of §2, ◯G′, F′ ⇒ r.

**Contraction.** Refuted (`PLLG4Gap.contraction_not_admissible`): two
copies of F′ make the sequent derivable — one consumed by L○→ outside the
box, the other inside it — but one copy does not: ◯G′, F′, F′ ⇒ r holds
while ◯G′, F′ ⇒ r does not.

Both witnesses have a clean axiom audit (`propext` only). Contraction
failure is what a corrected balancedness claim would need to add; cut
failure directly contradicts Fact 3.

---

## 4. A local flaw in the soundness proof: Lemma 7, (DPN)-L○, first case

Independent of §§2–3, and not fixed by restoring cut: a slip in the
induction of Lemma 7 (soundness of the interpolant assignment).

**Setup.** For the L○ rule the last inference is S_1 = (Γ, ψ ⇒ ◯φ) over
S = (Γ, ◯ψ ⇒ ◯φ). For an i-part S^i non-principal for L○, the paper
splits into two cases — S^i = (Γ^i ⇒ ◯φ), or S^i = (Γ^i ⇒) with empty
succedent — with two obligations:

> "We have to show that ⊢ Γ^r, ◯ψ, ∃p S^i ⇒ ∀p S^i in the first case,
> and ⊢ Γ^r, ◯ψ, ∃p S^i ⇒ ◯φ in the second case."

So the first case's target has succedent ∀p S^i. But the derivation given
is:

> "If S^i = (Γ^i ⇒ ◯φ), we have ⊢ Γ^r, ψ, ∃p S_1^i ⇒ ◯φ by the induction
> hypothesis. An application of L○ gives ⊢ Γ^r, ◯ψ, ∃p S_1^i ⇒ ◯φ, and
> since S_1^i = S^i, this is what we had to show."

*(Lemma 7's proof, arXiv:2209.08976v1; lax modality rendered ◯, the
derivability decoration D^p_R written ⊢.)*

That is the *second* case's sequent, not the first case's ∀p S^i, so it
closes the wrong obligation — and no L○ instance can close the right one:
L○ needs a ◯-shaped succedent, but ∀p S^i is by definition
∀^+p S^i ∨ ∀^-p S^i ∨ ∀^at p S^i, never ◯-shaped, and no disjunct
anticipates a succedent-side box — the L○/γ-disjuncts range over
antecedent-side boxes and implications (◯α→β ∈ Γ^i), while the
R○-disjunct ◯∀p(Γ^i ⇒ φ) needs an induction hypothesis at (Γ, ψ ⇒ φ)
that a derivation ending in L○ lacks.

**Status.** Refuted as a proof step, machine-locatable
(`wip/g4ill_ui.lean`, the (DPN)-L○ first case). Not an easy fix: the
natural repair — a box-goal clause recursing at the *same* sequent — is a
self-reference the Dershowitz–Manna order behind your Fact 1/2
termination forbids, so this would break termination. The flaw and the §2
completeness gap are complementary, not the same error.

The flaw looks to be in the *proof*, not the *statement*: `G4`-derivability
is decidable and both interpolants computable, so the lemma's claims are
checkable instance by instance. A sweep (`wip/g4ill_probe.lean`) decided
roughly 2,550 instances of the soundness statements — including 1,080 of
the L4→ conjunct of §5, and every decided (DPN)-L○ instance, including
the exact breaking shape — and found *no counterexample*: the required
`G4`-derivation always exists. A few large instances remain undecided, so
this is evidence, not a theorem; the natural conjecture is that Lemma 7
holds of G4iLL and only its proof needs repair. **Status.** Open, with
instance-level evidence in favour.

---

## 5. The L4→ interpolant: a second, independent deviation

A related but separate issue concerns the ∃-assignment for the L4→ rule:

```
  Γ, ψ→γ ⇒ φ→ψ    Γ, γ ⇒ Δ
  ────────────────────────── L4→
     Γ, (φ→ψ)→γ ⇒ Δ
```

for which the standard assignment (APAL 2019 §5) sets ι∃^R p S = ∃p S_1 ∧
(∀p S_1 → ∃p S_2).

Soundness of the *first conjunct*, ∃p S_1 — property (IPP), that
Γ ⊢ ∃p S_1 — is argued (APAL 2019, p. 26) from the "obvious fact that
⊢ ⋀S^a → ⋀S_1^a," replacing the context along that derivable implication.
That replacement is a composition of derivabilities — a cut — and cut is
unavailable in G4iLL (§3); nor does induction supply it, since the
premise-1 context B→D, Γ∖F is not reachable from Γ by any G4iLL rule
without changing the goal, which the L4→ instance fixes at φ→ψ.

By contrast, Pitts's guarded shape for the same conjunct —
(E(S_1)→A(S_1)) → E(D, Γ∖F) rather than bare E(S_1) — is derivable
cut-free in G4iLL (machine-checked, `wip/g4ill_ui.lean`: fire the
retained L○-style implication rule, discharge the guard by an
in-context, consumed-form modus ponens). It is the printed assignment's
deviation from this guarded shape that costs the (IPP) argument its cut —
a second, independent point where the assignment, not the calculus,
wants revisiting.

---

## 6. What survives, and the positive core

**Craig interpolation for PLL.** Proved (`LaxLogic/PLLCraig.lean`:
`craig_interpolation`, `craig_implication`), via Maehara's method over
the cut-free calculus `SC` (proved equivalent to natural deduction and
the term calculus): from a derivation of Γ_1,Γ_2 ⊢ C it yields an
interpolant I with Γ_1 ⊢ I, I,Γ_2 ⊢ C, and every atom of I shared between
Γ_1 and Γ_2,C. The construction is the textbook intuitionistic one plus
one lax-specific move: when the ◯-left rule's principal formula lies in
Γ_1, box the premise interpolant, I ↦ ◯I — forced, since Γ_1 ⊢ ◯I opens
the boxed antecedent under a now-◯-shaped goal, and ◯I, Γ_2 ⊢ ◯B (the
end-formula is necessarily of this shape for the ◯-left rule to apply)
opens ◯I under the ◯-shaped end-formula. Axiom audit: Lean's standard axioms
only (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no
compiled evaluation.

**A repaired G4iLL.** Proved complete and structural: the one-token
repair from §2 lets three rules retain their principal formulas rather
than consume them — L○→'s first premise keeps its implication (compare
→SL of van der Giessen–Iemhoff's G4iSL, whose first premise likewise
retains its principal), and, as the admissibility proofs also required,
the box rules keep their box and R○→ keeps its context. The result
(`G4c`, `LaxLogic/PLLG4H*.lean`) is proved complete for PLL, slotting
into G4c = SC = natural deduction = term calculus (`PLLG4HComp.lean`:
`completeness`, `equiv_sc`, `equiv_nd`, `equiv_tm`), with cut
(`PLLG4HCut.lean`) and contraction admissible. So the calculus your
programme needs does exist: your G4iLL with these three retentions.

**Uniform interpolation for PLL.** Open in the formalisation. With the
tables transcribed faithfully, essentially all of it is machine-checked
(p-freeness, both independent interpolant properties bar the §5
conjunct, and the adequacy commutations for the axioms, all right rules,
and the box rules) except a single stabilization lemma: three systematic
finite-countermodel searches found no counterexample, but it is not yet
proved. "PLL has uniform interpolation" is thus neither established nor
refuted here; the honest status is one outstanding lemma.

---

## 7. Closing

I hope this is read in the spirit intended: mechanisation is unusually good at
locating the exact sequents where a hand proof and a proof assistant part
company, and the separating sequent of §2 is a small and, I think, genuinely
interesting one. The substantive corrections are two — the incompleteness of
G4iLL (with the attendant failure of Corollary 1, Fact 3, and the completeness
premise of the Theorem 5–6 chain) and the local L◯ slip in Lemma 7 —
and the programme's positive goal is intact: Craig interpolation holds, and a
minimally repaired calculus recovers the structural properties the argument
relies on.

Every claim above is a checkable Lean statement in
`github.com/fairflow/lax-logic-in-lean`; the file and theorem names are given
inline, and M. Fairtlough can supply any of the derivations, the decision-
procedure verdicts, or the transcribed tables in whatever form is most useful.

---

### Numbering cross-reference

| Claim | arXiv:2209.08976v1 | Book chapter† |
|---|---|---|
| G3iLL ≡ G4iLL (refuted) | Corollary 1 | Corollary 8.1 |
| G4iLL balanced (refuted) | Fact 3 | — |
| Interpolation engine (balanced ⇒ UI) | Theorem 5 | — |
| PLL has uniform interpolation | Theorem 6 | Theorem 8.6 |
| Interpolant assignment (§) | §6.3–6.8 | §8.6 |
| Soundness of assignment (local flaw) | Lemma 7, (DPN)-L◯ | — |

† Book-chapter numbers are the correspondences recorded in the repository's
transcription notes; the arXiv numbers in the left column were each checked
against the arXiv source text, the book numbers were not independently verified
against a book PDF here.

---

## Appendix: the calculi and the key statements, precisely

*For self-containedness, this appendix states the central definitions and
theorems both as they stand in the Lean sources (verbatim) and in ordinary
mathematical language. `PLLFormula` is the propositional lax language
(atoms `prop a`, `falsePLL`, `and`, `or`, `ifThen`, `somehow` = ◯);
contexts are lists; `Γ.Perm Δ` is list permutation, so a premise of the
form `Γ.Perm (F :: Δ)` reads "the principal formula F occurs in Γ, and Δ
is the rest". Everything is in `github.com/fairflow/lax-logic-in-lean`.*

### A.1 The transcribed G4iLL (`G4`, `LaxLogic/PLLG4.lean`)

```lean
inductive G4 : List PLLFormula → PLLFormula → Prop
  | init     (h : prop a ∈ Γ) : G4 Γ (prop a)
  | botL     (h : falsePLL ∈ Γ) : G4 Γ C
  | andR     : G4 Γ A → G4 Γ B → G4 Γ (A.and B)
  | orR1     : G4 Γ A → G4 Γ (A.or B)
  | orR2     : G4 Γ B → G4 Γ (A.or B)
  | impR     : G4 (A :: Γ) B → G4 Γ (A.ifThen B)
  | laxR     : G4 Γ A → G4 Γ A.somehow
  | andL     (h : Γ.Perm (A.and B :: Δ)) :
      G4 (A :: B :: Δ) C → G4 Γ C
  | orL      (h : Γ.Perm (A.or B :: Δ)) :
      G4 (A :: Δ) C → G4 (B :: Δ) C → G4 Γ C
  | laxL     (h : Γ.Perm (A.somehow :: Δ)) :
      G4 (A :: Δ) B.somehow → G4 Γ B.somehow
  | impLProp (h : Γ.Perm ((prop a).ifThen B :: Δ)) (ha : prop a ∈ Δ) :
      G4 (B :: Δ) C → G4 Γ C
  | impLBot  (h : Γ.Perm (falsePLL.ifThen B :: Δ)) :
      G4 Δ C → G4 Γ C
  | impLAnd  (h : Γ.Perm ((A.and B).ifThen D :: Δ)) :
      G4 (A.ifThen (B.ifThen D) :: Δ) E → G4 Γ E
  | impLOr   (h : Γ.Perm ((A.or B).ifThen D :: Δ)) :
      G4 (A.ifThen D :: B.ifThen D :: Δ) E → G4 Γ E
  | impLImp  (h : Γ.Perm ((A.ifThen B).ifThen D :: Δ)) :
      G4 (B.ifThen D :: Δ) (A.ifThen B) → G4 (D :: Δ) E → G4 Γ E
  | impLLax  (h : Γ.Perm (A.somehow.ifThen B :: Δ)) :
      G4 Δ A → G4 (B :: Δ) C → G4 Γ C
  | impLLaxLax (h : Γ.Perm (A.somehow.ifThen B :: X.somehow :: Δ)) :
      G4 (X :: Δ) A.somehow → G4 (B :: X.somehow :: Δ) C → G4 Γ C
```

*(Implicit binders elided for readability here; the source spells them
out. This is our transcription of Fig. 2.3 of arXiv:2209.08976v1.)*

In words: the right rules and `init`/`⊥L` are as in G3; every left rule
**consumes** its principal formula — the premise context is `Δ`, the rest
of `Γ`. In particular: `laxL` (from A, Δ ⊢ ◯B infer Γ ⊢ ◯B when ◯A ∈ Γ)
deletes the box; `impLLax` — the first of the two rules for an
implication with ◯-antecedent — proves its first premise Δ ⊢ A *without*
the implication ◯A ⊃ B; and `impLLaxLax` — the second such rule, which
uses an auxiliary box ◯X from the context — proves its first premise
X, Δ ⊢ ◯A with *both* the implication and the auxiliary box deleted.
Contraction-freeness is thus taken in the strongest possible sense:
nothing principal survives into any premise.

### A.2 The repair (`G4h`/`G4c`, `LaxLogic/PLLG4H.lean`)

`G4h` is the same calculus with a height index (`G4h n Γ C`: derivable
with height at most `n`; the index is bookkeeping for the termination
and interpolation analyses) and with exactly **three rules changed**, all
in the direction of *retention*:

```lean
  | laxL {n Γ A B} (h : A.somehow ∈ Γ) :
      G4h n (A :: Γ) B.somehow → G4h (n + 1) Γ B.somehow
  | impLLax {n Γ Δ A B C} (h : Γ.Perm (A.somehow.ifThen B :: Δ)) :
      G4h n Γ A → G4h n (B :: Δ) C → G4h (n + 1) Γ C
  | impLLaxLax {n Γ Δ A B X C}
      (h : Γ.Perm (A.somehow.ifThen B :: Δ)) (hX : X.somehow ∈ Δ) :
      G4h n (X :: Γ) A.somehow → G4h n (B :: Δ) C → G4h (n + 1) Γ C

def G4c (Γ : List PLLFormula) (C : PLLFormula) : Prop := ∃ n, G4h n Γ C
```

In words, the one-token repair: `laxL` now **keeps the box** — the
premise is A, Γ ⊢ ◯B with ◯A still present in Γ; `impLLax`'s first
premise is now Γ ⊢ A over the **full** context — the implication
◯A ⊃ B is retained there (compare the →SL rule of van der
Giessen–Iemhoff's G4iSL, whose first premise likewise retains its
principal); and `impLLaxLax`'s first premise is X, Γ ⊢ ◯A over the full
context — implication and auxiliary box both retained. Every other rule
is unchanged. We write G4iLL″ for the repaired calculus in prose, `G4c`
in Lean.

### A.3 The counterexample and the two failed structural rules

With `Fa := ◯p ⊃ r` and `Ga := (◯p ⊃ r) ⊃ ◯p`:

```lean
theorem sep_SC : SC [Ga.somehow, Fa] (prop "r")          -- audit: [propext, Quot.sound]
theorem sep_not_G4 : ¬ G4 [Ga.somehow, Fa] (prop "r")    -- audit: [propext]
```

In words: the sequent ◯((◯p ⊃ r) ⊃ ◯p), ◯p ⊃ r ⊢ r is derivable in the
cut-free G3-style calculus (hence in PLL), and underivable in the
transcribed G4iLL. The underivability is a genuine finite analysis of
the (finite, loop-checked) G4-search space, kernel-checked with
`propext` as the only axiom — no classical logic, no trusted evaluation.

```lean
theorem contraction_not_admissible :
    G4 [Ga.somehow, Fa, Fa] (prop "r") ∧ ¬ G4 [Ga.somehow, Fa] (prop "r")

theorem cut_not_admissible :
    G4 [Ga.somehow, Fa] ((prop "p").somehow) ∧
    G4 [(prop "p").somehow, Ga.somehow, Fa] (prop "r") ∧
    ¬ G4 [Ga.somehow, Fa] (prop "r")
```

In words: with *two* copies of ◯p ⊃ r the sequent becomes G4-derivable,
with one it is not — contraction fails; and ◯p interpolates (both
premises of the cut are G4-derivable) while the conclusion is not —
cut fails. The mechanism in both is the same consumed token: a
derivation needs ◯p ⊃ r once to *produce* ◯p and once more to *use* it,
and the consuming rules cannot have both.

### A.4 The repaired calculus is the right one

```lean
theorem G4c.cut : G4c Γ (A) → G4c (A :: Γ) C → G4c Γ C        -- [propext, Quot.sound]
theorem G4c.completeness : SC Γ C → G4c Γ C                    -- [propext, Quot.sound]
theorem G4c.equiv_tm : G4c Γ φ ↔ Nonempty (Tm Γ φ)             -- [propext, Quot.sound]

instance decidablePLL (Γ : List PLLFormula) (φ : PLLFormula) :
    Decidable (Nonempty (Tm Γ φ))

theorem height_bound (h : G4c Γ C) : G4sh (decideFuel Γ C) Γ.toFinset C
```

In words: cut is admissible in G4iLL″; G4iLL″ derives everything the
cut-free G3 calculus does; and G4iLL″-derivability coincides with
PLL-derivability (stated through the proof-term calculus `Tm`; the
natural-deduction form `equiv_nd` is also proved). Backward search in
G4iLL″ over set-contexts with a loop check terminates, giving a full
decision procedure for PLL (`decidablePLL`) — the mechanised form of
Fairtlough–Mendler's Theorem 2.8 — and, as a by-product of the
termination analysis, an explicit derivation-height bound
(`height_bound`), which is exactly the ingredient a fuel-recursive
Pitts-style interpolant assignment needs. The audits shown are the
current measured values; the two `Decidable` instances additionally use
`Classical.choice` in two identified places of their totality proof
(a least-height step, and Mathlib finite-set internals), currently
being removed.

*(Statement sources: `LaxLogic/PLLG4Gap.lean`, `LaxLogic/PLLG4HComp.lean`,
`LaxLogic/PLLG4Dec.lean`. The `#print axioms` audits are pinned by
`#guard_msgs` at build time, so the values quoted here are enforced by
the build, not transcribed by hand.)*
