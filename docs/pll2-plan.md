# PLL2: second-order propositional lax logic — calculus, plan, and mechanisation

*Written 2026-08-09. Companion to `docs/second-order-pll-survey.md`, which is the
literature survey; this file is the design document. Nothing here is machine-checked.
Every claim carries a label: **PROVED** (machine-checked in this repository, with the file
named), **DERIVABLE** (a complete derivation is given here or is a two-line consequence of
something PROVED), **CONJECTURED**, **OPEN**, **REFUTED**.*

*Verification discipline for citations: **CONFIRMED** = bibliographic data read off a
publisher, DOI, arXiv, Project Euclid or JSTOR record, or off a fetched PDF.
**SEMI-VERIFIED** = certainly real, one field from a secondary listing. **UNVERIFIED** =
could not confirm; must not be cited as fact. No page numbers or theorem numbers are
invented. Items marked *(carried)* are inherited from `second-order-pll-survey.md` at the
status recorded there.*

> **Correction to the survey, carried at the top.** `second-order-pll-survey.md` §0.2 and
> §2.5(i) state that PLL has uniform interpolation, PROVED by Iemhoff 2024. That is not
> this project's assessment. Iemhoff's uniform-interpolation theorem routes through her
> Corollary 8.1, whose adequacy needs `G4iLL ≡ PLL`, and `G4iLL` is machine-checked
> **INCOMPLETE** for PLL here: the sequent `◯((◯p→r)→◯p), ◯p→r ⇒ r` is derivable in `SC`
> and rejected by the verified `G4` decider (`LaxLogic/PLLG4Gap.lean`, and
> `docs/calculus-map.md` under "`G3iLL`, `G4iLL`"). **Uniform interpolation for PLL is
> OPEN.** Everything below that depends on UI is therefore conditional, and is marked so.
> Iemhoff's *Craig* interpolation result is unaffected, its proof using `G3iLL` only.

---

## 0. Summary

1. **PLL2 = IPC2 + `◯`**, where `◯` is a primitive nucleus with exactly the two PLL
   natural-deduction rules (unit and bind), and IPC2 is intuitionistic propositional logic
   with impredicative propositional quantifiers. §1 gives the natural deduction system, the
   Pfenning–Davies two-judgment variant, and the G3-style sequent calculus.
2. **`◯` binds nothing, changes no free variables, and commutes with substitution.** Every
   quantifier-related property of the system turns on that one fact, and it is why the
   design has so few genuinely new obligations. §1.4.
3. **Do not add a second quantifier sort.** The survey's `∀°p` over `◯`-fixpoints is
   *relativised* quantification, definable in the one-sorted language:
   `∀°p.φ := ∀p.((◯p→p) → φ)`, `∃°p.φ := ∃p.((◯p→p) ∧ φ)`. §1.6. This removes an entire
   sort, its rules, and its metatheory from the plan, and Proposition C survives intact.
4. **Conservativity over IPC2: prove it by the `◯`-erasure, not proof-theoretically and not
   semantically.** The repository's existing `conservativity_prop` (`PLLNDCore.lean:193`)
   lifts *verbatim*: four new cases, all of them identity cases. §2.4 gives the complete
   argument and the Lean statement. This is the single cheapest real theorem in the plan.
5. **The proof-theoretic route to conservativity is dead, and for a robust reason**: L∀
   instantiates with an arbitrary formula `χ`, so a cut-free PLL2 derivation of a `◯`-free
   end-sequent may contain `◯` inside an instance. The subformula property fails for the
   quantifiers, and it was the whole engine of that argument. §2.2.
6. **The semantic route is blocked too**, and the diagnosis is precise: the route needs a
   completeness theorem *for the target logic*. It therefore succeeds for PLL over IPL and
   for IPC2 over IPC (both targets are first-order and complete), and fails for PLL2 over
   IPC2, whose target is itself second-order and has no completeness theorem (Kremer 1997,
   Skvortsov 1997). §2.3 tabulates the three cases.
7. **Models.** Admissible propositions of an F&M constraint model are the up-sets
   containing the fallible set `F`; both conditions are forced, and they form a *complete
   nuclear Heyting algebra* whose nucleus is the `◯`-clause. Full second-order semantics =
   quantification over that algebra. On a **finite** model there are finitely many
   admissible propositions, so second-order forcing is decidable and countermodels are
   `decide`-checkable in the exact style of `PLLFrames.lean`. §3.
8. **PLL2 is expected to be sound but incomplete for the full semantics**, by analogy with
   Kremer/Skvortsov. That is normal for second-order propositional logics and is stated,
   not hidden. The standard repair is **Henkin semantics**, and the nearest neighbouring
   paper (Becker–Das–Marin–Padhiar 2026 on second-order intuitionistic tense logic) takes
   it explicitly, saying in terms that completeness for full semantics fails. PLL2 wants
   both semantics, doing different jobs. §3.4.
9. **Cut elimination is the expensive item and should be deferred.** The repository's cut
   measure (cut formula, sum of heights) *dies* at the ∀-reduction: `φ^χ` can have larger
   degree than `∀p.φ`. Girard's reducibility candidates then become mandatory, and the
   precise place is the definition of `Red` by recursion on the formula in
   `PLLReducibility.lean`, which must become `Red_η` parameterised by a candidate
   assignment. §4.3. **But there is a cheaper route, verified and one logic away**: a
   labelled sequent calculus plus Henkin semantics plus completeness by proof search yields
   cut-*admissibility* without any impredicative normalisation. That is what Becker et al.
   do, and it is what PLL2 should do if cut is wanted. §4.2(d), §4.4.
10. **Undecidability of PLL2 is a corollary of §2's conservativity theorem**, needing no
    separate translation argument. Cite **Löb 1976 and Sobolev 1977** for the undecidability
    of IPC2, **not Gabbay 1974 alone** — Gabbay proves it for IPC2 + constant domains and
    his argument was corrected by Sobolev. §5.1. And the Pitts image is a decidable *sound
    over-approximation* of PLL2, not its decidable fragment: Sørensen–Urzyczyn's Remark 3.3
    gives a concrete witness, `∀p(p∨¬p)`, that Pitts' quantifier is not a definition of `∀`.
    §5.3.

**Biggest design risk**: §7. **Two live corrections to the survey**: the UI status at the
head of this file, and the Gabbay attribution in item 10.

---

## 1. The calculus, formalised

### 1.1 Syntax

Propositional variables come from a countable set. The repository's `PLLFormula` uses
`String` atoms (`LaxLogic/PLLFormula.lean:3`), and the plan keeps them: **locally nameless**
representation, free variables are `String`s and bound variables are de Bruijn indices.
Justification in §6.1.

    φ ::= fvar s | bvar n | ⊥ | φ ∧ φ | φ ∨ φ | φ → φ | ◯φ | ∀.φ | ∃.φ

with `⊤ := ⊥→⊥` and `¬φ := φ→⊥`. In the displayed rules below, `∀p.φ` and `∃p.φ` are
written in the named style and `φ^χ` denotes instantiation of the outermost bound variable
by `χ` (so `φ^s` abbreviates `φ^(fvar s)`). `FV(φ)` is the finite set of free atoms of `φ`.

**Choice of base.** The presentation is the *full* connective set `⊥,∧,∨,→,◯,∀,∃`, not the
Russell–Prawitz-minimal `→,∀,◯`. Two reasons, both practical:

* The repository's entire PLL development is over the full connective set, and the whole
  point of the erasure argument of §2.4 is that it is the existing `PLLNDCore.lean` proof
  with four cases added. A minimal base would force a re-encoding of every existing PLL
  formula and would break the `decide`-based countermodel machinery.
* `∨` is exactly where PLL is interesting (the distribution axiom, mutual confluence, the
  disjunction property in `SC`) and exactly where the algebraic literature does **not**
  reach: Bezhanishvili et al. 2021 on nuclear implicative semilattices covers the `∨`-free
  fragment only *(carried, CONFIRMED)*.

The Russell–Prawitz definability of `⊥,∧,∨` from `→,∀` remains available as a *derived*
observation and is worth stating as a milestone theorem (§6.3, M7), not as the definition.

### 1.2 Natural deduction: `LaxND2`

The IPC2 base is the standard natural-deduction presentation (Prawitz-style second-order
ND; the modern textbook reference is Sørensen–Urzyczyn's *Lectures on the Curry–Howard
Isomorphism*, where IPC2 is the logic of System F *(carried, SEMI-VERIFIED)*). All the IPC
rules of `PLLND.LaxND` (`PLLNDCore.lean:72`) are kept unchanged, with contexts as lists,
membership-based `iden`, and no structural rules (weakening, exchange and contraction are
admissible by one renaming traversal, `LaxND.rename`, `PLLNDCore.lean:108`).

The four quantifier rules, in **cofinite** form (Aydemir–Charguéraud–Pierce–Pollack–Weirich,
"Engineering formal metatheory", POPL 2008 — see §6.1 for why cofinite):

    for all s ∉ L:  Γ ⊢ φ^s                    Γ ⊢ ∀p.φ
    ──────────────────────────── (∀I)         ──────────── (∀E)   χ any formula
    Γ ⊢ ∀p.φ                                   Γ ⊢ φ^χ

    Γ ⊢ φ^χ                        Γ ⊢ ∃p.φ    for all s ∉ L:  Γ, φ^s ⊢ ψ
    ─────────── (∃I)   χ any       ──────────────────────────────────────── (∃E)
    Γ ⊢ ∃p.φ                       Γ ⊢ ψ

`L` is any finite set of atoms; the reading is "for every `s` outside some finite `L`". In
the named presentation the side conditions are the usual eigenvariable conditions: in (∀I),
`p ∉ FV(Γ)`; in (∃E), `p ∉ FV(Γ) ∪ FV(ψ)`. Comprehension is **full**: no restriction on `χ`
beyond capture-avoidance, so `χ` may contain the quantifier being instantiated, and may
contain `◯`.

The two lax rules are exactly the repository's, unchanged
(`PLLNDCore.lean:93`, `:95`):

    Γ ⊢ φ                     Γ ⊢ ◯φ     Γ, φ ⊢ ◯ψ
    ─────── (laxIntro)        ─────────────────────── (laxElim)
    Γ ⊢ ◯φ                    Γ ⊢ ◯ψ

These are F&M's `◯R` / bind pair. Nothing about them changes in the presence of
quantifiers, and no new interaction rule is added: **`◯` is axiomatised exactly as in PLL**.
In Hilbert form the same content is `somehowR`, `somehowM`, `somehowS`, `somehowBind`
(`LaxLogic/PLLAxiom.lean`).

**Definition.** `Deriv2 Γ φ := Nonempty (LaxND2 Γ φ)` is what "PLL2 proves" means, by exact
analogy with `Deriv` for PLL (`docs/calculus-map.md`).

**The two commutation directions that hold, and their converses.** Both are inherited from
the survey and both are correct:

* `⊢ ∃p.◯φ → ◯∃p.φ` **[DERIVABLE]** — from `φ ⊢ ∃p.φ`, monotonicity of `◯`, then (∃E).
* `⊢ ◯∀p.φ → ∀p.◯φ` **[DERIVABLE]** — from `∀p.φ ⊢ φ`, monotonicity, then (∀I).
* `◯∃p.φ → ∃p.◯φ` and `∀p.◯φ → ◯∀p.φ` **[CONJECTURED FALSE]** — the `Rm`-successor
  witnessing `◯φ` may depend on the proposition substituted for `p`. §3.5 says what a
  countermodel would have to look like and why it is `decide`-checkable.

Neither derivable direction uses anything about `◯` beyond monotonicity, so neither is
PLL-specific. The PLL2-specific content is in §1.6 and §2.

### 1.3 The judgmental variant: `PD2`

The Pfenning–Davies two-judgment presentation (`LaxLogic/PLLJudgmental.lean`) extends with
no surprises. Judgments `Γ ⊢ φ true` and `Γ ⊢ φ lax`; hypotheses are always `true`. The lax
rules are unchanged (`PLLJudgmental.lean:69`, `:71`, `:74`):

    Γ ⊢ φ true              Γ ⊢ φ lax               Γ ⊢ ◯φ true    Γ, φ ⊢ χ lax
    ──────────── (laxU)     ───────────── (circI)   ───────────────────────────── (circE)
    Γ ⊢ φ lax               Γ ⊢ ◯φ true             Γ ⊢ χ lax

**Design decision: the quantifier rules live in the `true` judgment only.** This mirrors the
repository's treatment of `orE`, which also concludes only in `.tru`, and it costs nothing,
because the `lax` versions are derivable through `circInvert` (`PLLJudgmental.lean:175`).
Explicitly, to get `Γ ⊢ χ lax` from `Γ ⊢ ∃p.φ true` and `Γ, φ^s ⊢ χ lax`:

    Γ, φ^s ⊢ χ lax  ⟹(circI)  Γ, φ^s ⊢ ◯χ true  ⟹(∃E)  Γ ⊢ ◯χ true  ⟹(circInvert)  Γ ⊢ χ lax

**[DERIVABLE]**. The (∃E) step needs `s ∉ FV(Γ) ∪ FV(◯χ)`, and `FV(◯χ) = FV(χ)` because `◯`
binds nothing — the eigenvariable condition transfers with no adjustment. This is the first
of several places where the free-variable-neutrality of `◯` does all the work.

### 1.4 The substitution property

    **(Sub)**  If  Γ ⊢ φ  then  Γ[χ/p] ⊢ φ[χ/p],  for every PLL2-formula χ.

This is the coherence condition on the whole system, and (∀E)/(∃I) with arbitrary `χ` are
incoherent without it. Two facts make it routine, and both are consequences of `◯` binding
nothing:

* **`◯` commutes with substitution**: `(◯φ)[χ/p] = ◯(φ[χ/p])`, by definition of
  substitution. So the `laxIntro`/`laxElim` cases of the induction are pure constructor
  applications, with no side conditions to re-establish. **[DERIVABLE]**
* **Erasure and substitution commute** (needed in §2): `(φ[χ/p])^e = (φ^e)[χ^e/p]` where
  `(−)^e` is `◯`-erasure. The `◯` case is
  `(◯φ)[χ/p]^e = (◯(φ[χ/p]))^e = (φ[χ/p])^e = (φ^e)[χ^e/p] = ((◯φ)^e)[χ^e/p]`.
  **[DERIVABLE]**
* **Erasure preserves free variables exactly**: `FV(φ^e) = FV(φ)`. So every eigenvariable
  side condition survives erasure unchanged. **[DERIVABLE]**

In the locally nameless setting (Sub) splits into the standard pair — substitution for a
free atom, and instantiation of a bound variable — related by the `subst_intro` lemma. §6.2
lists the infrastructure.

### 1.5 The sequent calculus `SC2`

The base is the repository's `SCh` (`LaxLogic/PLLSequent.lean:30`): G3-style, single
succedent, height-indexed, left rules keep their principal formula in the context via a
membership hypothesis, so weakening/contraction/exchange are height-preserving admissible
(`SCh.rename`). There is no cut rule; in PLL, cut is *admissible* and that is PROVED
(`SC.cut`, and see `docs/calculus-map.md`). The two lax rules, F&M Figure 2, are

    Γ ⇒ A                    ◯A ∈ Γ    Γ, A ⇒ ◯B
    ─────── (laxR)           ───────────────────── (laxL)
    Γ ⇒ ◯A                   Γ ⇒ ◯B

`SC2` adds four quantifier rules, in the same membership-based style:

    ∀p.φ ∈ Γ     Γ, φ^χ ⇒ C                 for all s ∉ L:  Γ ⇒ φ^s
    ─────────────────────────── (L∀)        ─────────────────────────── (R∀)
    Γ ⇒ C                                    Γ ⇒ ∀p.φ

    ∃p.φ ∈ Γ     for all s ∉ L:  Γ, φ^s ⇒ C      Γ ⇒ φ^χ
    ────────────────────────────────────── (L∃)  ─────────── (R∃)
    Γ ⇒ C                                         Γ ⇒ ∃p.φ

with `χ` an arbitrary formula in (L∀) and (R∃), and `L ⊇ FV(Γ) ∪ FV(C) ∪ FV(∀p.φ)` resp.
`FV(∃p.φ)` in the named reading.

Three observations, all of which matter downstream.

* **(L∀) is not proof-search-shaped.** Its premise ranges over *all* formulas `χ`. There is
  no finite branching, no G4-style terminating refinement, and no decision procedure by
  proof search. This is the proof-theoretic face of the undecidability of §5, and it means
  the repository's entire G4 machinery (`PLLG4H.lean`, `PLLG4Dec.lean`) is inapplicable to
  PLL2. **[DERIVABLE as an observation; the undecidability itself is §5.]**
* **The subformula property fails**, since `φ^χ` is not a subformula of `∀p.φ`. This is
  standard for second-order calculi, and it kills the proof-theoretic conservativity route
  (§2.2).
* **The `◯`-rules are untouched by all of this.** `laxR`/`laxL` neither bind nor create
  variables, and the height measure behaves on them exactly as it does in `SC`. Any cut- or
  normalisation-theoretic method that works for LJ2 will extend to `SC2` with the single
  extra principal case being F&M's `laxR`/`laxL` reduction, which is already PROVED in this
  repository. §4 makes this precise.

**Relation to `G4c`.** None. `G4c` (`PLLG4H.lean`) is the repaired terminating calculus on
which everything computational in this repository runs, and it has no second-order
extension, because (L∀) has no terminating form. PLL2 work belongs to `LaxND2` and `SC2`.
Recording this explicitly because `docs/calculus-map.md` exists precisely to stop this
class of confusion.

### 1.6 The `◯`-fixpoint quantifier is *definable*, not a second sort

The survey (§3.4, "Design consequence") proposes that a serious PLL2 should have two
quantifier sorts, plain `∀p` and `∀°p` restricted to `◯`-fixpoints. **That is not
necessary.** Relativisation does it inside the one-sorted language:

    ∀°p.φ  :=  ∀p.((◯p → p) → φ)          ∃°p.φ  :=  ∃p.((◯p → p) ∧ φ)

with the derived rules

    for all s ∉ L:  Γ, ◯s→s ⊢ φ^s              Γ ⊢ ∀°p.φ      Γ ⊢ ◯χ → χ
    ─────────────────────────────── (∀°I)      ───────────────────────────── (∀°E)
    Γ ⊢ ∀°p.φ                                   Γ ⊢ φ^χ

both **[DERIVABLE]** from (∀I)/(∀E) and (→I)/(→E) alone, and dually for `∃°`. The saving is
large: no second sort in the syntax, no second binder in the substitution machinery, no
second set of cases in every induction, and no separate soundness argument.

**Proposition C survives verbatim.** With the abbreviation above:

    ◯φ  ⊣⊢  ∀°p.((φ→p)→p)          **[DERIVABLE]**

*Proof.* (⊢) Fix `p`; assume `◯p→p` and `φ→p`. Monotonicity of `◯` gives `◯φ→◯p`; compose
with `◯p→p` to get `◯φ→p`; discharge and apply (∀I), legitimate since `p ∉ FV(◯φ)`.
(⊣) Instantiate `p := ◯φ` by (∀°E). The obligation `◯◯φ → ◯φ` is `◯M`, the obligation
`φ → ◯φ` is `◯R`. ∎

**Proposition A survives verbatim.** With `Jφ := ∀p.((φ→p)→p)` (Aczel 2001 *(carried,
CONFIRMED)*):

    ⊢ Jφ → ◯φ          **[DERIVABLE]**

*Proof.* (∀E) at `p := ◯φ` gives `Jφ ⊢ (φ→◯φ)→◯φ`; the antecedent is `◯R`. ∎ The argument
uses only the unit, so `J` is below every modality with a unit: `J` is the strongest.

**Proposition B needs more care than the survey gives it.** The claim is `⊬ ◯φ → Jφ`. The
survey's argument reduces it to `⊬ ¬◯⊥` via `J⊥ ≡ ⊥` and then cites the machine-checked PLL
countermodel in `PLLFrames.lean`. The first half is fine and is now purely syntactic:

* `J⊥ ⊢ ⊥`: instantiate `J⊥ = ∀p.((⊥→p)→p)` at `χ := ⊥` by (∀E), giving `(⊥→⊥)→⊥`, and
  discharge the antecedent by `⊢ ⊥→⊥`. Conversely `⊥ ⊢ J⊥` by ⊥-elimination and (∀I). So
  `J⊥ ⊣⊢ ⊥` **[DERIVABLE]**, purely syntactically, no semantics needed. (The same pair of
  moves gives `J⊥ ⊣⊢ ∀p.p ⊣⊢ ⊥`, which is the form the semantic sanity check of §3.2 uses.)

The second half does **not** follow from the PLL countermodel, because a PLL countermodel
refutes derivability in *PLL*, and `¬◯⊥` being underivable in PLL2 needs either
conservativity of PLL2 over PLL (OPEN, §5) or a PLL2 countermodel. The fix is cheap and is
milestone M4 of §6.3: the F&M two-world model `modelFallible` (`PLLFrames.lean:64`) has
`W = {false, true}`, `F = {true}`, and therefore **exactly two** admissible propositions,
`{true}` and `W`. Second-order forcing on it is a finite computation, so `decide` settles
it. At `w = false`: `◯⊥` holds, `⊥` fails, and `∀p.p` denotes `⋂{{true}, W} = {true}`, so
`∀p.p` fails at `false`. Hence `◯⊥ → J⊥` fails at `false`, and soundness of PLL2 for
second-order constraint models (§3.3) gives

    ⊬_PLL2 ◯⊥ → J⊥,  hence  ⊬_PLL2 ◯φ → Jφ.     **[CONJECTURED until M2 and M4 land;
                                                  the model computation is DERIVABLE]**

**Together, A and B say what PLL2 is for**: `◯` is a genuine new primitive, strictly weaker
than the lax modality that second-order quantification already defines, and the separation
is exactly the fallible-world phenomenon that separates PLL from IPC. C says the gap closes
once the quantifier is restricted to the algebras of the nucleus. That is the headline, and
all three are cheap.

---

## 2. Conservativity over IPC2

### 2.1 The requirement

    **(Cons)**  For ◯-free Γ and ◯-free φ:   PLL2 ⊢ φ from Γ   iff   IPC2 ⊢ φ from Γ.

Right-to-left is inclusion of rules. Left-to-right is the content. Three routes were
considered.

### 2.2 Route (i), proof-theoretic: **dead, and not marginally**

The shape of the argument: cut-eliminate, then observe that in a cut-free derivation every
formula is a subformula of the end-sequent, so if the end-sequent is `◯`-free then no `◯`
occurs anywhere, so `laxR` (whose conclusion is `◯`-shaped) and `laxL` (which needs `◯A ∈ Γ`)
never fire, so the derivation is a G3ip derivation.

**For PLL over IPC this argument works.** `SC` has cut elimination (PROVED,
`PLLSequent.lean`) and its rules are subformula-respecting, so a cut-free `SC` derivation of
a `◯`-free sequent is literally an IPC derivation. The repository does not use this route —
it uses erasure — but the route exists at first order.

**For PLL2 it fails, twice over.**

1. **The subformula property is false in `SC2`.** (L∀) introduces `φ^χ` for an arbitrary
   `χ`, and `χ` may contain `◯`. So a cut-free `SC2` derivation of a `◯`-free end-sequent
   can perfectly well contain `laxR` and `laxL` applications, buried inside an instance.
   Concretely, with `∀p.ψ ∈ Γ` and the instance `χ := ◯θ`, the premise `Γ, ψ^{◯θ} ⇒ C`
   contains `◯`. The engine of the argument is gone. **[DERIVABLE as a refutation of the
   route; this is standard for second-order calculi and is not a PLL2 defect.]**
2. **Cut elimination for `SC2` is itself the expensive open item** (§4). Even if (1) could
   be patched, the premise of the argument would cost months.

The brief's warning about retention rules is a *different* phenomenon and should not be
conflated with this one: `SC`'s `laxL` retains its principal formula, which defeats naive
*termination* arguments (this is why `G4iLL` was needed and why it turned out incomplete,
`PLLG4Gap.lean`); it does not defeat the subformula property. What defeats the subformula
property at second order is impredicative instantiation, which has nothing to do with `◯`.

### 2.3 Route (ii), semantic: **blocked by the cited literature**

The shape: give PLL2 a second-order Kripke semantics (§3), observe that every IPC2 model is
a `◯`-degenerate PLL2 model, conclude by soundness plus completeness of IPC2.

The first two steps are fine and are worth having anyway:

* **Every IPC2 Kripke model is a PLL2 constraint model with `◯` the identity.** Take
  `(W, ≤, V)`, set `Ri := ≤`, `Rm := (=)`, `F := ∅`. Then `Rm` is reflexive, transitive and
  `⊆ Ri`; and `w ⊩ ◯φ` unfolds to `∀v ≥ w. v ⊩ φ`, which by persistence is `w ⊩ φ`. So
  `⟦◯φ⟧ = ⟦φ⟧`. Admissible propositions (§3.2) are the up-sets containing `F = ∅`, i.e. all
  up-sets, matching IPC2's full second-order semantics exactly. **[DERIVABLE]**
* Hence PLL2 ⊢ φ with φ `◯`-free implies φ is valid in every full second-order Kripke model
  of IPC2, given soundness (§3.3).

The step that fails is the last one. To conclude `IPC2 ⊢ φ` we need IPC2 to be **complete**
for that semantics, and it is not: the Kripke-semantic second-order intuitionistic logic
`Hπ+` (quantifiers over all up-sets, class of all partial orders) is recursively isomorphic
to full second-order classical logic (Kremer 1997, §8.2), and the second-order IPC of the
class of all *principal* frames is not recursively axiomatisable (Skvortsov 1997, §8.2),
whereas IPC2 is r.e. The gap is precisely the (a)/(b) distinction of the survey's §1.5.

**The diagnosis is sharper than "semantics does not work", and worth stating carefully,
because the same route succeeds one level down.** What the route actually needs is a
completeness theorem *for the target logic*. So:

| Statement | Target | Target complete? | Semantic route |
|---|---|---|---|
| PLL conservative over IPL | IPL | **yes**, ordinary Kripke completeness | **works** |
| IPC2 conservative over IPC | IPC | **yes** | **works** |
| **PLL2 conservative over IPC2** | **IPC2** | **no** (Kremer, Skvortsov) | **blocked** |

The middle row is worth recording because it means **conservativity of IPC2 over IPC does not
need Pitts 1992 at all**: IPC2 is sound for principal Kripke semantics, a principal model
restricted to a quantifier-free formula is an ordinary Kripke model, and IPC is complete for
those. The top row is the same argument with `Rm = (=)`, `F = ∅`, and it is a second proof of
the repository's `conservativity_IPL` (`PLLNDCore.lean:211`) that the repository does not
use. **[DERIVABLE. The IPC2-over-IPC reconstruction is my own; I found no published
attribution for it, so it should not be cited to anyone.]** The bottom row is blocked because
its target is itself second-order.

**The route is repairable in principle, and not worth repairing.** Passing to **Henkin
semantics** (§3.4) restores completeness in principle, for both IPC2 and PLL2, and that is
what Becker–Das–Marin–Padhiar 2026 do for the neighbouring logic. But then the argument
requires: a Henkin-completeness theorem for IPC2, a Henkin-soundness theorem for PLL2, a
canonical-model construction, and the observation that the `◯`-degenerate models are closed
in the relevant sense. That is three theorems and a construction, where §2.4 is one induction
with four new cases, all of them identity cases. **Take §2.4.** The Henkin machinery is worth
building for §4.2 route (d), not for conservativity.

(Kremer 2018 *(carried, CONFIRMED)* does give a topological completeness theorem for
second-order H; whether that particular axiom system coincides with IPC2 as presented here,
and whether the nucleus can be carried through the topological argument, is **OPEN**.)

### 2.4 Route (iii), the `◯`-erasure: **recommended, and it lifts verbatim**

The repository already proves conservativity of PLL over IPL this way, and the proof is
short (`PLLNDCore.lean:193`, `conservativity_prop`; `:211`, `conservativity_IPL`). The
translation is

    (fvar s)^e = fvar s        (φ ∧ ψ)^e = φ^e ∧ ψ^e        (◯φ)^e = φ^e
    ⊥^e = ⊥                    (φ ∨ ψ)^e = φ^e ∨ ψ^e
    (bvar n)^e = bvar n        (φ → ψ)^e = φ^e → ψ^e        (∀p.φ)^e = ∀p.(φ^e)
                                                             (∃p.φ)^e = ∃p.(φ^e)

**Theorem (Cons-e) [CONJECTURED, but with a complete proof sketch; this is milestone M3].**
If `Γ ⊢_PLL2 φ` then `Γ^e ⊢_IPC2 φ^e`.

*Proof.* Induction on the derivation. All IPC cases are constructor applications, exactly as
in `conservativity_prop`. The two lax cases are the existing ones:

* `laxIntro`: the conclusion `◯φ` erases to `φ^e`, which is the induction hypothesis. The
  case is the identity.
* `laxElim`: from `Γ^e ⊢ φ^e` and `φ^e :: Γ^e ⊢ ψ^e` conclude `Γ^e ⊢ ψ^e` by
  `impElim (impIntro ih₂) ih₁` — the erased rule is a cut, discharged by →I/→E. This is
  `PLLNDCore.lean:207` character for character.

The four new cases:

* `(∀E)`: from `Γ^e ⊢ ∀p.(φ^e)` conclude `Γ^e ⊢ (φ^e)^{χ^e}` by IPC2's (∀E) at the instance
  `χ^e`, which is a legitimate IPC2 formula. The goal is `(φ^χ)^e`, and
  `(φ^χ)^e = (φ^e)^{χ^e}` by §1.4. **Note that this is where impredicative instantiation is
  handled, and it is handled by erasing the instance** — the `◯`s inside `χ` simply vanish.
  This is exactly the step that Route (i) could not survive.
* `(∃I)`: dual, same commutation lemma.
* `(∀I)`: the eigenvariable condition is `s ∉ L` with `L ⊇ FV(Γ)`; erasure preserves free
  variables exactly (§1.4), so `FV(Γ^e) = FV(Γ)` and the same `L` works.
* `(∃E)`: same, with `FV(ψ^e) = FV(ψ)`. ∎

**Corollary (Cons).** If `Γ` and `φ` are `◯`-free then `Γ^e = Γ` and `φ^e = φ`, so
`Γ ⊢_PLL2 φ` implies `Γ ⊢_IPC2 φ`. **[CONJECTURED, immediate from (Cons-e)]**

**What makes this route work, stated as a single fact.** `(−)^e` is a translation, not a
proof-theoretic analysis: it never inspects the *shape* of a derivation, only its last rule.
So it is immune to the failure of the subformula property, immune to the absence of cut
elimination, and immune to the non-termination of (L∀). The only obligations it creates are
the two commutation lemmas of §1.4, and both are true because `◯` binds nothing.

**Lean statement.** In the style of the existing file:

```lean
/-- **Conservativity of PLL2 over IPC2, Prop form.** -/
theorem conservativity2_prop {Γ : List PLL2Formula} {φ : PLL2Formula}
    (p : LaxND2 Γ φ) : IPC2ND (Γ.map erase2) (erase2 φ)

/-- **Conservativity, classic form.** -/
theorem conservativity2_IPC2 {Γ : List PLL2Formula} {φ : PLL2Formula}
    (hφ : isIPC2 φ) (hΓ : ∀ ψ ∈ Γ, isIPC2 ψ) (p : LaxND2 Γ φ) : IPC2ND Γ φ
```

with the two supporting lemmas

```lean
theorem erase2_subst (φ χ : PLL2Formula) (s : String) :
    erase2 (φ.subst s χ) = (erase2 φ).subst s (erase2 χ)

theorem freeAtoms_erase2 (φ : PLL2Formula) : (erase2 φ).freeAtoms = φ.freeAtoms
```

### 2.5 What (Cons) does and does not give

* It gives undecidability of PLL2 for free (§5).
* It gives consistency of PLL2 from consistency of IPC2, and it gives the `◯`-free fragment
  exactly.
* It does **not** give conservativity of PLL2 over **PLL**. That is the Pitts-projection
  conjecture, it is a different theorem, it needs uniform interpolation for PLL, and UI for
  PLL is OPEN in this project. §5.3.
* It does **not** give the disjunction property or the existence property for PLL2. Those
  need cut elimination or a normalisation argument (§4), and they are the only real payoff
  that cut elimination would buy here.

---

## 3. Models

### 3.1 The base: F&M constraint models

`LaxLogic/PLLKripke.lean:28`. A constraint model is `(W, Ri, Rm, F, V)` with `Ri` and `Rm`
preorders, `Rm ⊆ Ri`, `F ⊆ W` an `Ri`-upward-closed set of *fallible* worlds, `V` an
`Ri`-persistent valuation that is *full on `F`* (fallible worlds satisfy every atom).
Forcing (`PLLKripke.lean:52`):

    w ⊩ ⊥        iff  w ∈ F
    w ⊩ φ → ψ    iff  ∀v. Ri w v → (v ⊩ φ → v ⊩ ψ)
    w ⊩ ◯φ       iff  ∀v. Ri w v → ∃u. Rm v u ∧ u ⊩ φ

Soundness (`PLLKripke.lean:97`) and completeness (`PLLCompleteness.lean:614`) for PLL are
both PROVED here, as is `consequence_iff_derivable` (`:634`).

### 3.2 Admissible propositions, and why the two conditions are forced

**Definition.** An *admissible proposition* of a constraint model is `X ⊆ W` that is
`Ri`-upward closed and satisfies `F ⊆ X`.

Both conditions are forced by the two structural lemmas that the repository already proves
for PLL, and the forcing is worth spelling out because it is a genuine design constraint:

* **Upward closure** is needed for `force_hered` (`PLLKripke.lean:61`) to survive the atom
  case under an environment: if `p` may denote a non-up-set, persistence of forcing fails at
  `p` and every implication clause breaks.
* **`F ⊆ X`** is needed for `force_of_fallible` (`PLLKripke.lean:75`), the lemma that
  fallible worlds force everything, whose atom case is exactly `full_F`. Under an
  environment the atom case becomes "`w ∈ F` implies `w ∈ env p`", i.e. `F ⊆ env p`. Without
  it, `⊥`-elimination is unsound. **[DERIVABLE]**

Note the payoff: with these two conditions, `∀p.p` denotes `⋂{X admissible} = F = ⟦⊥⟧`, so
the second-order definition of falsum agrees with PLL's fallible-world falsum
**[DERIVABLE]**, which is the sanity check the survey identified. Dropping `F ⊆ X` would
break both `⊥`-elimination and that agreement, so the design has no slack here.

### 3.3 Second-order constraint models

An **environment** is a map `η` from atoms to admissible propositions. Forcing becomes
`C, η, w ⊩ φ`, with the atom clause `w ∈ η s`, the old clauses unchanged, and

    C, η, w ⊩ ∀p.φ   iff  for every admissible X,  C, η[p ↦ X], w ⊩ φ^p
    C, η, w ⊩ ∃p.φ   iff  for some admissible X,   C, η[p ↦ X], w ⊩ φ^p

This is the **full** reading. Everything in this subsection is parametric in the quantifier
range: replacing "every admissible `X`" by "every `X ∈ 𝒜`" for a designated family `𝒜` closed
under the operations of the language gives the **Henkin** reading, and the soundness proof
below is unchanged provided `𝒜` is closed. §3.4 says why both are wanted. Mechanise the
definition with the range as a parameter from the start; retrofitting it later is a
whole-file rewrite.

**The three lemmas soundness needs**, all straightforward extensions of PROVED PLL lemmas:

1. `force_hered` under an environment: persistence. The `∀`/`∃` cases are immediate since
   the environment does not mention worlds.
2. `force_of_fallible` under an environment: fallible worlds force everything. The `∀` case
   uses `F ⊆ X` for every admissible `X` (§3.2).
3. **The substitution lemma**: `C, η, w ⊩ φ^χ` iff `C, η[p ↦ ⟦χ⟧_η], w ⊩ φ^p`, where
   `⟦χ⟧_η := {w | C, η, w ⊩ χ}`. This is well-formed exactly because `⟦χ⟧_η` is admissible,
   which is (1) plus (2). This is the only genuinely new lemma, and it is the standard
   second-order semantic substitution lemma.

**Theorem (Sound2) [CONJECTURED; milestone M2].** If `Γ ⊢_PLL2 φ` then for every constraint
model `C`, environment `η` and world `w`, if `C, η, w ⊩ ψ` for all `ψ ∈ Γ` then
`C, η, w ⊩ φ`.

*Proof sketch.* The PLL cases are `PLLKripke.lean:97` verbatim. (∀E) and (∃I) are the
substitution lemma; (∀I) and (∃E) are the eigenvariable manipulation, which in the cofinite
formulation reduces to "pick a fresh atom", the standard locally nameless pattern. ∎

### 3.4 Algebraic form, and the expected incompleteness

**The algebra.** For a constraint model `C`, the admissible propositions ordered by
inclusion form a **complete Heyting algebra** (bottom `F`, top `W`, arbitrary meets and
joins computed as intersection and up-closure of union, all of which preserve "contains
`F`"), and the map

    j(X) := {w | ∀v. Ri w v → ∃u. Rm v u ∧ u ∈ X}

is a **nucleus** on it: inflationary by reflexivity of `Rm`; idempotent by transitivity of
`Rm`; and finite-meet-preserving, the non-trivial direction `jX ∩ jY ⊆ j(X∩Y)` being exactly
the argument that validates `◯S`, using `Rm ⊆ Ri`, transitivity of `Rm` and persistence.
**[DERIVABLE — and note it is the semantic content of `somehowS`, already PROVED sound.]**

So: **full second-order constraint semantics = quantification over all elements of a
complete nuclear Heyting algebra**, and the two proposals in the brief (Kripke-with-all-
up-sets versus Pitts-style algebraic) are the same object seen twice. The algebraic reading
is the one to state in a paper; the Kripke reading is the one to mechanise, because `decide`
works on it.

**Incompleteness, stated and not hidden.**

> **[CONJECTURED]** PLL2 is sound but **not complete** for the class of all second-order
> constraint models with the full range of admissible propositions.

Reason: PLL2 is r.e.; the analogous statement for IPC2 is a theorem (Kremer 1997: `Hπ+` is
recursively isomorphic to full second-order classical logic; Skvortsov 1997:
non-axiomatisability over principal frames — §8.2); and by §2.3 the `◯`-degenerate constraint
models (`Rm = (=)`, `F = ∅`) are exactly the IPC2 Kripke models, so the second-order
constraint validities include the second-order Kripke validities of IPC. A full proof needs
the transport of Kremer's recursive-isomorphism argument through the `◯`-degenerate
embedding, which looks routine but is not free, and it is a *negative* result, so it should
be scheduled last (§6.3, M9).

**Do not expect Fritz 2024 to do this by citation.** Its setting is **classical** modal logic
on relational frames with quantifiers over **arbitrary sets** of worlds — not intuitionistic,
not up-sets. Its axiomatisable/non-axiomatisable classification (axiomatisable: KE and normal
extensions, KD4E, S5, certain extensions of K4.3; non-axiomatisable: K, T, K4, S4, S4.2, B
and weaker) does not cover PLL's intuitionistic bimodal fallible constraint frames, and the
"finite diversity" machinery would have to be redone in the intuitionistic setting. **It
supplies methods, not a citation.** [§8.2, CONFIRMED bibliographically; scope warning
verified.]

This incompleteness is **normal**. It is the reason the survey's §1.5 (a)/(b) distinction
exists, and a PLL2 paper should open by making it, not by apologising for it.

**And there is a standard repair, which the nearest neighbouring paper takes.** Restrict the
quantifier range to a **designated family** `𝒜` of admissible propositions, closed under the
operations of the language (finite meets, joins, Heyting implication, `j`, and the
quantifier-formed propositions themselves) — that is, **Henkin semantics** rather than full
semantics. Becker–Das–Marin–Padhiar 2026, working on second-order intuitionistic tense
logic, do precisely this and say why, verbatim on their p. 1: *"Completeness for standard
(or full) semantics, where properties vary over the full powerset, fails, necessitating the
more general Henkin semantics."* [CONFIRMED at source.] Under Henkin semantics a completeness
theorem for PLL2 is available in principle, by a canonical-model construction in which `𝒜`
is the family of definable propositions — which is, structurally, the survey's "definable
range" and the Pitts reading (a).

**Design consequence: PLL2 wants both semantics, and they do different jobs.**

| Semantics | Quantifier range | Job |
|---|---|---|
| **Full** | all admissible propositions | Soundness (M2), and `decide`-checkable countermodels on finite models (M4, M8). Completeness expected FALSE. |
| **Henkin** | a designated closed family `𝒜` | Completeness, and hence the cut-admissibility route (d) of §4.2. |

Note that the two coincide on the finite models used for countermodels, provided `𝒜` is
taken to be all admissible propositions there — so **the countermodel programme of §3.5 is
valid under both readings** and nothing in M4 or M8 depends on the choice. **[DERIVABLE]**

### 3.5 Countermodels are decidable on finite models

**Observation [DERIVABLE].** On a finite constraint model there are finitely many admissible
propositions (a subset of `2^W`), so second-order forcing is a finite computation and is
**decidable**. The repository's `ConstraintModel.decForce` (`PLLFrames.lean:30`) extends by
two cases, quantifying over `Finset`s of worlds subject to two decidable conditions.

This is the largest single mechanisation win in the plan. Everything in `PLLFrames.lean` —
`decide`-checked underivability, the whole style of `not_provable_not_somehow_false`
(`:88`) — carries over to PLL2 unchanged. The immediate targets:

* `◯⊥ → J⊥` fails on `modelFallible` (2 worlds, 2 admissible propositions). §1.6, M4.
* `◯∃p.φ → ∃p.◯φ` and `∀p.◯φ → ◯∀p.φ`: countermodels wanted. `modelOrSplit`
  (`PLLFrames.lean:116`, 3 worlds, `F = ∅`, so 5 up-sets) is the natural first candidate,
  since it already refutes `◯(A∨B) → ◯A ∨ ◯B`, and `◯∃p.φ → ∃p.◯φ` is the same
  "witness depends on the successor" phenomenon with `∃p` in place of `∨`. Instantiating
  `φ := p` gives `◯∃p.p → ∃p.◯p`, and `∃p.p ≡ ⊤`, so that instance is trivial; the search
  wants `φ` with a real dependence, e.g. `φ := p ∧ (p → A ∨ B)`. **[OPEN — this is a search
  task for the finite-model machinery, not a proof task.]**

---

## 4. Cut elimination for `SC2`

### 4.1 Where the repository's method dies, exactly

`SC.cut` (`PLLSequent.lean`) is the standard lexicographic induction on **(cut formula, sum
of heights)**, with heights carried explicitly by `SCh : Nat → List PLLFormula → PLLFormula
→ Prop` so that a `Prop`-valued calculus can support the induction. The one reduction beyond
IPC is the `laxR`/`laxL` principal case, F&M Figure 2.

**That measure fails at the ∀-reduction, and not repairably.** The principal case is

    Γ ⇒ φ^s  (all s ∉ L)          ∀p.φ ∈ Γ',  Γ', φ^χ ⇒ C
    ─────────────────── (R∀)      ───────────────────────── (L∀)
    Γ ⇒ ∀p.φ                       Γ' ⇒ C

and the reduction replaces the cut on `∀p.φ` by a cut on `φ^χ`. Since `χ` is arbitrary and
may itself contain `∀p.φ`, the degree of `φ^χ` is not bounded by the degree of `∀p.φ`. The
induction has nothing to descend on. This is **the** characteristic difficulty of second-
order cut elimination and it is why Takeuti's conjecture was a conjecture.

### 4.2 What the literature supplies: four routes, and none of them is free

*(§8.3 carries the verified bibliographic data.)*

**(a) Semantic cut elimination — the Takahashi–Prawitz method.** Show that a
cut-free-underivable sequent has a countermodel, hence by soundness is underivable with cut.
Non-constructive: it gives the *existence* of a cut-free proof, not a reduction procedure.
This was historically the first route to Takeuti's conjecture, at second order by Tait 1966
(whose title says "nonconstructive") and Prawitz 1967, extended to simple type theory by
Takahashi 1967 and Prawitz 1968. Attractive for mechanisation because it reduces to
soundness plus a completeness-style construction, and `PLLCompleteness.lean` is already a
Zorn-based canonical-model construction of exactly that shape.

**(b) Girard's reducibility candidates.** Constructive-in-method but impredicative in the
metatheory, and it gives strong normalisation of the proof terms rather than merely cut
elimination. Girard 1971, and the 1972 thèse d'État. This is the route that matches what
this repository already has (§4.3).

**(c) Buchholz's Ω-rule.** A syntactic, ordinal-free route. **Caveat, verified and
important**: as analysed by Terui (arXiv:1804.11066), the Ω-rule route covers the
**parameter-free** fragments of second-order intuitionistic logic, not full LJ2 with
unrestricted comprehension. It does not settle the system in §1.5. Large investment, no
scaffolding here, and the wrong scope.

**(d) The route to prefer: labelled sequents + completeness by proof search, giving
cut-*admissibility* — and the template is exactly one logic away.**

> **J. Becker, A. Das, S. Marin, P. Padhiar, "The proof theory and semantics of second-order
> (intuitionistic) tense logic", arXiv:2602.06253, February 2026.** [CONFIRMED; abstract and
> pp. 1, 2, 5, 6 of the PDF read at source.]

Their systems are a Hilbert axiomatisation `IKt2` and a labelled sequent calculus `ℓIKt2`
for second-order intuitionistic *tense* logic (constructive modal base CK, conservatively
extending Fischer Servi/Simpson's `IK` and Ewald's `IKt`). Comprehension is **full and
impredicative** — their Remark 2.3 notes one may even take the instance `C := ∀XA` — and
binding is by named variables with a freshness side condition on the generalisation rule,
not de Bruijn. Their **Main Theorem 4.2** is a Hauptsatz, and it is obtained *not* by a
syntactic cut-reduction but as a by-product of completeness of the labelled calculus proved
by **proof search**: the abstract says completeness is established "via a proof search
argument, yielding at the same time a cut-admissibility result".

**The price, and it is the crux of §3.4.** Their p. 1, verbatim: *"Completeness for standard
(or full) semantics, where properties vary over the full powerset, fails, necessitating the
more general Henkin semantics."* So route (d) buys cut-admissibility by giving up full
second-order semantics for **Henkin semantics** — quantifiers ranging over a designated
family of propositions closed under the operations of the language. That is the standard and
correct move, it is Henkin's, and it is exactly the completeness/incompleteness trade the
survey's §1.5 (a)/(b) distinction is about.

Two further points of contact worth recording. Their driving equivalence is
`◇A ⟺ ∀X(□(A → ■X) → X)`: a modality *recovered* from the negative fragment by a restricted
Russell–Prawitz formula, which is structurally Proposition C of §1.6 with the restriction
carried by the tense modality instead of by the `◯`-fixpoint condition. And they cite Tait,
Prawitz, Takahashi and Girard's 1972 thesis as the resolution of Takeuti's conjecture, so
their positioning of routes (a)/(b) matches this document's.

**This is the nearest methodological template for PLL2 and it should be read before any
cut-elimination work starts.** It is also, per the survey's §2.4, the nearest competitor for
the niche.

### 4.3 The precise place Girard's method becomes indispensable

The repository has the monadic half of the argument already, and it is worth naming exactly
what is missing.

`LaxLogic/PLLReducibility.lean` defines reducibility `Red φ t` **by recursion on the
formula**: Kripke function spaces at `⊃`, elimination clauses at `∧`, value clauses at `∨`
and `◯`, with SN conjoined into every clause so CR1 is free, and CR2/CR3 proved by induction
on the formula. `LaxLogic/PLLTopTop.lean` upgrades the `◯`-clause to Lindley–Stark
⊤⊤-lifting (biorthogonality) to get strong normalisation of the *full* interleaved reduction
including `let`-assoc.

**Recursion on the formula is exactly what breaks at `∀p.φ`.** `Red (∀p.φ)` would have to be
defined in terms of `Red (φ^χ)` for arbitrary `χ`, and `φ^χ` is not structurally smaller.
Girard's fix is not a patch but a change of the definition's shape:

    Red_η (∀p.φ) t   :=   for every reducibility candidate 𝒞,  Red_{η[p ↦ 𝒞]} (φ^p) t

where `η` assigns a *candidate* (a set of terms satisfying CR1–CR3) to each free
propositional variable, and the recursion is now on the *structure of `φ`* with the
candidate assignment carrying the impredicativity. The fundamental theorem quantifies over
all candidate assignments.

**Two consequences worth recording.**

* **The `◯`-clause is orthogonal to the second-order machinery.** `◯` binds nothing and adds
  no candidate; the ⊤⊤-lifted clause of `PLLTopTop.lean` becomes
  `Red_η (◯φ) t := ∀ K reducible for Red_η φ, K[t] is SN`, with `η` passed through
  unchanged. So the plan is: take Girard's candidate assignment, take Lindley–Stark's
  ⊤⊤-lifted `◯`-clause, and compose. Neither modifies the other. **[CONJECTURED, but the
  independence is structural: the two constructions touch disjoint clauses.]**
* **The irony the brief points at is real and is worth stating in a paper.**
  `docs/lax-interpolation-candidates-strategy.md` proposes "interpolation candidates" by
  explicit analogy with Girard's reducibility candidates, as a strategy of last resort for
  uniform interpolation, on the grounds that "the propositional quantifier `∀p φ` ranges
  over propositions, including possibly φ itself". For PLL2 that sentence stops being an
  analogy: the quantifier is literally there, and the *actual* Girard method is required.
  The methodological bet the repository placed on candidate-shaped strengthenings for UI is
  the same bet, one level down.

### 4.4 Recommendation

**Defer cut elimination.** Ranked by payoff per unit of effort:

1. Conservativity by erasure (§2.4) gives consistency and the `◯`-free fragment, with none
   of the cost. Do that first.
2. The only things cut elimination buys that erasure does not are the **disjunction
   property** and the **existence property** for `∃p`. Both are desirable, neither is on the
   critical path for anything else in this plan.
3. If and when they are wanted, take **route (d)**: a labelled sequent calculus for PLL2
   plus Henkin semantics plus completeness by proof search, following Becker–Das–Marin–
   Padhiar 2026. It yields cut-admissibility as a corollary, it does not require an
   impredicative normalisation argument, and PLL's `◯` is a *relational* modality in exactly
   the sense a labelled calculus is designed for — the `∀∃` clause of `PLLKripke.lean:58`
   translates to labelled rules directly. The cost is Henkin semantics rather than full, and
   a canonical-model/proof-search argument to mechanise.
4. Route (b), Girard candidates composed with Lindley–Stark ⊤⊤-lifting (§4.3), is the right
   choice **only if the Curry–Howard reading is the goal** — strong normalisation of PLL2
   proof terms, i.e. System F plus an abstract strong monad. That is a genuinely new
   normalisation theorem and a genuinely large mechanisation, and it should not be started
   before M1–M5 of §6.3 are done.
5. Route (a) is the cheapest *paper* route but gives no reduction procedure and no proof
   terms.

**A verified negative that bears on scheduling**: there appears to be **no purely syntactic,
constructive cut-elimination proof for full LJ2/LK2** in the literature. The routes are
non-constructive (a), impredicative (b), or restricted to parameter-free fragments (c). This
is reported as the finding of a search, not as a proved non-existence result — but it means
a syntactic cut-elimination mechanisation for `SC2` would be new mathematics, not a
formalisation exercise, and it should be priced accordingly. Pfenning's *Structural Cut
Elimination: I. Intuitionistic and Classical Logic* (*Information and Computation* 157,
2000), the standard reference for the nested-structural-induction technique this repository
uses in `SC.cut`, is **first-order only**: its formula grammar has `∀x.A`/`∃x.A` over
first-order terms and no propositional quantification. [CONFIRMED, p. 86 read at source.]

---

## 5. Un/decidability

### 5.1 PLL2 is undecidable, and (Cons) is the whole proof

**Theorem [CONJECTURED, contingent only on (Cons) of §2.4 and on the undecidability of
IPC2].** PLL2 is undecidable.

*Proof.* By (Cons), for `◯`-free `φ`, `PLL2 ⊢ φ` iff `IPC2 ⊢ φ`. `◯`-freeness is decidable.
So a decision procedure for PLL2 decides IPC2. ∎

This is worth emphasising because it means **no Löb-style translation is needed**. The
survey's §4 item 6 proposes "undecidability of PLL2 by transport of Löb/Sobolev"; that
transport is unnecessary once conservativity is in hand, and conservativity is the cheaper
theorem. Schedule accordingly.

**The attribution matters and the obvious one is wrong.** Cite **Löb 1976 and Sobolev 1977**
for "IPC2 is undecidable". **Do not cite Gabbay 1974 alone**: what Gabbay proves is
undecidability of **IPC2 + CD**, IPC2 plus the constant-domains (Grzegorczyk) scheme
`∀p(φ ∨ ψ(p)) → (φ ∨ ∀p ψ(p))` with `p` not free in `φ`; his argument was later corrected by
Sobolev, and his claim that the result descends to IPC2 without CD rested on a finite
axiomatisation of CD over IPC2 that is not known. Sobolev's corrected and strengthened
statement — every logic between `IPC2⁻` and `IPC2 + CD` is undecidable, where `IPC2⁻`
restricts (∀E) and (∃I) to atomic instances — *does* deliver IPC2 itself. Sørensen–Urzyczyn
2010 record the two-proof structure: one semantical, due to Gabbay and Sobolev, and one via
Löb's translation, with their own paper supplying a purely syntactic replacement. Details and
statuses in §8.2.

### 5.2 What is decidable

* **PLL itself.** PROVED here: `decidablePLL` (`LaxLogic/PLLG4Dec.lean:675`), via the
  repaired terminating calculus `G4c`, F&M Theorem 2.8. `docs/calculus-map.md` records that
  this is a `G4c` result. On complexity, U. Egly, "Embedding lax logic into intuitionistic
  logic", CADE-18, LNCS 2392, Springer, 2002, pp. 78–93, DOI 10.1007/3-540-45620-1_6, gives a
  polynomial-time embedding and, per the publisher abstract, **PSPACE-completeness of PLL
  provability**. [Bibliographic data CONFIRMED via Crossref, including pages; the
  PSPACE-completeness claim SEMI-VERIFIED, from two independent retrievals of the Springer
  abstract, the publisher page itself being behind an auth redirect. Confirm from a library
  copy before print. Hardness presumably rides on Statman 1979 for IPC — UNVERIFIED.]
* **Second-order forcing on any fixed finite constraint model.** §3.5. This is what makes
  countermodels mechanisable.
* **The `◯`-free fragment of PLL2 is IPC2**, which is undecidable — so no help there.

### 5.3 The Pitts-interpretation image, and the conjecture to record

Suppose the repository's uniform-interpolation campaign completes, i.e. suppose the four
obligations E1/A1/E2/A2 of `LaxLogic/LJF.lean` are discharged unconditionally (they are
currently PROVED for E1/A1 and proved *modulo* the saturated-context hypotheses `SatE2`,
`SatA2` for E2/A2). Then there is a total computable map on formulas

    (−)° : PLL2 → PLL,   (∀p.φ)° ↦ ∀p(φ°),  (∃p.φ)° ↦ ∃p(φ°),  identity elsewhere,

where `∀p(−)` and `∃p(−)` on the right are the PLL uniform interpolants, and:

> **Conjecture (Pitts-projection for PLL2) [CONJECTURED; conditional on UI for PLL, which is
> OPEN in this project].** `PLL2 ⊢ φ` implies `PLL ⊢ φ°`, and `(−)°` is the identity on
> `◯`-formulas and on quantifier-free formulas. Corollary: **PLL2 is conservative over
> PLL**.

Status of the pieces:

* Existence of uniform interpolants for PLL: **OPEN** in this project (see the correction at
  the head of this file). Iemhoff's proof routes through a calculus machine-checked
  incomplete here.
* That the four characteristic laws suffice to validate (∀I)/(∀E)/(∃I)/(∃E) under `(−)°`:
  Pitts' own argument for IPC, with one new case, `◯`. **OPEN, expected routine** — and note
  that the `◯` case is where §3.5's `∃p(Γ, ◯φ) ≡ ∃p Γ ∧ ◯∃p(Γ, φ)` conjecture of the survey
  lives.
* Faithfulness of `(−)°`: **FALSE, and there is a concrete witness, not merely a counting
  argument.** The counting argument is that `(−)°` is computable and PLL is decidable, so
  `{φ : PLL ⊢ φ°}` is decidable while PLL2 is undecidable by §5.1, so the inclusion is
  strict. The concrete witness is better, and it is already in the literature for the
  first-order case: **Sørensen–Urzyczyn 2010, Remark 3.3** warns that Pitts' result is
  routinely misread, because **Pitts' quantifier is not a definition of `∀`**. Their example
  is that Pitts' `∀p(p ∨ ¬p)` computes to `⊥` — it is the weakest `p`-free antecedent for
  `p ∨ ¬p`, and there is none but `⊥` — whereas `∀p(p ∨ ¬p) ⊬ ⊥` in IPC2, as (∀E) at `⊥`
  shows. So `IPC ⊢ (∀p(p∨¬p) → ⊥)°` while `IPC2 ⊬ ∀p(p∨¬p) → ⊥`. The same formula is
  `◯`-free, so **the same witness refutes faithfulness for PLL2 over PLL**, as soon as
  `(−)°` exists. [Sørensen–Urzyczyn Remark 3.3 read at source, CONFIRMED. The transfer to
  PLL2 is DERIVABLE.] Połacik 1998 *(carried, CONFIRMED)* is the other citation for the same
  moral.

> **The conjecture the brief asks to record.** Pitts-style quantifier elimination for PLL2
> over PLL exists **iff** the uniform-interpolation campaign succeeds: the interpolant engine
> *is* the elimination procedure, and its four obligations E1/A1/E2/A2 are literally
> ∃-intro, ∀-elim, ∃-elim, ∀-intro (the survey's §3.7 table). Under it, `{φ : PLL ⊢ φ°}` is
> decidable, and `LJF.lean` — the focused calculus and interpolant engine — is that decision
> procedure. **[CONJECTURED]**

**But state what that set is, precisely.** By the previous bullet it is a **decidable, sound
over-approximation** of PLL2: it contains every PLL2 theorem and strictly more. It is not
"the decidable fragment of PLL2", and calling it that would repeat exactly the misreading
Sørensen–Urzyczyn warn against. The honest formulation of "the decidable core" is the set of
PLL2 formulas `φ` for which PLL2 itself proves `φ ⊣⊢ φ°` — on those, `(−)°` really is
quantifier elimination and PLL's decision procedure really does decide them. Characterising
that set is **OPEN**, and it is a good question: the `◯`-free, `∀p(p∨¬p)`-free shape of the
counterexample suggests the boundary is about quantifiers over *undecided* propositions, not
about `◯` at all.

**One discrepancy to resolve before relying on this**, carried from the survey's §3.7 and
still live: the repository's A2 concludes `∃p(Γ), Δ ⊢ ∀p(Γ→G)`, handing the proof an extra
hypothesis `∃p(Γ)` that plain (∀I) does not need (`LJF.lean:1139`). That is a weakening of
(∀I), so it is sound, but the Pitts-projection argument needs the *unweakened* rule to
validate (∀I). Either A2 is a deliberate strengthening of the induction hypothesis that the
recursion needs, or the constructed `∀`-interpolant is weaker than `∀p(Γ→G)`. Cheap to
settle, and it should be settled before any PLL2 paper claims the projection.

---

## 6. Mechanisation plan

### 6.1 Binder representation: **locally nameless**, and why

The repository represents atoms as `String` (`PLLFormula.prop (constantName : String)`), and
the whole computational apparatus depends on `PLLFormula` having a derived `DecidableEq` and
on `decide` working over finite models. Three options were weighed:

| Representation | Verdict |
|---|---|
| **Pure de Bruijn** (all variables are indices) | **Reject.** Every existing PLL formula would have to be re-encoded; named models (`vSplit`, `vChain` in `PLLFrames.lean`, keyed on `"A"`, `"B"`) would need rewriting; and free-variable side conditions become level arithmetic, which is exactly the kind of index bookkeeping the repository's "no green slime" discipline (`PLLNDCore.lean` header) was set up to avoid. |
| **Named with explicit α-equivalence** | **Reject for mechanisation** — though note it is what Becker–Das–Marin–Padhiar 2026 use on paper, with a freshness side condition on generalisation, and it is the right choice for a paper presentation. In Lean, α-equivalence stops being syntactic equality, `DecidableEq` stops being derivable in the useful sense, `decide` stops working, and every rule acquires a renaming obligation. |
| **Locally nameless**: `fvar (s : String)` for free, `bvar (n : Nat)` for bound | **Recommend.** |

Locally nameless wins on four counts specific to this repository:

1. **The embedding of PLL into PLL2 is the identity on atoms**: `PLLFormula.prop s ↦ fvar s`.
   Every existing formula, model and countermodel transports unchanged.
2. **α-equivalence is syntactic equality**, so `deriving DecidableEq` still works and so does
   `decide` — which is what §3.5's countermodel programme depends on entirely.
3. **Eigenvariable conditions become `Finset String` freshness**, and the repository already
   has that machinery: `listAtoms` (`PLLG4Dec.lean:611`), `atoms` (`PLLCtxCompleteness.lean:289`,
   `PLLG4Space.lean:39`).
4. **Cofinite quantification** in (∀I) and (∃E) — "for all `s ∉ L`" rather than "for some
   fresh `s`" — makes the renaming lemma unnecessary, which is the single largest saving in
   locally nameless developments (Aydemir et al., POPL 2008; Charguéraud, JAR 2012; §8.3).

The one cost is the standard locally nameless infrastructure: `open`/`close`, `subst`,
local closure, and roughly fifteen commutation lemmas. It is boilerplate, it is well
documented, and it is a one-time cost.

**And the cost may be largely avoidable.** The Lean **CSLib** project (`leanprover/cslib`)
already contains a locally nameless development of exactly this shape, verified at source
(GitHub tree read 2026-08-09):

    Cslib/Languages/LambdaCalculus/LocallyNameless/Context.lean
    Cslib/Languages/LambdaCalculus/LocallyNameless/Fsub/{Basic,Opening,WellFormed,
                                                          Typing,Subtype,Reduction,Safety}.lean
    Cslib/Languages/LambdaCalculus/LocallyNameless/Stlc/{Basic,Safety,StrongNorm}.lean
    Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/…

`Fsub` is System F with subtyping — a *second-order* binder, opened and instantiated by the
same `Opening.lean` machinery PLL2 needs, with typing contexts built on mathlib's `List`
infrastructure and with generic proof automation for the substitution and freshness lemmas.
CSLib also has a `Cslib/Logics/` tree (classical linear logic with cut elimination, modal
logic, propositional natural deduction), so it is a plausible eventual home for a PLL2
development as well as a source of infrastructure. **Read `Opening.lean` and `Context.lean`
before writing a line of `PLL2/Formula.lean`.** *(CONFIRMED: arXiv:2602.15078 full text and
the repository tree both read at source; see §8.3.)*

### 6.2 File plan

All under a new `LaxLogic/PLL2/` directory, so that nothing in the existing development is
touched and the PLL2 work can be built and audited independently.

| File | Contents |
|---|---|
| `LaxLogic/PLL2/Formula.lean` | The locally nameless syntax; `freeAtoms : PLL2Formula → Finset String`; `openRec`/`open_`/`close`; `subst`; `LC` (local closure); the standard infrastructure lemmas (`subst_fresh`, `subst_open`, `subst_intro`, `open_lc`, …). The embedding `ofPLL : PLLFormula → PLL2Formula` and the proof that it is injective and lands in the `LC`, quantifier-free fragment. |
| `LaxLogic/PLL2/ND.lean` | `LaxND2` with cofinite (∀I)/(∃E); `rename` (weakening/exchange/contraction in one traversal, as `PLLNDCore.lean:108`); **(Sub)** of §1.4; the derived monotonicity of `◯`. |
| `LaxLogic/PLL2/Judgmental.lean` | `PD2`, the two-judgment version; `circInvert`; soundness and completeness against `LaxND2`, following `PLLJudgmental.lean` line for line. *(Optional; only if the polarised route is to be extended.)* |
| `LaxLogic/PLL2/Erasure.lean` | `erase2`; `erase2_subst`; `freeAtoms_erase2`; `IPC2ND`; `conservativity2_prop`; `conservativity2_IPC2`. **This is the payload file.** |
| `LaxLogic/PLL2/Sequent.lean` | `SC2h`/`SC2` with (L∀)/(R∀)/(L∃)/(R∃); `rename`; soundness of `SC2` into `LaxND2` and completeness back. **No cut.** |
| `LaxLogic/PLL2/Kripke.lean` | `Admissible`; environments; `force2`; `force2_hered`; `force2_of_fallible`; the semantic substitution lemma; `soundness2`. **Parameterise the quantifier range from the start** (§3.3): `force2` takes the family `𝒜` as an argument, with the full semantics as the instance `𝒜 = all admissible`. Retrofitting Henkin semantics later is a whole-file rewrite, and route (d) of §4.2 needs it. |
| `LaxLogic/PLL2/Frames.lean` | `decForce2` on finite models; the `◯⊥ → J⊥` countermodel by `decide`; the search for `◯∃`/`∀◯` countermodels. |
| `LaxLogic/PLL2/RussellPrawitz.lean` | `J`, `∀°`, `∃°` as abbreviations; Propositions A, B, C; the Russell–Prawitz definability of `⊥,∧,∨` from `→,∀`. |

### 6.3 Milestones

Effort figures are working-day estimates at this repository's demonstrated pace. **Calibration
note**: my own estimates in this development have historically run about four times
pessimistic (recorded 2026-08-05), and the figures below already have that correction
applied; treat them as optimistic-realistic rather than safe.

| # | Milestone | Statement | Status target | Effort |
|---|---|---|---|---|
| **M1** | Syntax and substitution | `LaxND2` well-defined; `(Sub)` proved; `ofPLL` injective | PROVED | 2–3 d |
| **M2** | Soundness for second-order constraint models | `soundness2` | PROVED | 1–2 d |
| **M3** | **Conservativity over IPC2** | `conservativity2_IPC2` | PROVED | 1–2 d |
| **M4** | Propositions A, B, C | `J φ ⊢ ◯φ`; `⊬ ◯⊥ → J⊥` by `decide`; `◯φ ⊣⊢ ∀°p((φ→p)→p)` | PROVED | 1–2 d |
| **M5** | The sequent calculus | `SC2 ≡ LaxND2` (no cut) | PROVED | 2–3 d |
| **M6** | Undecidability of PLL2 | corollary of M3, modulo a cited undecidability of IPC2 | stated, cited | 0.5 d |
| **M7** | Russell–Prawitz definability | `⊥, ∧, ∨` definable from `→, ∀` in PLL2 | PROVED | 1 d |
| **M8** | `◯∃`/`∀◯` converse countermodels | finite second-order countermodels by `decide` | PROVED or OPEN | 1–3 d, search |
| **M9** | Incompleteness for full semantics | transport of Kremer/Skvortsov, or citation of Fritz 2024 | stated; PROVED unlikely | research |
| **M10a** | Cut admissibility, route (d) | labelled `SC2` + Henkin semantics + completeness by proof search, after Becker et al. 2026 | deferred | weeks–months |
| **M10b** | Strong normalisation, route (b) | Girard candidates ∘ Lindley–Stark ⊤⊤; System F + a strong monad | deferred | months |

M1–M4 are the publishable core and total under ten days. They deliver: the first
formulation of second-order propositional lax logic, a machine-checked conservativity
theorem over IPC2, and the machine-checked separation `J ⊢ ◯`, `◯ ⊬ J`, `◯ = ∀°`-Russell–
Prawitz, which is the result that says why `◯` is worth adding to System F.

### 6.4 Milestone theorem statements

```lean
-- M1
theorem subst_admissible {Γ : List PLL2Formula} {φ χ : PLL2Formula} {s : String}
    (p : LaxND2 Γ φ) : LaxND2 (Γ.map (·.subst s χ)) (φ.subst s χ)

-- M2
theorem soundness2 {Γ : List PLL2Formula} {φ : PLL2Formula}
    (p : LaxND2 Γ φ) (C : ConstraintModel) (η : Env C) (w : C.W)
    (h : ∀ ψ ∈ Γ, C.force2 η w ψ) : C.force2 η w φ

-- M3  (the payload)
theorem conservativity2_IPC2 {Γ : List PLL2Formula} {φ : PLL2Formula}
    (hφ : isIPC2 φ) (hΓ : ∀ ψ ∈ Γ, isIPC2 ψ) (p : LaxND2 Γ φ) : IPC2ND Γ φ

-- M4, Proposition A
theorem J_imp_circ (φ : PLL2Formula) :
    Nonempty (LaxND2 [] ((J φ).ifThen φ.somehow))

-- M4, Proposition B  (via decidable second-order forcing on a two-world model)
theorem not_provable_circ_imp_J :
    ¬ Nonempty (LaxND2 [] ((PLL2Formula.falsePLL.somehow).ifThen (J .falsePLL)))

-- M4, Proposition C  (stated as the two derivations, since PLLFormula has no `iff`)
theorem circ_to_nuclearRP (φ : PLL2Formula) :
    Nonempty (LaxND2 [φ.somehow] (allNuc ((φ.ifThen (.bvar 0)).ifThen (.bvar 0))))
theorem nuclearRP_to_circ (φ : PLL2Formula) :
    Nonempty (LaxND2 [allNuc ((φ.ifThen (.bvar 0)).ifThen (.bvar 0))] φ.somehow)
```

`J φ := .all ((φ.ifThen (.bvar 0)).ifThen (.bvar 0))` and
`allNuc φ := .all (((.bvar 0).somehow.ifThen (.bvar 0)).ifThen φ)` are the two abbreviations
of §1.6, in locally nameless form. Note that `PLLFormula` has no biconditional constructor
(`PLLFormula.lean:3` lists `prop, falsePLL, and, or, ifThen, somehow`, with only `notPLL` and
`truePLL` as abbreviations), so two-sided statements are stated as a pair of sequents, in
keeping with the existing files.

### 6.5 What must not be attempted

* **Do not extend `G4c` or `LJF` to PLL2.** (L∀) has no terminating form; the G4 discipline
  and the focused calculus are first-order objects. The PLL2 work belongs to `LaxND2`,
  `SC2` and the second-order models.
* **Do not attempt cut elimination before M1–M5.** §4.4.
* **Do not add a second quantifier sort.** §1.6.
* **Do not claim conservativity over PLL.** That is §5.3 and it depends on UI, which is OPEN.

---

## 7. The single biggest design risk

**The locally nameless infrastructure swallowing the schedule.** M3, the theorem that makes
the whole system coherent, is a fifteen-line induction — but it rests on `erase2_subst` and
`freeAtoms_erase2`, and those rest on the full complement of open/close/subst commutation
lemmas, which in typical locally nameless developments run to several hundred lines of
mutually-dependent boilerplate whose statements have to be exactly right before anything
above them will typecheck. The mathematical content of M1–M4 is small and every proof
sketch in this document is short; the risk is entirely that the binder layer, which has no
mathematical content at all, costs more than the mathematics it supports.

Three mitigations, in order:

1. **Build `Formula.lean` and `Erasure.lean` first and in that order, before any calculus.**
   If the infrastructure is going to be expensive, that must be discovered on day one, not
   after `LaxND2` and `SC2` are written against it.
2. **Restrict the first pass to `∀` only.** `∃` doubles the infrastructure and buys nothing
   for M3, M4 or M7 (Propositions A, B, C and Russell–Prawitz definability are all `∀`-only,
   and Zdanowski's work *(carried, CONFIRMED)* shows the `∃`-only fragment behaves
   differently anyway, so `∃` deserves its own pass).
3. **Reuse CSLib's layer.** `Cslib/Languages/LambdaCalculus/LocallyNameless/` already carries
   opening, local closure, contexts and the freshness automation, and `Fsub/` exercises all
   of it on a genuinely second-order binder (§6.1). Read `Opening.lean` and `Context.lean`
   first; if the layer is generic enough to depend on, this risk largely evaporates, and if
   it is not, the file is still the specification to copy. Either way, budget the boilerplate
   as its own milestone rather than folding it into M1. There is no such layer in mathlib.

A second, smaller risk worth naming: **the correction at the head of this document must
propagate**. Any PLL2 write-up that repeats the survey's claim that Iemhoff 2024 proved UI
for PLL will be making a claim this project has machine-checked evidence against, and §5.3's
conjecture would be miscategorised as a near-theorem rather than as conditional on an open
problem.

---

## 8. Bibliography

Items marked *(carried)* are inherited from `docs/second-order-pll-survey.md` §5 at the
status recorded there and were not re-verified for this document. Items in §8.2 and §8.3
were verified for this document; their statuses are recorded individually.

### 8.1 Carried, load-bearing here

| Item | Status |
|---|---|
| A. M. Pitts, "On an interpretation of second order quantification in first order intuitionistic propositional logic", *JSL* 57(1):33–52, 1992. DOI 10.2307/2275175 | CONFIRMED *(carried)* |
| P. Aczel, "The Russell–Prawitz modality", *MSCS* 11(4):541–554, 2001 | CONFIRMED *(carried)* |
| M. Fairtlough, M. Mendler, "Propositional Lax Logic", *Information and Computation* 137(1):1–33, 1997 | CONFIRMED *(carried)* |
| F. Pfenning, R. Davies, "A judgmental reconstruction of modal logic", *MSCS* 11(4):511–540, 2001 | CONFIRMED *(carried)* |
| R. Iemhoff, "Proof theory for lax logic", in *Dick de Jongh on Intuitionistic and Provability Logics*, OCL 28, Springer, 2024, pp. 203–229. DOI 10.1007/978-3-031-47921-2_8; arXiv:2209.08976 | CONFIRMED *(carried)*. **The UI theorem is contested here**: see the correction at the head of this file. |
| P. Kremer, "Completeness of second-order propositional S4 and H in topological semantics", *RSL* 11(3):507–518, 2018. DOI 10.1017/S1755020318000229 | CONFIRMED *(carried)* |
| K. Zdanowski, "On second order intuitionistic propositional logic without a universal quantifier", *JSL* 74(1):157–167, 2009. DOI 10.2178/jsl/1231082306 | CONFIRMED *(carried)* |
| P. Fritz, *Propositional Quantifiers*, Cambridge Elements, CUP, 2024. DOI 10.1017/9781009177740 | CONFIRMED *(carried)* |

*(Kremer 1997, Skvortsov 1997, Połacik 1998, Fritz 2024 on axiomatisability, Pitts 1992 and
Egly 2002 were re-verified for this document and appear in §8.2 with their scope warnings.)*
| R. E. Møgelberg, A. Simpson, "Relational parametricity for computational effects", LICS 2007; arXiv:0906.5488 | CONFIRMED as arXiv item *(carried)*; LMCS data UNVERIFIED |
| N. Valliappan, "Lax modal lambda calculi", CSL 2026; arXiv:2512.10779 | CONFIRMED as arXiv item *(carried)* |
| S. Lindley, I. Stark, "Reducibility and ⊤⊤-lifting for computation types", TLCA 2005 | SEMI-VERIFIED *(carried from `PLLTopTop.lean`)* |
| G. Bezhanishvili, N. Bezhanishvili, L. Carai, D. Gabelaia, S. Ghilardi, M. Jibladze, "Diego's theorem for nuclear implicative semilattices", *Indagationes Mathematicae* 32(2):498–535, 2021 | CONFIRMED *(carried)*. **∨-free fragment only.** |

### 8.2 Undecidability and non-axiomatisability

*Verified for this document, 2026-08-09. **Bibliographic** data below is CONFIRMED from
Crossref or from fetched reference lists; **content** claims are marked separately, and where
they come from secondary sources that is said. None of Gabbay 1974, Sobolev 1977, Löb 1976,
Kremer 1997, Skvortsov 1997, Pitts 1992 or Egly 2002 could be read in full — all paywalled.*

**Keep the two logics apart.** The calculus **IPC2** (r.e., full impredicative comprehension)
is *undecidable but axiomatisable by construction*. The **Kripke-semantic** logic (quantifiers
over all up-sets) is *not axiomatisable at all*, and worse than Π¹₁. Every entry below belongs
to one or the other.

**The calculus IPC2**

| Item | Status |
|---|---|
| D. M. Gabbay, "On 2nd order intuitionistic propositional calculus with full comprehension", *Archiv für mathematische Logik und Grundlagenforschung* 16(3–4):177–186, 1974. DOI 10.1007/BF02015377 | Bibliographic CONFIRMED (Crossref). **Content SEMI-VERIFIED and narrower than usually reported: it proves undecidability of IPC2 + CD (constant domains), and the argument was later corrected by Sobolev.** Do not cite it alone for "IPC2 is undecidable" |
| S. K. Sobolev, "The intuitionistic propositional calculus with quantifiers", *Matematicheskie Zametki* 22:69–76, 1977; English translation *Mathematical Notes of the Academy of Sciences of the USSR* 22(1):528–532, 1977. DOI 10.1007/BF01147694 | Bibliographic CONFIRMED (Crossref; **note the translation pages 528–532**, which the survey did not have). Content SEMI-VERIFIED: corrects Gabbay and strengthens to *every logic between `IPC2⁻` and `IPC2 + CD` is undecidable*, which does yield IPC2 |
| M. H. Löb, "Embedding first order predicate logic in fragments of intuitionistic logic", *JSL* 41(4):705–718, 1976. DOI 10.2307/2272390 | CONFIRMED. **Note the DOI: 10.2307/2272390, not 2270331.** Translates the universal-implicational fragment of first-order classical logic with equality into IPC2 |
| M. H. Sørensen, P. Urzyczyn, "A syntactic embedding of predicate logic into second-order propositional logic", *NDJFL* 51(4):457–473, 2010. DOI 10.1215/00294527-2010-029 | CONFIRMED; PDF fetched. Records the two-proof structure — one semantical, "due to Gabbay and Sobolev", one via Löb — and supplies a purely syntactic replacement. **Remark 3.3** is the "Pitts' quantifier is not a definition of ∀" warning used in §5.3 |
| M. H. Sørensen, P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, Studies in Logic and the Foundations of Mathematics 149, Elsevier, 2006 | SEMI-VERIFIED *(carried)* |

**The Kripke-semantic logic**

| Item | Status |
|---|---|
| P. Kremer, "On the complexity of propositional quantification in intuitionistic logic", *JSL* 62(2):529–544, 1997. DOI 10.2307/2275545 | CONFIRMED. The system **is** called **`Hπ+`**; quantifiers range over **all up-sets** (not all subsets) on **the class of all partial orders**; it is **recursively isomorphic to full second-order classical logic**, so not in the analytical hierarchy at all |
| D. Skvortsov, "Non-axiomatizable second order intuitionistic propositional logic", *APAL* 86(1):33–46, 1997. DOI 10.1016/S0168-0072(96)00034-6 | Bibliographic CONFIRMED (Crossref gives **issue 1**; dblp says issue 2 — prefer Crossref). Content SEMI-VERIFIED from consistent secondary summaries: the second-order IPC of all **principal** frames is not recursively axiomatisable, likewise for any class of principal frames containing every finite frame. **Verify the "containing every finite frame" clause at source before it carries weight** |
| P. Fritz, "Axiomatizability of propositionally quantified modal logics on relational frames", *JSL* 89(2):758–793, June 2024. DOI 10.1017/jsl.2022.79 | CONFIRMED. **Scope warning (§3.4): classical modal logic, relational frames, quantifiers over arbitrary sets of worlds. Not intuitionistic, not up-sets. It does not cover PLL's bimodal fallible constraint frames** |
| D. Skvortsov, "On the predicate logics of finite Kripke frames", *Studia Logica* 54(1):79–88, 1995. DOI 10.1007/BF01058533 | CONFIRMED. **First-order predicate logic — do not conflate with the second-order propositional results** |
| D. Skvortsov, "The superintuitionistic predicate logic of finite Kripke frames is not recursively axiomatizable", *JSL* 70(2):451–459, 2005. DOI 10.2178/jsl/1120224722 | CONFIRMED. Also **first-order predicate**; same warning |

**Conservativity, Pitts, and complexity**

| Item | Status |
|---|---|
| A. M. Pitts, "On an interpretation of second order quantification in first order intuitionistic propositional logic", *JSL* 57(1):33–52, 1992. DOI 10.2307/2275175 | CONFIRMED. The abstract gives an interpretation of IPC2 in IPC restricting to the identity on first-order propositions, i.e. conservativity in all but the word. **Whether Pitts uses the word "conservative": UNVERIFIED** |
| U. Egly, "Embedding lax logic into intuitionistic logic", in A. Voronkov (ed.), *Automated Deduction — CADE-18*, LNCS 2392, Springer, 2002, pp. 78–93. DOI 10.1007/3-540-45620-1_6 | Bibliographic CONFIRMED via Crossref **including pages 78–93**, which the survey lacked. The PSPACE-completeness claim: SEMI-VERIFIED from the publisher abstract |
| T. Połacik, "Pitts' quantifiers are not topological quantification", *NDJFL* 39(4):531–544, 1998 | CONFIRMED *(carried)* |

**Two attribution traps, both verified**

* **Conservativity of IPC2 over IPC does not require Pitts 1992.** It follows from soundness
  of IPC2 for principal Kripke semantics plus completeness of *IPC* for ordinary Kripke
  semantics (§2.3). **No published attribution for this argument was found**, so it is
  recorded here as a reconstruction and must not be cited to anyone.
* **Goldblatt's "Cover semantics for quantified lax logic" (*JLC* 21(6):1035–1063, 2011) is
  first-order**, quantifying over individuals, and the paper says so. At least one search
  engine summarises it as covering quantification over *propositions*. That is wrong, it is
  the kind of error that propagates, and it was checked against the paper's own text.

**The negative result stands.** Searches for propositional quantifiers over a nucleus, lax,
geometric or Lawvere–Tierney modality returned nothing beyond the two near-misses the survey
already records: Aczel 2001 (a lax modality *definable inside* IPC2 as `∀p((φ→p)→p)`) and
Goldblatt 2011 (first-order). Nobody has added a *primitive* nucleus to IPC2. The absence is
a search result, not a proof of non-existence, but it is now corroborated by two independent
searches with disjoint query sets.

### 8.3 Second-order cut elimination, normalisation, and binder representation

*Verified for this document, 2026-08-09.*

**Second-order cut elimination and Takeuti's conjecture**

| Item | Status |
|---|---|
| G. Takeuti, "On a generalized logic calculus", *Japanese Journal of Mathematics* 23:39–96, 1953; **Errata**, ibid. 24:149–156, 1954 | CONFIRMED (via the *JSL* review record, which cites paper and errata together) |
| W. W. Tait, "A nonconstructive proof of Gentzen's Hauptsatz for second order predicate logic", *Bulletin of the AMS* 72(6):980–983, 1966 | CONFIRMED (Project Euclid, `bams/1183528497`). **Semantic/non-constructive**; the Schütte semi-valuation lineage is SEMI-VERIFIED |
| D. Prawitz, "Completeness and Hauptsatz for second order logic", *Theoria* 33:246–258, 1967 | SEMI-VERIFIED (*JSL* review listing). **This is the second-order one**, and the "Prawitz" half of the Takahashi–Prawitz method |
| M. Takahashi, "A proof of cut-elimination theorem in simple type-theory", *J. Math. Soc. Japan* 19(4):399–410, 1967. DOI 10.2969/jmsj/01940399 | CONFIRMED (Project Euclid). Note the title hyphenates **"type-theory"** |
| D. Prawitz, "Hauptsatz for higher order logic", *JSL* 33(3):452–457, 1968. DOI 10.2307/2270331 | CONFIRMED (Cambridge Core). Its abstract says Tait's method appeared limited to second order, and that it generalises Prawitz's own 1967 second-order proof |
| J.-Y. Girard, "Une extension de l'interprétation de Gödel à l'analyse, et son application à l'élimination des coupures dans l'analyse et la théorie des types", in J. E. Fenstad (ed.), *Proceedings of the Second Scandinavian Logic Symposium*, Studies in Logic and the Foundations of Mathematics 63, North-Holland, 1971, pp. 63–92 | CONFIRMED (title/venue/editor/publisher/year/pages from a published bibliography; series volume 63 confirmed independently) |
| J.-Y. Girard, *Interprétation fonctionnelle et élimination des coupures de l'arithmétique d'ordre supérieur*, thèse de doctorat d'État, Université Paris VII, defended **26 June 1972** | CONFIRMED — the scanned title page was read at source. No page count confirmed |
| J.-Y. Girard, Y. Lafont, P. Taylor, *Proofs and Types*, Cambridge Tracts in Theoretical Computer Science 7, CUP, 1989. ISBN 0-521-37181-3 | CONFIRMED for series/volume/publisher/year/ISBN. **Page count disputed**: the *JSL* review gives xi + 176 pp., retail listings 192 pp. Do not cite a page count casually |
| G. Takeuti, *Proof Theory*, Studies in Logic and the Foundations of Mathematics 81; 1st ed. North-Holland/American Elsevier, 1975, vii + 372 pp.; 2nd ed. North-Holland, 1987, x + 490 pp. | CONFIRMED (*JSL* review record, both editions) |
| W. Buchholz, "The Ω_{μ+1}-rule", in Buchholz–Feferman–Pohlers–Sieg, *Iterated Inductive Definitions and Subsystems of Analysis*, Lecture Notes in Mathematics 897, Springer, 1981, pp. 188–233 | CONFIRMED bibliographically; page range SEMI-VERIFIED |
| K. Terui, "MacNeille completion and Buchholz' Omega rule for parameter-free second order logics", arXiv:1804.11066, 2018/2019; CSL 2018, LIPIcs 119, art. 37 | CONFIRMED (arXiv abstract). **Scope caveat**: the Ω-rule route as analysed there covers the **parameter-free** fragments, not full LJ2 |
| T. Arai, "Cut-eliminability in second order logic calculi", arXiv:1701.00929, 2017 | CONFIRMED (arXiv abstract). Unifies Takahashi–Prawitz and Maehara via complete-Boolean-algebra-valued semantics |
| F. Pfenning, "Structural Cut Elimination: I. Intuitionistic and Classical Logic", *Information and Computation* 157:84–141, 2000. DOI 10.1006/inco.1999.2832 | CONFIRMED (first printed page read). **First-order only** — the formula grammar on p. 86 has `∀x.A`/`∃x.A` over first-order terms and no propositional quantification |
| M. Parigot, "Strong normalization for second order classical natural deduction", *JSL* 62(4):1461–1479, 1997 | SEMI-VERIFIED (secondary citation) |

**Negative finding, reported as a search result and not as a theorem**: no purely syntactic,
constructive cut-elimination proof for **full** LJ2/LK2 was located. The routes available are
non-constructive (Tait/Takahashi/Prawitz/Arai), impredicative (Girard), or restricted to
parameter-free fragments (Buchholz/Terui). §4.4 prices the consequence.

**Correction to a claim that should not be made**: I could not confirm that
D. Prawitz, "Ideas and results in proof theory", in *Proceedings of the Second Scandinavian
Logic Symposium*, Studies in Logic 63, North-Holland, 1971, **pp. 235–307** [CONFIRMED
bibliographically via the *JSL* review; a secondary bibliography gives 237–309, prefer
235–307] contains a second-order normalisation proof or conjecture. Authoritative secondary
sources cite it only for first-order strong normalisation. **Do not assert the second-order
claim.** What *is* attributed to Prawitz, and is relevant to milestone M7, is the
**definability** of `∨, ∧, ⊥` from `→` and the second-order quantifier. [SEMI-VERIFIED, from
the *Stanford Encyclopedia of Philosophy*.]

**Second-order modal / intuitionistic-modal proof theory**

| Item | Status |
|---|---|
| J. Becker, A. Das, S. Marin, P. Padhiar, "The proof theory and semantics of second-order (intuitionistic) tense logic", arXiv:2602.06253, submitted 5 February 2026 | CONFIRMED — abstract and pp. 1, 2, 5, 6 read at source |

Verified content, since this is the closest work to PLL2 and §4.4 recommends following it:
Hilbert systems `IKt2`/`Kt2`, labelled sequent calculi `ℓIKt2`/`ℓKt2`, and a multi-succedent
Maehara-style variant for the proof-search argument; comprehension **full and impredicative**
(their Remark 2.3 allows the instance `C := ∀XA`); binding by **named variables with a
freshness side condition** on generalisation, not de Bruijn; **Henkin** rather than full
semantics, with their p. 1 stating that completeness for full semantics fails; **Main Theorem
4.2** is a Hauptsatz obtained as a by-product of completeness by proof search, i.e.
**cut-admissibility, not a syntactic cut-elimination procedure**; `IKt2` conservatively
extends Fischer Servi/Simpson's `IK` and Ewald's `IKt`; driving equivalence
`◇A ⟺ ∀X(□(A → ■X) → X)`. **Nothing else was found on cut elimination for second-order modal
or intuitionistic-modal logics with propositional quantifiers.**

**Mechanisation precedent, and binder representation**

| Item | Status |
|---|---|
| T. Altenkirch, "A formalization of the strong normalization proof for System F in LEGO", TLCA 1993, LNCS 664, pp. 13–28. DOI 10.1007/BFb0037095 | CONFIRMED for pages/DOI via dblp; LNCS volume SEMI-VERIFIED. Girard's candidates, Curry-style System F |
| B. E. Aydemir, A. Bohannon, M. Fairbairn, J. N. Foster, B. C. Pierce, P. Sewell, D. Vytiniotis, G. Washburn, S. Weirich, S. Zdancewic, "Mechanized metatheory for the masses: the PoplMark challenge", TPHOLs 2005, LNCS 3603, pp. 50–65. DOI 10.1007/11541868_4 | CONFIRMED for authors/pages/DOI via dblp; LNCS volume SEMI-VERIFIED. Basis is System F<: |
| A. Abel, G. Allais, A. Hameer, B. Pientka, A. Momigliano, S. Schäfer, K. Stark, "POPLMark reloaded: mechanizing proofs by logical relations", *JFP* 29:e19, 2019. DOI 10.1017/S0956796819000170 | CONFIRMED via dblp. Benchmark is **simply typed**, not System F |
| B. E. Aydemir, A. Charguéraud, B. C. Pierce, R. Pollack, S. Weirich, "Engineering formal metatheory", POPL 2008, pp. 3–15. DOI 10.1145/1328438.1328443 | CONFIRMED via dblp. **Locally nameless + cofinite quantification** — the source for §1.2 and §6.1 |
| A. Charguéraud, "The locally nameless representation", *Journal of Automated Reasoning* 49(3):363–408, 2012. DOI 10.1007/s10817-011-9225-2 | CONFIRMED via dblp |
| C. Henson, F. Montesi et al., "Computer science as infrastructure: the spine of the Lean Computer Science Library (CSLib)", arXiv:2602.15078, v1 16 February 2026, v2 22 July 2026 | CONFIRMED — full text read. Verbatim: *"CSLib contains a growing formalisation of the metatheory of λ-calculi, currently including the simply typed λ-calculus and System F with subtyping"*, and *"our use of locally nameless variable binding in conjunction with proof automation and metaprogramming is novel"*. Repository `github.com/leanprover/cslib`, tree verified at source 2026-08-09: `Cslib/Languages/LambdaCalculus/LocallyNameless/{Context.lean, Fsub/*, Stlc/*, Untyped/*}`, plus `Cslib/Logics/{LinearLogic/CLL/CutElimination.lean, Modal/*, Propositional/NaturalDeduction/*}` |
| A. Ramos, A. Oliveira, R. de Queiroz, T. de Veras, "A modular Lean 4 framework for confluence and strong normalization of lambda calculi with products and sums", arXiv:2512.09280, 10 December 2025 | CONFIRMED (arXiv abstract). de Bruijn; untyped λ, combinatory logic, term rewriting, STLC, STLC with products and sums. **System F is not in it** |

**No mechanisation of IPC2 — second-order intuitionistic *propositional* logic — or of its
cut elimination was found in any proof assistant.** CSLib's `Fsub` is the metatheory of
System F<: as a *type system* (typing, subtyping, progress, preservation), not provability in
IPC2. So a Lean development of PLL2 would be new on both counts, and the positioning in §0
holds.

**No community verdict exists on binder representations.** The POPLmark challenge issues a
challenge rather than a ruling, and no consensus is recorded. §6.1's recommendation rests on
the four repository-specific reasons given there, plus the availability of CSLib's layer, not
on an appeal to authority.

---

## 9. Cross-references

* `docs/second-order-pll-survey.md` — the literature survey this plan implements, with the
  correction at the head of this file.
* `docs/calculus-map.md` — which proof system a result belongs to. PLL2 adds `LaxND2` and
  `SC2` to that map; `G4c` and `LJF` do **not** extend (§6.5).
* `LaxLogic/PLLNDCore.lean` — `LaxND`, and `conservativity_prop` / `conservativity_IPL`, the
  proof that §2.4 lifts.
* `LaxLogic/PLLJudgmental.lean` — the Pfenning–Davies presentation and `circInvert`.
* `LaxLogic/PLLSequent.lean` — `SC`, `laxR`/`laxL`, and the cut-elimination measure that
  §4.1 says fails at second order.
* `LaxLogic/PLLKripke.lean`, `LaxLogic/PLLFrames.lean` — the constraint models, the
  structural lemmas that force the admissibility conditions of §3.2, `decForce`, and the
  `◯⊥` countermodel that §1.6 upgrades to second order.
* `LaxLogic/PLLReducibility.lean`, `LaxLogic/PLLTopTop.lean` — the reducibility method by
  recursion on the formula, which §4.3 says must become candidate-assignment-indexed.
* `LaxLogic/LJF.lean` — the four obligations E1/A1/E2/A2, i.e. the four quantifier rules, and
  the A2 discrepancy of §5.3.
* `LaxLogic/PLLG4Gap.lean` — the machine-checked incompleteness of `G4iLL`, on which the
  correction at the head of this file rests.
* `docs/lax-interpolation-candidates-strategy.md` — the "interpolation candidates" method,
  which §4.3 identifies as the same bet one level down.

## §7 Addendum (Matthew, 2026-08-09): completion vs the closed fragment

The per-model algebra of admissible propositions is complete; PLL's
Lindenbaum algebra is not. So PLL2's quantifiers act as a completion —
per model, not of the logic. The closed fragment RN(◯,{}) carries
machine-checked families with no bounds in the fragment (the ascending
chainF with no supremum, the descending Gmeet with no infimum, the gap
antichain — see wip/ and PROGRESS). QUESTIONS to develop:

1. In each model, these families acquire sups/infs in the admissible
   algebra. Are those bounds *definable* — closed PLL2-sentences? A
   definable bound is precisely the kind of full-semantics-valid sentence
   the calculus may miss (Kremer territory); a machine-checked instance
   would be a sharp incompleteness witness for PLL2 over full semantics.
2. The completion of RN(◯,{}) inside a nuclear algebra connects to the
   N(RN(◯,{})) / assembly-tower thread: is the (per-model) completion of
   the closed fragment's image related to the assembly of the fragment's
   frame? On finite models everything is decide-checkable.
3. Candidate first experiment: the 8-element ∨-free fragment (Fig. 6) in
   a small model — compute the completion-points the quantifiers add.
