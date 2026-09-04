# Belief in Lax Logic

*SUPERSEDED AS WORKING MASTER (2026-07-19): the paper now lives in
`paper/` (`belief.tex`/`body.tex`/`appendix.tex`), where the merge pass
(selection doc §2, decisions D1–D9) was applied; edits are not
back-ported here. This file remains the revision-2 record.*

*Master draft, revision 2 (2026-07-18) — rewritten in the register of
Fairtlough–Mendler, I&C 137(1), 1997, whose completeness construction
this paper finitises and whose introduction it deliberately echoes.
Every mathematical claim is machine-checked in the Lean 4 + Mathlib
artefact at `github.com/fairflow/lax-logic-in-lean` unless explicitly
marked open; each theorem is anchored to its Lean name, and the axiom
audit of every named result is recorded in
`docs/pll-formalisation-ledger.md`. Line-level walk-throughs of the
three central proofs are in `docs/annotated/`.*

## Abstract

We propose a doxastic reading of Propositional Lax Logic (PLL), the
intuitionistic modal logic of Fairtlough and Mendler whose single
modality ◯ has a flavour both of possibility and of necessity: we read
◯M as "M is believed", by a single idealised believer whose belief is
disciplined by evidence. The reading is defended by a chain of
machine-checked results. On the negative side, over classical logic the
reading is empty: on a Boolean algebra every nucleus is closed, so a
classical belief modality collapses to ◯M ≡ M ∨ a for a fixed
proposition a. Over intuitionistic logic belief is rich, and its
richness is evidential in a precise sense inherited from the constraint
reading.

The paper's technical core is a new realisability semantics for PLL
over the constraint models of the original paper, in which atoms carry
evidence from a partial applicative structure and the clauses for ⊃ and
◯ differ in how much a realiser is told about the future of the
inquiry. Three clause families arise — uniform, strategy, and
presented-strategy — and a sequence of separation theorems shows the
choice determines the logic: rigid evidence validates schemes PLL does
not prove; strategy evidence restores the countermodels but provably
cannot support a completeness theorem, by an obstruction created by the
modality's own strategies; presenting the future at implications yields
completeness. The countermodels are supplied by a finitisation of the
original canonical-model construction in which Zorn's lemma is replaced
by an iterated appeal to PLL's own mechanised decision procedure, and
the resulting models are executable: a verified checker certifies them
by computation, and each world reads as a belief state — what is
believed, and what is promised never to be evidenced.

Every result is formalised in Lean 4; the axiom footprint of each
theorem is tracked, and the greater part of the development, including
the entire decoration argument, is choice-free. We conclude with an
account of the method, in which several of the paper's results were
found by the failure, itself provable, of the theorems we first
attempted.

## 1. Introduction

The object of this paper is a reading of the rather curious modality ◯
characterised by the axiom schemes

    ◯R : M ⊃ ◯M
    ◯M : ◯◯M ⊃ ◯M
    ◯S : (◯M ∧ ◯N) ⊃ ◯(M ∧ N)

with Modus Ponens and the rule "from M ⊃ N infer ◯M ⊃ ◯N". The
introduction of [F&M 1997] motivated ◯ by a list of six perspectives —
Curry's 1948 lectures, nuclei on complete Heyting algebras, Kripke and
J-space semantics, the strong monads of computational type theory, the
proof-theoretic constraint reading, and the timing analysis of
combinational circuits — and settled on the constraint reading: ◯M as
"for some constraint c, formula M holds under c". This paper adds a
seventh reading and pursues it:

(7) ◯M is "**M is believed**". The unit ◯R says "what is true is
believed"; the multiplication ◯M says "what is believed to be believed
is believed"; ◯S says "beliefs combine". The reading is doxastic and
not epistemic: nothing gives ◯M ⊃ M, and indeed ◯false is consistent —
a believer may harbour an absurd belief without thereby believing
everything outright. The modality quarantines inconsistency rather than
exploding it.

Two features distinguish the present pursuit of (7) from a routine
exercise in modal-logic reinterpretation, and they are connected.

The first is that the reading earns its keep by *theorems*, the central
ones new. Classically the reading is degenerate: every nucleus on a
Boolean algebra is closed, so a classical ◯ is determined by the single
proposition ◯false, its "credulity level", and the spectrum of possible
believers is bracketed by the total sceptic (◯M ≡ M) and the total
credulist (◯M ≡ true). Constructively the picture is quite different —
open nuclei, invisible classically, model belief under a hypothesis,
and the closed ◯-fragment of even one free algebra is infinite — and,
by the context-completeness theorem descending from Curry's problem, a
proof of ◯M literally contains the evidence for believing M. Belief
worth the name is *evidential* belief, and evidential belief is
non-degenerate only over intuitionistic logic. Making this argument
precise occupies Sections 3–6, whose main novelty is a realisability
semantics in which the slogan becomes a completeness theorem: PLL is
exactly the logic of belief whose evidence may react to the future of
the inquiry.

The second feature is methodological. Every claim in this paper is
machine-checked, in a Lean 4 formalisation that also contains the whole
of [F&M 1997] — the calculi and their equivalences, cut elimination,
the constraint semantics, soundness, completeness, decidability — and
the axiomatic footprint of every theorem is tracked, most of the new
material being choice-free. We do not regard the formalisation as an
audit performed after the mathematics. Three times in this development
the attempt to prove a plausible statement produced instead a proof of
its negation, and each failure redirected the theory; the most
consequential of these, the obstruction of Section 5, is the reason the
completeness-grade semantics has the shape it has. The checker, in our
experience, is a collaborator with an unerring nose for the case one
has not considered. Section 9 reports the method, including the
division of labour between the human author and the language model that
operated the proof assistant.

The paper is organised as follows. Section 2 fixes the mechanised base
and recalls the constraint semantics. Section 3 proves the classical
collapse and the constructive richness. Section 4 defines evidence and
the three realisability clause families; Section 5 proves the
separation theorems and the obstruction; Section 6 the completeness
theorem, in three steps — decoration, the finitised canonical model,
and their composition. Section 7 runs the theory: executable
countermodels read as belief states, and a proof compiled to its
evidence. Sections 8–10 treat related work, method, and open problems.

## 2. The mechanised base

The formulas of PLL are generated by the grammar

    M ::= A | false | M ∧ M | M ∨ M | M ⊃ M | ◯M

over a countable supply of propositional constants; ¬M abbreviates
M ⊃ false. The artefact presents PLL as a natural deduction system with
membership-based contexts (`LaxND`, `PLLNDCore.lean`), as an
intrinsically-typed term calculus in the sense of the computational
lambda-calculus (`Tm`, `PLLTerms.lean`), as a Hilbert system, and as a
cut-free single-succedent sequent calculus (`SC`, `PLLSequent.lean`);
all four are proved equivalent, cut elimination, the disjunction
property and ◯-reflection are theorems, and the term calculus is
strongly normalising for β together with the monadic associativity law,
by a ⊤⊤-lifting argument that appears to be the first mechanised one
with sums (`PLLTopTop.lean`). Decidability is likewise mechanised, as a
terminating, kernel-honest procedure over a contraction-free calculus —
with the wrinkle, documented in the artefact and communicated
separately to its author, that the published G4-style calculus for PLL
is provably incomplete and a small repair is both necessary and
sufficient. After an axiom-hygiene pass, the entire proof-theoretic
chain audits at `[propext, Quot.sound]`: no choice.

The semantics is that of [F&M 1997], Definitions 3.1–3.2, mechanised
verbatim (`PLLKripke.lean`):

```lean
structure ConstraintModel where
  W : Type
  Ri : W → W → Prop      -- intuitionistic accessibility: a preorder
  Rm : W → W → Prop      -- constraint accessibility: a preorder, Rm ⊆ Ri
  F : Set W              -- fallible worlds; hereditary, valuation full there
  V : String → Set W     -- hereditary valuation
  ...                    -- (eight structural conditions)
```

Forcing is as in intuitionistic logic on the frame (W, Rᵢ, V), with
false holding exactly at the fallible worlds, and the modal clause is
the ∀∃ statement

    w ⊨ ◯N   iff   for all v with w Rᵢ v there exists u with
                   v Rₘ u and u ⊨ N.

The clause endows ◯ with properties both of possibility and of
necessity, as the original paper observed. Under reading (7) it is a
stability statement. Call N **credible** at a world v when a constraint
step from v reaches a world satisfying N:

    N is credible at v   iff   ∃ u. v Rₘ u and u ⊨ N.

Then w ⊨ ◯N says exactly that N *remains credible in all future
worlds*: however inquiry develops, some admissible discharge of the
constraint still verifies N. The
fallible worlds — worlds with inconsistent information, validating
everything — are what keep ◯false satisfiable, and under (7) they are
the semantic form of quarantined absurdity. Soundness for sequents is
`soundness` (`PLLKripke.lean`, audit `[propext]`); the classical
completeness theorem of [F&M 1997, §4] is `completeness`
(`PLLCompleteness.lean`), kept in the artefact deliberately, Zorn and
all, as the foil for Section 6.2.

## 3. Classical belief collapses; constructive belief is rich

We first make precise the claim that reading (7) has no classical
content.

**Theorem 3.1** (`BeliefCollapse.lean`, `BeliefBooleanIso.lean`). *On a
Boolean algebra every nucleus is closed: j x = x ⊔ j ⊥. The nuclei on B
form a lattice order-isomorphic to B itself.*

Under (7): a classical believer is exhausted by one proposition,
a = ◯false, the strongest thing believed for no reason; belief is then
"M, or a" — disjoining one's credulity onto every proposition alike. At
a = false the believer is the total sceptic, believing only what is
true; at a = true, the total credulist. Nothing between these poles
distinguishes one classical believer from another except the choice of
a. There is, classically, no structure of belief; there is only a
measure of laxity.

**Theorem 3.2** (`BeliefOpenClosed.lean`, `PLLLaxInfinite.lean`).
*Intuitionistically, the open nucleus uₐ = (a ⊃ ·) coincides with a
closed nucleus exactly when excluded middle holds at a; and the closed
◯-fragment RN(◯, {}) of the free algebra on no generators is infinite.*

The open nucleus is belief under the hypothesis a — the natural logic
of conditional commitment, "believing M modulo a" — and it is invisible
classically precisely because a ⊃ M and M ∨ ¬a coincide there. That the
closed fragment of even the generator-free algebra is infinite says the
constructive believer has infinitely many pairwise inequivalent modal
degrees where the classical believer had a single parameter.

**Theorem 3.3** (context completeness; `PLLCtxCompleteness.lean`, after
the Curry-problem analysis of TYPES 2000). *PLL ⊢ φ iff for every
standard constraint context C, IPL ⊢ φ^C; and no finite set of
constraint contexts suffices.*

This is the theorem that makes "evidential" more than a slogan: a proof
of ◯M is, uniformly in the constraint, a proof of M under that
constraint — the grounds are contained in the belief. Taken together,
Theorems 3.1–3.3 give the paper's philosophical spine: classically
belief collapses; constructively it is rich; the richness is
evidential; and so a non-degenerate logic of evidential belief is
possible only over intuitionistic logic. Each vertebra is a theorem.

We also record, following Hintikka, the idealisation being adopted
rather than smuggled: the unit says the believer accepts what is true;
the derived rule "from Γ ⊢ M infer ◯Γ ⊢ ◯M" is logical omniscience,
machine-checked as a theorem *about* the system
(`BeliefIdealisation.lean`); introspection is exact, ◯◯M ⊣⊢ ◯M; and
there is no factivity and no D axiom — ⊬ ¬◯false, by one of the three
countermodels of [F&M 1997, Fig. 3], so absurd belief is consistent and
quarantined.

## 4. Evidence

We now equip the constraint models with evidence. The equipment is
deliberately light.

```lean
structure Pca where
  Carrier : Type
  app : Carrier → Carrier → Option Carrier
  pair : Carrier → Carrier → Carrier
  fst snd : Carrier → Carrier
  tag : Bool → Carrier → Carrier
  untag : Carrier → Bool × Carrier
  ...                        -- pairing and tagging laws only

structure Evidence (P : Pca) (C : ConstraintModel) where
  E : String → C.W → Set P.Carrier
  hered_E : ∀ {s w v}, C.Ri w v → E s w ⊆ E s v
  full_E  : ∀ {s w}, w ∈ C.F → ∀ x, x ∈ E s w
```

A partial applicative structure with total pairing and tag decoding —
no combinatory completeness is assumed at this stage — and, for each
atom and world, a set of elements evidencing that atom there. Evidence
is hereditary ("belief increases along the branching order"; heredity
of all the realisability relations below is a theorem) and full at
fallible worlds, mirroring the fullness of the valuation there.

Three realisability relations are defined over this equipment. They
agree at atoms (membership in the evidence set, or fallibility), at
false (fallibility), at ∧ (pairing) and at ∨ (tagging), and differ only
at ⊃ and ◯ — and there only in *how much the realiser is told about the
future*. Uniform realisability ⊩ᵘ tells it nothing:

    x ⊩ᵘ M ⊃ N at w  iff  for all v ≥ w and all b ⊩ᵘ M at v,
                          x·b is defined and ⊩ᵘ N at v;
    x ⊩ᵘ ◯M at w     iff  for all v ≥ w there is u with v Rₘ u
                          and x ⊩ᵘ M at u

— the same element must serve every future and every
constraint-witness. Strategy realisability ⊩ˢ, relative to an injective
coding κ of worlds into the carrier, makes ◯-evidence a function of the
presented future:

```lean
| .somehow φ, x, w =>
    ∀ v, C.Ri w v → v ∈ C.F ∨
      (∃ y, P.app x (κ v) = some y ∧
        ∃ u, C.Rm v u ∧ P.fst y = κ u ∧ realS P Ev κ φ (P.snd y) u)
```

In words: evidence for ◯M is a strategy which, handed the code of
whatever future v has actually arrived, answers with a package naming a
constraint-witness u — naming it, as κ u, rather than merely having
one — together with evidence for M there. The strategy has no
foreknowledge; the future is its input. The witness must be named
because the elimination rule's computational content applies its
continuation at that name; this is the point at which the semantics
remembers that it is a semantics of proofs.

Presented-strategy realisability ⊩ᵖ extends the same courtesy to
implication: the realiser of M ⊃ N receives the pair ⟨κ v, b⟩ of the
presented world and the argument:

```lean
| .ifThen φ ψ, x, w =>
    ∀ v, C.Ri w v → v ∈ C.F ∨
      (∀ b, realP P Ev κ φ b v →
        ∃ y, P.app x (P.pair (κ v) b) = some y ∧ realP P Ev κ ψ y v)
```

One might suspect this of being a convenience. Section 5 shows it is
forced.

## 5. The separations, and the obstruction

The three relations are separated on one three-world model — the split
model: a root r below two incomparable leaves, A true at one leaf and B
at the other — together with small variants. All four separations are
machine-checked; we state them in narrative order.

First, the *bite* (`bite_uniform_split`): at the root of the split
model, ◯(A ∨ B) is truth-forced — every future can still reach an
A-leaf or a B-leaf — but no element ⊩ᵘ-realises it. A uniform realiser
carries one tag, and would have to decide the disjunct before the
branch happens. Truth outruns rigid evidence.

Second, and dually (`uniform_dist_valid`): the identity element
⊩ᵘ-realises the scheme ◯(A ∨ B) ⊃ (◯A ∨ ◯B) at every world of every
model — a scheme PLL demonstrably does not prove
(`not_provable_somehow_or_dist`). So PLL is incomplete for uniform
realisability: rigid evidence validates a strictly stronger logic,
which we call PLLᵘ and whose axiomatisation we leave open.

Third (`strategy_realises_obAB`, `strategy_dist_refuted`): under ⊩ˢ a
case-splitting strategy realises ◯(A ∨ B) at the root — the bite
vanishes — while the distribution scheme acquires a genuine
countermodel. Strategy evidence is the first point in the development
at which evidence is a program in more than name.

Fourth, the ⊃-barrier (`impdist_not_uniform`): (◯A ⊃ ◯B) ⊃ ◯(A ⊃ B) is
not ⊩ᵘ-valid; uniformity fails at implication in its own way.

The natural question is then whether ⊩ˢ is the completeness-grade
relation. It is not, and the reason is a theorem.

**Theorem 5.1** (the obstruction; `realS_fullness_obstruction`, audit
`[propext, Quot.sound]`). *There is a three-world constraint model on
which no evidence assignment whatever is simultaneously atom-adequate
(evidence only where the atom holds) and full for ⊩ˢ (every forced
formula has a realiser) — for every applicative structure able to
implement finite lookup tables against the world-coding.*

```lean
theorem realS_fullness_obstruction (P : Pca) (κ : obsC.W → P.Carrier)
    (htab : ∀ g : obsC.W → P.Carrier, ∃ s, ∀ i, P.app s (κ i) = some (g i)) :
    ¬ ∃ Ev : Evidence P obsC,
      (∀ (a : String) (w : obsC.W), ∀ x ∈ Ev.E a w, w ∈ obsC.V a) ∧
      (∀ (φ : PLLFormula) (w : obsC.W), obsC.force w φ →
        ∃ x, x ⊩ˢ[Ev, κ, w] φ)
```

Note the quantifier structure: the evidence assignment is inside the
negation. This is an obstruction, not a counterexample to one
decoration. Since adequacy together with fullness is exactly the mutual
induction any completeness-by-decoration proof must run — each consumes
the other at the ⊃-clause — completeness of PLL for ⊩ˢ is not provable
this way on these frames.

The model has a root below two incomparable leaves; an atom t holds at
both leaves, p only at the first, q only at the second; the constraint
relation is trivial. The proof is short enough to give whole. Fullness
at the atom t hands over tokens m₁, m₂ at the two leaves. One
application of the table hypothesis then produces a *single* element s
realising ◯t at both leaves simultaneously: presented κ(leaf), it
answers with that leaf's own name and that leaf's token — and nothing
about s betrays which leaf it is serving, for a strategy is a function
of the presented future and carries no world-marks. Now ◯t ⊃ (p ∨ q) is
truth-forced at the root (vacuously there, since ◯t fails at the root;
via the local atom at each leaf), so fullness hands over a realiser x.
The ⊃-clause of ⊩ˢ shows x the argument alone; instantiating it at each
leaf with the same argument s, application being a function, both
instantiations receive the same answer y — whose tag must be false at
the p-leaf, since atom-adequacy has emptied the q-evidence there, and
true at the q-leaf for the symmetric reason. One Boolean cannot be
both. ∎

Two remarks. First, the obstruction is ◯-essential. For a purely
intuitionistic antecedent the argument collapses: world-tagged atom
evidence would let a table-building structure case on the argument
after all, and heredity ensures that forcing a disjunction at a branch
point has already committed to a disjunct. What cannot carry
world-marks is precisely a strategy — the modality's own evidence
discipline creates the obstruction to its own naive completeness.
Second, the repair is thereby dictated rather than chosen: the ⊃-clause
must be told the world, exactly as the ◯-clause already is, and that
single change is the definition of ⊩ᵖ. The separations survive the
repair untouched, being stated for ⊩ᵘ and ⊩ˢ. The moral of the section,
and the slogan of the paper: **what one may assume about how evidence
meets the future determines which logic of belief one obtains.**

## 6. Completeness

In this section we prove completeness of PLL with respect to
⊩ᵖ-realisability. The proof has two independent halves — a decoration
theorem, saying that every suitable countermodel refutes in the
realisability sense, and a countermodel-existence theorem — and we take
them in that order. Both halves are effective in a sense made precise
below; the existence half finitises the canonical construction of
[F&M 1997, §4], replacing its one appeal to Zorn's lemma with an
iterated appeal to the mechanised decision procedure.

### 6.1 Decoration: adequacy and fullness

The frames to be decorated are *finite models as data*: the structure
`FinCM` (`PLLCountermodelEmit.lean`) packages worlds 0,…,n−1, the two
relations as lists of pairs, the fallible set and the valuation as
lists, together with an executable forcing function `forceB` and a
verified reflection lemma (`force_iff`) identifying the computation
with genuine forcing in the induced constraint model. On such a frame,
*token evidence* gives each atom one designated element, exactly where
the atom holds. All the evidence a completeness proof needs, it turns
out, is one token per atom.

**Theorem 6.1** (`realP_adequate_and_full`, audit
`[propext, Quot.sound]`). *Over any checked finite frame with token
evidence, and any applicative structure with two table-forming
capacities against the world-coding: for every formula φ,*

```lean
    (∀ w x, (x ⊩ᵖ[tokenEvidence P M h tok, κ, w] φ) →
       (M.toModel h).force w φ) ∧
    (∃ wit : Fin M.n → P.Carrier, ∀ w,
       (M.toModel h).force w φ →
         (wit w) ⊩ᵖ[tokenEvidence P M h tok, κ, w] φ)
```

*— whatever is realised is forced (adequacy), and whatever is forced is
realised by an explicit per-world witness function (fullness).*

The shape of the fullness clause deserves a remark before the proof:
not "at each world there is a witness" but "there is a function of
worlds". The induction requires the whole function at once, because the
witnesses at ⊃ and ◯ are tables whose entries are the subformula's
witnesses at other worlds.

**Proof.** By a single induction on φ proving the conjunction; each
case may use both halves of the inductive hypotheses, and the cases at
⊃ exhibit the mutual dependency in both directions. Throughout, the
reflection lemma converts freely between forcing and its executable
form, and this is the engine of the theorem's constructivity: every
branch decision in a witness is a computation, not a case split on an
undecided proposition.

At atoms, false, and ∧ there is nothing surprising. At ∨, adequacy
reads the realiser's tag; fullness is the first interesting witness:

```lean
fun w => if M.forceB w.1 φ = true then P.tag false (witφ w)
         else P.tag true (witψ w)
```

— run the executable forcing of the left disjunct at w and tag
accordingly. If the test succeeds the left inductive fullness supplies
the payload; if it fails while the disjunction is forced, the failed
computation refutes the left disjunct outright, so the right one is
forced and its fullness supplies the payload. No excluded middle is
consulted; the decision procedure for forcing is.

At ⊃, adequacy: given a realiser x of φ ⊃ ψ and a future v forcing φ,
feed x the pair ⟨κ v, witφ v⟩ — the antecedent's fullness witness — and
apply ψ's adequacy to the answer. Fullness: apply the pair-table
capacity to ψ's witness function, obtaining a single element s with
s·⟨κ v, b⟩ = witψ v for every v and b. The obligation fires only when b
realises φ at v; then φ is forced at v by φ's adequacy, so ψ is forced
at v since φ ⊃ ψ is forced below, and witψ v realises it by ψ's
fullness. The table ignores its second argument entirely: the presented
world alone determines the right answer — which is precisely the lookup
Theorem 5.1 proves impossible when the world is not presented.

At ◯, adequacy is a direct reading of the strategy's answers. Fullness
applies the plain table capacity to the function which, presented a
future v, *searches the finite frame* — a bounded, decidable search —
for a constraint-successor of v forcing φ, and answers with its name
paired with φ's witness there. When ◯φ is forced the ∀∃ clause
guarantees the search succeeds. ∎

From Theorem 6.1 and soundness one obtains at once the *squeeze*
(`realP_refutes_sequent`): every countermodel validated by the verified
checker is a ⊩ᵖ-refutation of its sequent — hypotheses realised at the
refuting world, conclusion unrealisable. Both table capacities are
discharged, with nothing assumed, by an explicit algebra of finite
lookup tables (`Tbl`, `tblPca`: base codes, formal pairs and tags, two
table formers; application is decidable lookup; the laws hold by
definitional computation), so the squeeze has a closed, hypothesis-free
form (`realP_refutes_sequent_tbl`).

### 6.2 The countermodels, finitely and without Zorn

It remains to produce a checked countermodel for every underivable
sequent. Here the paper rejoins its parent most closely, and the reader
may find it useful to have [F&M 1997, §4] open beside this subsection.

The canonical model there is built from worlds which are *triples*
(Γ, Δ, Θ) of sets of formulas — validated, falsified, and falsified at
every Rₘ-reachable world — the third component being, as the original
explains, a special feature introduced because the falsity of a formula
◯M cannot be recorded by placing M, or any subformula of M, in the
other two components; it must be tracked separately. Under reading (7)
the third component is the record of a *promise*: a formula the
believer has pledged never to evidence, however the constraint is
discharged. Promises are what prevent the fallible world, which
validates everything, from trivialising the ∀∃ clause. A triple is
consistent if for no finite selections N₁,…,Nₙ from Δ and K₁,…,Kₖ from
Θ, jointly nonempty, does

    Γ ⊢ N₁ ∨ ⋯ ∨ Nₙ ∨ ◯(K₁ ∨ ⋯ ∨ Kₖ)

— note the ◯ guarding the promises, the load-bearing subtlety of the
whole construction: refuting a promise-selection means deriving
somehow-one-of-the-promised, which is exactly the shape the elimination
behaviour of ◯ can manipulate. The original then takes *maximal*
consistent triples, by Zorn, and proves a truth lemma.

The present construction (`PLLFinComp.lean`) keeps every one of these
design decisions and changes exactly two things: the triples are finite
(`FTheory`: three finite sets, and the classical consistency notion is
reused verbatim through the evident coercion, so the entire lemma
library about the consistency formula transfers without re-proof); and
maximality is replaced by *totality over the subformula closure* of the
sequent under refutation. The replacement is licensed by two
observations, each pleasant.

The first observation (`cons_iff_check`) is that consistency of a
finite triple is *one derivability question*: since the consistency
formula is monotone in both selections, the universally quantified
condition collapses to its worst case, the full selections. That single
question is decided by the mechanised decision procedure. Consistency
of finite triples is decidable — and so the Lindenbaum construction can
be a computation:

```lean
noncomputable def extendStep (T : FTheory) (φ : PLLFormula) : FTheory :=
  if (T.insVal φ).Cons then T.insVal φ else T.insFal φ
```

Walk the closure once; at each formula ask the decision procedure
whether believing it preserves consistency; believe if so, refute if
not. The else-branch is safe by the extension dichotomy
(`cons_insVal_or_insFal`): if both extensions were inconsistent, the
two failure witnesses would combine — by the same selection surgery as
in the original's maximality lemma — into an inconsistency of the
triple one started with. The result (`lindenbaum`) is a closure-total
consistent extension *with the promises untouched*: the fold never
writes to the third component, an equality the truth lemma uses twice.

The second observation is that under totality the original's
maximal-theory lemmas — deductive closure, primeness of Γ, the
decomposition laws for falsified conjunctions, disjunctions and
implications, Θ ⊆ Δ — all *simplify*. Maximality entered those proofs
only through extension-failure witnesses, existentially quantified
selections needing combination; under totality every witness is a
singleton. Primeness, in full: if M ∨ N is validated but neither
disjunct is, totality refutes both, and the selection {M, N} together
with ∨-elimination contradicts consistency directly. Five lines of
formal text against the original's thirty. Constructivisation, for
once, is a simplification.

**Theorem 6.2** (truth lemma; `truth_lemma`). *On the model whose
worlds are the closure-total consistent triples, with Rᵢ inclusion of
validated parts, Rₘ inclusion of validated and promised parts, the
fallible worlds those validating false, and atoms outside the closure
true everywhere: for every closure formula φ, membership in the
validated part forces φ, and membership in the falsified part refutes
it.*

The propositional cases ride on the simplified lemma suite. Three cases
require a Lindenbaum extension, and they are the exact three of the
original, each start-triple carried over unchanged; only the engine
that extends them has changed. To refute a falsified M ⊃ N one extends
(Γ ∪ {M}, {N}, ∅). To force a validated ◯M at an arbitrary future one
extends (Γ₁ ∪ {M}, ∅, Θ₁) — the body added, the *promises carried
across* — and consistency of this triple is the ◯-guard's showcase: a
violation would give Γ₁ ⊢ M ⊃ ◯(⋁ of a Θ₁-selection), whence, since ◯M
is validated at the future, the elimination composite yields
Γ₁ ⊢ ◯(⋁ of the selection), an inconsistency of the future with its own
promises. The extension is then a constraint-successor — beliefs grew,
promises exactly preserved — forcing M. To refute a falsified ◯M one
extends (Γ, ∅, {M}): a promise *created*. Its consistency reduces, by
the monotonicity composite for ◯, to Γ ⊢ ◯M, contradicting the
falsification; and every constraint-successor of the extension inherits
the promise, hence — promises being falsified, by the Θ ⊆ Δ law —
refutes M. So the ∀∃ clause fails at the extension, which is an
ordinary future of the world one started at. This is the semantic machinery
of promises in its native habitat; the executable countermodels
of Section 7 merely print it.

**Corollary 6.3** (`finite_canonical_countermodel`,
`emitter_completeness`). *Every underivable sequent is refuted at a
world of its finite canonical model; enumerating the (finitely many)
worlds yields the countermodel as literal checker data:*

    ¬ (Γ ⊢ C)  implies  ∃ M w, checkB M w Γ C = true.

We pause on what has been achieved axiomatically. No maximality
principle appears anywhere above, and after the axiom-hygiene pass the
entire chain of this subsection — the decidability of consistency, the
decided Lindenbaum fold (now, in fact, a computable function), the
truth lemma, and the countermodel enumeration — audits at
`[propext, Quot.sound]`: no choice. Two named statements in the
artefact remain classical for a reason worth recording, since it is a
lesson about audits rather than about mathematics: an axiom audit walks
the bodies of the constants a *statement* mentions, and Mathlib's
`List.toFinset` is choice-tainted at definition level (its
deduplication carries a permutation-invariance proof that uses choice) —
so any theorem phrased through it can never audit clean, however its
proof is conducted. The artefact provides clean restatements through a
local choice-free deduplicator, and keeps the original phrasings as
one-line wrappers. It is tempting, and would be wrong, to say that the
logic proves its own completeness: the proof
lives in the metatheory, and a quantifier-free propositional logic
cannot so much as state completeness. What is true, and we think worth
saying carefully, is that the metatheoretic proof's only oracle is the
object logic's own decision procedure — an arrangement made possible by
the fact, special to a decidable logic with no embedded arithmetic,
that there is no Gödelian obstruction to consulting it.

**Remark 6.4 (the apparent circle).** Decidability before completeness
has an air of circularity about it, since the familiar route runs the
other way: the original paper's own Theorem 2.8 obtained decidability
*from* completeness, through the finite model property, and a
decidability so obtained could not be used inside a completeness proof
without vicious regress. The present arrangement is innocent, for three
reasons which it is worth setting out once. First, the decision
procedure's correctness is a fact of proof theory alone: it rests on
the repaired terminating calculus proving exactly the PLL sequents —
established by cut admissibility, the structural lemmas, and the
translations among the four calculi — and on the loop-checked search
deciding that calculus; no model is mentioned anywhere in the chain.
Second, the completeness proof consumes decidability only as a
*derivability* oracle, never a semantic one: what the Lindenbaum fold
asks, formula by formula, is whether a particular disjunction is
derivable, and what the oracle really contributes is the totality of a
case analysis — "believe or refute" — for which the classical proof
pays with Zorn and excluded middle and we pay with a computation. The
semantics enters only afterwards, in the truth lemma, which is the
genuinely new fact and presupposes nothing about the decider beyond its
proof-theoretic correctness. Third — and this is a kind of argument
available only to a mechanised development — the absence of the circle
is itself machine-checked: a proof assistant's import graph is acyclic
by construction, the completeness modules import the decidability
module, and the decidability module imports no semantic module
whatever. The reversal has a respectable pedigree: decidability of
intuitionistic propositional logic (Gentzen, 1935) preceded its Kripke
completeness (1965) by thirty years, and for the same reason — a
terminating calculus is a creature of syntax. Completeness then
discovers that this syntactic creature knows enough to build every
countermodel. The discovery flows one way, and the compiler enforces
the direction.

### 6.3 The theorem

**Theorem 6.5** (`derivable_iff_no_realP_refutation`,
`PLLRealCompleteness.lean`). *A sequent is derivable in PLL exactly
when no token-decorated, checker-verified finite model
⊩ᵖ-realisability-refutes it:*

```lean
Nonempty (LaxND Γ C) ↔
  ¬ ∃ (M : FinCM) (w : Nat) (hwf : M.WellFormed) (hlt : w < M.n),
    (∀ ψ ∈ Γ, ∃ x, x ⊩ᵖ[tokenEvidence tblPca M hwf tok₀, tblκ, ⟨w, hlt⟩] ψ) ∧
    ¬ ∃ x, x ⊩ᵖ[tokenEvidence tblPca M hwf tok₀, tblκ, ⟨w, hlt⟩] C
```

Forward: soundness together with Theorem 6.1 — a derivable conclusion
is forced wherever its realised hypotheses are, hence realised by its
own fullness witness. Backward: Corollary 6.3 composed with the closed
squeeze. Every quantifier ranges over concrete objects — finite models
as printable data, one token per atom, realisers in an explicit algebra
of lookup tables — and the backward case decision is made by the
decision procedure, not by excluded middle. The theorem audits at
`[propext, Quot.sound]`, enforced by build-time guards: the
completeness of PLL for realisability is, in the formal sense the audit
measures, a choice-free theorem. PLL is complete for the semantics in
which evidence may react to the future; incomplete, by Section 5, for
every more rigid discipline.

## 7. The theory, run

*(This section's artefacts are all generated: countermodels by
evaluation of the emitter, proof terms by the kernel; each is
re-checkable from the cited files.)*

The completeness theorem's countermodels are not merely finite but
executable, and the artefact exploits this in both directions. An
untrusted search procedure (`CounterEmit.emit`) proposes countermodels
from failed proof search; the verified checker certifies them; a wrong
proposal can produce only a failure, never a wrong certificate. In the
other direction, any certified model refutes in the full realisability
sense, by the squeeze.

For ◯p ⊢ p the emitter produces a five-world model, pinned in the
artefact as data (`demoM`), whose worlds read as belief states: a state
believing exactly ◯p (the refuting world); above it a state where the
constraint has been discharged and p is believed; the fallible ceiling;
and — the instructive one — a state that has *promised* never to
evidence p, whose only constraint-successor is itself. The
kernel-checked certificate

```lean
theorem somehow_p_not_p :
    ¬ Nonempty (LaxND [(prop "p").somehow] (prop "p")) :=
  FinCM.not_provable_of_check (M := demoM) (w := 2) (by decide)
```

runs the verified checker inside the kernel; no compiled evaluation is
trusted, and the audit is choice-free. Under reading (7): believing ◯p
cannot be cashed for believing p, and the countermodel says why — there
is a coherent belief state committed to the constraint's discharge
remaining forever pending.

For the distribution scheme ◯(p ∨ q) ⊢ ◯p ∨ ◯q the emitter builds
twenty worlds, and its report is worth displaying verbatim, for it is
the machinery of promises from Theorem 6.2, printed by a program:

    refuting world: w4  (20 worlds)
      w4: believes [◯(p ∨ q)]
      w5: believes [◯(p ∨ q)], promises-false [◯p, p]
      w6: believes [◯(p ∨ q)], promises-false [◯q, q]
      ...

The refuting world believes exactly ◯(p ∨ q); its two critical futures
carry the standing promises "never p" and "never q"; a promise binds
all constraint-successors, so ◯p dies along one future and ◯q along the
other, while each future can still discharge the *disjunction* through
its unpromised disjunct. The twenty worlds are an artefact of the
systematic construction — the canonical enumeration keeps every
coherent belief state — and a checker-gated *minimisation* strips the
scaffolding: repeatedly delete any world whose removal leaves the
certificate intact (`emitMin`; untrusted, like the emitter, and
harmless for the same reason). For this sequent the minimiser descends
from twenty worlds to three — a root believing ◯(p ∨ q) below one leaf
satisfying p and one satisfying q, with Rₘ = Rᵢ and neither promises
nor a fallible world remaining — which is *precisely* the hand-built
split model of [F&M 1997, Fig. 3], now pinned as a build-time
regression guard. The systematic model proves existence; deletion
recovers the presentable one; and a failed proof search terminates in
a structured epistemic explanation rather than a bare verdict. A
second, finer pass (`emitMinClean`) sweeps attributes rather than
worlds — a fallible flag, a valuation pair, a relation pair is deleted
whenever the checker still certifies the sequent without it — and
answers small questions a reader might not think to ask: one
constraint arrow of the split model does no work (◯(p ∨ q) at the root
is witnessed through the q-leaf alone), and the countermodel to
◯p ⊢ p needs no fallible world at all — the emitted model's fallible
ceiling survives world-deletion but not attribute-cleaning, leaving a
two-world model: believe nothing, then p. Both prunings are pinned.

**Remark 7.1 (preorder, not partial order).** In all these models Rᵢ
is a genuine preorder: distinct worlds can be mutually related. The
five-world model of ◯p ⊬ p has one such pair — the belief-empty world
and its promise-bound twin — and the twenty-world model has thirteen,
among them the refuting world and its two critical futures: w₄, w₅, w₆
believe exactly the same formulas and differ only in their standing
promises, so the refutation just displayed is transacted entirely
inside a single Rᵢ-equivalence class. This is the geometry of the
construction: canonical Rᵢ compares beliefs and deliberately ignores
promises, and refuting a ◯-formula is a move that changes no belief —
it only takes on a commitment. Rₘ, which carries promises along, is
antisymmetric in every model of this section. Nothing is lost for
validity: forcing is hereditary along Rᵢ (`force_hered`), so mutually
related worlds force the same formulas, and the parent paper already
observed on this ground that Rᵢ may be assumed a partial order
[F&M 1997]; one may also simply pass to the quotient. The artefact
effects the reduction by deletion instead — minimisation removes the
equivalent twins, and both minimised models above are posets. Each of
these counts is a build-time guard (`riEquiv`/`rmEquiv`,
`PLLDiagram.lean`). We record one design observation without
mechanised warrant: a canonical Rᵢ refined to respect promises — which
would be antisymmetric by construction — would obstruct the ◯-case of
the truth lemma, whose refuting step needs a same-belief future in
which the old promises have lapsed and one fresh promise stands. The
preorder is not an accident of the construction but the room the
modality moves in.

Finally, evidence in the positive direction. The sequent
◯A, ◯(A ⊃ B) ⊢ ◯B — combine a belief with a believed implication — has
the kernel-checked proof term

    let val• := #0 in (let val• := #2 in val (#0 #1))

two monadic binds and an application: run the belief in A, obtaining
evidence under its constraint; under that constraint run the belief in
A ⊃ B; apply; return under the composed constraint. The uniform
extraction of the artefact (`extract_sound`) compiles this derivation,
by the equations "laxIntro is the identity, laxElim is
abstraction-then-application", to the polynomial

    (λa. (λg. g · a) · f) · x

whose value ⊩ᵘ-realises the conclusion wherever the context is
realised; the strategy extraction compiles the same derivation to the
reactive form in which the presented future is fed to the first
strategy, the named witness it returns is where the second strategy is
run, and the results compose. Sequential composition of beliefs is the
meet law of the evidence semantics (`ob_strength`), and the artefact
records — it was one of the development's early machine-checked
surprises — that no confluence assumption appears anywhere: belief
composition is ordered, as inquiry is.

A further exercise in the same currency, this time negative.
Idempotence ◯◯M ⊣⊢ ◯M is two proof terms: the multiplication
μ = λx. let val y ⇐ x in y and the unit η = λx. val x. Are they
mutually inverse? One composite is the identity: μ ∘ η reduces to
λx. x — the monad's unit law, holding as computation, since the let
fires on the val. The other is not: η ∘ μ normalises to
λx. val (let val y ⇐ x in y), a stuck term in which the collapse
remains pending inside the re-assertion, and the artefact computes the
composite's complete reduction graph — four terms, closed under
reduction, the identity not among them
(`mu_eta_not_mutually_inverse`, `PLLIdempotency.lean`, audited at
[propext] alone). So idempotence is inter-derivability, not
isomorphism: under reading (7), collapsing a belief about a belief and
then re-asserting belief in the result is not a null operation on
evidence, although it is one on truth. The separation holds in the
strongest sense the calculus can express: the artefact proves the
reduction confluent (`PLLConfluence.lean` — Newman's lemma from strong
normalisation, the critical pairs being `let`-β and `let`-assoc
overlapping at a `bind`), so normal forms are unique, conversion is
decided by the normaliser, and η ∘ μ is not *convertible* to the
identity (`eta_mu_not_conv_id`), not merely unable to reduce to it.

One asymmetry visible in these examples deserves promotion to a remark.
Evidence extracted from proofs is *frame-uniform*: one polynomial
serves every model. The fullness witnesses of Theorem 6.1 are
*frame-aware*: tables built by surveying the finite frame. Provable
formulas have evidence needing no knowledge of the situation; merely
true ones have evidence only relative to a survey of this situation's
futures. The idealisation Hintikka told us to own lives exactly in the
completeness theorem's omniscient survey — stated, and confined to
where it belongs.

## 8. Related work

The nearest neighbour of reading (7) in the literature is the
intuitionistic epistemic logic of Artemov and Protopopescu, whose
belief system IEL⁻ adopts co-reflection A ⊃ KA and rejects factivity,
so that K false is consistent — the same quarantining of absurdity. PLL
adds idempotence; we conjecture PLL-◯ is exactly IEL⁻ extended by
◯◯A ⊃ ◯A, and record the question as open. Justification logic in its
forgetful reading forces factivity and is therefore not this. The
constraint reading of the parent paper and the monadic reading of
computational type theory are the two established computational faces
of ◯; the doxastic reading is compatible with both, and the
double-negation believer — in constraint models with Rₘ = Rᵢ and no
fallible worlds, ◯M is forced exactly where ¬¬M is (machine-checked,
`force_somehow_iff_notnot`) — recovers the continuation reading as a
special case. We are not aware of a prior completeness theorem for a
lax logic with respect to a realisability semantics, nor of a prior
mechanised canonical-model construction whose Lindenbaum step is an
appeal to the object logic's decision procedure. The
terminating-calculus route to decidability for PLL is due to Iemhoff;
the artefact contains a machine-checked counterexample to the published
calculus and a repaired one, communicated separately.

## 9. Method

Every claim of this paper is a theorem of a Lean 4 development that
also contains its parent paper entire. The axiom footprint of each
result is recorded: nothing at all for a handful of results (among them
a well-foundedness theorem for the Kleene–Brouwer order, a standalone
fully constructive result in the artefact); `[propext]` or
`[propext, Quot.sound]` — no choice — for the proof theory, the
decoration half of completeness, the obstruction, and the executable
countermodel certificates, the decidability of the logic, the finitised
canonical model, and the completeness theorem itself; classical axioms
remain only in the parent's Zorn completeness (kept deliberately, as
the foil) and in two statements whose Mathlib vocabulary is
choice-tainted at definition level, each provided with a clean
restatement.

We have already said that the formalisation functioned as an
instrument. It is worth saying how. Three intended theorems failed, and
their failures were themselves established: a collapse lemma for ⊩ˢ
(refuted; the reformulation became the squeeze), the claim that ◯ is
not a normal modality (refuted; it is normal, every nucleus validating
K), and the intended completeness of ⊩ˢ, whose failure is Theorem 5.1
and whose repair is the paper's central definition. A referee may
reasonably ask what in this paper was found by the human author and
what by the machine; the honest answer, recorded commit-by-commit in
the artefact's history, is that the direction, the reading, the
standards and the corrections were human, and a large part of the
construction, the drafting and two of the three failures were found by
a language model operating the proof assistant under those standards.
Section 9.1 states this precisely.

### 9.1 Disclosure of AI assistance

The formalisation and the drafting of this paper were carried out in an
extended collaboration between the author and a large language model
(Anthropic's Claude — Opus 4.8 and Fable 5 — operating the Lean
toolchain directly). The model wrote the majority of the Lean proof
scripts and of the prose here, proposed constructions, and in several
instances discovered the mathematical turning points — notably the
fullness obstruction of Section 5, found in the attempt to prove its
negation. The author set the research programme and the doxastic
reading, fixed the methodological standard — no claim asserted beyond
its machine-checked status, with axiom audits recorded per theorem —
directed every design decision, rejected and corrected the model's
errors, and takes sole responsibility for the mathematics and the text.
Under prevailing authorship norms a language model cannot be an author;
its contribution is recorded here and, commit by commit, in the
artefact's history. The kernel-checked artefact is indifferent to the
provenance of its proofs; the reader need trust neither the author nor
the model, which is the point of the method.

On routes to publication for machine-checked mathematics by
unaffiliated authors, and the artefact-citation norms this paper relies
on (Zenodo-archived repository, `CITATION.cff`), see the survey in the
artefact (`docs/publication-routes.md`).

## 10. Conclusion and open problems

However strange a belief modality without factivity may at first
appear, it is a rather natural object, known already from half a dozen
mathematical contexts; what the present paper adds is that its logic of
evidential belief is non-degenerate exactly over intuitionistic logic,
and that PLL is precisely complete for the evidence discipline in which
realisers meet the future as an input. The countermodels witnessing the
"precisely" are finite, executable, and legible as belief states; the
canonical construction that produces them is the parent paper's, with
Zorn's lemma traded for the logic's own decision procedure.

Open problems. The axiomatisation of PLLᵘ, the logic of rigid evidence.
The exact relation of PLL-◯ to IEL⁻ (conjecturally: idempotence). A
Kleene-algebra instantiation of the table capacities via partial
computable functions (the choice-free statement needs care around
partiality). The tripos-level formulation of the evidence semantics.
Uniform interpolation for PLL — the repaired terminating calculus
supplies the height bound the published method lacked, and the
mechanised investigation continues.

---

*Appendix: annotated walk-throughs, at line level, in
`docs/annotated/` — `fullness-obstruction.md`, `adequacy-fullness.md`,
`finite-truth-lemma.md`; the strong-normalisation exposition
`strong-normalisation.md` covers the term calculus's metatheory. Lean
statements quoted in this draft are verbatim from the artefact at the
commit recorded in the ledger.*
