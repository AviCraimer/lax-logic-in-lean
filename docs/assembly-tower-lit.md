# The frame of nuclei and the assembly tower: a literature survey

*Point-free topology / lattice theory. Focus: techniques for the algebraic structure of the
frame of nuclei of a Heyting algebra, the assembly tower, and the Rieger–Nishimura lattice.*

Compiled 2026-07-13. Every reference is tagged **CONFIRMED** (actual source or a
publisher/catalogue record was reached) or **UNVERIFIED** (attested only by a secondary
mention). Theorems are separated into **established** (statement + cited source) and
**open / not found**. Where the searched literature does not answer a question, this is said
plainly rather than papered over.

---

## 0. Objects and one motivating identification

Let `H` be a Heyting algebra (in the complete case, a **frame**). A **nucleus** is a map
`j : H → H` with `a ≤ ja`, `j(ja) = ja`, and `j(a ∧ b) = ja ∧ jb`. Nuclei are exactly
Macnab's **modal operators** on a Heyting algebra [Macnab 1981]. In the vocabulary of the
present project this is one and the same as the semantic interpretation of the lax modality
`◯` of Fairtlough–Mendler Propositional Lax Logic: PLL is sound and complete for Heyting
algebras equipped with a nucleus, so a nucleus *is* a `◯`-structure and the algebra of nuclei
is the algebra of possible lax modalities on `H`. This identification is stated once, for
orientation; the remainder is kept locale-theoretic.

The set of all nuclei on `H`, ordered pointwise (`j ≤ k` iff `ja ≤ ka` for all `a`), is again
a frame / complete Heyting algebra: the **assembly** of `H`, written variously `N(H)`, `NH`,
`A(H)`, the **frame of nuclei**, the **assembly frame**, the **splitting frame**, or (Isbell/
Plewe) the **dissolution** of `H`. The user's notation is `◯H`. Iterating gives the
**assembly tower**
```
   H → NH → N²H → … → NᵚH (colimit at limit ordinals) → Nᵚ⁺¹H → …
```
with the two canonical maps into each successor supplied by the open and closed nuclei
(below). The four sections that follow answer: (1) techniques for `N(H)`; (2) the tower and
its stabilization; (3) the Rieger–Nishimura lattice specifically; (4) explicit low-level data.

---

## 1. Techniques for investigating `N(H)` (the primary ask)

### 1.1 The three-way (four-way) correspondence

The backbone technique is to trade nuclei for other representations of a quotient:

> **[established]** For a frame `L`, there are canonical order isomorphisms between
> (i) nuclei on `L`, (ii) onto frame homomorphisms out of `L` (up to iso), (iii) frame
> congruences on `L`, and (iv) **sublocales** of the locale `L`. A nucleus `j` corresponds to
> its set of fixpoints `L_j = {a : ja = a}`, which is a sublocale; conversely a sublocale `S`
> induces `j_S(a) = ⋀{s ∈ S : a ≤ s}`. A congruence `E` induces `j(x) = ⋁{y : (x,y) ∈ E}` and
> `j` induces `E = {(x,y) : jx = jy}`.

Sources: Dowker–Papert, *Quotient frames and subspaces* (1966); Johnstone, *Stone Spaces*,
II.2 (1982); Picado–Pultr, *Frames and Locales* (2012); nLab `nucleus`, nLab `sublocale`.

A subtlety worth stating precisely, because it governs every lattice computation in `N(H)`:

> **[established]** Ordered pointwise, the nuclei form a **frame** `N(L)`. Ordered by
> inclusion, the sublocales form a **coframe** `S(L)`. The fixpoint bijection is
> order-*reversing*, so `N(L) ≅ S(L)ᵒᵖ`. Hence joins in `N(L)` are the subtle operation
> (they are *not* pointwise suprema of the operators), while meets are pointwise.

Sources: Johnstone, *Stone Spaces* II.2; Picado–Pultr; Plewe, *Sublocale lattices* (2002)
studies the lattice-theoretic fine structure of `S(L)` directly. The non-pointwise join is
exactly why `N(L)` is hard; Johnstone's *Two notes on nuclei* (see 1.5) exists to give
workable formulae for it.

### 1.2 Open and closed nuclei; generation

For `a ∈ L` there are two distinguished nuclei:

- the **open** nucleus `u_a(x) = (a → x)`, whose sublocale is the open sublocale `↑`-type
  complement — the assignment `a ↦ u_a` is order-*reversing*;
- the **closed** nucleus `c_a(x) = (a ∨ x)`, whose sublocale is the closed sublocale — the
  assignment `a ↦ c_a` is an order-preserving **frame embedding** `L ↪ N(L)`.

> **[established]** In `N(L)` the nuclei `u_a` and `c_a` are complements of each other. The
> closed nuclei give the canonical copy of `L` inside `N(L)`; `N(L)` is generated (under its
> frame operations) by the open together with the closed nuclei.

Sources: nLab `sublocale` (open `j_U(V)=U⇒V`, closed `j_{U'}(V)=U∨V`, complementary);
Johnstone, *Stone Spaces* II.2; Picado–Pultr. These two embeddings are the maps that build
the assembly tower: at each level one re-embeds via open and closed nuclei.

### 1.3 Booleanization / the double-negation nucleus

> **[established]** `j_{¬¬}(a) = ¬¬a` is a nucleus. Its sublocale `L_{¬¬}` is the **smallest
> dense sublocale**, is always dense, and is a **complete Boolean algebra** — the
> **Booleanization** of `L`. This is a *reflection* of `L` into Boolean frames realised as a
> sublocale (a quotient, i.e. a single point of the assembly), not the top of the tower.

Sources: nLab `sublocale` (`L_{¬¬} ≔ ¬¬U`, "smallest dense sublocale"); Johnstone,
*Stone Spaces* II.2; Picado–Pultr. (The dedicated nLab `Booleanization` page returned 404 at
time of writing; the content is on `sublocale`.) Note the contrast with §2: the double-negation
nucleus is one element of `N(L)`; the tower's Boolean *coreflection*, when it exists, is a
different and larger object obtained by iterating `N` upward.

### 1.4 Duality methods (Priestley / Esakia) — the most productive modern technique

For distributive lattices one has Priestley duality; for Heyting algebras, **Esakia duality**
(Esakia, *Topological Kripke models*, 1974; *Heyting algebras I*, 1985). The payoff for nuclei:

> **[established]** Under Esakia duality the nuclei on a Heyting algebra `H` correspond to
> certain **closed subsets of the Esakia space** `X_H` (called *nuclear sets*, or *L-sets* in
> Pultr–Sichler). This dualises the entire assembly: `N(H)` is (dually) the lattice of nuclear
> subsets of `X_H`.

Sources: Pultr–Sichler, *A Priestley view of spatialization of frames* (2000) [the "L-sets"];
Bezhanishvili–Ghilardi, *An algebraic approach to subframe logics. Intuitionistic case* (2007)
[nuclei via Esakia duality]; Ávila–Bezhanishvili–Morandi–Zaldívar (ABMZ),
*When is the frame of nuclei spatial: a new approach*, J. Pure Appl. Algebra 224 (2020) [terms
these closed sets *nuclear* and works with the special subset `Y_L ⊆ X_L` of *nuclear points*].
This is the technique of choice for a concrete `H`: compute `X_H`, then read off nuclei as
closed/nuclear subsets. A very recent systematisation is Bezhanishvili et al., *Priestley
perspective on point-free topology* (arXiv 2511.01426, 2025) and *Algebraic frames in Priestley
duality* (arXiv 2306.06745).

The ABMZ programme yields, purely by this route, sharp structural theorems (see §2), and
**recovers** the classical results of Beazer–Macnab, Simmons, Niefield–Rosenthal and Isbell as
corollaries — direct evidence that Esakia-dual "nuclear sets" are the right computational
handle.

### 1.5 Explicit nucleus formulae (prenuclei, generation)

Because joins in `N(L)` are not pointwise, one needs generation formulae:

> **[established]** Johnstone, *Two notes on nuclei*, gives an explicit formula for the
> nucleus **generated by a prenucleus** on a frame, and for the fibrewise closure of a nucleus.

Source: Johnstone, *Two notes on nuclei*, Order, doi:10.1007/BF00383767 (CONFIRMED via
publisher record). Macnab (1981) develops the parallel generation theory at the level of
Heyting algebras (his "modal operators"), including the calculus of how nuclei are built and
the behaviour of `N(H)` when `H` is not complete — the setting relevant to the RN lattice.

### 1.6 Simmons' idioms and algebraic Cantor–Bendixson

Simmons' distinctive technique is to do a **points-free Cantor–Bendixson analysis** on the
lattice itself. He works in **idioms** (upper-continuous modular lattices; every frame is a
distributive idiom) and defines lattice-theoretic *derivatives* generalising the topological
Cantor–Bendixson derivative.

Sources: Simmons, *A framework for topology* (1978); *An algebraic version of Cantor–Bendixson
analysis*, LNM 915 (1982), pp. 310–323; *Spaces with Boolean assemblies*, Colloq. Math. 43
(1980); *Cantor–Bendixson properties of the assembly of a frame* (2014). The modern
idiom/derivative literature continues this line: e.g. *Boolean perspectives of idioms and the
Boyle derivative* (arXiv 1708.02619) and *Residual stratification and the Cantor–Bendixson
structures of dual algebraic coframes* (arXiv 2605.04851, 2026).

### 1.7 Combinatorial / computational methods for finite or poset `H`

For `H` finite, or `H` the upsets of a poset (Alexandroff), the dual space is (essentially) the
poset with its specialization order, and nuclei become a finite/combinatorial object:

> **[established]** (ABMZ, *The frame of nuclei on an Alexandroff space*, Order 38 (2021)
> 67–78.) For an Alexandroff space `S`, `N(𝒪S)` is **spatial iff the infinite binary tree `T₂`
> does not embed** into the specialization preorder `(S, ≤)`.

This is a genuinely computable criterion. Related finite-side machinery: Bezhanishvili–
Bezhanishvili, *Profinite Heyting algebras* (Order 2008); Bezhanishvili–Gabelaia–Jibladze,
*Funayama's theorem revisited* (Algebra Universalis 2013), which is precisely about the frame
of *all* congruences (= the assembly) and when it is Boolean.

---

## 2. The assembly tower and its stabilization

### 2.1 The fixpoint of the tower

> **[established]** For a frame, the canonical embedding `L ↪ N(L)` (closed nuclei) is an
> isomorphism **iff `L` is a complete Boolean algebra**. Beazer–Macnab proved the direction
> "`L` Boolean ⟹ `N(L) ≅ L`" and gave a necessary-and-sufficient condition for `N(L)` to be
> Boolean; the biconditional "`N(A) ≅ A` iff `A` is a complete Boolean algebra" is the standard
> characterisation of the tower's fixpoints.

Sources: Beazer–Macnab, *Modal extensions of Heyting algebras*, Colloq. Math. 41 (1979) 1–12
(read in ABMZ's bibliography and paraphrased there: "if `L` is boolean then `N(L)` is
isomorphic to `L`"); Simmons (1980, 2014). So the tower is designed to "control the Boolean
behaviour" of `H`: it stops exactly when it reaches a complete Boolean algebra.

> **PRECISION NOTE (2026-07-14).** The whole biconditional is quantified **over frames** —
> `N(L)` is even *defined* as a frame only when `L` is a frame (complete). So it is silent about
> non-complete algebras: it neither asserts nor denies `N(H) ≅ H` for an incomplete `H`. The
> "`L` Boolean" in Beazer–Macnab means a **Boolean frame** (= complete Boolean algebra); the
> word "Boolean algebra" in the paraphrase must be read that way inside the frame universe.
> Two consequences, both important here (see `nuclei-noncomplete-lit.md`):
> (i) The "complete" in "complete Boolean" is a **frame artifact**: for **any** Boolean algebra
> `B`, complete or not, every nucleus is closed (`j(x) = x ∨ j(0)`, using only `x∨¬x=1`), so
> `N(B) ≅ B` and the tower over `B` **collapses at step 0**. In particular the constraint algebra
> `𝕊` (an *incomplete* BA) satisfies `N(𝕊) ≅ 𝕊` — it *is* its own assembly, contrary to a
> tempting inference from the "iff complete Boolean" statement.
> (ii) The genuinely subtle objects are the non-complete **non-Boolean** Heyting algebras (RN,
> the closed lax fragment). There, off-frame, `N(H)` is in general only a bounded meet-semilattice
> — both the join and `⊃` are extremal-fixpoint constructions requiring completeness properties
> (Erné 2022) — so "the assembly tower over RN" may not even be a tower of Heyting algebras
> without first completing RN to a frame.

### 2.2 When is a single assembly Boolean? (the scattered/Cantor–Bendixson theorem)

Reading the primary text of ABMZ (arXiv 1906.03636 v3, published J. Pure Appl. Algebra 224
(2020) no. 7, 106302), the landmark results are:

> **[established]**
> - (Simmons 1980; ABMZ Cor. 7.16) For a **T₀** space `S`: `N(𝒪S)` is Boolean **iff `S` is
>   scattered** (iff `𝒪S` is scattered).
> - (Simmons 1980, Thm 4.5; ABMZ Cor. 7.17) For an **arbitrary** space `S`: `N(𝒪S)` is Boolean
>   **iff `S` is dispersed** (iff `𝒪S` is scattered); dropping T₀ replaces "scattered" by
>   "dispersed".
> - (Isbell 1972; ABMZ) if `S` is sober, `N(𝒪S)` is **spatial iff `S` is weakly scattered**;
>   Simmons (Thm 4.4) gives the general weakly-scattered n.a.s.c.
> - (ABMZ Thm 7.14) For a **spatial** frame `L`, TFAE: `N(L)` is Boolean; `N(L)` is a complete
>   **atomic** Boolean algebra; the space of nuclear points `(Y_L, τ)` is **scattered**.
> - (Niefield–Rosenthal 1987) n.a.s.c. for `N(L)` spatial, and: `N(L)` spatial ⟹ `L` spatial.

"Scattered" is exactly a Cantor–Bendixson condition: `S` is scattered iff its CB derivative
sequence reaches `∅`, and the least such ordinal is the CB rank. This is the precise sense in
which *a single assembly being Boolean is a Cantor–Bendixson / scattered-ness phenomenon.*

### 2.3 The tower, dissolution, and (non-)stabilization

The tower is Isbell's **dissolution** iterated. Writing `A_d` for the dissolution (= assembly)
of a locale `A`:

> **[established]** (Plewe, *Higher order dissolutions and Boolean coreflections of locales*,
> J. Pure Appl. Algebra 154 (2000) 273–293.)
> - If a locale has a **Boolean coreflection**, it is obtained by **iterating the dissolution
>   functor `A ↦ A_d` until it stabilises at a Boolean locale**. Call `A` *α-soluble* if its
>   α-th dissolution is Boolean.
> - The α-soluble locales are **characterised for `α ≤ 4`**. There are examples stabilising at
>   the **1st, 2nd, and 3rd** dissolution; **beyond that, no examples are known.**
> - A sufficient condition for **insolubility** shows the **locale of rationals `ℚ` has no
>   Boolean coreflection**; consequently the only **metrizable** spaces with a Boolean
>   coreflection are the **scattered** ones.

Two consequences of the first importance for sub-question 2:

1. **The assembly tower does *not* always stabilize.** `ℚ` (insoluble) is an explicit locale
   whose tower never reaches a Boolean algebra. So "does the tower stabilize?" has answer
   *not in general*; stabilization is a nontrivial solubility/scattered-ness condition, not a
   theorem.
2. **Where it does stabilize, the stopping ordinal is a Cantor–Bendixson rank.** Simmons'
   *Cantor–Bendixson properties of the assembly of a frame* (2014) makes this the organising
   idea: a frame has a Boolean *reflection* precisely when some member of the assembly tower is
   Boolean, and "the nature of the assembly tower appears to be connected with a generalization
   of the Cantor–Bendixson process." For a T₀ space this reduces to §2.2.

> **[established]** Wilson's thesis, *The assembly tower and some categorical and algebraic
> aspects of frame theory* (Carnegie Mellon, 1994; advisor D. Scott), introduces **extensional
> operators** and **regular operators** and links regular operators to the assembly tower,
> giving a second (categorical + operator-algebraic) route to the same tower. Plewe,
> *Sublocale lattices* (2002), analyses the lattice `S(L) ≅ N(L)ᵒᵖ` at each level.

### 2.4 Net answer to sub-question 2

- *Does the tower stabilize?* **Not in general** (Plewe: `ℚ` is a counterexample).
- *Under what condition?* Precisely **solubility**, i.e. some `NᵅH` is Boolean; for spatial /
  metrizable objects this is **scattered-ness** of the associated space (Simmons, Plewe, ABMZ).
- *Is the stable value Boolean?* **Yes** — the tower can only halt at a complete Boolean
  algebra (`N(A) ≅ A` iff `A` complete Boolean), which is Plewe's Boolean coreflection.
- *`N(H) ≅ H`?* Characterised: **iff `H` is a complete Boolean algebra** (Beazer–Macnab +
  Simmons).
- *Stopping ordinal?* A **Cantor–Bendixson rank**; but the exact soluble locales are known
  only for `α ≤ 4`, and no example is known to require more than the 3rd dissolution.

---

## 3. The Rieger–Nishimura lattice specifically

### 3.1 What it is (context, all established)

`RN` is the **free Heyting algebra on one generator** — the algebra of the (Rieger–Nishimura)
one-variable formulae. Rieger (1949) and Nishimura (*On formulas of one variable in
intuitionistic propositional calculus*, J. Symbolic Logic 25 (1960) 327–331) showed there are
infinitely many inequivalent one-variable formulae `Fₙ`; the resulting lattice is the
**Rieger–Nishimura lattice** `RN` (a.k.a. the free *cyclic* Heyting algebra). Its **dual** is
the **Rieger–Nishimura ladder** (an infinite fishbone poset); as an **Esakia space** it is the
ladder together with a single limit point. Its finite quotients are the finite truncations of
the ladder (the finite Gödel/RN algebras), and **Bezhanishvili–Grigolia** characterised **all
subalgebras and homomorphic images**: every subalgebra of `RN` is projective, and a finite
Heyting algebra embeds in `RN` iff it is projective.

Sources (all CONFIRMED except Rieger 1949): Nishimura 1960 (JSL 25, 327–331); Bezhanishvili–
Grigolia, *Subalgebras and homomorphic images of the Rieger–Nishimura lattice* (Semantic
Scholar record; reported venue Proc. Inst. Cybernetics Georgian Acad. Sci. 1, 2000, 9–16);
Bezhanishvili–Gehrke, *Free Heyting algebras: revisited*; the 1980s dual-space descriptions of
Grigolia, Shehtman, Bellissima, Rybakov.

### 3.2 Its nuclei / assembly / tower height — VERDICT: **not found in the searched literature**

> **[open / not found]** No source located in this search computes the assembly `N(RN)`, the
> lattice of nuclei of the Rieger–Nishimura lattice, or the height of its assembly tower. The
> user's conjecture that the tower closes at `ω` or `ω+1` (i.e. `Nᵚ⁺¹(RN) ≅ Nᵚ(RN)`) is
> **neither confirmed nor refuted** by anything found. The RN lattice is heavily studied on the
> *free-algebra / intermediate-logic* side (subalgebras, dual space, Ruitenburg's theorem,
> Kuznetsov–Gerčiu logics) but does **not appear by name** in the assembly / frame-of-nuclei /
> dissolution literature (Simmons, Plewe, Wilson, ABMZ). This is a genuine gap, and it is
> reported as such rather than guessed at.

### 3.3 What machinery *would* settle it (established tools, not a claimed answer)

The question is not intractable given §1–§2; the honest statement is only that no one is
recorded as having carried it out:

- **Reduction to a rank computation.** By §2.2–§2.3 the tower height is governed by a
  Cantor–Bendixson / dissolution rank of the RN Esakia space. Since that space is countable
  with essentially one non-isolated point (the ladder plus its limit), it is scattered of low
  CB rank, which is consistent with — and the natural source of — a small finite or `ω`-level
  closure. This is the plausibility behind the `ω`/`ω+1` conjecture; it is **not** a located
  theorem.
- **Esakia-dual computation.** The ABMZ "nuclear subsets of `X_H`" technique (§1.4) applied to
  the concrete `X_RN` is the direct way to enumerate `N(RN)`.
- **A completeness caveat that must not be glossed.** `RN` is a Heyting algebra but is **not
  complete** (not a frame). The stabilization theorems of Simmons, Plewe and ABMZ are stated
  for **frames** (complete Heyting algebras); Macnab's "modal operators" theory is the correct
  framework for nuclei on a *possibly incomplete* Heyting algebra. Whether the frame-level
  tower results transfer verbatim to the RN tower, and whether `N(RN)` is already complete
  (so that the tower becomes frame-theoretic after the first step), is exactly the kind of
  point that needs checking before any "`ω`/`ω+1`" claim; **it was not resolved in any source
  found.**

---

## 4. Explicit computations / known sizes at low tower levels

- **Fixpoints.** For every complete Boolean algebra `B` (in particular each finite Boolean
  algebra `2ⁿ`), `N(B) ≅ B` (Beazer–Macnab). These are the only fixpoints.
- **Plewe's low levels.** Soluble locales are classified only through `α ≤ 4`; explicit
  examples are exhibited whose dissolution chain stabilises at the **1st, 2nd, or 3rd** step,
  and **none is known beyond the 3rd** (Plewe 2000). This is the sharpest explicit data on how
  far up a tower can actually be observed to run.
- **Finite / Alexandroff criterion.** `N(𝒪S)` spatial iff `T₂` does not embed in the
  specialization poset (ABMZ, Order 2021) — a decidable check for finite/poset `H`, hence a
  computational handle on `N(H)` for small `H`.
- **Not found.** No published table of `|N(H)|` for small Heyting algebras, and no computed
  value for `N(RN)` or the finite RN truncations `RNₙ`, was located. (One ResearchGate item,
  "The Generative Stack … Lean 4 Formalization … Frames, Nuclei …", surfaced but could not be
  verified as a reliable mathematical source and is **not** relied upon here.)

---

## Open / not found in the searched literature

1. **The RN assembly tower height** (the central sub-question 3 target): no source computes
   `N(RN)` or its tower; the `ω` / `ω+1` conjecture is **unresolved** in what was found.
2. **General stabilization ordinals:** the exact soluble locales are characterised only for
   `α ≤ 4` (Plewe); it is (as of the located literature) **open** whether locales exist whose
   dissolution tower first becomes Boolean at the 4th step or beyond, and the general
   supremum of finite stabilization levels is not pinned down.
3. **Incomplete-`H` transfer:** whether the frame-level tower theorems (Simmons/Plewe/ABMZ)
   apply to the assembly tower of a non-complete Heyting algebra such as `RN` was not settled
   by any source found; Macnab (1981) is the right framework but the specific transfer is not
   recorded.
4. **Booleanization vs. tower-top:** both are "Boolean" but they are different constructions
   (a sublocale/reflection vs. an iterated-`N` coreflection); no located source treats them
   together for `RN`.

---

## References

Tags: **[C]** CONFIRMED (actual source or a publisher/catalogue/primary-bibliography record was
reached); **[U]** UNVERIFIED (attested by a secondary mention only). Items marked
"(in ABMZ bib.)" were verified against the **read** reference list of arXiv:1906.03636v3.

**nLab entry points**
- **[C]** nLab, *nucleus* — https://ncatlab.org/nlab/show/nucleus
- **[C]** nLab, *sublocale* — https://ncatlab.org/nlab/show/sublocale (carries the open/closed
  nucleus, congruence, and `¬¬`-Booleanization material; cites Johnstone II.2, Picado–Pultr,
  Vickers)
- note: nLab *Booleanization* returned HTTP 404; nLab *assembly* is a realizability page,
  unrelated to the assembly frame.

**Nuclei on Heyting algebras / modal operators (PLL side)**
- **[C]** D. S. Macnab, *Modal operators on Heyting algebras*, Algebra Universalis **12**
  (1981), no. 1, 5–29. doi:10.1007/BF02483860 (in ABMZ bib.)
- **[U]** D. S. Macnab, *An algebraic study of modal operators on Heyting algebras with
  applications in topology and sheafification*, Ph.D. thesis, University of Aberdeen, 1976
  (title from a secondary snippet; primary/catalogue record not reached).
- **[C]** R. Beazer and D. S. Macnab, *Modal extensions of Heyting algebras*, Colloq. Math.
  **41** (1979), no. 1, 1–12 (in ABMZ bib.).

**Assembly, sublocales, congruences (structure of `N(L)`)**
- **[C]** C. H. Dowker and D. Papert, *Quotient frames and subspaces*, Proc. London Math. Soc.
  (3) **16** (1966), 275–296 (in ABMZ bib.).
- **[C]** P. T. Johnstone, *Stone Spaces*, Cambridge Studies in Advanced Mathematics **3**,
  CUP, 1982 (II.2 = nuclei/assembly) (in ABMZ bib.; ISBN 9780521337793).
- **[C]** P. T. Johnstone, *Two notes on nuclei*, Order, doi:10.1007/BF00383767 (explicit
  prenucleus-generation and fibrewise-closure formulae).
- **[C]** J. Picado and A. Pultr, *Frames and Locales: Topology without points*, Frontiers in
  Mathematics, Birkhäuser, 2012. doi:10.1007/978-3-0348-0154-6 (in ABMZ bib.).
- **[C]** T. Plewe, *Higher order dissolutions and Boolean coreflections of locales*, J. Pure
  Appl. Algebra **154** (2000), 273–293 (ScienceDirect S0022404999001930; in ABMZ bib.) —
  *the* tower-stabilization paper (α-solubility, `ℚ` insoluble).
- **[C]** T. Plewe, *Sublocale lattices*, J. Pure Appl. Algebra **168** (2002), no. 2–3,
  309–326 (in ABMZ bib.).
- **[C]** J. T. Wilson, *The assembly tower and some categorical and algebraic aspects of frame
  theory*, Ph.D. thesis, Carnegie Mellon University, 1994 (advisor D. Scott; ResearchGate pub.
  35295449; in ABMZ bib.).

**Booleanness / spatiality of the assembly (Cantor–Bendixson lineage)**
- **[C]** J. Isbell, *Atomless parts of spaces*, Math. Scand. **31** (1972), 5–32 (in ABMZ
  bib.).
- **[C]** J. Isbell, *On dissolute spaces*, Topology Appl. **40** (1991), no. 1, 63–70 (in ABMZ
  bib.).
- **[C]** S. B. Niefield and K. I. Rosenthal, *Spatial sublocales and essential primes*,
  Topology Appl. **26** (1987), no. 3, 263–269 (in ABMZ bib.).
- **[C]** H. Simmons, *A framework for topology*, Logic Colloquium '77, Stud. Logic Found.
  Math. **96**, North-Holland, 1978, pp. 239–251 (in ABMZ bib.; ScienceDirect
  S0049237X0872007X).
- **[C]** H. Simmons, *Spaces with Boolean assemblies*, Colloq. Math. **43** (1980), no. 1,
  23–39 (in ABMZ bib.).
- **[U]** H. Simmons, *An algebraic version of Cantor–Bendixson analysis*, in *Categorical
  Aspects of Topology and Analysis*, Lecture Notes in Math. **915**, Springer, 1982,
  pp. 310–323 (well-attested by multiple secondary citations with these exact pages; the PDF/
  catalogue record itself was not opened).
- **[C]** H. Simmons, *Cantor–Bendixson properties of the assembly of a frame*, in *Leo Esakia
  on Duality in Modal and Intuitionistic Logics*, Outstanding Contributions to Logic **4**,
  Springer, 2014, pp. 217–255. doi:10.1007/978-94-017-8860-1_9 (in ABMZ bib.).

**Duality / Esakia-dual technique and modern computations**
- **[C]** L. L. Esakia, *Topological Kripke models*, Dokl. Akad. Nauk SSSR **214** (1974),
  298–301 (in ABMZ bib.); *Heyting algebras I. Duality theory*, Metsniereba, Tbilisi, 1985.
- **[C]** H. A. Priestley, *Ordered topological spaces and the representation of distributive
  lattices*, Proc. London Math. Soc. (3) **24** (1972), 507–530 (and Bull. LMS **2** (1970),
  186–190) (in ABMZ bib.).
- **[C]** A. Pultr and J. Sichler, *A Priestley view of spatialization of frames*, Cahiers
  Topologie Géom. Différentielle Catég. **41** (2000), no. 3, 225–238 (the "L-sets"; in ABMZ
  bib.); also *Frames in Priestley's duality*, ibid. **29** (1988), 193–202.
- **[C]** G. Bezhanishvili and S. Ghilardi, *An algebraic approach to subframe logics.
  Intuitionistic case*, Ann. Pure Appl. Logic **147** (2007), 84–100 (nuclei via Esakia
  duality; in ABMZ bib.).
- **[C]** F. Ávila, G. Bezhanishvili, P. J. Morandi, A. Zaldívar, *When is the frame of nuclei
  spatial: a new approach*, J. Pure Appl. Algebra **224** (2020), no. 7, 106302
  (doi:10.1016/j.jpaa.2019.106302; arXiv:1906.03636 — **read in full for §2.2**).
- **[C]** F. Ávila, G. Bezhanishvili, P. J. Morandi, A. Zaldívar, *The frame of nuclei on an
  Alexandroff space*, Order **38** (2021), no. 1, 67–78. doi:10.1007/s11083-020-09528-1
  (arXiv:1906.03640).
- **[C]** G. Bezhanishvili, D. Gabelaia, M. Jibladze, *Funayama's theorem revisited*, Algebra
  Universalis **70** (2013), 271–286 (congruence frame = assembly; in ABMZ bib.).
- **[C]** G. Bezhanishvili and N. Bezhanishvili, *Profinite Heyting algebras*, Order **25**
  (2008), no. 3, 211–227 (in ABMZ bib.).
- **[C]** *Boolean perspectives of idioms and the Boyle derivative*, arXiv:1708.02619;
  *More on a curious nucleus*, arXiv:1807.08020; *Residual stratification and the
  Cantor–Bendixson structures of dual algebraic coframes*, arXiv:2605.04851 (2026);
  *Algebraic frames in Priestley duality*, arXiv:2306.06745; *Priestley perspective on
  point-free topology*, arXiv:2511.01426 (2025) — Simmons-idiom / Esakia-dual continuation
  (abstracts reached; used for orientation, not for specific theorems here).

**Rieger–Nishimura lattice**
- **[C]** I. Nishimura, *On formulas of one variable in intuitionistic propositional calculus*,
  J. Symbolic Logic **25** (1960), 327–331 (via SEP and multiple secondary records).
- **[U]** L. Rieger, *On the lattice theory of Brouwerian propositional logic*, Acta Fac. Rerum
  Nat. Univ. Carolinae **189** (1949) (canonical; primary not reached).
- **[C]** G. Bezhanishvili and R. Grigolia, *Subalgebras and homomorphic images of the
  Rieger–Nishimura lattice* (Semantic Scholar catalogue record reached; venue reported as
  Proc. Inst. Cybernetics Georgian Acad. Sci. **1** (2000), 9–16 — venue detail **[U]**).
- **[C]** N. Bezhanishvili and M. Gehrke, *Free Heyting algebras: revisited*
  (staff.fnwi.uva.nl/n.bezhanishvili/Papers/BezhGehrke.pdf) — RN dual-space structure.

*Coverage note.* Solid: the correspondence/duality techniques (§1), the Booleanness and
tower-stabilization theory (§2), and the full reference apparatus (verified against a read
primary bibliography). Thin / honest gaps: the **RN-specific** assembly and tower height
(§3.2 — not found), the general finite-stabilization-ordinal question beyond `α ≤ 4` (§2.4),
and the incomplete-`H` transfer (§3.3). No stabilization ordinal or theorem has been invented
to fill these.
