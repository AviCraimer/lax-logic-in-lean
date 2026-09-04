> **Repo correction note (2026-07-09).** Where this report treats
> Iemhoff's G4iLL-based results as settled (uniform interpolation for
> PLL via G4LL, Cor. 8.1 equivalence), see `LaxLogic/PLLG4Gap.lean`:
> the equivalence is refuted (machine-checked), so PLL uniform
> interpolation is OPEN — task #9. Reports are otherwise verified
> literature extractions.

I have thoroughly researched and verified all three questions. Here is the report.

---

# Nuclei, Model Completions, and Monad Composition in Propositional Lax Logic

**A research briefing for Matthew Fairtlough.** Three interlocking questions, one arc: *nuclei compose by join-iteration ⟸ idempotent monads have coproducts ⟸ general monads need distributive laws or sums; and the model-completion question is that same algebra seen model-theoretically.* Precision markers: **[VERIFIED]** = confirmed against the primary source (often read directly); **[UNVERIFIED]** = plausible/asserted but not confirmed at source.

---

## Q1. Model completions for nuclear Heyting algebras (uniform interpolation, algebraically)

### The machinery, precisely

**Ghilardi–Zawadowski** is the origin. *Sheaves, Games, and Model Completions: A Categorical Approach to Nonclassical Propositional Logics*, Silvio Ghilardi & Marek Zawadowski, Trends in Logic **14**, Kluwer, 2002. **[VERIFIED]** The book "deals with the structure of the category of finitely presented Heyting and modal algebras, relating it both with proof theoretic and model theoretic facts: existence of model completions, amalgamability, Beth definability, interpretability of second order quantifiers and uniform interpolation." The technical toolkit is dualities + sheaf representations + Ehrenfeucht–Fraïssé games/bounded bisimulations. Their headline results: IPC's finitely-presented-Heyting-algebra category has the properties that make uniform interpolation hold and the first-order theory of Heyting algebras admit a **model completion**; and the corresponding property **fails for S4**. (Book page: [Stanford SearchWorks](https://searchworks.stanford.edu/view/5051983); [PhilPapers record](https://philpapers.org/rec/GHISGA).)

The clean modern re-statement is **van Gool–Metcalfe–Tsinakis** (vGMT). *Uniform interpolation and compact congruences*, S. J. van Gool, G. Metcalfe, C. Tsinakis, **Annals of Pure and Applied Logic 168(10), 2017, pp. 1927–1948** ([ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0168007217300684); [arXiv:1904.06091](https://arxiv.org/abs/1904.06091); open [BORIS/Bern PDF](https://boris-portal.unibe.ch/server/api/core/bitstreams/a8e55491-35fe-4613-8804-a417d00d5949/content)). I read the paper's setup directly. **[VERIFIED]** From the abstract, verbatim: *"Uniform interpolation properties are defined for equational consequence in a variety of algebras and related to properties of compact congruences on first the free and then the finitely presented algebras of the variety. It is also shown, following related results of Ghilardi and Zawadowski, that a combination of these properties provides a sufficient condition for the variety's first-order theory to admit a model completion."*

The apparatus you would actually need for nuclear HAs, from vGMT §2:
- **Compact congruence** = finitely generated congruence; for any algebra **A**, the compact congruences KCon **A** form a join-subsemilattice of Con **A** (Definition/§2.1). **[VERIFIED]**
- A homomorphism *h*: **A** → **B** lifts to an **adjoint pair** *h*\* ⊣ *h*⁻¹ between congruence lattices (Definition 2.1). Its restriction to compact congruences (the *compact lifting*) has a right adjoint **iff** *h*⁻¹ preserves compact congruences (Proposition 2.2). Left/right uniform interpolation is exactly the existence of these right/left adjoints on KCon over the free/finitely-presented algebras. **[VERIFIED]**
- **Remark 2.4** (load-bearing for nuclei): *"The congruence lattice of any Heyting algebra **A** is isomorphic to the filter lattice of **A** … The compact filters are just the principal filters, and hence **A** is isomorphic to the opposite of KCon **A**."* **[VERIFIED]** This is why, for Heyting-based varieties, compact congruences "may be harmlessly identified with certain elements of the algebras" — the machinery collapses to something concrete, which is precisely the feature you would want to exploit for HAs-with-nucleus.

**The extra hinge: coherence.** *Uniform interpolation and coherence*, T. Kowalski & G. Metcalfe, **APAL 170(7), 2019, pp. 825–841** ([arXiv:1803.09116](https://arxiv.org/abs/1803.09116)); conference version *Coherence in Modal Logic*, AiML 12, 2018 ([arXiv:1902.02540](https://arxiv.org/abs/1902.02540)). **[VERIFIED]** A variety **V** is **coherent** iff *"any finitely generated subalgebra of a finitely presented member of **V** is finitely presented."* Coherence is the missing ingredient linking amalgamation + interpolation to the model completion: coherence ⇔ a restricted uniform deductive interpolation (compact congruences on a f.g. free algebra, restricted to a free algebra over a subset of generators, stay compact). **The cautionary result, verbatim from the abstract of the AiML paper: they "prove the failure of coherence and uniform deductive interpolation for a broad family of modal logics, including K, KT, K4, and S4."** **[VERIFIED]** These are exactly the Boolean-algebras-with-a-single-operator varieties — the classical-modal cousins of Heyting-algebras-with-a-nucleus. This is the reason to be *pessimistic* by default about nuclear HAs (see the honest assessment below).

**How restrictive "model completion" is for the Heyting world.** *On the model-completion of Heyting algebras*, L. Darnière ([arXiv:1810.01704](https://arxiv.org/abs/1810.01704)); with Junker, *Model-completion of varieties of co-Heyting algebras* ([arXiv:1001.1663](https://arxiv.org/abs/1001.1663)). **[VERIFIED]** *"It is known that exactly eight varieties of Heyting algebras have a model-completion"* — and independently, exactly eight varieties of Heyting algebras have the amalgamation property, and only these can have a model completion. Before Darnière–Junker only the trivial and Boolean cases were explicitly axiomatized; they axiomatize the remaining six (via *Density*, *Splitting*, and a *QE Property*), four of them (the locally finite ones) getting a finite axiomatization. Takeaway: even *without* a nucleus, "has a model completion" is a rare, delicate property among Heyting varieties.

### (a) Has anyone studied the model completion of nuclear HAs / frames-with-nucleus?

**Honest answer: no, not under that name — this appears to be genuinely open/unstudied. [VERIFIED as a negative]** Direct searches for `"nuclear Heyting algebra" / "Heyting algebra with a nucleus" + model completion / amalgamation / uniform interpolation` return the general Heyting/modal machinery above but nothing that treats the variety of HAs-with-nucleus (equivalently the algebras of PLL) as such. The search explicitly noted these terms "did not appear prominently." I could not find Ghilardi–van Gool, Carai–Ghilardi, or anyone else stating a model-completion result — positive or negative — for nuclei/lax modalities.

Nearest neighbours actually located (none of which is nuclear HAs, but all in the target program):
- **Ghilardi**, *Existentially Closed Brouwerian Semilattices* ([arXiv:1702.08352](https://arxiv.org/pdf/1702.08352)) — model-completion/existentially-closed analysis for implicative (∧,→) structures. The closest methodological template. **[VERIFIED it exists; contents not read in full]**
- The **Carai–Ghilardi-adjacent ortholattice program** you half-remembered: *Monadic ortholattices: completions and duality* ([arXiv:2406.06917](https://arxiv.org/pdf/2406.06917)) confirms the program has reached *operator-enriched* varieties (a Boolean quantifier on ortholattices), but I found **no** evidence it touched nuclei. **[VERIFIED it exists; no nucleus content found]**
- **Lingyuan Ye**, *Coexact completion of profinite Heyting algebras and uniform interpolation* ([arXiv:2604.08267](https://arxiv.org/pdf/2604.08267), 2026) — recasts UI for finitely-presented HAs via a sheaf/"K-topos" (ex/reg-completion), squarely in the G–Z model-completion tradition, and extends to profinite interior (S4-box) algebras in a companion. This is the most modern machine and the one most likely to be *adaptable* to a nucleus, but it is about the box/interior operator, **not** a nucleus. **[VERIFIED it exists; nucleus not treated]**

So: **the nuclear-HA model-completion question is, to the best of a thorough search, unasked in the literature.**

### (b) The closest positive relative: iSL

**iSL (intuitionistic strong Löb)** is the analogue with a *positive* uniform-interpolation result, and its algebras are HAs with a **coreflective/Löb □** (satisfying (□φ→φ)→φ). *Mechanised Uniform Interpolation for Modal Logics K, GL, and iSL*, H. Férée, I. van der Giessen, S. van Gool, I. Shillito, **IJCAR 2024, LNCS 14740, pp. 43–61 (Best Paper Award)** ([arXiv:2402.10494](https://arxiv.org/abs/2402.10494); [Springer](https://link.springer.com/chapter/10.1007/978-3-031-63501-4_3)). **[VERIFIED]** They give the first proof-theoretic construction of uniform interpolants for iSL and **mechanise it in Coq**.

**Does any paper state the corresponding model-completion consequence for iSL? Answer: no — I found none. [VERIFIED as a negative]** The iSL literature (Férée et al. 2024; van der Giessen's 2022 Utrecht thesis, which also shows **iK4 and iS4 do *not* have UI**; Shillito–van der Giessen's TABLEAUX 2023 calculus) proves/mechanises UI *proof-theoretically* and stops short of the algebraic model-completion statement. That corollary — "the variety of iSL-algebras has a model companion/completion" — appears to be an available-but-unclaimed consequence, obtainable by feeding iSL's UI into vGMT + coherence. It is a genuine gap.

### (c) Honest assessment: what proving/refuting the nuclear-HA model completion would involve, and which technique is most promising

**What it would take.** A model completion of the first-order theory of nuclear HAs (equivalently, quantifier elimination for the theory of *existentially closed* nuclear HAs) would, via vGMT, follow from establishing **all** of:
1. **Amalgamation** for the variety of nuclear HAs (equivalently deductive interpolation, given CEP). PLL is known to have Craig interpolation, which is encouraging, but amalgamation of *algebras with the nucleus operator* is the precise thing to check.
2. **Left and right uniform (deductive) interpolation** — i.e. the adjoints on compact congruences over free/finitely-presented nuclear HAs. Iemhoff's *Proof Theory for Lax Logic* (below) already gives the *proof-theoretic* half of this.
3. **Coherence** — the finitely-generated-subalgebra-of-finitely-presented-stays-finitely-presented condition. **This is the danger point.** Kowalski–Metcalfe show coherence *fails* for K, KT, K4, S4 — every standard single-operator classical modal variety. A nucleus *j* is a single unary operator (inflationary, idempotent, meet-preserving), structurally close to those. The realistic prior is that **coherence fails for nuclear HAs and hence they have *no* model completion** — this would be the analogue of the S4 failure, and it would be a *refutation*, likely the more probable outcome.
4. (Also needed: whether the variety has the **congruence extension property**; Heyting-based varieties typically do, and Remark 2.4 makes congruences=filters, which helps.)

**Which technique is most promising for *PLL* uniform interpolation specifically:**

- **Best bet for a *proof* of UI: Pitts-style syntactic, via Iemhoff's lax calculus.** This is already essentially done. *Proof Theory for Lax Logic*, R. Iemhoff, in the de Jongh Festschrift, 2024 ([arXiv:2209.08976](https://arxiv.org/abs/2209.08976)). **[VERIFIED]** She introduces **G4LL**, a terminating, cut-admissible sequent calculus for propositional lax logic, and *proves lax logic has uniform interpolation* by the (Pitts–Dyckhoff, contraction-free) proof-theoretic method — the first proof of lax UI that uses a proof system rather than models. So UI for PLL is *settled positively*, syntactically. This dovetails with your MEMORY note on the G4iLL/G4 route to decidability. **[VERIFIED]**

- **Best bet for the *model-completion corollary*: vGMT compact congruences (+ coherence check).** Given Iemhoff's UI, the shortest path to a model-completion statement is to run PLL's UI through the vGMT criterion, *and* settle coherence for the nuclear-HA variety. Because of Remark 2.4 (congruences = filters for HAs), the compact-congruence bookkeeping is tractable here; the whole question reduces to **coherence + amalgamation for the nucleus**.

- **G–Z games/sheaves**: the heaviest machinery, but the one most likely to yield a clean *structural* verdict (positive *or* negative) on the finitely-presented category of nuclear HAs, and the natural home if you want the "existentially closed nuclear HA" picture. Ye's 2026 coexact-completion topos is the modern incarnation and the thing I'd adapt first if going this route.

**Bottom line for Q1:** UI for PLL is *proven* (Iemhoff, syntactically). The *model-completion* question for nuclear HAs is *open and unstudied*; the most likely truth, by analogy with S4/K4, is **failure of coherence ⇒ no model completion**, and the cleanest way to decide it is vGMT compact-congruences with a focused coherence analysis of the nucleus.

---

## Q2. Joins / composition of nuclei — the algebra you half-remember

Your memory is essentially right, with one important sharpening at the end.

### (a) The assembly / frame of nuclei N(H), and finite vs transfinite iteration

The canonical reference is **M. H. Escardó, *Joins in the Frame of Nuclei*, Applied Categorical Structures 11(2), April 2003, pp. 117–124** ([author PDF](https://martinescardo.github.io/papers/hmj.pdf); [Springer](https://link.springer.com/article/10.1023/A:1023555514029)). I read the full paper. Set-up (§1), **[VERIFIED] and quotable**:

> *"A frame, or locale, is a complete lattice in which binary meets distribute over arbitrary joins. A **nucleus** on a frame is an inflationary and idempotent map that preserves finite meets. Under the pointwise ordering, the nuclei on a frame form themselves a frame. **Meets of nuclei are calculated pointwise, but joins are harder to describe explicitly, as pointwise joins fail to be idempotent in general.**"*

The fix is prenuclei. **[VERIFIED]** A **prenucleus** is *"an inflationary map that preserves finite meets"* (dropping idempotence). Prenuclei are closed under composition and under pointwise directed joins; the inclusion of nuclei into prenuclei has a left adjoint sending a prenucleus *p* to the **least nucleus p̄ ≥ p**, the *nuclear reflection*. **The join of a set of nuclei in the frame of nuclei is the nuclear reflection of its join computed in the lattice of prenuclei** — i.e. **the least nucleus above the pointwise join / composite.** That is exactly what you remembered.

**When finitely many iterations suffice vs. transfinite — Escardó's central analysis. [VERIFIED, quotable].** He lists *"at least four ways of obtaining the reflection."* The **transfinite** one is **Simmons'**: for a prenucleus *p* on frame *T*, define by ordinal recursion

  *p*⁰(*u*) = *u*,  *p*^{α+1}(*u*) = *p*(*p*^α(*u*)),  *p*^λ(*u*) = ⋁{ *p*^α(*u*) : α < λ } (λ limit),

and then *"p^α must be idempotent for a sufficiently large ordinal α, and p̄ is then p^α for such α."* So in general you need **transfinite** iteration; the ordinal at which it closes up is where idempotence is finally achieved. The explicit closed forms (no iteration) are also recorded:
- **Banaschewski**: p̄(u) = ⋀{ v ∈ T | u ≤ v = p(v) };
- **Johnstone**: p̄(u) = ⋀{ ((u⇒v) ∧ (p(v)⇒v)) ⇒ v | v ∈ T };
- **Wilson**: p̄(u) = ⋀{ (p(v)⇒v) ⇒ v | u ≤ v }.

Escardó's own contribution is the **fifth/sixth** way: p̄ is *"the least nucleus k satisfying the fixed-point equation p∘k = k"* (**Lemma 3.1** [VERIFIED]: for a prenucleus *p*, a nucleus *k* satisfies *p ≤ k* iff *p∘k = k*), and he derives it from a **Pataraia fixed-point theorem** (a choice-free, intuitionistic substitute for transfinite induction), yielding an **induction principle for joins of nuclei**:

- **Theorem 2.2 / Corollary 2.1 [VERIFIED]**: *any set of inflationary maps on an inductive poset (= dcpo with least element) has a least common fixed point*; any monotone endomap of an inductive poset has a least fixed point.
- **Reflection induction (Cor. 3.1) [VERIFIED]**: *"If p is a prenucleus and Q is an inductive set of prenuclei such that q∈Q implies p∘q∈Q, then p̄∈Q."*
- **Join induction (Thm 3.2 / Cor. 3.2) [VERIFIED]**: *"If J is a set of nuclei and Q is an inductive set of prenuclei such that j∈J and q∈Q together imply j∘q∈Q, then ⋁J∈Q."*

The point of Pataraia/Escardó: you can **reason about the join of nuclei as-if by induction, without ever running the transfinite ordinal tower** — the finite/transfinite distinction is dissolved into a fixed-point-and-induction principle. (He uses it to give a choice-free proof of the localic **Hofmann–Mislove–Johnstone** theorem, §4.) So the honest statement of "when do finitely many iterations suffice" is: **not in general — you generally need the transfinite tower (idempotence at a large ordinal) or, better, Escardó's induction principle** — the finitary case is special (it holds when *p* is, e.g., finitary/Scott-continuous, so the tower closes at ω).

Terminology origin: frame theorists "call the frame of nuclei the **assembly** of a frame" (H. Simmons); the standard textbook home is **Johnstone, *Stone Spaces*, CUP 1982**, and Simmons' *A Framework for Topology* (Logic Colloquium '77, Wrocław) and *Spaces with Boolean assemblies* (Colloq. Math. 43(1), 1980). **[VERIFIED]**

### (b) Connection to Lawvere–Tierney topologies / subtoposes

Escardó states this crisply in §4, **[VERIFIED] and quotable**:

> *"A quotient of a frame is a direct image of a nucleus on the frame. Topologically, (spatial) quotient frames correspond to (sober) subspaces. **Moreover, joins of nuclei correspond to intersections of subspaces.**"*

Lift this from Ω = frame-of-a-locale to Ω = subobject classifier of a topos and nuclei become **Lawvere–Tierney topologies**, whose algebras (the *j*-sheaves) form **subtoposes**. Under the order-reversal, **the join of two topologies ↔ the meet (intersection) of the corresponding subtoposes** — the composite localization onto the sheaves for *both*. Concretely: a nucleus/LT-topology *j* is a meet-preserving closure operator on Ω = a *localization*, and combining two of them is the least localization refining both, computed exactly by the reflection/iteration of (b). (This is the same fact the nLab records: *"a nucleus is a meet-preserving closure operator / sublocale"*, [Heyting algebra — nLab](https://ncatlab.org/nlab/show/Heyting+algebra).)

### (c) Your Studia Logica / Curry's-problem paper — and where it matches vs. differs

The paper is **Matt Fairtlough & Michael Mendler, *On the Logical Content of Computational Type Theory: A Solution to Curry's Problem*, in *Types for Proofs and Programs* (TYPES 2000), P. Callaghan, Z. Luo, J. McKinna, R. Pollack (eds.), **Springer LNCS 2277, 2002, pp. 63–78**. **[VERIFIED — read in full.]** (Not Studia Logica — that was a misremember; the constraint-programming variant is the separate **Fairtlough–Walton** tech report *First-order Lax Logic as a framework for Constraint Logic Programming*, Sheffield 1997. **Michael Walton is a coauthor of *that* report, not of the Curry's-problem paper.**) The Studia Logica hit your memory latched onto is a *different, later* paper by other authors: *Correspondence Theory for Modal Fairtlough–Mendler Semantics*, Studia Logica 2023.

**What the Curry's-problem paper actually does** (this is the precise version of what you half-remember):

- CTT/PLL has the single lax modality ◯ with axioms ◯I: φ⊃◯φ, ◯M: ◯◯φ⊃◯φ, ◯S: (◯φ∧◯ψ)⊃◯(φ∧ψ), plus MP and the extensionality rule Ext (⊢φ⊃ψ ⇒ ⊢◯φ⊃◯ψ). **[VERIFIED]**
- A **constraint context** (a.k.a. *constraint*) is *"any syntactic context C[·] for which the axioms and rule for ◯ are provable in IPL."* **[VERIFIED]** Two atomic families interpret ◯: the **state-reader** ◯φ ≡ K⊃φ and the **exception** ◯φ ≡ φ∨L (the two monads whose duality the paper analyses).
- **Basic constraint** (the "interval"): **[K,L]φ =df K⊃(φ∨L)** — φ is "switched on" only in the interval of worlds between where K holds (inclusive) and L holds (exclusive). **[VERIFIED, Fig. 1]**
- **Composition = finite conjunction of basic constraints.** *"if C₁ and C₂ are constraints, then (C₁⊓C₂)[x] =df C₁[x]∧C₂[x] is a constraint too. A finite conjunction of basic constraints ⊓_{i=0}^{n−1}[Kᵢ,Lᵢ] is called a **standard constraint**. We refer to n as the **depth** of the constraint."* **[VERIFIED]** The class **S** of standard constraints (all finite depths) is what PLL is complete for.
- **Theorem 2 [VERIFIED]:** *"The collection S of standard constraints is a **Boolean algebra** generated by formulas as atomic constraints."* Meet ⊓ = conjunction; the **join ⊔ has an *explicit finite formula* (Definition 1)**: for C₁ = ⊓ᵢ[K₁ᵢ,L₁ᵢ], C₂ = ⊓ⱼ[K₂ⱼ,L₂ⱼ], the join is ⊓_{i<m, j<n}[K₁ᵢ∧K₂ⱼ, L₁ᵢ∨L₂ⱼ] — a distributive-lattice/DeMorgan calculation on the interval representation. The main completeness theorem: **PLL ⊢ φ iff IPL ⊢ φ^C for every standard context C ∈ S**, and *no finite subset of S suffices*. **[VERIFIED]**

**Match vs. difference with the nucleus-join iteration — the sharpening you should note:**

- **The nesting/iteration you remember is real, but it lives in the ◯M axiom and the term-level composition, not in the join.** ◯◯φ⊃◯φ is exactly the *idempotence* of the modality; the composition terms C_M : C_j[C_j[A]]⊃C_j[A] and the "depth n" parameter are the finite-nesting data. So context *nesting* C[D[·]] and its collapse **is** the syntactic face of "iterate the pre-modality until idempotent."
- **But Fairtlough–Mendler's ⊔ is *not* the transfinite nucleus-reflection.** In N(H) the join is generally hard/transfinite (Escardó); in **S** the join is a *finite, closed-form Boolean-algebra operation* (Definition 1). The reason they diverge: **S is a Boolean algebra** (the constraints are *decidable* intervals with complements L̄ = [L,false]), so joins are *finitary and even complemented* — a far more rigid, better-behaved structure than a general frame of nuclei, where joins fail to be pointwise and idempotence must be forced. In your language: **the constraint algebra is the "nice/finitary/accessible" special case where the join-iteration terminates immediately (indeed is given by a formula), precisely because the ambient modality-lattice is Boolean rather than a bare frame of nuclei.** That is the honest reconciliation of "finite iterations of C[D[·]]" with "the join is generally transfinite."

---

## Q3. "Monads don't compose" (Hughes' criticism) vs. nuclei composing fine

### (a) General monads compose only via distributive laws (Beck), with genuine counterexamples

**Jon Beck, *Distributive Laws*, in *Seminar on Triples and Categorical Homology Theory* (ETH 1966/67), Springer LNM 80, 1969, pp. 119–140.** **[VERIFIED via nLab + Zwart–Marsden]** A **distributive law** of a monad *S* over a monad *T* is a natural transformation **λ: S∘T ⇒ T∘S** satisfying **four coherence axioms** (compatibility with both units and both multiplications: λ∘S(η^T)=(η^T)_S, λ∘η^S_T=T(η^S), λ∘S(μ^T)=(μ^T)_S∘T(λ)∘λ_T, λ∘μ^S_T=T(μ^S)∘λ_S∘S(λ)). Given λ, the composite **T∘S becomes a monad**, with multiplication T∘S∘T∘S →^λ T∘T∘S∘S →^{μμ} T∘S. **Existence of λ is sufficient but *not* necessary** for T∘S to carry a monad structure. (Definitions: [distributive law — nLab](https://ncatlab.org/nlab/show/distributive+law).)

**The concrete non-composition results — verbatim from Zwart–Marsden.** *No-Go Theorems for Distributive Laws*, Maaike Zwart & Dan Marsden, **LMCS 18(1), 2022** (extended version of LICS 2019) ([arXiv:2003.12531](https://arxiv.org/abs/2003.12531)). I read the introduction. **[VERIFIED]**
- Beck's caveat, restated: *"composing the functor parts of two monads does not, in general, result in a new monad."*
- **The Plotkin counterexample:** *"there is no distributive law combining the powerset and probability distribution monads"* — the canonical result *Distributing probability over non-determinism* [Varacca–Winskel 2006], the negative result *"credited to Plotkin."* **Strengthened by Dahlqvist–Neves [DN18]** to show *"the composite functor carries no monad structure at all."* **[VERIFIED]**
- **List over list:** their **Theorem 4.16** *"negatively answers the open question of whether the list monad distributes over itself."* **[VERIFIED]**
- **Powerset over multiset:** **Theorem 4.21** — *"there is no distributive law for the powerset monad over the multiset monad P∘M ⇒ M∘P."* **[VERIFIED]**
- **Theorem 5.2** *"confirms a negative conjecture of Beck from the original paper"* (the Abelian-group monad does not distribute over the list monad). **[VERIFIED]**
- Their method is algebraic (binary terms that are *idempotent* / violate *unitality* / the Yang–Baxter–style *abides* equation), building on Piróg–Staton's algebraic characterization of distributive laws.

This is the precise content of "Hughes' criticism": in the general/effectful setting, stacking two monads is *not* automatic and often provably *impossible*.

### (b) But monads *can* always be combined by coproduct/sum — no distributive law needed

**Hyland–Plotkin–Power, *Combining effects: Sum and tensor*, Theoretical Computer Science 357(1–3), 2006, pp. 70–99** ([open author PDF](https://homepages.inf.ed.ac.uk/gdp/publications/Comb_Effects_Jour.pdf); [DOI](https://doi.org/10.1016/j.tcs.2006.03.013)). **[VERIFIED]** Reformulating Moggi's monadic paradigm via enriched Lawvere theories, they combine computational effects by the **sum** (= coproduct of theories: disjoint operations, no interaction equations — *needs no distributive law*) and the **tensor** (commutative combination, adding interaction equations). This is the "you can always add effects side-by-side" answer.

The general existence engine is **G. M. Kelly, *A unified treatment of transfinite constructions for free algebras, free monoids, colimits, associated sheaves, and so on*, Bull. Austral. Math. Soc. 22(1), 1980, pp. 1–83** ([DOI](https://doi.org/10.1017/S0004972700006353)) — the **transfinite construction of free algebras** underlying coproducts/colimits of monads, which converges under accessibility/finitarity hypotheses ([transfinite construction of free algebras — nLab](https://ncatlab.org/nlab/show/transfinite+construction+of+free+algebras)). **[VERIFIED]** Sharper term-level formulas: **Ghani–Uustalu, *Coproducts of ideal monads*, ITA 38(4), 2004, pp. 321–342** ([open NUMDAM PDF](https://www.numdam.org/item/ITA_2004__38_4_321_0.pdf)) — for *ideal* monads (Id + T₀) the coproduct is a fixpoint, **F\*A = μX. FX + A**, dodging the transfinite machinery; and **Adámek–Milius–Bowler–Levy, *Coproducts of Monads on Set*, LICS 2012** ([arXiv:1409.3804](https://arxiv.org/abs/1409.3804)), the sharpest general result: coproducts of *consistent* monads via an initial-algebra formula; and the striking corollary that the only always-defined monad transformers "T ⊔ (−)" are, up to iso, the **exception** and **terminal** monads. **[VERIFIED]**

### (c) The idempotent case: idempotent monads = localizations, joins = coproducts, and a nucleus *is* one

An **idempotent monad** is one whose multiplication μ: TT→T is an isomorphism (equivalently Tη = ηT, or the EM-forgetful functor is fully faithful). **[VERIFIED, [idempotent monad — nLab](https://ncatlab.org/nlab/show/idempotent+monad)]** *"Giving an idempotent monad on C is equivalent to giving a reflective subcategory (a localization) of C."* Idempotent monads are *"categorified projection operators."*

**On a poset, a monad is exactly a closure operator** (monotone + inflationary + idempotent), and idempotent-monad-on-a-poset = closure operator. **[VERIFIED]** A **nucleus** adds one condition: preservation of binary meets. So:

> **A nucleus *is* an idempotent (strong) monad on the poset of truth values** — monotone, inflationary, idempotent, and ∧-preserving (the strength/monoidality). **[VERIFIED]** This is stated essentially verbatim by **Pavlovic–Hughes, *The nucleus of an adjunction and the Street monad on monads*** (a.k.a. *The nucleus: Mining concepts from adjunctions*), [arXiv:2004.07353](https://arxiv.org/abs/2004.07353), 2020: *"Monads over posets are closure operators… For closure operators T(T(x)) = T(x)"*, and their "Street monad on monads is strictly idempotent" — it *extracts the nucleus of a monad*. The strong-monad phrasing ("a nucleus is a strong monad on the poset of truth values") appears in the paper's framing. **[VERIFIED that the identification is made; the exact one-line quote is [UNVERIFIED] verbatim]**

**Consequently the two pictures coincide:** idempotent monads/localizations on a fixed base form a **poset in which joins exist**, and that join *is* the coproduct — computed by **iterating the alternation of the two localizations until idempotence** (finite iterations sufficing under accessibility/finitarity; transfinite in general). On a poset this is *precisely* Escardó's frame-of-nuclei story from Q2: the pointwise join of two closure operators isn't idempotent, so you take the least closure operator (nucleus) above it — the reflection/iteration. **So: nuclei composing "fine" and idempotent monads having coproducts are the same theorem, one on a poset and one in a general category.** The "clunky finite-iteration context composition" you built for PLL is the **term/syntactic face of the coproduct-of-idempotent-monads construction** — with the extra rigidity (Q2c) that your constraint algebra is Boolean, so the coproduct is a finite formula.

### (d) Term-level "sum of monads": what the combined modality looks like, and the honest gap

At the categorical/algebraic level the term-level sum is well developed: **Lüth–Ghani, *Composing monads using coproducts*, ICFP 2002** ([ACM](https://dl.acm.org/doi/10.1145/581478.581492)) argue the coproduct (not a distributive law) is the right combination and identify it with the coproduct in the functor category; **Ghani–Uustalu**'s μX.FX+A gives the *free* combined syntax; **Jaskelioff–Moggi, *Monad transformers as monoid transformers*, TCS 2010** ([ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0304397510004901)) give the categorical account of **monad transformers** — the *pragmatic non-solution* (Liang–Hudak–Jones, POPL 1995) that hand-picks a lifting instead of taking the honest coproduct. The engineering face is *Data Types à la Carte*-style free-monad coproducts.

**The honest gap [VERIFIED as a negative]:** there is **no dedicated published term calculus** for "◯₁ *joined* with ◯₂" as a **quotiented alternating bind-tower**. The available answers are (i) categorical (Beck λ; the no-go theorems) or (ii) algebraic-effects (HPP sum/tensor). The nearest thing to a *syntactic quotient of a monad* is the HIT-quotiented delay monad in dependent type theory (Chapman–Uustalu–Veltri), not tied to lax modalities. So the "alternating bind-towers quotiented" object you're imagining is a **genuine, apparently-unfilled niche** at the term level.

### (e) A term-level analogue for the nucleus-join, and what PLL-with-two-◯s-and-their-join looks like

**Is there a good term-level analogue for the nucleus-join?** Partially — and this is the most promising direction:

- **Adjoint logic is the cleanest fit.** Pruiksma–Chargin–Pfenning–Reed, *Adjoint Logic*, 2018 ([CMU PDF](https://www.cs.cmu.edu/~fp/papers/adjoint18.pdf)); Pruiksma–Pfenning, *Adjoint Natural Deduction* ([arXiv:2402.01428](https://arxiv.org/abs/2402.01428)). **[VERIFIED]** Here **the lax modality/Moggi monad arises as a composite UF of two adjoint modalities** (up-shift/down-shift between modes), and the framework is *parametric in a preorder of modes* — so it natively supports **several modalities in one system** and their interaction. This is the nearest published home for "a join of localizations" done proof-theoretically, because it builds each modality as a *localization* (adjunction) and lets you mix them. ([adjoint logic — nLab](https://ncatlab.org/nlab/show/adjoint+logic): "lax logic = monad = UF".)
- **Multimode/multimodal frameworks**: Kavvos–Gratzer, *Under Lock and Key* (Bull. Symbolic Logic 2023, [arXiv:2211.06217](https://arxiv.org/abs/2211.06217)) and MTT (Gratzer–Kavvos–Nuyts–Birkedal, LMCS 2021, [arXiv:2011.15021](https://arxiv.org/abs/2011.15021)) give a **mode theory** (a 2-category) parametrizing *many* modalities and how they compose — the mature machinery for "several modalities, combined per a specification." They use □/adjunctions rather than a bare join of two lax monads, but a lax multimode instance is exactly where a "◯₁ ⊔ ◯₂" would live.
- **The one existing PLL-specific multimodal proof theory**: Mendler–Scheele, *Cut-free Gentzen calculus for multimodal CK*, Information and Computation 209(12), 2011 ([ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0890540111001404)) — a multimodal constructive-K calculus in which **the lax/computational modality CL** appears as one theory among several. This is the natural substrate to *extend* to two lax modalities. **[VERIFIED]**
- **Brand-new and worth pulling:** N. Valliappan, *Lax Modal Lambda Calculi*, **CSL 2026** ([arXiv:2512.10779](https://arxiv.org/abs/2512.10779); [LIPIcs](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CSL.2026.46)) — a 2025 term-calculus paper *specifically* about lax modalities; the first place to check whether anyone has already treated more than one ◯ or their combination. **[VERIFIED it exists; whether it does *multiple* lax modalities is [UNVERIFIED] — not yet read]**
- **Foundational anchors**: Moggi, *Notions of Computation and Monads*, I&C 93(1), 1991; Benton–Bierman–de Paiva, *Computational Types from a Logical Perspective*, JFP 8(2), 1998; Pfenning–Davies, *A Judgmental Reconstruction of Modal Logic*, MSCS 11(4), 2001 (which **decomposes the lax modality as ◇ following □**, a useful lever for a multimodal treatment). **[VERIFIED]**

**What "PLL with two ◯s and their join" would look like proof-theoretically.** Two lax modalities ◯₁, ◯₂ (two nuclei j₁, j₂), each with its own I/M/S/Ext (its own G4LL-style rules). Their **join ◯ = j₁∨j₂** in N(H) is the least nucleus above both; proof-theoretically it is the modality whose rules are the *closure* of the two rule-sets under **alternating nesting** — the sequent-calculus incarnation of "iterate ◯₁◯₂◯₁… until idempotent (◯M for the composite holds)." In Fairtlough–Mendler's Boolean constraint algebra this closure is *finite and explicit* (Definition 1's ⊓ᵢⱼ[K₁ᵢ∧K₂ⱼ, L₁ᵢ∨L₂ⱼ]); in a general frame of nuclei it is the transfinite reflection tamed by Escardó/Pataraia induction. The right formal setting to *build* it is adjoint/multimode logic (each ◯ = UF, the join = the reflective combination), and the honest status is that **no one has yet written down "multi-nucleus lax logic with an explicit join modality" as such** — it is a well-motivated, apparently-open construction, and your PLL-in-Lean development is unusually well placed to be the first to mechanise it.

---

## Synthesis: one theorem, three faces

The three questions are **one phenomenon** viewed model-theoretically, order-theoretically, and categorically.

**Categorically (Q3):** general monads do *not* compose — Beck's distributive law is needed and often provably absent (Zwart–Marsden: powerset⊗distribution, list⊗list, powerset⊗multiset all fail). The escape is to *combine* rather than compose: coproducts/sums always exist (HPP; Kelly; Ghani–Uustalu), built by a transfinite/fixpoint construction that terminates finitely under accessibility. **In the idempotent case this collapses to something clean:** idempotent monads = localizations, which form a *poset with joins*, and the join **is** the coproduct, obtained by iterating the alternation to idempotence.

**Order-theoretically (Q2):** restrict that idempotent-monad poset to a poset base and you get **closure operators**; add ∧-preservation and you get **nuclei**. A nucleus *is* an idempotent strong monad on the truth-values (Pavlovic–Hughes). The frame of nuclei N(H) is exactly the "poset of localizations," its **join is the least nucleus above the composite/pointwise join** (generally transfinite, Simmons; tamed to an induction principle by Escardó–Pataraia), and this join **is** intersection of subtoposes / composite of Lawvere–Tierney localizations. Your Fairtlough–Mendler constraint algebra is the *finitary, Boolean* special case where the join is a closed formula — the syntactic shadow of the coproduct-of-idempotent-monads.

**Model-theoretically (Q1):** ask that same algebra a model-theoretic question. A nucleus is a single unary operator; the variety of nuclear HAs is a Heyting-algebra-with-operator variety. Its **uniform interpolation is *proven*** (Iemhoff's G4LL, syntactically — the Pitts face of "the join/reflection is well-behaved"). Its **model completion is the open question**: by vGMT it would follow from amalgamation + left/right UI + **coherence**, and coherence is exactly where the classical single-operator modal varieties K, KT, K4, S4 *fail* (Kowalski–Metcalfe) — so the model completion of nuclear HAs is *unstudied* and, by that analogy, *more likely to fail than hold*. The very iteration that makes the nucleus-join transfinite (Q2) and the coproduct non-elementary-to-construct (Q3) is what threatens finite presentability of subalgebras — i.e. **coherence is the model-theoretic name for "the join-iteration doesn't terminate finitely."** The three questions are the same fact about *how idempotent modalities combine*, read in three registers: model completion (logic/model theory) ⟺ join in N(H) (order theory) ⟺ coproduct of idempotent monads (category theory).

---

## Key sources (files read directly are marked ⬇)

- ⬇ Escardó, *Joins in the Frame of Nuclei*, ACS 11(2), 2003 — [PDF](https://martinescardo.github.io/papers/hmj.pdf). *(read in full; Q2)*
- ⬇ Fairtlough & Mendler, *On the Logical Content of Computational Type Theory: A Solution to Curry's Problem*, TYPES 2000, LNCS 2277, pp. 63–78 — [nLab PDF](https://ncatlab.org/nlab/files/MendlerComputationalTypeTheory.pdf). *(read in full; Q2c)*
- ⬇ van Gool–Metcalfe–Tsinakis, *Uniform interpolation and compact congruences*, APAL 168(10), 2017 — [arXiv:1904.06091](https://arxiv.org/abs/1904.06091). *(setup read; Q1)*
- ⬇ Zwart & Marsden, *No-Go Theorems for Distributive Laws*, LMCS 18(1), 2022 — [arXiv:2003.12531](https://arxiv.org/abs/2003.12531). *(intro read; Q3a)*
- Ghilardi & Zawadowski, *Sheaves, Games, and Model Completions*, Trends in Logic 14, 2002.
- Kowalski & Metcalfe, *Uniform interpolation and coherence*, APAL 170(7), 2019 ([arXiv:1803.09116](https://arxiv.org/abs/1803.09116)); *Coherence in Modal Logic*, AiML 12, 2018 ([arXiv:1902.02540](https://arxiv.org/abs/1902.02540)).
- Darnière (& Junker), *On the model-completion of Heyting algebras*, [arXiv:1810.01704](https://arxiv.org/abs/1810.01704); [arXiv:1001.1663](https://arxiv.org/abs/1001.1663).
- Iemhoff, *Proof Theory for Lax Logic*, 2024 — [arXiv:2209.08976](https://arxiv.org/abs/2209.08976).
- Férée–van der Giessen–van Gool–Shillito, *Mechanised Uniform Interpolation for K, GL, iSL*, IJCAR 2024 — [arXiv:2402.10494](https://arxiv.org/abs/2402.10494).
- Ye, *Coexact completion of profinite Heyting algebras and uniform interpolation*, 2026 — [arXiv:2604.08267](https://arxiv.org/pdf/2604.08267).
- Hyland–Plotkin–Power, *Combining effects: Sum and tensor*, TCS 357, 2006 — [PDF](https://homepages.inf.ed.ac.uk/gdp/publications/Comb_Effects_Jour.pdf). Kelly 1980, Bull. Austral. Math. Soc. 22(1). Ghani–Uustalu, *Coproducts of ideal monads*, ITA 38(4), 2004 — [PDF](https://www.numdam.org/item/ITA_2004__38_4_321_0.pdf). Adámek–Milius–Bowler–Levy, *Coproducts of Monads on Set*, LICS 2012 — [arXiv:1409.3804](https://arxiv.org/abs/1409.3804).
- Pavlovic & Hughes, *The nucleus of an adjunction and the Street monad on monads*, 2020 — [arXiv:2004.07353](https://arxiv.org/abs/2004.07353).
- Pruiksma–Chargin–Pfenning–Reed, *Adjoint Logic*, 2018 ([PDF](https://www.cs.cmu.edu/~fp/papers/adjoint18.pdf)); Kavvos–Gratzer, *Under Lock and Key*, 2023 ([arXiv:2211.06217](https://arxiv.org/abs/2211.06217)); Mendler–Scheele, *Cut-free Gentzen calculus for multimodal CK*, I&C 209(12), 2011; Valliappan, *Lax Modal Lambda Calculi*, CSL 2026 ([arXiv:2512.10779](https://arxiv.org/abs/2512.10779)).
- Beck, *Distributive Laws*, LNM 80, 1969; [distributive law](https://ncatlab.org/nlab/show/distributive+law), [idempotent monad](https://ncatlab.org/nlab/show/idempotent+monad) — nLab.

**Two corrections to the brief's memory, flagged:** (1) the constraint-composition paper is the **TYPES 2000 / LNCS 2277** Fairtlough–Mendler paper, *not* Studia Logica, and **Walton** coauthored the separate 1997 *constraint-logic-programming* report, not it; (2) in that paper the context **join** is a *finite Boolean-algebra formula* (Def. 1), **not** a transfinite iteration — the iteration you remember is the ◯M idempotence / context-nesting, and it terminates finitely there precisely because the constraint algebra is Boolean rather than a general frame of nuclei.

🕒 2026-07-09 13:05 BST
— Opus 4.8 (1M context) · effort unknown
