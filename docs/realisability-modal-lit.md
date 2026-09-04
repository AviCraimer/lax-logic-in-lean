# Realisability model theory for `◯`: a literature search

*Literature dig, 2026-07-15. Question: is there a **realisability-style model theory**
in which (i) each world/stage carries **computational information** (realisers,
evidence, a partial computation); (ii) the lax/belief modality `◯M` is **evaluated
at a world** against that information ("M is realised/verified given what is available
here"); and (iii) worlds are ordered by **growth of information** — a preorder/poset,
possibly **branching**, not necessarily linear — so **belief increases monotonically**?
Background taken as given: `◯` = nucleus = Lawvere–Tierney (LT) local operator = strong
monad; F&M read `◯M` as "M holds subject to constraints".*

Tag key: **VERIFIED** = primary/authoritative source fetched (location given);
**MY-INFERENCE** = sound reading not stated verbatim in a source; **UNVERIFIED** = cited
but full text not reached. **Recency caveat:** several strongest hits are 2025–2026
preprints — confirm refereed status and exact statements before citing in print.

---

## Verdict (foregrounded)

**The exact model theory is not packaged anywhere in the literature** (MY-INFERENCE,
from the sweep). No single source gives all of: realisers/evidence at each node, a
*single* lax `◯` evaluated at a node against those realisers, *and* monotone growth over
a branching poset, in a **belief** key. It must be **assembled from three pieces**:

1. **Realisers at nodes** — a PCA / typed-λ / justification-term algebra supplying, at
   each stage, the realisers of each proposition.
2. **Order structure** — a preorder/poset (or site) of stages with **hereditary
   (monotone)** realisability, so realisers persist upward; branching = an arbitrary
   poset or a covering site, not a linear order.
3. **How `◯` reads against realisers** — as the **nucleus / LT-operator `j`** on the
   per-stage realisability Heyting algebra, evaluated by Kripke–Joyal forcing.

**Key "for free" observation (MY-INFERENCE, well-grounded).** Clause (iii) — increasing
belief — is *not* an extra axiom: upward-closure of realiser-sets along the order is the
*same* condition as Fitting's evidence-monotonicity, Valliappan's transport map `mon_P`,
and persistence of forcing. Any Kripke-indexed (hereditary) realisability gives it. This
is exactly the monotonicity the mechanised `ConstraintModel` already has (`refl_i`,
`trans_i`, `hered_V`); the new ingredient is putting realisers on those worlds.

**Two connections to the paper's own thesis:**
- Yamada's `¬¬`-sheaf subtopos = the CPS / classical-realisability collapse (arXiv
  2602.23086) is a concrete **topos-theoretic instance of "classical belief is
  degenerate"** (§2A): passing to the classical (`¬¬`) local operator collapses the
  effectful/constructive content. Worth a paragraph in §2A/§7.
- The effective-topos **LT-topology** view is the categorical home of the
  **nucleus/assembly-tower** thread (`nuclei-noncomplete-lit.md`, `assembly-tower-lit`):
  the candidate `◯`'s over a realisability model are exactly the local operators on the
  effective topos, and these are *classified* (framework 2 below).

---

## Sources fetched (usable content returned)

- **[VERIFIED]** M. Fitting model theory via **SEP, *Justification Logic* (Artemov–Fitting),
  §3** — reproduces Fitting, "The logic of proofs, semantically", *Ann. Pure Appl. Logic*
  **132** (2005). (Fitting 2005 itself: **UNVERIFIED** — used the SEP reproduction.)
- **[VERIFIED]** Nakata, *A j-translation with Kripke forcing relation* (2026),
  arXiv:2602.23218 — Def. 4.4 reached.
- **[VERIFIED]** Valliappan, *Lax Modal Lambda Calculi* (2026), arXiv:2512.10779 — frame +
  modal clause reached (Agda-checked).
- **[VERIFIED]** Yamada, *Effectful Toposes and Their Lawvere–Tierney Topologies* (2026),
  arXiv:2602.23086.
- **[VERIFIED]** Cohen–Grunfeld–Kirst–Miquey, *Syntactic Effectful Realizability in HOL*
  (2025), arXiv:2506.09458.
- **[VERIFIED, abstract only]** S. Lee & J. van Oosten, *Basic subtoposes of the effective
  topos*, *APAL* (2013), arXiv:1201.2571.
- **[VERIFIED]** Marin–Padhiar–Shillito, *Intuitionistic Justification Logic, Semantically*
  (2026), arXiv:2606.31884.
- **[UNVERIFIED]** van Oosten, *Realizability: An Introduction to its Categorical Side*
  (2008); Hyland, *The effective topos* (1982); Kihara arXiv:2106.03061; Lipton,
  *Constructive Kripke Semantics and Realizability* (in Moschovakis ed., *Logic from
  Computer Science*, MSRI Publ. 21, Springer 1992); Pfenning–Davies (2001);
  van Benthem–Pacuit, *Dynamic Logics of Evidence-Based Beliefs* (*Studia Logica* 2011).

---

## Ranked frameworks (by fit to (i)–(iii))

### 1. Fitting models for justification logic — closest *conceptual/epistemic* match
**[VERIFIED, SEP §3]** A model `M = ⟨G, R, E, V⟩`: worlds `G`, accessibility `R`, atomic
valuation `V`, and an **evidence function** `E : Tm × Fml → 𝒫(G)`, with `Γ ∈ E(t,X)` read
"`t` is admissible evidence for `X` at `Γ`". Closure conditions:
`E(s, X→Y) ∩ E(t, X) ⊆ E(s·t, Y)` (application), `E(s,X) ∪ E(t,X) ⊆ E(s+t, X)` (sum),
`E(t,X) ⊆ E(!t, t:X)` (proof-checker). Truth clause:

> `M, Γ ⊨ t:X`  iff  `Γ ∈ E(t,X)` **and** for all `Δ` with `Γ R Δ`, `M, Δ ⊨ X`.

**Monotonicity (VERIFIED):** `Γ R Δ` and `Γ ∈ E(t,X)` ⟹ `Δ ∈ E(t,X)` — evidence grows
monotonically along the frame order. Fit: (i)✓ evidence terms = computational info at
worlds; (ii)✓ `t:X` = "X, warranted by the evidence here, and true onward"; (iii)✓ monotone
over arbitrary (branching) `R`. **Mismatches:** a *term-indexed family* `{t:−}`, not one
`◯` (natural collapse `◯X ≈ ∃t. t:X`); standard LP semantics is **classical**-based.

### 2. Nucleus / LT-topology forcing over the effective topos — deepest *structural* fit
Since `◯` = nucleus = LT-topology, "`◯` over a realisability model" **is** a local operator
`j` on the realisability tripos, evaluated by Kripke–Joyal forcing in the sheaf subtopos
`E_j`. A concrete stage-indexed, order-monotone version: **[VERIFIED, Nakata Def. 4.4]**
forcing `j ⊩_ℙ φ` is parametrised by a nucleus `j` and an internal subposet `ℙ` of local
operators, with

> `j ⊩_ℙ (φ → ψ)  :=  ∀ k ≥_ℙ j. ((k ⊩_ℙ φ) → (k ⊩_ℙ ψ))`

— the **nodes are themselves nuclei**, ordered by refinement, with Kripke monotonicity.
**[VERIFIED, Yamada 2602.23086]** builds *effectful toposes* from evidenced frames;
LT-topologies correspond to *computational oracles*; the `¬¬`-sheaf subtopos ≅ the
CPS-effectful (classical-realisability) model. **[VERIFIED abstract, Lee–van Oosten
1201.2571]** (+ Kihara 2106.03061, UNVERIFIED) **classify** the local operators (=
candidate `◯`'s) on the effective topos via *sights* (well-founded trees). Fit: (i)✓
realisers `n ⊩ φ`; (ii)✓ `◯` = `j`-closure by forcing; (iii)✓ growth over stages/nuclei.
**Mismatch:** "world" = topos stage/nucleus, not obviously an agent's evidence state — the
epistemic reading is MY-INFERENCE.

### 3. Valliappan, proof-relevant possible-world semantics of *lax logic itself* — closest packaged artifact
**[VERIFIED, arXiv 2512.10779]** A proof-relevant frame `F = (W, R_i, R_m)`: `R_i`
reflexive-transitive ("increase in assumptions" = information growth), `R_m` a modal
accessibility with forward confluence, and lax modality `⟦◆A⟧w = Σ v. (w R_m v) × ⟦A⟧v`.
Worlds carry proof-relevant content (λ-terms = realisers); interpretation is monotone along
`R_i` via a transport `mon_P : w R_i w′ → P w → P w′`. Fit: **the single closest existing
artifact** — realiser-worlds + `◯`-at-world + monotone branching preorder, for lax
specifically, machine-checked in Agda. **Mismatch:** a normalisation-by-evaluation
semantics, `◯` read as *proof-relevant possibility* over `R_m` (not "verified subject to
constraints") — though these coincide on F&M's `◯`.

### 4. Monad-parametrised realizability (EffHOL) — `◯` = strong monad against realisers
**[VERIFIED, arXiv 2506.09458]** A realizability translation HOL → EffHOL **parametrised by
a monad `T`**; propositions become specifications for *effectful* realisers; the monad is
the modality connecting propositions to their effectful realizations. Fit: (i)+(ii) strong
— realisers carry effects, `◯` = `T` against them; (iii) **absent** — a translation, not a
Kripke structure. Directly operationalises "`◯` = strong monad".

### 5. Constructive Kripke + realizability (the scaffold without a modality)
**[UNVERIFIED, Lipton 1992]** Kripke nodes over a poset each carrying realizability
structure — the base onto which `◯` = nucleus would be layered. **Prefer its intuitionistic
evidence variant:** **[VERIFIED, Marin–Padhiar–Shillito 2026, 2606.31884]** *intuitionistic*
justification logic with "modular models" fusing an evidence function with intuitionistic
Kripke machinery — the intuitionistic analogue of framework 1, hence the right **base
logic** for PLL.

### 6. van Benthem–Pacuit dynamic evidence logic — vocabulary for belief-growth
**[UNVERIFIED]** Evidence = neighbourhood families; distinguishes "has evidence for φ" from
"believes φ"; models evidence dynamics. Good for the branching-belief-growth *narrative*;
(i) weak (set-theoretic evidence, not realisers); classical base.

---

## Highest-value references to read first
1. **van Oosten, *Realizability* (2008)** — canonical effective topos / triposes /
   LT-topologies; home for "`◯` = nucleus over realisers". *(UNVERIFIED — get the book.)*
2. **Nakata, *A j-translation with Kripke forcing relation* (2026, 2602.23218)** — literally
   forces a nucleus `j` at stages ordered by refinement (Def. 4.4); working template for
   evaluating `◯` at growing stages. *(VERIFIED.)*
3. **SEP *Justification Logic* §3 / Fitting 2005; then Marin–Padhiar–Shillito 2026
   (2606.31884)** — evidence-function-at-worlds with monotone evidence, and its
   *intuitionistic* version matching PLL's base. *(VERIFIED.)*
4. **Valliappan, *Lax Modal Lambda Calculi* (2026, 2512.10779)** — the one existing
   realiser-carrying possible-world model of lax, Agda-checked. *(VERIFIED.)*
5. **Lee–van Oosten, *Basic subtoposes of the effective topos* (2013, 1201.2571)** (+ Kihara
   2106.03061) — *which* nuclei/`◯`'s the effective topos supports (classification by
   sights). *(VERIFIED abstract.)*

---

## Open questions / design choices for Matthew
1. **Realiser structure.** PCA (Kleene `K₁` — maximal generality, effective-topos machinery
   for free) vs typed λ-terms (Valliappan/EffHOL — tighter Curry–Howard with `◯`-as-monad)
   vs justification terms (Fitting — named evidence `t`, the explicit "`t` warrants the
   belief" reading). PCA buys the LT-topology classification; justification terms buy the
   epistemic story.
2. **Source of branching.** Arbitrary poset/preorder (Lipton/Kripke) vs Grothendieck site
   with covers (sheaf-theoretic, matches `◯` = LT-topology exactly) vs Valliappan's two
   relations (`R_i` growth + `R_m` modal). Is branching *epistemic* (incomparable evidence
   states) or *geometric* (covers/constraints, à la F&M)?
3. **How `◯` reads against realisers.** (a) `◯M` realised by a realiser that `M` is
   **`j`-covered** here (nucleus/forcing — framework 2); (b) `◯M` = **`∃t. t:M`** (Fitting
   collapse — framework 1); (c) `◯M` = a **monadic value** `T⟦M⟧` (EffHOL/Moggi — framework
   4). These agree when `j` is the LT-topology induced by `T`, but differ in what the
   realiser *is*. Pick one as primitive.
4. **Classical vs intuitionistic base.** Standard Fitting/LP is classical; PLL is
   intuitionistic. Prefer Marin et al.'s intuitionistic modular models or the effective-topos
   internal logic. **This is where the paper's thesis bites:** Yamada's `¬¬`-sheaf collapse
   (2602.23086) is a concrete classical-belief-degenerates instance.
5. **Literally a subtopos `E_j ⊆ Eff`, or merely resembling one?** The former makes `◯ = j`
   with everything Kripke–Joyal forcing (and Lee–van Oosten/Kihara tell you which `◯`'s
   exist — ties to the assembly-tower thread); the latter is elementary and self-contained.
6. **Does monotone realisability give "increasing belief" for free? — the load-bearing
   check.** Yes for persistence (MY-INFERENCE). Open sub-question, and the **natural first
   thing to machine-check** for any soundness theorem: is `◯` inflationary and idempotent at
   *every* stage (nucleus laws holding locally) *and* stable under growth, or must
   stability-under-growth be imposed as a separate frame condition?

---

## Part II — relating the four presentations (follow-up, 2026-07-16)

*New sources reached: nLab, *Lawvere–Tierney topology* and *effective topos*.*

### The four are NOT one construction — three distinct `◯`-mechanisms
A common spine ("world-indexed `◯` over realisers/evidence"), but **three genuinely
different mechanisms**, coinciding only under explicit conditions:
- **(A) `◯` = LT-topology / nucleus** — definitional closure (effective topos); a monad iff lex + idempotent.
- **(B) `◯` = birelational possibility** over an extra accessibility `Rₘ` (Valliappan) — *not* an LT-topology.
- **(C) `◯` = `∃t. t:M`** over an evidence-term family with decoupled admissibility (Fitting).

**Monad ↔ LT-topology [VERIFIED, nLab].** On a topos, LT-topologies `j:Ω→Ω` ⟺ reflective
subtoposes ⟺ **left-exact idempotent monads**; the LT axioms are exactly `j⊤=⊤, jj=j,
j(x∧y)=jx∧jy`. So a strong monad induces an LT-topology **iff idempotent and left-exact** —
which Moggi's computational monads (state, continuations) deliberately are not. Every
LT-topology is a monad; not conversely (`LT ⊂ monads`).

**Nucleus = the propositional shadow [VERIFIED-standard + Nakata].** On a Heyting algebra
(a poset) a monad is a monotone inflationary `j`; in a poset `jja=ja` is **automatic**, so
every poset-monad is idempotent. The substantive extra condition is meet-preservation =
**left-exactness**. Hence
> **nucleus = lex idempotent monad on the poset = internal LT-topology on `Ω`.**
Sharp consequence: over **propositions** (a poset) idempotency of `◯` is *free* and only
meet-preservation is substantive; over **types/proofs** (EffHOL) idempotency is *not* free.
So **PLL's `◯` is precisely the lex-idempotent fragment of Moggi's monads** — which is why
belief needs `◯◯=◯`, a law Moggi's monads lack.

**Fitting ↔ realizability [clauses VERIFIED SEP §3; identification MY-INFERENCE].** The
evidence function `E(t,X)` is a possible-worlds combinatory-realizability predicate: the
application clause `E(s,X→Y)∩E(t,X)⊆E(s·t,Y)` is the Kleene/PCA realizer clause for `→`, but
**admissibility is decoupled from truth**. The forgetful `◯M=∃t.t:M` is a genuine
translation; its hard inverse is the **realization theorem** (S4↔LP). A **lax-`◯` realization
theorem** (splitting `◯` as LP splits `□`) was not found — **OPEN**.

**Valliappan ↔ presheaf forcing [MY-INFERENCE, grounded].** A proof-relevant Kripke model
over `(W,Rᵢ)` is a covariant functor to `Type` = a presheaf; forcing = Kripke–Joyal
semantics with λ-terms as realisers. **But** `⟦◆A⟧w = Σv.(w Rₘ v)×⟦A⟧v` uses an *extra* `Rₘ`
— a **birelational** modality (Simpson / Alechina–de Paiva), not an LT-topology. So "`◯` =
nucleus" is here a **theorem to prove from frame conditions**, not definitional.

| pair | translation | sourced vs conjecture |
|---|---|---|
| strong monad ↔ LT-topology | restriction: monad→LT iff idempotent+lex; every LT is a monad | SOURCED (nLab) |
| nucleus (propositional `◯`) ↔ LT-topology on `Ω` | equivalence | SOURCED (nLab; Nakata) |
| Fitting `E(t,X)` ↔ combinatory realizability | yes, with decoupled admissibility | clauses SOURCED; identification MY-INFERENCE |
| Fitting `◯=∃t.t:` ↔ modal forcing | erase (easy) / realization (hard) | SOURCED for S4/LP; **lax-`◯` OPEN** |
| Valliappan λSL ↔ Kripke–Joyal forcing | presheaf over `(W,Rᵢ)`; `◯` birelational | MY-INFERENCE |
| Valliappan `◯` ↔ nucleus/LT | conditional (frame conditions force `◆` idempotent+lex) | MY-INFERENCE (proof obligation) |

### Metatheory vs object theory [VERIFIED]
The claim "classical vs intuitionistic is metatheoretic, not about PLL" is **half right**:
- **[VERIFIED, nLab effective topos]** The effective topos is built in **classical ZFC** yet
  its internal logic is **intuitionistic** — modelling intuitionistic PLL needs *no*
  constructive metatheory. *An intuitionistic `◯` is free over a classical metatheory — this
  is the true metatheoretic content.*
- **BUT the object logic is fixed at the object level by two independent dials:** (i) the
  **realizer structure** — Kleene/λ → intuitionistic; Krivine/`call-cc` → classical (realizes
  Peirce) [VERIFIED-standard]; (ii) the **chosen nucleus** — `id` keeps the base, `¬¬` forces
  Boolean [VERIFIED, Yamada: `¬¬`-sheaf topos = CPS/classical realizability]. Neither is
  inherited from the metatheory.

**Restatement:** *an intuitionistic `◯` can be modelled over a classical metatheory — that
freedom is metatheoretic; but whether belief lives in a Heyting vs Boolean algebra of
propositions is an object-level determination.* The **degeneracy thesis (`N(B)≅B` vs rich
`N(H)`) is OBJECT-level** — both the degenerate and rich `◯` are realizable over the *same*
classical metatheory, as different subtoposes/nuclei of one effective topos. Upshot:
**"classical belief = collapse to the `¬¬`/Boolean subtopos" can be made a theorem inside the
model** (Yamada's `¬¬`-instance is the witness).

### Local-nucleus-stability: automatic vs proof obligation [VERIFIED anchor]
**Anchor [VERIFIED, nLab]:** an LT-topology `j:Ω→Ω` is *by definition* an internal nucleus
`(j⊤=⊤, jj=j, j∧=∧∘(j×j))` **and** a natural transformation, so it commutes with restriction
— **stability under stage-growth = naturality**.
- **LT-topology (A): AUTOMATIC/DEFINITIONAL** — nucleus laws = LT axioms; stability =
  naturality. Only *exhibiting* a `j` remains (Lee–van Oosten/Kihara enumerate which exist).
- **Monad/EffHOL: stability AUTOMATIC; nucleus laws PARTIAL** — `η` gives inflation, `μ` gives
  `◯◯→◯`, but **idempotency (`μ` iso) and meet/lex** are obligations. *On propositions
  idempotency is free; on types both remain.*
- **Valliappan/Lipton hand-built Kripke (B): GENUINE OBLIGATION on both** — per-world nucleus
  laws need `Rₘ` conditions (forward confluence); **`Rᵢ`-stability** is a monotonicity lemma
  needing `Rₘ`–`Rᵢ` compatibility. **This is where soundness lives.**
- **Fitting evidence: OBLIGATION** — inflation needs a constant specification, idempotence the
  proof-checker `!`, meet a pairing combinator; **stability = evidence-monotonicity, imposed
  as a model axiom**.

**One-line verdict:** `◯` is a stable nucleus *for free* only where it is **defined** as one
(LT-topology). Wherever `◯` is **derived** — monadic, birelational, or evidential — at least
idempotency and meet/lex become obligations, and the hand-built Kripke case adds stability.

### New design questions
1. **Central fork:** `◯` **primitive-as-nucleus/LT** (obligations vanish, but you inherit the
   effective topos's *fixed menu* of nuclei — Lee–van Oosten/Kihara) vs **primitive-as-
   birelational/monadic** (design freedom, but you owe idempotency + lex + stability).
2. **Lax-`◯` realization theorem?** Does PLL's `◯` split into intuitionistic justification
   terms (Marin et al. base) as S4's `□` splits into LP terms? If yes, evidence and nucleus
   presentations are *provably* inter-translatable; else only loosely analogous. **OPEN.**
3. **Do you want idempotency?** Belief-as-nucleus *requires* `◯◯=◯`; Moggi's monads are
   deliberately non-idempotent. State PLL's `◯` = the idempotent-lex fragment of Moggi's
   monads as a positive design commitment.
4. **Instantiate the degeneracy thesis** as the `¬¬`-subtopos inside the model (Yamada):
   "classical belief = double-negation collapse" as a theorem, not a slogan.
5. **If hand-building a Kripke-realizability soundness proof** (per the mandate), the
   **`Rₘ`–`Rᵢ` compatibility / forward-confluence** lemma validating `◯◯→◯` + monotonicity is
   the single load-bearing obligation to formalize first — *free* only in the LT/monad routes.
