I have everything I need, verified against both the actual papers (Lindley–Stark PDF extracted verbatim; Doczkal AFP; Lindley 2007; ADHS 2001; BDCF 2004; BBdP 1998; surjective-pairing confluence facts) and the actual repo files. Let me write the structured report.

---

# Rewrite theory for Moggi's computational metalanguage — η-extensions for the PLL Lean development

Scope note: I read the three named files in full (`PLLTerms.lean`, `PLLStrongNorm.lean`, `PLLTopTop.lean`) plus `PLLNormal.lean`, `PLLReducibility.lean`, and `PLLTactics.lean`. I extracted the Lindley–Stark paper's rule figures verbatim (via `pdftotext` on the author's PDF). Claims I could not fully pin to a primary source are marked **[UNVERIFIED]**.

## 1. Monad-law inventory — what Lindley–Stark's SN proof actually covers

**Answer: β + η + assoc, for every connective — not β-only, not β+assoc.** This is stronger than the task's framing assumed, and it is the single most important finding.

The reduction relation of λ_ml is given in **Figure 1** of Lindley & Stark, *Reducibility and ⊤⊤-lifting for Computation Types* (TLCA 2005). Reproduced verbatim from the PDF:

```
Reductions
→.β                     (λx.M)N            −→  M[x := N]
→.η                     λx.M x             −→  M                       (x ∉ fv(M))
×.βi                    πi(⟨M1, M2⟩)       −→  Mi                      (i = 1,2)
×.η                     ⟨π1(M), π2(M)⟩     −→  M
T.β                     let x ⇐ [N] in M   −→  M[x := N]
T.η                     let x ⇐ M in [x]   −→  M
T.assoc                 let y ⇐ (let x ⇐ L in M) in N
                                           −→  let x ⇐ L in (let y ⇐ M in N)   (x ∉ fv(N))
```

The body text confirms scope (§2, line-for-line): *"These extend those for the simply-typed lambda-calculus with three reductions that act only on terms of computation type: T.β, T.η and T.assoc."*

So **all three η-rules (→.η, ×.η, T.η) are in their oriented reduction relation, and the SN theorem (Thm. 10) covers the full βη+assoc system.** In the dictionary of this repo:

| law | our name | in `Step`? | Lindley–Stark |
|---|---|---|---|
| left unit (monadic β) | `bindVal` | yes | T.β |
| associativity | `bindAssoc` | yes | T.assoc |
| **right unit (η_◯)** | — | **no** | **T.η** (present) |
| function β | `beta` | yes | →.β |
| **function η** | — | **no** | →.η (present) |
| product β | `fstPair`/`sndPair` | yes | ×.βi |
| **surjective pairing (×η)** | — | **no** | ×.η (present) |
| sum β | `caseInl`/`caseInr` | yes | — (added in §4.1) |

The repo currently mechanises the **β + assoc** fragment (`Step` in `PLLTerms.lean` lines 182–234; the seven redex rules are `beta, fstPair, sndPair, caseInl, caseInr, bindVal, bindAssoc`). **No η-rule of any kind is present** — confirmed by grep across `LaxLogic/*.lean` (the only "η" hits are prose in `PLLNormal.lean` and doc comments). So relative to the Lindley–Stark target, the repo is **missing exactly the three η-rules**, and the SN machinery it already contains was designed by people who had η in mind (Fig. 2 orients T.η through the *same* rewrite context `let x ⇐ M in −` as the pole).

**Crucial corollary for Q2:** the ⊤⊤-technique in `PLLTopTop.lean` is not merely *compatible* with T.η — Lindley–Stark's own proof already discharges it, and it is nearly free. See §2.

## 2. Adding η_◯ (`bind t (val #0) ↝ t`): SN and confluence

### 2a. SN — yes, and the proof is a two-line extension

Lindley–Stark's principal lemma is **Lemma 7**, which is *literally* the repo's `principal` (`PLLTopTop.lean` L671–722). Their proof enumerates the reducts of `K @ (let x ⇐ [P] in N)`; the **T.η case** is handled thus (verbatim):

> *"T.η when N = [x], giving K @ [P]. But K @ [P] = K @ (N[x := P]), which is again SN by hypothesis."*

That is the whole argument. When the body `N` happens to be `[x]` (in our notation `u = val #0`), the T.η-contractum of `bind (val P) (val #0)` is `val P`, and plugging it, `K.plug (val P)`, is *definitionally equal* to `K.plug (u.subst1 P)` because `u.subst1 P = (val #0).subst1 P = val P`. So the η-reduct reuses the **existing SN hypothesis `hKu`** with no change of measure at all — it is even easier than the assoc case (which needs the stack-length component of the lexicographic triple; η needs nothing).

Concretely, the repo's SN proof survives adding `η_◯` with these edits, all mechanical:

- **`PLLTerms.lean`** — add one constructor to `Step`:
  `| bindEta {Γ φ} (t : Tm Γ (somehow φ)) : Step (.bind t (.val (.var .here))) t`
  (Note the body is fixed to `val #0`; there is no premise. Type-correct: `bind : Tm Γ (◯φ) → Tm (φ::Γ)(◯φ) → Tm Γ (◯φ)`, body `val (var here) : Tm (φ::Γ)(◯φ)`, result `Tm Γ (◯φ)`. ✓)
- **`Step.rename` / `Step.subst` / `Step.rename_reflect`** (L146–342): add a `bindEta` arm. Renaming/substituting `bind t (val #0)` gives `bind (t·ρ) (val #0)` since `(val #0)` is invariant under `lift ρ` and `lift σ` (both fix `#0` and `val` commutes) — so the arm is `⟨t·ρ, .bindEta _, rfl⟩`. This is the one **new lemma obligation**: `(val (var here)).rename (Ren.lift ρ) = val (var here)` and the `subst` analogue, both `rfl`/one-liners.
- **`plug_step_cases`** (L606–642): the classification of steps of `K.plug X`. Currently the innermost-frame head-steps are `bindVal` and `bindAssoc`; add a **fifth alternative** for when `X` steps by `bindEta` *and* when the interface frame `cons u₀ K₀` meets a `val`-headed `X` with `u₀ = val #0`. Actually cleaner: η is a step of `X` itself (`X = bind t (val #0) ↝ t`), so it falls under the existing "X steps" branch `⟨X', hX, rfl⟩` — **no new alternative needed** in `plug_step_cases`; only the *consumers* that `cases hX` must gain a `bindEta` arm.
- **`principal`** (L687–722): in the `rcases … | ⟨X', hX, rfl⟩` branch, the `cases hX` currently covers `bindVal | bindCong₁ | bindCong₂`. Add `| bindEta => exact hKu` (the reduct `K.plug (val s)` — wait: here `X = bind (val s) u`; an η-step needs `u = val #0`, giving `K.plug (val s) = K.plug (u.subst1 s) = hKu`'s subject). One line.
- **`sn_plug_neut`** (L882–905), **`SRed.step`** (L810–832, `somehow` case), **`SRed.cr3`** (`somehow` case, L966–975): each already quantifies "for all reducts"; the extra reduct is absorbed by the same `hred`/plug reasoning. Expect ~1 arm each.
- **`not_step_of_nf`**, **`nf_or_step`**, **`Tm.step?`/`bindRedex?`**, **`Nf` grammar** in `PLLNormal.lean`: see §5 — the normal-form grammar must change, because `bind t (val #0)` is currently `Nf` (via `Nf.bind` with neutral `t`) but would become a redex.

**Estimated effort: small** — this is the easiest of the four η-rules by a wide margin, precisely because the repo's `principal`/⊤⊤ scaffold was built to Lindley–Stark's spec and their spec already includes T.η.

### 2b. Critical pairs (worked explicitly)

The two overlaps the task names, plus the third that actually matters:

**(i) η_◯ vs T.assoc at `bind (bind r s) (val #0)`.** Two redexes:
- η_◯ (outer): `bind (bind r s) (val #0) ↝ bind r s`.
- assoc: `bind (bind r s) (val #0) ↝ bind r (bind s (val #0 ↑))`. Now `(val #0)↑ = (val #0).rename skip1 = val #0` (skip1 fixes `#0`; `val` commutes). So the assoc reduct is `bind r (bind s (val #0))`, whose inner `bind s (val #0)` is itself an η_◯-redex `↝ bind r s`. **Joinable**, converging on `bind r s`. This is exactly Lindley–Stark's continuation-level observation (§3.1): under T.η at position i, `|K'| = |K|−1`; both paths land on the shorter stack. ✓ **local confluence holds here.**

**(ii) η_◯ vs monadic β at `bind (val t) (val #0)`.** Two redexes:
- η_◯: `↝ val t`.
- T.β (`bindVal`): `↝ (val #0).subst1 t = val t`. **Trivially joinable — identical reducts.** ✓

**(iii) η_◯ vs congruence in the body — the *only* subtle pair.** `bind t (val #0)` where the *body* `val #0` cannot step, but if we ever allowed the body to be more than `#0`… With the body pinned to `val (var here)` there is **no non-trivial overlap with body-congruence**, because `val #0` is a normal, closed-under-nothing term. Had we instead written η as the more permissive Lindley–Stark T.η (`let x ⇐ M in [x]` for the specific bound `x`, i.e. our `bind t (val #0)`), the two are the same rule. Good — pinning the body is what keeps this clean and is the standard "restricted η" orientation. **[Note]** A *generalised* right-unit `bind t u ↝ t` whenever `u ≡ val #0` up to reduction would reintroduce a genuine η/congruence critical pair; do **not** do that — keep `u` syntactically `val #0`.

**Technique verdict.** You do **not** need η-postponement or a separate "SN of η alone + commutation" argument. Lindley–Stark's ⊤⊤ candidates already absorb T.η directly (the contractum-coincidence above), so the *extended ⊤⊤ candidates route* — which the repo already implements — is the right one. Confluence of β+η_◯+assoc then follows from **local confluence (all three critical pairs above join) + SN**, via Newman's lemma. The repo has SN machinery but **no confluence development yet** (grep shows no `confluent`/`diamond`/`Newman`/local-confluence lemmas); adding η_◯ does not obstruct a later Newman-based confluence proof and, per the critical-pair analysis, is confluence-safe.

## 3. Function/product/sum η — per-rule assessment and recommendation

### 3a. Function η (`λx. t x ↝ t`, x ∉ fv t) — **safe; add it**
Present as →.η in Lindley–Stark; their SN proof covers it (rewrite context `−`, active term `λx.Mx`). For a **typed, intrinsically-typed** calculus this is unproblematic: SN is standard, and confluence care is minor (the classic β/η critical pair `(λx. t x) s` joins). The only real friction in an intrinsically-typed de Bruijn setting is that the rule's premise "x ∉ fv" becomes "the body is `app (t↑) #0` for some `t` not mentioning `#0`", i.e. `η_→ : lam (app (t.weaken) (var here)) ↝ t`. That is expressible with the repo's `weaken`/`skip1` API and mirrors how η_◯ pins its body. **Recommendation: add η_→ to `Step′`.** Cost: comparable to η_◯ but with a slightly fiddlier reflect-lemma (must invert `app (t.weaken) #0`).

### 3b. Surjective pairing / product η (`⟨π₁ t, π₂ t⟩ ↝ t`) — **add it (typed), but know the folklore trap**
Present as ×.η in Lindley–Stark. The famous danger — **untyped λ-calculus with surjective pairing is not confluent** (Klop–de Vrijer: the equational theory λπ has systems that fail Church–Rosser; Klop's counterexample) — **does not apply here**, because our calculus is **typed**. The verified literature is explicit: *"The λ-calculus extended with surjective pairing is not confluent in the untyped case, and confluent in the typed case."* (multiple sources incl. Curien–Di Cosmo). For the simply-typed calculus with products and terminal object, confluence of the extensional reduction is a solved problem (Curien–Di Cosmo, *A confluent reduction for the λ-calculus with surjective pairing and terminal object*, JFP; the subtlety is only the **terminal/unit type η**, which PLL does not have — there is no `⊤`/unit constructor in `Tm`). SN with ×.η is standard and Lindley–Stark cover it.
One orientation nuance: ×.η as a *reduction* `⟨π₁ t, π₂ t⟩ ↝ t` needs the scrutinee of both projections to be *syntactically identical* `t`; the critical pair with ×.β (`π₁⟨a,b⟩`) joins. **Recommendation: add ×η to `Step′`.** Cost: moderate; the reflect-lemma must recognise `pair (fst t) (snd t)`.

### 3c. Sum η + commuting conversions — **do NOT add to `Step`; treat equationally (NBE)**
This is the genuinely hard case and the recommendation is to **keep it out of the oriented `Step′`**.

The problem is threefold and well-documented:
- **Sum η is not a simple local rule.** The general η-axiom for sums (`case e of inl x ⇒ C[inl x] | inr y ⇒ C[inr y] = C[e]`, roughly) is *not* confluent as a naive rewrite and interacts with **commuting conversions** (pushing eliminators through `case`). Lindley's own *Extensional Rewriting with Sums* (TLCA 2007) exists precisely because this is hard: he must **decompose the general η axiom into several simpler axioms** and prove only *weak* normalisation and *confluence-modulo-∼* (an equivalence relation), not plain SN+CR, for the full system. That is far more machinery than β+η_◯+assoc.
- **The decision problem was historically solved semantically, not by rewriting.** Altenkirch–Dybjer–Hofmann–Scott, *NBE for typed λ-calculus with coproducts* (LICS 2001), decide equality for strong binary sums via a **sheaf model / NBE**, "inverting the interpretation of the syntax into a suitable sheaf model" — explicitly *because* a good confluent term-rewriting system was not available. Balat–Di Cosmo–Fiore (POPL 2004), *Extensional normalisation and type-directed partial evaluation for typed λ-calculus with sums*, likewise solve it via **Grothendieck logical relations + TDPE**, calling strong sums an "open problem" for the rewriting style.
- **Commuting conversions are avoidable for β-normalisation but not for extensionality.** The repo already made the correct design call for the *β/assoc* system: `PLLNormal.lean`'s doc says *"case and abort with neutral scrutinee are neutral … there are no commuting conversions in Step"* and `Ne.case` is neutral. That is fine for β-SN. But a genuinely *extensional* sum theory (needed for, e.g., deciding `A+B` equalities) requires either commuting conversions or an NBE detour.

**Recommendation:** For the PLL mechanisation, add **only** the βη rules that are confluent-safe and SN-preserving as *oriented reductions* — function η, product η, monad η_◯ — to `Step′`. Handle **sum extensionality as an equational theory decided separately by normalisation-by-evaluation** (or leave it out entirely if the project's goal is proof-term SN + cut-elimination rather than deciding the full extensional equational theory). Reasons: (i) sum-η needs modulo-∼ confluence and defeats the clean `Acc`-based SN the repo is built on; (ii) the repo's whole `Nf`/`Ne` grammar and `⊤⊤` scaffold assume no commuting conversions; retrofitting them is a research-grade effort disproportionate to a lax-logic proof-term calculus; (iii) if decidability of extensional PLL equality is ever wanted, NBE (ADHS-style) is the proven route and is *orthogonal* to the `Step` reduction — it would live in a new file, not perturb `PLLTopTop.lean`.

## 4. Literature anchor points (verified)

- **Benton–Bierman–de Paiva, *Computational types from a logical perspective*, JFP 8(2):177–193, 1998.** The Curry–Howard origin the repo cites (PLL = their intuitionistic modal logic; ◯ = strong monad `T`). They give ND, sequent and Hilbert presentations and prove **strong normalisation and confluence** for the associated term calculus. **[Partially verified]** I confirmed authorship, venue, and that SN+confluence are claimed; I could *not* extract from the abstract-level sources whether their oriented system includes the monad-η rule or treats it equationally — **[UNVERIFIED which orientation of the monad laws they reduce vs. equate]**. Worth a direct check of their Fig. 3 if the exact orientation matters to you.
- **Moggi, *Notions of computation and monads*, Inf.&Comp. 1991 / *Computational λ-calculus and monads*, LICS 1989.** Source of λ_ml and λ_c; the two extra λ_c rules (`let.1 : PM ↝ let x⇐P in xM`, `let.2 : VQ ↝ let y⇐Q in Vy`) are quoted verbatim in Lindley–Stark §4.3 and are **not** part of λ_ml — relevant if you ever move from the metalanguage to the computational λ-calculus proper.
- **Sabry–Wadler, *A reflection on call-by-value*, ICFP 1996 / TOPLAS 1997** (reflection between λ_c/λ_ml and monadic normal forms). **[UNVERIFIED — not fetched this session]**; flagged as the standard reference for the λ_c ↔ λ_ml correspondence and monadic normal forms, which is the natural home for "assoc-normal form = monadic normal form" that `PLLNormal.lean` already gestures at.
- **Filinski** (representing monads / *Representing layered monads*, POPL 1999; *Representing monads*, POPL 1994). **[UNVERIFIED — not fetched]**; the reflection/reification story relevant if NBE for ◯ is pursued.
- **Commutativity flag (important):** lax ◯ is a **strong monad but not commutative**. Any result that assumes a **commutative** monad (symmetric monoidal monad structure; the exchange law `let x⇐M in let y⇐N in P = let y⇐N in let x⇐M in P`) does **not** transfer to PLL. This rules out, e.g., the extra permutation equations of the *commutative* computational calculus and some of Hasegawa/Ohta's linear-effects results that presuppose commutativity. **The Lindley–Stark SN proof does NOT require commutativity** (their method is "independent of the nature of computations T"), so the repo is safe; but if you reach for decidability/normal-form results from the commutative-monad literature (e.g. certain NBE-for-effects papers), check the commutativity hypothesis first. **[Verified that commutativity is a real dividing line; specific Hasegawa citations not individually fetched — treat as UNVERIFIED at the paper level.]**
- **Existing mechanised SN for λ_ml with the commuting conversion:** **Doczkal & Schwinghammer**, *Formalizing a strong normalization proof for Moggi's computational metalanguage*, **LFMTP 2009**, Isabelle/HOL-Nominal; archived as AFP entry **`Lam-ml-Normalization`** ("Strong Normalization of Moggi's Computational Metalanguage", C. Doczkal). Verified abstract: it formalises **Lindley–Stark's ⊤⊤-lifting** with "stacks of elimination contexts", emphasising bound-variable handling, and explicitly features "a commuting conversion rule that rearranges the binding structure." Since it formalises the Lindley–Stark calculus, it covers **T.β + T.η + T.assoc** — but the abstract does not itemise rules, so "**includes T.η**" is inferred from "formalises Lindley–Stark", **[UNVERIFIED at the rule level]**; and it is the calculus **without sums** (Lindley–Stark handle sums only in prose §4.1, not in the mechanisation). The repo's own comment (`PLLTopTop.lean` L39–42) states this is the only prior ⊤⊤ mechanisation it knows of, and claims to be **the first in Lean and the first with sums + intrinsic typing** — consistent with what I found. No Coq/Agda mechanised λ_ml-with-η SN surfaced in the searches; **[UNVERIFIED — absence of evidence]**.

## 5. Recommended `Step′`, expected normal forms, risk list

### 5a. Recommended rule set for `Step′`
Keep the seven existing redex rules (`beta, fstPair, sndPair, caseInl, caseInr, bindVal, bindAssoc`) and all congruences, and **add three restricted η-reductions**, each with a syntactically pinned body so no η/congruence critical pairs arise:

```
η_→   :  lam (app (t.weaken) (var here))                  ↝  t        -- t : Γ ⊢ φ⇒ψ
η_×   :  pair (fst t) (snd t)                             ↝  t        -- t : Γ ⊢ φ∧ψ
η_◯   :  bind t (val (var here))                          ↝  t        -- t : Γ ⊢ ◯φ
```

**Exclude** sum-η and commuting conversions from `Step′`; if extensional-sum decidability is ever required, add a *separate* NBE module. This gives a system that is (conjecturally, pending the Newman proof) **SN + confluent**, matching Lindley–Stark's λ_ml-with-products-and-functions βη + assoc, extended with the repo's sum-β.

### 5b. Expected normal forms (relate to `PLLNormal.lean`'s `Nf`/`Ne`)
Adding the three η-rules **shrinks** the normal forms; the current `Nf`/`Ne` grammar (`PLLNormal.lean` L36–72) must be tightened at exactly three constructors:

- **`Nf.lam`** must forbid η-expanded bodies: a normal `lam b` must have `b` not of the form `app (t.weaken) #0`. In practice, η-long/η-short discipline — the cleanest target is **η-long (β-normal-η-long) forms**, where instead you require every neutral of function type to be *fully applied*. If you instead adopt η-short (contractive) NFs, add a side condition to `Nf.lam`.
- **`Nf.pair`** must forbid `pair (fst t) (snd t)` with the *same* neutral `t`: a normal `pair a b` is excluded when `a = fst t`, `b = snd t`. Again η-long is the tidy alternative (expand neutrals of product type to `pair (fst ·) (snd ·)`).
- **`Nf.bind`** (currently `Ne t → Nf u → Nf (bind t u)`, L69–71) must forbid `u = val #0`: the assoc-normal `bind`-chains stay right-nested with neutral scrutinees, but a trailing `bind t (val #0)` collapses. So `Nf.bind hn hf` gains the side condition `u ≠ val (var here)`.

The doc comment in `PLLNormal.lean` L14–16 ("normal `bind`-chains are forced to be right-nested with non-`bind`, non-`val` scrutinees — exactly the assoc-normal forms") remains accurate; η_◯ just additionally rules out the degenerate final frame. The **monadic/assoc-normal form** picture (Sabry–Wadler monadic normal form) is unchanged in shape.

Decision to make: **η-long vs η-short NFs.** η-long (expansionary) NFs are what NBE produces and are cleaner to *specify* but awkward to reach by the contractive `Step`; η-short (the reductions above) are what `Step′` naturally reaches. Recommend **η-short reductions with η-short NFs** to stay compatible with the existing `Acc`-based `Tm.step?`/`normalize` pipeline (`PLLTopTop.lean` L1287–1305), which is contractive.

### 5c. Risk list

1. **`step?` determinism & the total normaliser.** `Tm.step?` (`PLLStrongNorm.lean` L181–242) is a deterministic innermost strategy feeding `Tm.normalize` (`PLLTopTop.lean` L1287). Adding η redex-dispatch to `bindRedex?`/new `lamRedex?`/`pairRedex?` is straightforward, **but** η_× dispatch on `pair (fst t) (snd t)` requires deciding *syntactic equality of the two scrutinees* `t` — needs `DecidableEq (Tm …)` or a structural check. **Risk: medium** (decidable-equality plumbing for an intrinsically-typed indexed family can be fiddly).
2. **Reflect-lemma inversions.** `Step.rename_reflect` (L174–342) grows an arm per η-rule; η_→ and η_× arms must invert `app (t.weaken) #0` and `pair (fst t) (snd t)` *through renaming*, which is more delicate than η_◯'s `bind _ (val #0)`. **Risk: medium.** η_◯ alone is **low risk**.
3. **Confluence is not yet mechanised at all.** The repo proves SN but has **no** confluence/Newman/local-confluence development. The claim "β+η+assoc is confluent" rests on Newman + the critical-pair joins in §2b/§3; mechanising that is **net-new work** (a `local_confluence` lemma enumerating all critical pairs). **Risk: medium-high if confluence is a deliverable; zero if only SN is.**
4. **Sum-η scope creep.** If a stakeholder asks for "full extensional PLL," resist adding commuting conversions to `Step`. It breaks the neutral-`case` design, the `⊤⊤` candidate for sums, and SN-via-`Acc`. **Risk: high (design corruption)** — mitigate by routing extensional sums to a separate NBE artifact.
5. **Commutativity assumptions in cited results.** Do not import normal-form/decidability lemmas that silently assume a *commutative* monad; ◯ is non-commutative. **Risk: correctness (silent unsoundness) if unchecked.**
6. **`Nf` grammar / `progress` drift.** The three `Nf` tightenings must stay in exact lockstep with the three new `Step′` rules, or `not_step_of_nf`/`nf_or_step` (`PLLNormal.lean` L155–338, the `Nf ↔ stuck` characterisation) will break. Every η-rule needs matching arms in **both** directions of that equivalence. **Risk: medium (mechanical but pervasive — ~6 files touched).**
7. **[UNVERIFIED items to close before relying on them]:** (a) whether Benton–Bierman–de Paiva orient the monad-η as reduction or equation; (b) exact Doczkal rule list (infer T.η included, but confirm from the theory files if it matters); (c) Sabry–Wadler and Filinski specifics were not fetched this session; (d) precise Hasegawa citations on commutativity.

---

**Bottom line.** The task's premise that Lindley–Stark cover "β+assoc" understates them: they cover **βη+assoc including the monad right-unit T.η**, and their principal lemma discharges T.η essentially for free (contractum coincides with the β-plug). Adding **η_◯** to the repo's `Step` is therefore low-risk and well-supported by the existing `PLLTopTop.lean` scaffold. **η_→** and **η_×** are also SN- and confluence-safe in this typed setting (surjective pairing's confluence trouble is untyped-only) and worth adding. **Sum-η + commuting conversions** are the hard case — keep them out of `Step′` and, if ever needed, decide them by NBE (ADHS 2001 / Balat–Di Cosmo–Fiore 2004) in a separate module.

Sources:
- [Lindley & Stark, *Reducibility and ⊤⊤-Lifting for Computation Types*, TLCA 2005 (PDF)](https://homepages.inf.ed.ac.uk/stark/reducibility.pdf) — Figs. 1–2 quoted verbatim
- [Springer record for the above](https://link.springer.com/chapter/10.1007/11417170_20)
- [Lindley, *Extensional Rewriting with Sums*, TLCA 2007](https://homepages.inf.ed.ac.uk/slindley/papers/sum.pdf)
- [Doczkal & Schwinghammer, *Formalizing a strong normalization proof for Moggi's computational metalanguage*, LFMTP 2009 (PDF)](https://www.ps.uni-saarland.de/Publications/documents/Doczkal_Schwinghammer_09.pdf) and [AFP entry `Lam-ml-Normalization`](https://www.isa-afp.org/entries/Lam-ml-Normalization.html)
- [Altenkirch, Dybjer, Hofmann, Scott, *NBE for typed λ-calculus with coproducts*, LICS 2001](https://people.cs.nott.ac.uk/psztxa/publ/lics01.pdf)
- [Balat, Di Cosmo, Fiore, *Extensional normalisation and TDPE for typed λ-calculus with sums*, POPL 2004](https://www.dicosmo.org/Articles/2004-BalatDiCosmoFiore-Popl.pdf)
- [Benton, Bierman, de Paiva, *Computational types from a logical perspective*, JFP 1998](https://www.semanticscholar.org/paper/Computational-Types-from-a-Logical-Perspective-Benton-Bierman/4111588f0d60ed2557a068598f75768db0fe3b00)
- Surjective pairing confluence (typed vs untyped): [Curien & Di Cosmo, JFP](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/confluent-reduction-for-the-calculus-with-surjective-pairing-and-terminal-object/325956525D5F9286604E8BA3C197AFA0), [Klop–de Vrijer, *Unique normal forms for λ-calculus with surjective pairing*](https://www.sciencedirect.com/science/article/pii/089054018990014X)

Repo files read (absolute paths): `/Users/matthew/Lean/Sources/lax-logic-in-lean/.claude/worktrees/g4ill/LaxLogic/PLLTerms.lean`, `.../PLLStrongNorm.lean`, `.../PLLTopTop.lean`, `.../PLLNormal.lean`, `.../PLLReducibility.lean`, `.../PLLTactics.lean`.

🕒 2026-07-09 (BST)
— Opus 4.8 (1M context) · effort unknown
