# Second-order propositional lax logic: survey and design memo

*Written 2026-08-09. Status: survey + design proposal. Nothing in §3 is machine-checked
unless explicitly said to be; everything is labelled PROVED / REFUTED / OPEN / CONJECTURED /
DERIVABLE-BY-HAND.*

*Verification discipline: every citation in §5 carries a status. CONFIRMED means the
bibliographic data was read off a publisher record, DOI record, Project Euclid / arXiv page,
or a fetched PDF. SEMI-VERIFIED means the item is certainly real and the core data confirmed,
but one field (usually page range) came from a secondary listing. UNVERIFIED means I could not
confirm it and it must not be cited as fact. No page numbers or theorem numbers are invented.*

---

## 0. Executive summary

1. **Uniform interpolation *is* the Pitts-style interpretation of second-order propositional
   quantification.** This is not an analogy: Pitts' 1992 theorem is literally stated as an
   interpretation of IPC2 in IPC. Matthew's observation is the received view of the subject.
2. **Propositional lax logic already has uniform interpolation** — Iemhoff, *Proof Theory for
   Lax Logic* (2024), proof-theoretically, from a cut-free terminating sequent calculus whose
   ◯-rules are exactly the `circL`/`◯R` pair the project's `PLLFocused.lean` implements. So the
   Pitts-style quantifiers for PLL are known to exist; the project's contribution is a
   *construction* and a *machine-checked* one, not an existence result.
3. **Pitts-style quantifiers and genuine (Kripke-semantic) second-order quantifiers are
   different objects for IPC**, and provably so. Połacik 1998 separates Pitts' quantifiers from
   the topological interpretation; Kremer 1997 shows the Kripke-semantic second-order IPC is
   recursively isomorphic to full second-order classical logic; Skvortsov 1997 shows it is not
   recursively axiomatisable. The Pitts image is decidable. They cannot coincide.
4. **Second-order propositional lax logic does not exist in the literature.** Exhaustive
   searching (queries logged in §5.7) returns nothing. A dblp full scan of `lax logic` contains
   no second-order entry. Valliappan (CSL 2026) explicitly lists "extensions of these calculi to
   second-order quantification and polymorphism" as *further work*. The gap is real.
5. **But there is a near-miss that must be engaged with: Aczel's Russell–Prawitz modality.**
   In IPC2, `Jφ := ∀p((φ→p)→p)` *is* a lax modality (Aczel 2001, in an MSCS special issue
   edited by Fairtlough, Mendler and Moggi). Any novelty claim must be stated against it.
6. **The non-collapse is easy and sharp** (§3.4): in PLL2, `Jφ ⊢ ◯φ` but `◯φ ⊬ Jφ`, because
   `J⊥ = ∀p.p ≡ ⊥` while `◯⊥` is satisfiable — F&M's fallible-world countermodel, already
   machine-checked in this repository (`LaxLogic/PLLFrames.lean`). So `◯` is a *primitive* worth
   adding: it is strictly weaker than the strongest second-order-definable lax modality.
7. **And there is a positive definability result** (§3.4): restricting the quantifier to
   ◯-fixpoints, `◯φ ⊣⊢ ∀°p((φ→p)→p)` exactly. This is the propositional shadow of
   Møgelberg–Simpson's `!B = ∀X.(B→X)→X` with `X` ranging over computation types. It says PLL2
   has two natural quantifier sorts and only the restricted one defines ◯.
8. **Recommended name: PLL2** (spelled out: *second-order propositional lax logic*). Free in
   the literature; follows the IPC2 / LL2 / S4₂ convention. **Do not use QLL** — taken by
   Fairtlough–Walton and Goldblatt for *first-order* quantified lax logic. **Do not use SLL** —
   taken by soft linear logic (Lafont 2004).
9. **The four LJF obligations are exactly the four quantifier rules** (§3.7): `eSound` = ∃-intro,
   `eMin` = ∃-elim, `aSound` = ∀-elim, `aMin` = ∀-intro. One discrepancy shows up under this
   reading and is worth checking: the repository's A2 carries `∃p(Γ)` as an extra hypothesis,
   which plain ∀-intro does not need.
10. **Obstruction check: PLL resembles the succeeding cases, not the failing ones.** UI fails for
    K4 and S4 (transitivity of the *accessibility* relation duplicating context); it holds for
    K, T, KD, GL, Grz, IPC, iSL and — by Iemhoff — PLL. PLL's ◯ is monotone with no negative
    introspection, its L◯ rule consumes rather than duplicates, and its ∨-free fragment is
    locally finite (Bezhanishvili et al. 2021 on nuclear implicative semilattices). Every
    indicator points the succeeding way.

---

## 1. Second-order propositional intuitionistic logic

### 1.1 Pitts' theorem, stated precisely

> **A. M. Pitts, "On an interpretation of second order quantification in first order
> intuitionistic propositional logic", *The Journal of Symbolic Logic* 57(1):33–52, 1992.**
> DOI 10.2307/2275175. [CONFIRMED]

The theorem, in Pitts' own framing (abstract, read at source): for each propositional variable
`p` and each formula `φ` there is a formula `A p φ`, effectively computable from `φ`, containing
only variables `≠ p` occurring in `φ`, such that for all `ψ` not involving `p`,

    ⊢ ψ → A p φ    iff    ⊢ ψ → φ.

Dually for the existential. The two operations satisfy the four characteristic laws

    ⊢ φ → ∃p φ                          (∃-intro)
    if ⊢ φ → ψ and p ∉ ψ then ⊢ ∃p φ → ψ  (∃-elim)
    ⊢ ∀p φ → φ                          (∀-elim)
    if ⊢ ψ → φ and p ∉ ψ then ⊢ ψ → ∀p φ  (∀-intro)

i.e. `∃p φ` is the **strongest** `p`-free consequence of `φ` and `∀p φ` is the **weakest**
`p`-free antecedent for `φ`. Pitts' abstract then draws the conclusion this memo is about:
*"quantification over propositional variables can be modelled in IpC, and there is an
interpretation of the second order propositional calculus IpC2 in IpC which restricts to the
identity on first order propositions."*

Note that ∃-intro in the *substitution* form — `⊢ φ[χ/p] → ∃p φ` for arbitrary `χ` — is a
consequence, not an extra axiom: `∃p φ` is `p`-free, so substituting `χ` for `p` in `⊢ φ → ∃p φ`
gives it directly, using only admissibility of substitution. The same argument gives
`⊢ ∀p φ → φ[χ/p]`. This matters in §3.4.

### 1.2 What is and is not conservative

Write `(−)°` for Pitts' translation of IPC2-formulas into IPC-formulas.

* **Conservativity of the second-order *calculus* over IPC: YES.** Since `(−)°` is the identity
  on first-order formulas and IPC2 ⊢ φ implies IPC ⊢ φ°, any first-order theorem of IPC2 is a
  theorem of IPC. [Immediate corollary of Pitts 1992.]
* **Faithfulness of `(−)°`: NO.** `(−)°` is computable and IPC is decidable, so
  `{φ : IPC ⊢ φ°}` is decidable; IPC2 is undecidable (§1.3). Hence the inclusion
  `IPC2 ⊆ {φ : IPC ⊢ φ°}` is strict. [OBSERVATION — an immediate consequence of the cited
  results, not itself a citable theorem. I did not find it stated in this form in a source, so
  treat it as folklore-obvious rather than attributable.]
* **Agreement with impredicative second-order semantics: NO.** See §1.5.

The correct slogan is therefore: *Pitts' quantifiers give a sound, effective, but non-faithful
interpretation of second-order syntax inside first-order syntax, and the propositional fragment
is conservative.* They are **not** a semantics for second-order quantification.

### 1.3 Full IPC2 with impredicative comprehension

The system: IPC plus `∀p φ`, `∃p φ` with the standard natural-deduction rules and full
comprehension (arbitrary formulas may instantiate a quantifier, including formulas containing
the quantifier being instantiated).

* **D. M. Gabbay, "On 2nd order intuitionistic propositional calculus with full comprehension",
  *Archiv für mathematische Logik und Grundlagenforschung* 16:177–186, 1974.** [SEMI-VERIFIED:
  title/journal/volume/pages/year confirmed from search results, publisher record not fetched.]
* **S. K. Sobolev, "The intuitionistic propositional calculus with quantifiers",
  *Matematicheskie Zametki* 22:69–76, 1977** (Russian; English translation in *Mathematical
  Notes*). Undecidability of IPC2. [SEMI-VERIFIED — volume/pages from search results.]
* **M. H. Löb, "Embedding first order predicate logic in fragments of intuitionistic logic",
  *The Journal of Symbolic Logic* 41(4):705–718, 1976.** [CONFIRMED via Project Euclid.] The
  translation route to undecidability.

The standard summary in the literature is that there are essentially two proofs of
undecidability, a semantic one (Gabbay, Sobolev) and one via Löb's translation from first-order
logic. [The attribution split is reported in secondary sources; I did not read either primary
paper, so treat the split as SEMI-VERIFIED.]

**Curry–Howard.** IPC2 is the type system of Girard–Reynolds System F: provability in IPC2 is
inhabitation in F. Two directly relevant references:

* **M. H. Sørensen and P. Urzyczyn, "A syntactic embedding of predicate logic into second-order
  propositional logic", *Notre Dame Journal of Formal Logic* 51(4):457–473, 2010.**
  DOI 10.1215/00294527-2010-029. [CONFIRMED via Project Euclid.] A syntactic (proof-theoretic)
  route to the undecidability, replacing the semantic arguments.
* **M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, Studies in Logic
  and the Foundations of Mathematics 149, Elsevier, 2006.** [SEMI-VERIFIED — series/volume/year
  from standard listings; publisher record not fetched.] The textbook treatment of IPC2 ↔ F.

### 1.4 Kripke-semantic (genuinely impredicative) second-order IPC

Here `∀p` ranges over *all* admissible propositions of a Kripke model — all upward-closed
subsets of the frame — rather than over the formulas of a language. This is a different logic.

* **P. Kremer, "On the complexity of propositional quantification in intuitionistic logic",
  *The Journal of Symbolic Logic* 62(2):529–544, 1997.** DOI 10.2307/2275545. [CONFIRMED.]
  The Kripke-semantic system (Kremer's `Hπ+`) is **recursively isomorphic to full second-order
  classical logic**. In particular it is not arithmetical, hence not recursively axiomatisable.
* **D. Skvortsov, "Non-axiomatizable second order intuitionistic propositional logic",
  *Annals of Pure and Applied Logic* 86(1):33–46, 1997.** DOI 10.1016/S0168-0072(96)00034-6.
  [CONFIRMED.] The second-order IPC of the class of all "principal" Kripke frames, and the
  version where quantifiers range over increasing subsets, are not recursively axiomatisable.

### 1.5 The separation: (a) Pitts-definable versus (b) impredicative

These are the two readings the design memo must keep apart.

**(a) Pitts-definable / eliminable / predicative.** `∃p` and `∀p` are *abbreviations* for
particular `p`-free formulas, computed by a terminating recursion. The resulting logic is
decidable (it is IPC). The quantifier rules hold. Instantiation holds for all *formulas* but the
quantifier does not "see" anything outside the language.

**(b) Impredicative / semantic.** `∀p` ranges over the propositions of a model. Not
recursively axiomatisable (Kremer 1997, Skvortsov 1997). Instantiation is genuinely
second-order.

**They differ, and here are the separating results:**

* **Complexity separation** [rigorous, from the cited results]: (a) is decidable; (b) is
  recursively isomorphic to full second-order logic (Kremer 1997). No translation can identify
  them.
* **Direct semantic separation:** **T. Połacik, "Pitts' quantifiers are not topological
  quantification", *Notre Dame Journal of Formal Logic* 39(4):531–544, Fall 1998.**
  [CONFIRMED via Project Euclid.] Pitts' modelling of propositional quantification (as the
  appropriate interpolants) does **not** coincide with the topological interpretation, in
  contrast with the monadic language over sufficiently regular spaces. The paper also separates
  the topological interpretation from the Kripke-model interpretation. This is the cleanest
  single citation for "Pitts' quantifiers are not the real second-order quantifiers".
* **Independent evidence that a *third* reading exists:** **P. Kremer, "Completeness of
  second-order propositional S4 and H in topological semantics", *Review of Symbolic Logic*
  11(3):507–518, 2018.** DOI 10.1017/S1755020318000229. [CONFIRMED.] S4 and H with propositional
  quantifiers and the natural axiom schemes are sound and complete for a topological semantics.
  So the axiomatic second-order systems are *complete for something*, just not for the Kripke
  reading.

**Consequence for the design memo:** a "second-order PLL" is not one system but a family. §3
proposes the natural-deduction system PLL2 (an axiomatic system, reading (a)-agnostic), states
its Kripke-semantic reading (b), and separates the conjecture that PLL's uniform interpolants
interpret PLL2 (a Pitts-style theorem) from the conjecture that PLL2 is complete for the
second-order Kripke semantics (which, by analogy with Kremer/Skvortsov, is expected to be
**false**).

### 1.6 Fragments

* **T. Połacik, "Propositional quantification in the monadic fragment of intuitionistic logic",
  *The Journal of Symbolic Logic* 63(1):269–300, 1998.** [SEMI-VERIFIED: journal/volume/issue/
  year/pages from JSTOR and Cambridge listings.] The one-variable (monadic) case, where the
  topological and Pitts readings *do* agree.
* **K. Zdanowski, "On second order intuitionistic propositional logic without a universal
  quantifier", *The Journal of Symbolic Logic* 74(1):157–167, 2009.**
  DOI 10.2178/jsl/1231082306. [CONFIRMED via Project Euclid.] The ∃-only fragment behaves
  differently from the full system.
* **K.-E. Fujita, A. Schubert, P. Urzyczyn and K. Zdanowski, "The existential fragment of
  second-order propositional intuitionistic logic is undecidable", *Journal of Applied
  Non-Classical Logics* 34(1):55–74, 2024.** [SEMI-VERIFIED — volume/issue/pages from PhilPapers.]
  The (∃,→) fragment with free variables is undecidable; by contrast the (∃,∧,¬) fragment is
  decidable.
* **P. Kremer, "Quantifying over propositions in relevance logic: nonaxiomatisability of primary
  interpretations of ∀p and ∃p", *The Journal of Symbolic Logic* 58(1):334–349, 1993.**
  DOI 10.2307/2275341. [CONFIRMED.] The substructural analogue of the non-axiomatisability
  phenomenon.
* **P. Fritz, *Propositional Quantifiers*, Cambridge Elements in Philosophy and Logic, Cambridge
  University Press, 2024, 118 pp.** DOI 10.1017/9781009177740. [CONFIRMED.] The modern survey;
  the right single reference for the whole landscape.

---

## 2. Propositional quantification in modal and substructural logics

### 2.1 Uniform interpolation in modal logic, and the quantifier-projection reading

* **A. Visser, "Uniform interpolation and layered bisimulation", in P. Hájek (ed.), *Gödel '96:
  Logical Foundations of Mathematics, Computer Science and Physics*, Lecture Notes in Logic 6,
  Springer, 1996, pp. 139–164.** DOI 10.1007/978-3-662-21963-8_9. [CONFIRMED — venue, editor,
  series, pages, DOI. The claim that the paper covers IPC, K, GL and S4Grz is corroborated from
  the abstract via secondary sources but the PDF itself was not read: SEMI-VERIFIED.] Visser
  reads uniform interpolants as propositionally quantified formulas, with bisimulation
  extension/reset as the accessibility relation for the quantifiers. This is the
  quantifier-projection reading in its clearest form.
* **S. Ghilardi, "An algebraic theory of normal forms", *Annals of Pure and Applied Logic*
  71(3):189–245, 1995.** DOI 10.1016/0168-0072(93)E0084-2. [CONFIRMED.] The algebraic route,
  giving UI for K.
* **M. Bílková, "Uniform interpolation and propositional quantifiers in modal logics",
  *Studia Logica* 85(1):1–31, 2007.** DOI 10.1007/s11225-007-9021-5. [CONFIRMED; abstract read
  at source.] Pitts' method transplanted to modal logic. **The paper covers K and T only** —
  a point on which the literature is often misquoted. Abstract, verbatim in part: *"The method is
  based on a simulation of certain quantifiers ranging over propositional variables and uses a
  terminating sequent calculus for which structural rules are admissible."*
* **M. Bílková, "Interpolation in modal logics", PhD dissertation, Charles University Prague,
  Faculty of Arts, Department of Logic, defended 22 November 2006** (supervisor Pavel Pudlák).
  [CONFIRMED via the Charles University repository record.]
* **GL.** UI for GL was first proved by **V. Yu. Shavrukov**, *Subalgebras of diagonalizable
  algebras of theories containing arithmetic*, Dissertationes Mathematicae 323, Instytut
  Matematyczny PAN, Warsaw, 1993, 82 pp. [CONFIRMED that the monograph exists with these data;
  that the UI result is inside it is the standard attribution but was NOT read at source:
  SEMI-VERIFIED. Do not cite a theorem number.] A proof-theoretic proof is
  **M. Bílková, "Uniform interpolation in provability logics", in J. van Eijck, R. Iemhoff and
  J. Joosten (eds.), *Liber Amicorum Alberti: A Tribute to Albert Visser*, Tributes 30, College
  Publications, 2016, pp. 57–90**; arXiv:2211.02591. [CONFIRMED via arXiv.] Covers GL and Grz.
* **KD.** UI holds: **R. Iemhoff, "Uniform interpolation and sequent calculi in modal logic",
  *Archive for Mathematical Logic* 58(1–2):155–181, 2019.** DOI 10.1007/s00153-018-0629-0.
  [CONFIRMED via Crossref.]
* **Mechanisation precedent, directly relevant to this project:**
  **H. Férée, I. van der Giessen, S. van Gool and I. Shillito, "Mechanised uniform interpolation
  for modal logics K, GL, and iSL", IJCAR 2024, Springer LNCS.**
  DOI 10.1007/978-3-031-63501-4_3; arXiv:2402.10494. [CONFIRMED.] Their abstract records that
  the GL formalisation resolved an incomplete sequent-style proof in the literature, and that
  theirs is the first proof-theoretic construction for iSL. Precedent both for the value of
  mechanising UI and for the fact that published UI proofs have had gaps.

### 2.2 Where uniform interpolation fails, and why

* **S. Ghilardi and M. Zawadowski, "Undefinability of propositional quantifiers in the modal
  system S4", *Studia Logica* 55(2):259–271, 1995.** DOI 10.1007/BF01061237. [CONFIRMED;
  abstract read at source.] There is **no** translation of S4 with propositional quantifiers
  into S4 preserving provability and acting as the identity on the Boolean connectives and □.
  The abstract itself contrasts this with the intuitionistic case, where such a translation
  exists (Pitts). This is *the* citation for "the Pitts programme can fail".
* **K4** fails by the same counterexample; the joint attribution in the literature is to
  Ghilardi–Zawadowski 1995 together with Bílková's thesis (2006). [SEMI-VERIFIED — reported in
  two survey sources; the K4 statement also appears in the abstract of Iemhoff's *Archive for
  Mathematical Logic* 2019 paper, which says K4 and S4 "are known not to have uniform
  interpolation".]
* **The proof-theoretic diagnosis** (why Pitts' *method* fails, which is not the same as why UI
  fails): the transitivity rule (4) duplicates the context Γ and rule (T) duplicates the
  principal formula in the premise, so the calculus is not strongly terminating, and Pitts'
  recursion has nothing to recurse on. [Reported in the survey **I. van der Giessen, R. Jalali
  and R. Kuznets, "Interpolation in proof theory", in *Theory and Applications of Craig
  Interpolation*, Ubiquity Press, 2026; arXiv:2602.16318** — SEMI-VERIFIED, the survey's
  bibliographic data confirmed via arXiv, the diagnosis paraphrased from it.]
* **The converse direction, and a warning.** Iemhoff's programme runs the implication backwards:
  if a logic lacks UI then certain shapes of sequent calculus for it cannot exist.
  **R. Iemhoff, "Uniform interpolation and the existence of sequent calculi", *Annals of Pure
  and Applied Logic* 170(11):102711, 2019.** DOI 10.1016/j.apal.2019.05.008. [CONFIRMED via
  Crossref.]
* **Algebraic characterisation — handle with care.** The often-quoted "a variety has UI iff its
  theory has a model completion" is **not** a correct biconditional as stated.
  - **S. J. van Gool, G. Metcalfe and C. Tsinakis, "Uniform interpolation and compact
    congruences", *Annals of Pure and Applied Logic* 168(10):1927–1948, 2017.**
    DOI 10.1016/j.apal.2017.05.001. [CONFIRMED.] Gives a **sufficient** condition for the
    first-order theory of the variety to admit a model completion.
  - **T. Kowalski and G. Metcalfe, "Uniform interpolation and coherence", *Annals of Pure and
    Applied Logic* 170(7):825–841, 2019.** DOI 10.1016/j.apal.2019.02.004; arXiv:1803.09116.
    [CONFIRMED; abstract read at source.] A genuine iff, but between *coherence* and a
    *restricted form of uniform deductive interpolation*. Their abstract notes that coherence
    and uniform deductive interpolation **fail** for varieties of Boolean algebras with
    operators, "in particular, algebras of modal logic K and its standard non-transitive
    extensions".
  - **The trap**: modal K *has* uniform interpolation (Pitts-style, local) while the variety of
    modal algebras *fails* uniform **deductive** interpolation. Local UI for formulas and
    uniform deductive interpolation for equational consequence are different properties.
    Conflating them produces a false statement. Any use of the algebraic machinery for PLL must
    say which property is meant.
  - Background: **L. Maksimova (1977)** — exactly eight varieties of Heyting algebras have the
    amalgamation property; and **S. Ghilardi and M. Zawadowski, "Model completions and r-Heyting
    categories", *Annals of Pure and Applied Logic* 88(1):27–46, 1997**, DOI
    10.1016/S0168-0072(97)00012-2 [CONFIRMED], where for the corresponding superintuitionistic
    logics IPC2 is interpretable in IPC. Sources differ on "eight" versus "seven non-trivial";
    count before writing it down. [Maksimova's exact reference: UNVERIFIED — I did not confirm
    the 1977 citation directly.]
  - **S. Ghilardi and M. Zawadowski, *Sheaves, Games, and Model Completions: A Categorical
    Approach to Nonclassical Propositional Logics*, Trends in Logic 14, Kluwer, 2002.**
    DOI 10.1007/978-94-015-9936-8. [CONFIRMED.] Book-length treatment.

### 2.3 Genuine propositional quantifiers in modal logic

* **K. Fine, "Propositional quantifiers in modal logic", *Theoria* 36(3):336–346, 1970.**
  DOI 10.1111/j.1755-2567.1970.tb00432.x. [CONFIRMED.] The propositionally quantified modal
  logic of reflexive-transitive frames is not recursively axiomatisable; the logic of frames
  with a universal relation (S5π+) is decidable. **Note the direction**: it is **S5**π+ that is
  decidable, not S4π+.
* **R. A. Bull, "On modal logic with propositional quantifiers", *The Journal of Symbolic Logic*
  34(2):257–263, 1969.** DOI 10.2307/2271102. [CONFIRMED.]
* **D. Kaplan, "S5 with quantifiable propositional variables", *The Journal of Symbolic Logic*
  35(2):355, 1970** — an *abstract*, not a paper. [UNVERIFIED at source; cite with care.]
* **M. Kaminski and M. Tiomkin, "The expressive power of second-order propositional modal
  logic", *Notre Dame Journal of Formal Logic* 37(1):35–43, 1996.**
  DOI 10.1305/ndjfl/1040067314. [CONFIRMED; result read at source.] Second-order propositional
  modal logic whose modalities are S4.2 or weaker has the same expressive power as second-order
  predicate logic.
* **P. Kremer, "Propositional quantification in the topological semantics for S4",
  *Notre Dame Journal of Formal Logic* 38(2):295–313, 1997.**
  DOI 10.1305/ndjfl/1039724892. [CONFIRMED bibliographically; the summary that the topological
  S4πt is strictly weaker than the Kripkean S4π+ is SEMI-VERIFIED from search snippets.]
* **P. Fritz, "Axiomatizability of propositionally quantified modal logics on relational
  frames", *The Journal of Symbolic Logic* 89(2):758–793, 2024.** DOI 10.1017/jsl.2022.79.
  [SEMI-VERIFIED — DOI and article id confirmed from the publisher PDF metadata; volume/pages
  from a search summary.] The modern general theory; the key notion is *finite diversity*.

### 2.4 Intuitionistic modal logic

* **UI for intuitionistic modal logics:** Iemhoff's *Annals of Pure and Applied Logic* 2019
  paper (above) gives a uniform, modular method for intermediate and intuitionistic modal logics
  based on extensions of the terminating calculus G4ip, with structural conditions on the rules
  ("centered"/"focussed") sufficient for UI. [The exact list of logics covered is SEMI-VERIFIED —
  ScienceDirect and PhilPapers both refused fetching.]
* **Propositional quantifiers in intuitionistic modal logic: essentially nothing before 2026.**
  The one item found is **J. Becker, A. Das, S. Marin and P. Padhiar, "The proof theory and
  semantics of second-order (intuitionistic) tense logic", arXiv:2602.06253, 5 February 2026.**
  [CONFIRMED as an arXiv item.] A second-order extension of intuitionistic modal logic with
  quantification over propositions: axiomatic, proof-theoretic and model-theoretic
  formulations shown equivalent, completeness of a labelled sequent calculus by proof search,
  and ◇ definable from □ plus the tense modalities. The words *lax*, *nucleus* and *monad* do
  not occur in it. **This is the nearest methodological template for PLL2, and the nearest
  competitor for the niche.**
* **Nuclei and local finiteness — directly relevant to PLL:**
  **G. Bezhanishvili, N. Bezhanishvili, L. Carai, D. Gabelaia, S. Ghilardi and M. Jibladze,
  "Diego's theorem for nuclear implicative semilattices", *Indagationes Mathematicae*
  32(2):498–535, 2021.** DOI 10.1016/j.indag.2020.12.005; preprint arXiv:2001.11060.
  [CONFIRMED; full text read.] Note the year is **2021**, not 2020.
  - Their definition, verbatim: *"A nucleus on an implicative semilattice A is a unary function
    j: A → A satisfying (1) a ⩽ ja, (2) jja = ja, (3) j(a ∧ b) = ja ∧ jb."*
  - Main theorem: **the variety of nuclear implicative semilattices is locally finite**,
    generalising Diego's theorem. Same for the bounded variant.
  - Method: duality plus the colouring technique from modal logic, building universal models;
    n-universal models shown finite for each n. Köhler duality is generalised to finite nuclear
    implicative semilattices. An explicit description of the free one-generated nuclear
    implicative semilattice is given.
  - Their own statement of the logical link, verbatim: *"In logic, nuclei model the so-called
    lax modality. As such, nuclear implicative semilattices provide algebraic semantics for the
    ∨-free fragment of the Lax Logic."*
  - **Important negative check:** the paper does **not** treat nuclear *Heyting* algebras as a
    separate variety and does not say whether that variety is locally finite. Do not cite it for
    a claim about the ∨-carrying case.
* **G. Bezhanishvili and N. Bezhanishvili, "Locally finite reducts of Heyting algebras and
  canonical formulas", *Notre Dame Journal of Formal Logic* 58(1):21–45, 2017.**
  DOI 10.1215/00294527-3691563. [CONFIRMED except pages, SEMI-VERIFIED.]
* **G. Bezhanishvili and S. Ghilardi, "An algebraic approach to subframe logics. Intuitionistic
  case", *Annals of Pure and Applied Logic* 147(1–2):84–100, 2007.**
  DOI 10.1016/j.apal.2007.04.001. [CONFIRMED bibliographically; the nuclei/subframe-logic
  connection as usually stated is UNVERIFIED at source.]
* **M. Erné, "Nuclear ranges in implicative semilattices", *Algebra Universalis* 83(2), 2022.**
  DOI 10.1007/s00012-022-00768-3. [CONFIRMED.]
* **D. S. Macnab, "Modal operators on Heyting algebras", *Algebra Universalis* 12:5–29, 1981.**
  [SEMI-VERIFIED.] The origin of nuclei as modal operators on Heyting algebras.

### 2.5 Lax logic specifically

**(i) PLL has uniform interpolation — PROVED, and recently.**

> **R. Iemhoff, "Proof theory for lax logic", in N. Bezhanishvili, R. Iemhoff and F. Yang (eds.),
> *Dick de Jongh on Intuitionistic and Provability Logics*, Outstanding Contributions to Logic
> 28, Springer Cham, 2024, pp. 203–229.** DOI 10.1007/978-3-031-47921-2_8. Preprint
> **arXiv:2209.08976**, 19 September 2022. [CONFIRMED — abstract fetched from arXiv.]

Abstract, verbatim: *"In this paper some proof theory for propositional Lax Logic is developed.
A cut free terminating sequent calculus is introduced for the logic, and based on that calculus
it is shown that the logic has uniform interpolation."* The chapter also gives a separate simple
proof of ordinary interpolation from the same calculus, and notes that PLL's interpolation was
previously known only model-theoretically.

The calculus (call it GLL) is Dyckhoff's G4ip plus

    Γ ⇒ φ                Γ, φ ⇒ ◯ψ
    ─────── (R◯)         ────────── (L◯)
    Γ ⇒ ◯φ               Γ, ◯φ ⇒ ◯ψ

[SEMI-VERIFIED — read off Iemhoff's LLAMA/ILLC slides of 25 January 2023, "On the existence of
sequent calculi: uniform interpolation for Lax Logic", not off the published chapter.] These are
exactly the rules the repository implements: `LaxLogic/PLLFocused.lean` line 111,
`circL : Inv Γ [Q] .lax (.up P) → LFoc Γ (.circ Q) .lax P`, with the `.lax` mode marking the
second judgment that L◯ needs.

**Consequence for the project's framing.** The *existence* of uniform interpolants for PLL is
not open. What the project can claim is: an explicit, terminating, **machine-checked**
construction over a focused calculus, in a setting where the modal-logic precedent (Férée et al.
2024, IJCAR) shows published UI proofs have contained gaps. That is a defensible and honest
positioning, and it should be stated that way rather than as a first proof.

**(ii) The lax modality is already definable in IPC2 — Aczel's Russell–Prawitz modality.**

> **P. Aczel, "The Russell–Prawitz modality", *Mathematical Structures in Computer Science*
> 11(4):541–554, August 2001.** [CONFIRMED — volume/issue/pages/year.] Earlier version:
> **P. Aczel, "The Russell–Prawitz modality", in M. Fairtlough (ed.), *Informal Proceedings of
> the Workshop on Intuitionistic Modal Logics and Applications (IMLA'99)*, Trento, 1999.**
> [SEMI-VERIFIED — cited in exactly this form in Pfenning–Davies's reference list.]

In IPC2, put `Jφ := ∀p((φ→p)→p)` for `p` not free in `φ`. Aczel shows `J` is a **lax modality**
and uses it for a translation of intuitionistic logic into itself generalising both the
double-negation interpretation and the Russell–Prawitz representation.

Two provenance facts that matter. The MSCS issue in which it appeared is 11(4), August 2001, the
special issue *Modalities in Type Theory* edited by **Fairtlough, Mendler and Moggi** (the same
issue contains Pfenning–Davies, pp. 511–540, and Howe, "Proof search in Lax Logic",
pp. 573–588). And the 1999 workshop version was edited by Fairtlough. So any claim of novelty
for a second-order lax logic has to be positioned explicitly against Aczel, in a venue Fairtlough
himself edited. §3.4 does that positioning.

**(iii) A name collision to flag loudly: "quantified lax logic" is taken, and is first-order.**

* **M. Fairtlough and M. Walton, "Quantified lax logic", Technical Report CS-97-11, Department
  of Computer Science, University of Sheffield, July 1997.** [SEMI-VERIFIED — cited in exactly
  this form by Goldblatt.]
* **R. Goldblatt, "Cover semantics for quantified lax logic", *Journal of Logic and Computation*
  21(6):1035–1063, December 2011.** DOI 10.1093/logcom/exq029. [CONFIRMED; preprint read.]
  Goldblatt's QLL quantifies over **individual** variables, not propositions: it is the
  first-order version of PLL, and he says so, citing Fairtlough–Walton. The semantics combines
  Beth–Kripke–Joyal cover semantics with a relational clause for the modality; the technique
  lifts a nucleus from a Heyting algebra to its MacNeille completion.
* **R. Goldblatt, "Grothendieck topology as geometric modality", *Zeitschrift für mathematische
  Logik und Grundlagen der Mathematik* 27:495–529, 1981**; reprinted in *Mathematics of
  Modality*, CSLI Lecture Notes 43, 1993. [SEMI-VERIFIED — from Goldblatt's own bibliography.]

**(iv) The second-order monadic metalanguage does exist, on the type-theory side.**

> **R. E. Møgelberg and A. Simpson, "Relational parametricity for computational effects",
> LICS 2007; journal version in *Logical Methods in Computer Science*; arXiv:0906.5488.**
> [CONFIRMED as an arXiv item; the LMCS issue/article number is UNVERIFIED.] Companion:
> **R. E. Møgelberg and A. Simpson, "A logic for parametric polymorphism with effects",
> TYPES 2007, LNCS 4941, pp. 142–156, 2008.** [SEMI-VERIFIED.]

Their type theory PE is a second-order (Girard–Reynolds) λ-calculus in call-by-push-value style,
with value types and computation types and ∀-quantification over **both** kinds. The monad is
**defined, not primitive**:

    !B  :=  ∀**X**. (B → **X**) → **X**,   **X** ranging over *computation* types only.

This is the type-theoretic twin of Aczel's `∀p((φ→p)→p)` with the quantifier **restricted to a
subclass**. They prove `!B` has its expected universal property, and that Plotkin's linear
parametricity and Hasegawa's control parametricity are special cases. §3.4 shows the
propositional shadow of exactly this move.

**(v) Explicit negatives, all checked.**

* **Moggi's computational metalanguage** (LICS 1989; *Information and Computation* 93(1):55–92,
  1991) is simply typed: no ∀. That Moggi, Hughes and Wadler *attempted* a polymorphic version
  is reported in secondary sources but I could not verify a worked-out polymorphic monadic
  metalanguage from Moggi. [UNVERIFIED.]
* **P. N. Benton, G. M. Bierman and V. C. V. de Paiva, "Computational types from a logical
  perspective", *Journal of Functional Programming* 8(2):177–193, 1998.** [CONFIRMED; author
  preprint read.] Their CL-logic has ND, sequent and Hilbert presentations, strong
  normalisation, confluence. **The words *second-order*, *polymorphism* and *System F* do not
  occur, and the reference list contains no polymorphism paper.**
* **F. Pfenning and R. Davies, "A judgmental reconstruction of modal logic", *Mathematical
  Structures in Computer Science* 11(4):511–540, 2001.** [CONFIRMED; conclusion and
  bibliography read.] Lax logic is embedded into their modal logic. Their stated further work is
  *"extensions to first-order logic and type theory, which require parametric judgments"* —
  **first-order, not second-order.** No polymorphic extension of the lax fragment is proposed
  there, and none was found downstream.
* **No paper by Fairtlough or Mendler mentions propositional quantification.** dblp's complete
  Fairtlough list is 7 items, none second-order.
* **There is no Fairtlough–Mendler paper titled "Ternary Kripke semantics."** PLL's semantics in
  their work is the fallible two-frame constraint semantics of *Information and Computation*
  1997; ternary-frame semantics for lax modalities appears only in the relevant-logic/quantale
  line.

**(vi) The gap, stated by a specialist.**

> **N. Valliappan, "Lax modal lambda calculi", CSL 2026 (34th EACSL Annual Conference on
> Computer Science Logic), LIPIcs 363, article 49; arXiv:2512.10779, 11 December 2025.**
> [CONFIRMED as an arXiv item; the LIPIcs volume/article numbers are SEMI-VERIFIED.]

Four sublogics — SL (axiom S alone), SRL (S+R), SJL (S+J), PLL (S+R+J) — with calculi,
possible-world and categorical semantics, normalisation and completeness. Section 6, verbatim:
*"Further work concerns extensions of these calculi to second-order quantification and
polymorphism"*. As of December 2025 a specialist working directly on lax calculi lists
second-order lax as **not yet done**.

**(vii) Verdict.** **Second-order propositional lax logic does not exist in the literature.**
The nearest objects are Aczel's *definable* lax modality in IPC2 (2001), Iemhoff's *Pitts-style
quantifiers definable inside PLL* (2024), Goldblatt's *first-order* quantified lax logic (2011),
and Møgelberg–Simpson's *second-order monadic type theory with a defined monad* (2007). Nobody
has studied **IPC2 plus a primitive, uninterpreted nucleus ◯**: its semantics, its proof theory,
or its collapse behaviour. That is the gap.

---

## 3. Design memo: PLL2, second-order propositional lax logic

### 3.1 Syntax

Over a countable set of propositional variables `p, q, …`:

    φ ::= p | ⊥ | φ ∧ φ | φ ∨ φ | φ → φ | ◯φ | ∀p.φ | ∃p.φ

`⊤ := ⊥→⊥`, `¬φ := φ→⊥`. Capture-avoiding substitution `φ[χ/p]` as usual.

Because the language is impredicative, `⊥`, `∧`, `∨` are Russell–Prawitz-definable from `→` and
`∀`, so a minimal presentation with primitives `→`, `∀p`, `◯` is available and is the right one
for the Curry–Howard reading (§3.8). §3.3 records a sanity check: under the intended semantics
`∀p.p ≡ ⊥`, and the ⊥ so defined agrees with PLL's fallible-world ⊥.

### 3.2 Natural-deduction rules

PLL's own rules, in the repository's Hilbert presentation (`LaxLogic/PLLAxiom.lean`), are

    ◯R:    φ → ◯φ                                    (`somehowR`)
    ◯M:    ◯◯φ → ◯φ                                  (`somehowM`)
    ◯S:    ◯φ ∧ ◯ψ → ◯(φ ∧ ψ)                        (`somehowS`)
    ◯bind: (φ → ◯ψ) → (◯φ → ◯ψ)                      (`somehowBind`)

plus the intuitionistic axioms. PLL2 adds the standard second-order rules:

    Γ ⊢ φ            p not free in Γ         Γ ⊢ ∀p.φ
    ─────────────────────────────── (∀I)    ────────────── (∀E)
    Γ ⊢ ∀p.φ                                Γ ⊢ φ[χ/p]

    Γ ⊢ φ[χ/p]                       Γ ⊢ ∃p.φ    Γ, φ ⊢ ψ    p not free in Γ, ψ
    ──────────── (∃I)                ─────────────────────────────────────────── (∃E)
    Γ ⊢ ∃p.φ                         Γ ⊢ ψ

No side condition on `χ` beyond capture-avoidance: comprehension is full (impredicative).

**Interaction with ◯: which directions hold.**

*Both "uniform-witness" directions are derivable, from monotonicity alone:*

* `⊢ ∃p.◯φ → ◯∃p.φ` **[DERIVABLE]**. From `φ ⊢ ∃p.φ` and monotonicity of ◯ (a consequence of
  `◯bind` and `◯R`) get `◯φ ⊢ ◯∃p.φ`; then ∃E, since `p` is not free in `◯∃p.φ`.
* `⊢ ◯∀p.φ → ∀p.◯φ` **[DERIVABLE]**. From `∀p.φ ⊢ φ` (∀E at `p` itself) and monotonicity get
  `◯∀p.φ ⊢ ◯φ`; then ∀I, since `p` is not free in `◯∀p.φ`.

*Both converses should fail, and the Kripke semantics of §3.3 says why:*

* `◯∃p.φ → ∃p.◯φ` **[CONJECTURED FALSE, semantic reason]**. `w ⊩ ◯ψ` demands, for every
  `Ri`-successor `v` of `w`, some `Rm`-successor `u` of `v` with `u ⊩ ψ`. Different `u` may
  require different witnesses for `p`; a single uniform witness need not exist. This is the
  familiar ◇∃/∃◇ (Barcan-converse) failure for an existential-flavoured clause.
* `∀p.◯φ → ◯∀p.φ` **[CONJECTURED FALSE, same reason]**: the `Rm`-successor witnessing `◯φ[X]`
  may depend on `X`.

Neither direction that holds is PLL-specific: they hold for *any* monotone modality. That is
worth saying explicitly, because it means the interesting PLL2 content is elsewhere — in §3.4
and §3.5.

### 3.3 Semantics: second-order constraint models

The repository's `ConstraintModel` (`LaxLogic/PLLKripke.lean`) is F&M's fallible two-frame
structure: `W`, an intuitionistic accessibility `Ri` (reflexive, transitive), a modal
accessibility `Rm` (reflexive, transitive, with `Rm ⊆ Ri`), a set `F ⊆ W` of fallible worlds
(`Ri`-upward closed), and a valuation `V` that is `Ri`-persistent and **full on `F`** (fallible
worlds satisfy every atom). Forcing:

    w ⊩ ⊥        iff  w ∈ F
    w ⊩ φ → ψ    iff  ∀v. Ri w v → (v ⊩ φ → v ⊩ ψ)
    w ⊩ ◯φ       iff  ∀v. Ri w v → ∃u. Rm v u ∧ u ⊩ φ

**Proposal.** An *admissible proposition* of a constraint model is a set `X ⊆ W` that is
`Ri`-upward closed and contains `F`. (Both conditions are forced: upward closure by
persistence, `F ⊆ X` because fullness on `F` is what makes the ⊥-clause behave. `F` is the least
admissible proposition and `W` the greatest.) Then

    w ⊩ ∀p.φ  iff  for every admissible X,  w ⊩_{V[p↦X]} φ
    w ⊩ ∃p.φ  iff  for some admissible X,   w ⊩_{V[p↦X]} φ

**Sanity check [DERIVABLE].** `∀p.p` denotes the intersection of all admissible propositions,
which is `F`, which is the denotation of `⊥`. So `∀p.p ≡ ⊥` and the second-order definition of
falsum agrees with PLL's fallible-world falsum. This is a genuine constraint on the design: it
is what rules out, for example, dropping `F ⊆ X` from admissibility.

**Two candidate quantifier ranges** (this is the "which ranges validate Pitts-projection"
question of the brief):

* **Full range** — all admissible `X`. Expected behaviour, by analogy with Kremer 1997 and
  Skvortsov 1997 for IPC: **not recursively axiomatisable**, hence PLL2 (an r.e. system) is
  **incomplete** for it. **[CONJECTURED]**
* **Definable range** — `X` ranging only over denotations of `p`-free formulas. This is the
  range for which a Pitts-style projection theorem can hold, and it is what uniform
  interpolation computes. **[This is the content of §3.5.]**

The gap between these is exactly the (a)/(b) distinction of §1.5, and Połacik 1998 is the
citation that they come apart already for IPC.

### 3.4 The Russell–Prawitz modality inside PLL2: non-collapse, and a definability theorem

This subsection is, I think, the sharpest content the second-order view supplies, and both
halves are short enough to machine-check.

Write `Jφ := ∀p.((φ→p)→p)` for `p` not free in `φ` (Aczel 2001).

**Proposition A (J is the strongest lax modality) [DERIVABLE-BY-HAND].**
In PLL2, `⊢ Jφ → ◯φ`.
*Proof.* Instantiate `p := ◯φ` by ∀E: `Jφ ⊢ (φ→◯φ)→◯φ`. The antecedent `φ→◯φ` is `◯R`. ∎

The argument uses nothing about `◯` beyond the unit, so it shows `J` is below *every* modality
with a unit — `J` is the strongest such.

**Proposition B (◯ does not collapse to J) [DERIVABLE-BY-HAND, semantically].**
`⊬ ◯φ → Jφ`.
*Proof.* By §3.3, `J⊥ = ∀p.p ≡ ⊥`. So `◯⊥ → J⊥` is `◯⊥ → ⊥`, i.e. `¬◯⊥`. F&M's
countermodel — two worlds `w₀ ≤ w₁` in both frames with `w₁` fallible — forces `◯⊥` at `w₀`
while `w₀ ∉ F`. That countermodel is already machine-checked in this repository
(`LaxLogic/PLLFrames.lean`, "Counter-model 1: `¬◯⊥` is not a theorem"). ∎

Together: **PLL2's `◯` is a genuinely new primitive**, strictly weaker than the lax modality
that second-order quantification already defines. This is precisely the answer to "is PLL2 just
Aczel 2001 again?": no, and the separation is exactly the fallible-world phenomenon that
distinguishes PLL from IPC in the first place.

**Proposition C (◯ *is* definable by a restricted quantifier) [DERIVABLE-BY-HAND].**
Let `∀°p.φ` quantify over **◯-fixpoints**, i.e. propositions `p` with `◯p → p`. Then

    ◯φ  ⊣⊢  ∀°p.((φ→p)→p).

*Proof.* (⊢) Instantiate `p := ◯φ`, which is a ◯-fixpoint by `◯M`; the antecedent `φ→◯φ` is
`◯R`. (⊣) Let `p` be a ◯-fixpoint and assume `φ→p`. Monotonicity gives `◯φ → ◯p`, and
`◯p → p` is the fixpoint property; so `◯φ ⊢ p`. Discharge and generalise. ∎

This is the propositional shadow of Møgelberg–Simpson's `!B = ∀**X**.(B→**X**)→**X**` with `**X**`
ranging over computation types. It says PLL2 naturally has **two quantifier sorts** — the plain
one, over all propositions, which over-shoots (Proposition B), and the restricted one, over the
◯-algebras, which lands exactly on `◯`. Category-theoretically the ◯-fixpoints are the algebras
of the nucleus, i.e. the sublocale; order-theoretically they are the image `N(A)` that the
project's nucleus/assembly thread already studies.

**Design consequence.** A serious PLL2 should probably have both `∀p` and `∀°p` (and duals). The
restricted sort is where the computational reading lives; the unrestricted sort is where the
metatheory (undecidability, non-axiomatisability) lives.

### 3.5 Pitts-style PLL2: the conjecture

**Conjecture (Pitts-projection for PLL) [CONJECTURED; the existence half is PROVED by Iemhoff
2024].** Define `∃p φ` and `∀p φ` to be PLL's uniform interpolants. Then the map `(−)°` sending
`∀p.φ ↦ ∀p(φ°)` and `∃p.φ ↦ ∃p(φ°)` is an interpretation of PLL2 in PLL restricting to the
identity on ◯-formulas and first-order formulas — i.e. PLL2 ⊢ φ implies PLL ⊢ φ°. Corollary:
**PLL2 is conservative over PLL**.

Status of the pieces:

* That uniform interpolants for PLL exist and satisfy the four characteristic laws: **PROVED**,
  Iemhoff 2024.
* That the four laws suffice to validate the ∀/∃ rules under `(−)°`: this is Pitts' own argument
  for IPC and should transfer verbatim; the only new obligation is the ◯-case of the induction.
  **OPEN** for PLL, but expected routine.
* Faithfulness of `(−)°`: **expected FALSE**, by the same complexity argument as §1.2 — PLL is
  decidable (and PSPACE-complete, via Egly's embedding into IPC; see §5) whereas PLL2 should be
  undecidable by transport of Löb/Sobolev.
* Completeness of PLL2 for the *full-range* second-order Kripke semantics of §3.3:
  **expected FALSE**, by analogy with Kremer 1997/Skvortsov 1997.

**A concrete sub-conjecture the engine can settle.** With `Γ` a context and `∃p Γ` its strongest
`p`-free consequence:

    ∃p (Γ, ◯φ)  ≡  ∃p Γ  ∧  ◯ ( ∃p (Γ, φ) )        [CONJECTURED]

The ⊢ direction of the ◯-conjunct is **DERIVABLE**: by `eSound`, `Γ, φ ⊢ ∃p(Γ,φ)`; by `◯R`,
`Γ, φ ⊢ ◯∃p(Γ,φ)`; by `L◯`, `Γ, ◯φ ⊢ ◯∃p(Γ,φ)`; and this is `p`-free, so `eMin` gives
`∃p(Γ,◯φ) ⊢ ◯∃p(Γ,φ)`. Note also that **L◯ is invertible** in PLL: `Γ,◯φ ⊢ ◯ψ` implies
`Γ,φ ⊢ ◯ψ` by cutting the unit `φ ⊢ ◯φ`. So the ◯-goals of `Γ,◯φ` are exactly those of `Γ,φ`,
which is what makes the shape above plausible. What is not automatic is that `∃p Γ` and
`◯∃p(Γ,φ)` *generate* all `p`-free consequences — that is the content of the conjecture, and it
is exactly the clause the PLL extension of `LaxLogic/LJF.lean` will have to write down.

### 3.6 Names

Checked against the literature (§5.6):

| Candidate | Verdict |
|---|---|
| **PLL2** | **Free.** Zero hits in logic. Follows IPC2, LL2, S4₂. **Recommended.** |
| QPLL | Free in logic, but "Q" reads as *quantified*, which is exactly what Fairtlough–Walton and Goldblatt already mean by first-order QLL. Invites the wrong reading. |
| ∀PLL / PLL∀ | Free, but ∀-only in appearance, and awkward to typeset and to say. |
| SLL ("second-order lax logic") | **COLLIDES.** SLL = *soft linear logic*, Y. Lafont, *Theoretical Computer Science* 318(1–2):163–180, 2004: a subsystem of second-order linear logic, sound and complete for PTIME. Reject. |
| SL / SRL / SJL | **Newly taken** (December 2025) by Valliappan for the lax sublogics S, S+R, S+J. Reject. |

Two further collisions to note in the prose of any paper: **PLL** itself is already overloaded in
logic (propositional lax logic; polarised linear logic; parsimonious linear logic), and
**"quantified lax logic" is taken and first-order**.

**Recommendation: PLL2, spelled out as *second-order propositional lax logic*, with a footnote on
first sight distinguishing it from Fairtlough–Walton/Goldblatt's first-order quantified lax
logic QLL.** If a two-sorted system with `∀°` is developed (§3.4), `PLL2°` or "PLL2 with nuclear
quantifiers" is the natural refinement.

### 3.7 What the second-order view teaches the interpolant construction

**(a) The quantifier rules *are* the four obligations — exactly.**

`LaxLogic/LJF.lean` states its contract as four properties E1, A1, E2, A2 (lines ~1100–1120),
with `interp p todo done none` the ∃-interpolant and `interp p todo done (some G)` the
∀-interpolant. Reading `interp p Γ none = ∃p(⋀Γ)` and `interp p Γ (some G) = ∀p(⋀Γ → G)`:

| Repository obligation | Second-order rule | Statement in `LJF.lean` |
|---|---|---|
| `eSound` (E1) | **∃-intro** `φ ⊢ ∃p φ` | `Inv (todo ++ done) [] (interp p todo done none)` |
| `eMin` (E2) | **∃-elim** (`p` not free in `Δ, ψ`) | `Inv (todo++done++Δ) [] ψ → Inv (interp … none :: Δ) [] ψ` |
| `aSound` (A1) | **∀-elim** `∀p φ ⊢ φ` | `Inv (interp p todo done (some G) :: todo ++ done) [] G` |
| `aMin` (A2) | **∀-intro** (`p` not free in `Δ`) | `Inv (todo++done++Δ) [] G → Inv (interp … none :: Δ) [] (interp … (some G))` |

The correspondence is exact for E1, E2, A1. **One discrepancy shows up under the reading, and is
worth checking:** plain ∀-intro says *if `Δ, Γ ⊢ G` and `p ∉ Δ` then `Δ ⊢ ∀p(Γ→G)`*. The
repository's A2 concludes `∃p(Γ), Δ ⊢ ∀p(Γ→G)`, i.e. it hands the proof an extra hypothesis
`∃p(Γ)`. That is a **weakening** of ∀-intro (more assumptions on the left), so it is sound but
not the standard statement. Either it is a deliberate strengthening of the induction hypothesis
that happens to be what the recursion needs, or the constructed `∀`-interpolant is weaker than
the genuine `∀p(Γ→G)`. This should be resolved before the PLL extension is written, because the
Pitts-projection conjecture of §3.5 needs the *unweakened* ∀-intro to validate (∀I).

Also note the **substitution forms** come free (§1.1): `⊢ φ[χ/p] → ∃pφ` and `⊢ ∀pφ → φ[χ/p]`
for arbitrary `χ`, since the interpolants are `p`-free and substitution is admissible. These
are the "full comprehension" instances, and they hold in the Pitts reading without extra work —
worth stating as a corollary, since they are what makes the interpolants deserve the quantifier
notation.

**(b) Semantic reading.** §3.3. The Pitts-projection theorem, if it holds, is a statement about
the *definable* range; the full range is expected to escape any r.e. axiomatisation. The
repository's semantic-UI thread (`LaxLogic/PLLSemUI*.lean`) is computing objects on the
semantic side; the second-order reading says exactly what those objects are supposed to be —
the ⋀/⋁ over a definable family, not over all admissible propositions — and predicts that the
two disagree.

**(c) Obstructions, and where PLL sits.**

The failures are Ghilardi–Zawadowski's: **S4 and K4 lack UI**, so the quantifiers are *not*
eliminable there. The diagnosis, proof-theoretically, is that (4) duplicates the context and (T)
duplicates the principal formula, so no terminating calculus of the required shape exists and
the interpolant has nothing to be built by recursion on. Semantically, transitivity of the
*accessibility relation* lets a formula see arbitrarily deep into a model, so no bounded
bisimulation-invariant approximation suffices.

**PLL resembles the succeeding cases on every indicator:**

* **PLL has UI — PROVED** (Iemhoff 2024). The question is settled; the rest of this list is
  explanation, not evidence.
* **◯ is monotone with no negative introspection.** The S4/K4 obstruction is `□φ → □□φ`
  *feeding the context back into itself*. PLL's transitivity axiom runs the other way,
  `◯◯φ → ◯φ`, which *consumes*.
* **L◯ consumes rather than duplicates**: `Γ, φ ⇒ ◯ψ / Γ, ◯φ ⇒ ◯ψ` replaces `◯φ` by `φ`,
  strictly decreasing in the G4-style weight. This is why Iemhoff's calculus terminates and why
  the repository's weighted recursion (`LJF.lean`, Part 2) can carry the ◯-case.
* **Local finiteness of the ∨-free fragment**: the variety of nuclear implicative semilattices
  is locally finite (Bezhanishvili, Bezhanishvili, Carai, Gabelaia, Ghilardi, Jibladze 2021).
  Local finiteness gives finite normal forms, which is the algebraic face of Pitts' recursion.
  **Caveat, and it matters:** that theorem is about the **∨-free** fragment, and the paper does
  **not** address nuclear Heyting algebras. Full PLL with ∨ is *not* covered, and no source I
  found settles it. Do not over-claim from this citation.
* **The K-trap** (§2.2): K has UI while the variety of modal algebras fails uniform *deductive*
  interpolation and coherence. So local UI is *not* an algebraic-model-completion property.
  Whatever algebraic statement is made about PLL must say which of the two properties is meant.

### 3.8 Curry–Howard, for completeness

If IPC2 is System F, PLL2 is System F plus a monadic type constructor `◯` with `return`,
`join`/`bind` and `map` — i.e. **a polymorphic λ-calculus with an abstract strong monad**, the
type theory that Møgelberg–Simpson's PE approximates by *defining* the monad. Proposition C
(§3.4) says the two agree once the quantifier is restricted to the monad's algebras; Proposition
B says they differ otherwise, and the difference is exactly the possibility of a *fallible*
computation `◯⊥` — a monad with no values, which the impredicative `J` cannot express because
`J⊥ = ⊥`. That is a pleasant way to say what lax logic adds to System F, and it is the
programme's natural headline.

---

## 4. Programme

Ordered by cost, cheapest first.

1. **[cheap, machine-checkable now]** Formalise Propositions A, B, C of §3.4 in the repository.
   B already has its countermodel in `PLLFrames.lean`; A and C are three-line derivations once
   `∀°` has rules. This alone is a publishable observation: *the lax modality is strictly weaker
   than the Russell–Prawitz modality, and is exactly the Russell–Prawitz modality of its own
   algebras.*
2. **[cheap]** Resolve the A2 discrepancy of §3.7(a): is the extra `∃p(Γ)` hypothesis needed?
3. **[medium]** Extend `LaxLogic/LJF.lean` to `LJF◯` and check the ◯-clause conjecture of §3.5:
   `∃p(Γ, ◯φ) ≡ ∃p Γ ∧ ◯∃p(Γ, φ)`.
4. **[medium]** Write out PLL2's ND rules and the second-order constraint semantics of §3.3;
   prove soundness. Confirm `∀p.p ≡ ⊥`.
5. **[larger]** Pitts-projection for PLL (§3.5): transport Pitts' argument, with the ◯-case new.
6. **[larger, and probably a negative result]** Undecidability of PLL2 by transport of
   Löb/Sobolev, and non-axiomatisability of the full-range Kripke semantics by transport of
   Kremer/Skvortsov.
7. **[positioning]** Any paper must open by engaging Aczel 2001, Iemhoff 2024, Goldblatt 2011
   and Møgelberg–Simpson 2007, and by citing Valliappan 2026 §6 for the gap.

---

## 5. Bibliography, with verification status

### 5.1 Pitts and IPC2

| Item | Status |
|---|---|
| A. M. Pitts, "On an interpretation of second order quantification in first order intuitionistic propositional logic", *JSL* 57(1):33–52, 1992. DOI 10.2307/2275175 | CONFIRMED |
| D. M. Gabbay, "On 2nd order intuitionistic propositional calculus with full comprehension", *Archiv für math. Logik* 16:177–186, 1974 | SEMI-VERIFIED |
| S. K. Sobolev, "The intuitionistic propositional calculus with quantifiers", *Matematicheskie Zametki* 22:69–76, 1977 | SEMI-VERIFIED |
| M. H. Löb, "Embedding first order predicate logic in fragments of intuitionistic logic", *JSL* 41(4):705–718, 1976 | CONFIRMED |
| D. Skvortsov, "Non-axiomatizable second order intuitionistic propositional logic", *APAL* 86(1):33–46, 1997. DOI 10.1016/S0168-0072(96)00034-6 | CONFIRMED |
| P. Kremer, "On the complexity of propositional quantification in intuitionistic logic", *JSL* 62(2):529–544, 1997. DOI 10.2307/2275545 | CONFIRMED |
| T. Połacik, "Pitts' quantifiers are not topological quantification", *NDJFL* 39(4):531–544, 1998 | CONFIRMED |
| T. Połacik, "Propositional quantification in the monadic fragment of intuitionistic logic", *JSL* 63(1):269–300, 1998 | SEMI-VERIFIED |
| K. Zdanowski, "On second order intuitionistic propositional logic without a universal quantifier", *JSL* 74(1):157–167, 2009. DOI 10.2178/jsl/1231082306 | CONFIRMED |
| K.-E. Fujita, A. Schubert, P. Urzyczyn, K. Zdanowski, "The existential fragment of second-order propositional intuitionistic logic is undecidable", *JANCL* 34(1):55–74, 2024 | SEMI-VERIFIED |
| M. H. Sørensen, P. Urzyczyn, "A syntactic embedding of predicate logic into second-order propositional logic", *NDJFL* 51(4):457–473, 2010. DOI 10.1215/00294527-2010-029 | CONFIRMED |
| M. H. Sørensen, P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, Studies in Logic and the Foundations of Mathematics 149, Elsevier, 2006 | SEMI-VERIFIED |
| P. Kremer, "Completeness of second-order propositional S4 and H in topological semantics", *RSL* 11(3):507–518, 2018. DOI 10.1017/S1755020318000229 | CONFIRMED |
| P. Kremer, "Quantifying over propositions in relevance logic: nonaxiomatisability of primary interpretations of ∀p and ∃p", *JSL* 58(1):334–349, 1993. DOI 10.2307/2275341 | CONFIRMED |
| P. Fritz, *Propositional Quantifiers*, Cambridge Elements in Philosophy and Logic, CUP, 2024. DOI 10.1017/9781009177740 | CONFIRMED |

### 5.2 Uniform interpolation, modal

| Item | Status |
|---|---|
| A. Visser, "Uniform interpolation and layered bisimulation", in P. Hájek (ed.), *Gödel '96*, Lecture Notes in Logic 6, Springer, 1996, pp. 139–164. DOI 10.1007/978-3-662-21963-8_9 | CONFIRMED (contents SEMI-VERIFIED) |
| S. Ghilardi, "An algebraic theory of normal forms", *APAL* 71(3):189–245, 1995. DOI 10.1016/0168-0072(93)E0084-2 | CONFIRMED |
| S. Ghilardi, M. Zawadowski, "Undefinability of propositional quantifiers in the modal system S4", *Studia Logica* 55(2):259–271, 1995. DOI 10.1007/BF01061237 | CONFIRMED |
| S. Ghilardi, M. Zawadowski, "Model completions and r-Heyting categories", *APAL* 88(1):27–46, 1997. DOI 10.1016/S0168-0072(97)00012-2 | CONFIRMED |
| S. Ghilardi, M. Zawadowski, *Sheaves, Games, and Model Completions*, Trends in Logic 14, Kluwer, 2002. DOI 10.1007/978-94-015-9936-8 | CONFIRMED |
| M. Bílková, "Uniform interpolation and propositional quantifiers in modal logics", *Studia Logica* 85(1):1–31, 2007. DOI 10.1007/s11225-007-9021-5 | CONFIRMED (covers K and T only) |
| M. Bílková, "Interpolation in modal logics", PhD thesis, Charles University Prague, 2006 | CONFIRMED |
| M. Bílková, "Uniform interpolation in provability logics", in *Liber Amicorum Alberti*, Tributes 30, College Publications, 2016, pp. 57–90; arXiv:2211.02591 | CONFIRMED |
| V. Yu. Shavrukov, *Subalgebras of diagonalizable algebras of theories containing arithmetic*, Dissertationes Mathematicae 323, Warsaw, 1993, 82 pp. | CONFIRMED (that UI-for-GL is inside: SEMI-VERIFIED) |
| R. Iemhoff, "Uniform interpolation and sequent calculi in modal logic", *Arch. Math. Logic* 58(1–2):155–181, 2019. DOI 10.1007/s00153-018-0629-0 | CONFIRMED |
| R. Iemhoff, "Uniform interpolation and the existence of sequent calculi", *APAL* 170(11):102711, 2019. DOI 10.1016/j.apal.2019.05.008 | CONFIRMED |
| I. van der Giessen, R. Jalali, R. Kuznets, "Uniform interpolation via nested sequents and hypersequents", arXiv:2105.10930 | CONFIRMED (journal data UNVERIFIED) |
| I. van der Giessen, R. Jalali, R. Kuznets, "Interpolation in proof theory", in *Theory and Applications of Craig Interpolation*, Ubiquity Press, 2026; arXiv:2602.16318 | SEMI-VERIFIED |
| H. Férée, I. van der Giessen, S. van Gool, I. Shillito, "Mechanised uniform interpolation for modal logics K, GL, and iSL", IJCAR 2024, LNCS. DOI 10.1007/978-3-031-63501-4_3; arXiv:2402.10494 | CONFIRMED |
| S. J. van Gool, G. Metcalfe, C. Tsinakis, "Uniform interpolation and compact congruences", *APAL* 168(10):1927–1948, 2017. DOI 10.1016/j.apal.2017.05.001 | CONFIRMED |
| T. Kowalski, G. Metcalfe, "Uniform interpolation and coherence", *APAL* 170(7):825–841, 2019. DOI 10.1016/j.apal.2019.02.004 | CONFIRMED |
| G. Metcalfe, "Interpolation and amalgamation", in *Theory and Applications of Craig Interpolation*; arXiv:2512.00924, 2025 | SEMI-VERIFIED |
| L. Maksimova, amalgamation for varieties of Heyting algebras, 1977 | UNVERIFIED |

### 5.3 Propositional quantifiers, modal

| Item | Status |
|---|---|
| K. Fine, "Propositional quantifiers in modal logic", *Theoria* 36(3):336–346, 1970. DOI 10.1111/j.1755-2567.1970.tb00432.x | CONFIRMED |
| R. A. Bull, "On modal logic with propositional quantifiers", *JSL* 34(2):257–263, 1969. DOI 10.2307/2271102 | CONFIRMED |
| D. Kaplan, "S5 with quantifiable propositional variables", *JSL* 35(2):355, 1970 (abstract) | UNVERIFIED |
| M. Kaminski, M. Tiomkin, "The expressive power of second-order propositional modal logic", *NDJFL* 37(1):35–43, 1996. DOI 10.1305/ndjfl/1040067314 | CONFIRMED |
| P. Kremer, "Propositional quantification in the topological semantics for S4", *NDJFL* 38(2):295–313, 1997. DOI 10.1305/ndjfl/1039724892 | CONFIRMED |
| P. Fritz, "Axiomatizability of propositionally quantified modal logics on relational frames", *JSL* 89(2):758–793, 2024. DOI 10.1017/jsl.2022.79 | SEMI-VERIFIED |
| J. Becker, A. Das, S. Marin, P. Padhiar, "The proof theory and semantics of second-order (intuitionistic) tense logic", arXiv:2602.06253, 2026 | CONFIRMED (arXiv) |

### 5.4 Lax logic, nuclei, monads

| Item | Status |
|---|---|
| M. Fairtlough, M. Mendler, "Propositional Lax Logic", *Information and Computation* 137(1):1–33, 1997 | CONFIRMED via four independent secondary sources (ScienceDirect refused fetching) |
| M. Fairtlough, M. Mendler, "An intuitionistic modal logic with applications to the formal verification of hardware", CSL'94, LNCS 933, Springer, 1995, pp. 354–368 | CONFIRMED (note conference 1994 / proceedings 1995) |
| M. Fairtlough, M. Mendler, "On the logical content of computational type theory: a solution to Curry's problem", TYPES 2000, LNCS 2277, Springer, 2002, pp. 63–78 | CONFIRMED |
| M. Fairtlough, M. Mendler, M. Walton, "First-order lax logic as a framework for constraint logic programming", TR MIP-9714, University of Passau, 1997 | SEMI-VERIFIED |
| M. Fairtlough, M. Walton, "Quantified lax logic", TR CS-97-11, University of Sheffield, July 1997 | SEMI-VERIFIED |
| R. Iemhoff, "Proof theory for lax logic", in *Dick de Jongh on Intuitionistic and Provability Logics*, Outstanding Contributions to Logic 28, Springer, 2024, pp. 203–229. DOI 10.1007/978-3-031-47921-2_8; arXiv:2209.08976 | CONFIRMED (abstract fetched) |
| R. Iemhoff, LLAMA/ILLC slides, "On the existence of sequent calculi: uniform interpolation for Lax Logic", 25 January 2023 | SEMI-VERIFIED (source of the GLL rule shapes) |
| P. Aczel, "The Russell–Prawitz modality", *MSCS* 11(4):541–554, 2001 | CONFIRMED |
| P. Aczel, "The Russell–Prawitz modality", in M. Fairtlough (ed.), *Informal Proceedings of IMLA'99*, Trento, 1999 | SEMI-VERIFIED |
| M. Fairtlough, M. Mendler, E. Moggi (eds.), special issue *Modalities in Type Theory*, *MSCS* 11(4), August 2001 | CONFIRMED |
| F. Pfenning, R. Davies, "A judgmental reconstruction of modal logic", *MSCS* 11(4):511–540, 2001 | CONFIRMED |
| J. M. Howe, "Proof search in Lax Logic", *MSCS* 11(4):573–588, 2001 | CONFIRMED |
| P. N. Benton, G. M. Bierman, V. C. V. de Paiva, "Computational types from a logical perspective", *JFP* 8(2):177–193, 1998 | CONFIRMED (no second-order content) |
| E. Moggi, "Notions of computation and monads", *Information and Computation* 93(1):55–92, 1991 | SEMI-VERIFIED |
| R. Goldblatt, "Cover semantics for quantified lax logic", *JLC* 21(6):1035–1063, 2011. DOI 10.1093/logcom/exq029 | CONFIRMED (first-order) |
| R. Goldblatt, "Grothendieck topology as geometric modality", *Zeitschrift für math. Logik und Grundlagen der Math.* 27:495–529, 1981; reprinted in *Mathematics of Modality*, CSLI Lecture Notes 43, 1993 | SEMI-VERIFIED |
| N. Valliappan, "Lax modal lambda calculi", CSL 2026, LIPIcs 363, art. 49; arXiv:2512.10779 | CONFIRMED (arXiv); LIPIcs numbering SEMI-VERIFIED |
| R. E. Møgelberg, A. Simpson, "Relational parametricity for computational effects", LICS 2007; *LMCS*; arXiv:0906.5488 | CONFIRMED (arXiv); LMCS data UNVERIFIED |
| R. E. Møgelberg, A. Simpson, "A logic for parametric polymorphism with effects", TYPES 2007, LNCS 4941, pp. 142–156, 2008 | SEMI-VERIFIED |
| G. Bezhanishvili, N. Bezhanishvili, L. Carai, D. Gabelaia, S. Ghilardi, M. Jibladze, "Diego's theorem for nuclear implicative semilattices", *Indagationes Mathematicae* 32(2):498–535, 2021. DOI 10.1016/j.indag.2020.12.005; arXiv:2001.11060 | CONFIRMED (full text read) |
| G. Bezhanishvili, N. Bezhanishvili, "Locally finite reducts of Heyting algebras and canonical formulas", *NDJFL* 58(1):21–45, 2017. DOI 10.1215/00294527-3691563 | CONFIRMED (pages SEMI-VERIFIED) |
| G. Bezhanishvili, S. Ghilardi, "An algebraic approach to subframe logics. Intuitionistic case", *APAL* 147(1–2):84–100, 2007. DOI 10.1016/j.apal.2007.04.001 | CONFIRMED |
| M. Erné, "Nuclear ranges in implicative semilattices", *Algebra Universalis* 83(2), 2022. DOI 10.1007/s00012-022-00768-3 | CONFIRMED |
| D. S. Macnab, "Modal operators on Heyting algebras", *Algebra Universalis* 12:5–29, 1981 | SEMI-VERIFIED |
| S. Ghilardi, G. Lenzi, "Unification in lax logic", *J. Algebraic Hyperstructures and Logical Algebras* 3(1):61–75, 2022. DOI 10.52547/HATEF.JAHLA.3.1.6 | SEMI-VERIFIED |
| S. A. Celani, D. Montangie, "Algebraic semantics of the {→,□}-fragment of Propositional Lax Logic", *Soft Computing* 24:813–823, 2020. DOI 10.1007/s00500-019-04536-9 | SEMI-VERIFIED |
| U. Egly, "Embedding lax logic into intuitionistic logic", CADE-18, LNCS 2392, 2002 (yields PSPACE-completeness of PLL provability) | SEMI-VERIFIED; pages UNVERIFIED |
| S. Kobayashi, "Monad as modality", *Theoretical Computer Science* 175(1):29–74, 1997 | SEMI-VERIFIED |
| H. B. Curry, "The elimination theorem when modality is present", *JSL* 17(4):249–265, 1952 | SEMI-VERIFIED |
| E. Rijke, M. Shulman, B. Spitters, "Modalities in homotopy type theory", arXiv:1706.07526; *LMCS* | SEMI-VERIFIED |
| Y. Lafont, "Soft linear logic and polynomial time", *TCS* 318(1–2):163–180, 2004 | CONFIRMED (the SLL collision) |

### 5.5 Things I could not settle

* Whether Filinski's thesis (*Controlling Effects*, CMU-CS-96-119, 1996) contains a polymorphic
  monadic metalanguage. UNVERIFIED.
* Whether Moggi's *Metalanguages and applications* (in Pitts & Dybjer (eds.), *Semantics and
  Logics of Computation*, CUP, 1997) or Benton–Hughes–Moggi's APPSEM notes (*Monads and
  Effects*, LNCS 2395, reported pp. 42–122) give a worked second-order monadic metalanguage.
  UNVERIFIED.
* Exact page numbers for Egly (LNCS 2392) and the LMCS data for Møgelberg–Simpson. UNVERIFIED.
* Maksimova's 1977 amalgamation reference, and whether the count of Heyting varieties with
  amalgamation is stated as eight or seven-non-trivial. Sources differ; count before writing.

### 5.6 Name-collision audit

| Name | Verdict |
|---|---|
| "quantified lax logic" / QLL | TAKEN, first-order: Fairtlough–Walton TR CS-97-11 (1997); Goldblatt *JLC* 2011 |
| "first-order lax logic" | TAKEN: Fairtlough–Mendler–Walton TR MIP-9714 (1997); Walton 1998 |
| SLL | TAKEN = soft linear logic (Lafont, *TCS* 2004) |
| LL2 / MALL2 / IMLL2 | TAKEN, standard for second-order linear logic |
| PLL | already overloaded in logic: propositional lax logic; polarised linear logic; parsimonious linear logic |
| SL / SRL / SJL | TAKEN since December 2025 (Valliappan, CSL 2026) |
| QPLL | FREE in logic (only hardware hits) |
| **PLL2** | **FREE — zero hits in logic** |
| ∀PLL | no hits; UNVERIFIED but almost certainly free |

### 5.7 Search audit for the negative result

The "second-order PLL does not exist" claim rests on these searches returning nothing relevant:
exact-phrase `"second-order lax logic"`; `"PLL2"`; `"quantified propositional lax logic"`;
`"impredicative lax logic"`; `"lax logic" "propositional quantifiers"`; `"lax logic"
"propositional quantification"`; `"second-order nuclei"`; `"quantification over nuclei"`;
a dblp API full search on `lax logic` (100 results, the entire lax-logic corpus, no second-order
entry); a dblp API full search on `Fairtlough` (complete list, 7 items, none second-order); and
targeted searches over Moggi, Wadler, Filinski, Plotkin–Power, Hasegawa, Benton–Bierman–de Paiva
and Pfenning–Davies for a polymorphic monadic metalanguage. Positive hits are all listed in
§2.5. The absence is a search result, not a proof of non-existence, but it is thorough and it is
corroborated by Valliappan's own "further work" statement (December 2025).

---

## 6. Repository cross-references

* `LaxLogic/LJF.lean` — the focused calculus and the UI engine; Part 2 the weighted recursion,
  Part 4 `eSound`/`aSound` (E1/A1, unconditional), Part 5 `eMin`/`aMin` (E2/A2, modulo the
  saturated-context hypotheses `SatE2`/`SatA2`). The contract is stated in the block headed
  "The contract that remains".
* `LaxLogic/PLLFocused.lean` — `LJF◯`, the lax extension; `circL` is the `L◯` rule, in the
  `.lax` mode.
* `LaxLogic/PLLKripke.lean` — `ConstraintModel`, the fallible two-frame semantics used in §3.3.
* `LaxLogic/PLLFrames.lean` — F&M's three countermodels by `decide`, including the `◯⊥`
  countermodel that Proposition B (§3.4) rests on.
* `LaxLogic/PLLAxiom.lean` — the Hilbert axioms `somehowR`, `somehowM`, `somehowS`,
  `somehowBind` quoted in §3.2.
* `docs/calculus-map.md` — which system each result belongs to; read before asserting
  provenance.
* `docs/nuclei-noncomplete-lit.md`, `docs/assembly-tower-lit.md` — the existing nuclei/assembly
  thread, which §3.4's Proposition C connects to.
* `docs/surveys/nuclei-model-completions-monads.md` — the adjacent survey on nuclei, model
  completions and monads; §2.2's model-completion caveat belongs with it.
