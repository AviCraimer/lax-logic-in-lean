All verification clusters are in. I've independently confirmed every load-bearing citation (Negri 2005, Schröder–Pattinson 2010, Licata–Shulman–Riley 2017, Gratzer 2020/2022, Benton–Bierman–de Paiva 1998, Pitts 1992, Ghilardi–Zawadowski 1995, Iemhoff 2019 with the "focused" terminology resolved, Maksimova 1977/1979, and the Melzer thesis). Here is the assembled report.

---

# Organising the Zoo: Frameworks and Invariants for Modal Proof Theory

*A structured literature review, prepared for a category-theory-fluent logician who finds proof theory "a big mixed bag of diverse calculi, hard to classify."*

The short answer to the framing question: order exists, but it comes in two distinct kinds. **(A)** *Uniform metatheorems parameterised by structured data* — four frameworks each prove cut-elimination/completeness *once*, for every logic presented by data of a certain shape (an axiom's position in a syntactic hierarchy, an analytic-inductive formula, a geometric frame condition, a rank-1 functor, a mode 2-category). **(B)** *Logic-level invariants with algebraic or categorical content* — interpolation-like properties that classify the lattice of logics and, in the newest work ("universal proof theory"), *obstruct* the existence of calculi. The two are converging, and lax logic sits at a well-charted point in both.

---

## 1. Organising frameworks for modal/substructural proof theory

### 1.1 Algebraic proof theory: the substructural hierarchy

- **A. Ciabattoni, N. Galatos, K. Terui, "From axioms to analytic rules in nonclassical logics", LICS 2008, IEEE, pp. 229–240.**
- **A. Ciabattoni, N. Galatos, K. Terui, "Algebraic proof theory for substructural logics: cut-elimination and completions", Annals of Pure and Applied Logic 163(3):266–290, 2012.**
- **A. Ciabattoni, N. Galatos, K. Terui, "Algebraic proof theory: hypersequents and hypercompletions", Annals of Pure and Applied Logic 168(3):693–737, 2017.**
- Background algebra: **N. Galatos, P. Jipsen, T. Kowalski, H. Ono, *Residuated Lattices: An Algebraic Glimpse at Substructural Logics*, Studies in Logic and the Foundations of Mathematics 151, Elsevier, 2007.**

**What it settles.** Axioms over full Lambek calculus FL are stratified into classes N_n/P_n by alternating the polarity (invertibility behaviour) of their outermost connectives, in deliberate analogy with the arithmetical hierarchy. The classification theorem: every axiom in **N₂** (e.g. weakening, exchange, contraction, knotted rules) is effectively equivalent to a finite set of *analytic structural sequent rules* preserving cut-elimination; every axiom in **P₃** (in the presence of weakening, P₃′ — e.g. prelinearity, weak excluded middle) converts to analytic *hypersequent* structural rules. The semantic counterpart is the deepest part: cut-elimination for the extended calculus is equivalent to closure of the corresponding variety of FL-algebras under **MacNeille completions** (hyper-MacNeille for the hypersequent level), so cut-elimination is proved once per hierarchy level by an algebraic completion argument rather than calculus-by-calculus rewriting. Matching limitative results show the correspondence is essentially optimal at each level — some axioms just above each threshold provably admit no analytic structural extension of the given format. This is the closest thing structural proof theory has to a classification theorem; its honest limits are that it is native to substructural (residuated-lattice) logics, the hierarchy climbs out of reach quickly (the general case above P₃ is open-to-impossible), and normal modal operators enter only via embeddings.

### 1.2 Display logic and the analytic-inductive classification

- **N. D. Belnap, "Display logic", Journal of Philosophical Logic 11(4):375–417, 1982.**
- **H. Wansing, *Displaying Modal Logic*, Trends in Logic 3, Kluwer, 1998.**
- **M. Kracht, "Power and weakness of the modal display calculus", in H. Wansing (ed.), *Proof Theory of Modal Logic*, Kluwer, 1996.**
- **W. Conradie, A. Palmigiano, "Algorithmic correspondence and canonicity for distributive modal logic", Annals of Pure and Applied Logic 163(3):338–376, 2012** (the ALBA algorithm).
- **G. Greco, M. Ma, A. Palmigiano, A. Tzimoulis, Z. Zhao, "Unified correspondence as a proof-theoretic tool", Journal of Logic and Computation 28(7):1367–1442, 2018.**

**What it settles.** Belnap's insight is congenial to a categorist: introduce enough structural connectives that every substructure can be *displayed* as the whole antecedent or succedent — and the display postulates enabling this are precisely residuation/adjunction laws. Any calculus satisfying Belnap's conditions C1–C8 gets cut-elimination *as a metatheorem* (C8 is the one local principal-cut condition to check). Wansing built the modal instances; Kracht proved the first genuine classification: the properly displayable tense logics are exactly those axiomatised by *primitive tense formulas*. The Greco–Ma–Palmigiano–Tzimoulis–Zhao line generalises Kracht via unified correspondence: the ALBA algorithm (Conradie–Palmigiano) eliminates propositional variables by Ackermann-lemma manoeuvres, and the axioms it succeeds on in a syntactically recognisable way — the **analytic inductive** inequalities — are exactly those convertible into analytic structural rules of a *proper display calculus*. So the display world has a decidable syntactic characterisation of "displayable", uniformly across signatures (including non-classical and multi-type settings). The honest cost: proliferating structural connectives, a subformula property only in a weakened (structure-level) sense, and the requirement that every connective have residuals — display logic works exactly where adjoints exist, which is illuminating and restrictive at once.

### 1.3 Labelled, nested, and hypersequent calculi: the jungle and its maps

- **S. Negri, "Proof analysis in modal logic", Journal of Philosophical Logic 34(5–6):507–544, 2005.** Uniform cut- and contraction-admissible *labelled* calculi (sequents over formulas x:A and relational atoms xRy) for every modal logic whose frame class is defined by *universal or geometric* conditions, via the geometric rule scheme; GL gets a bespoke labelled treatment beyond the scheme. Geometric means coherent ∀∃-conditions over atoms — transitivity, seriality, symmetry, Euclideanness, directedness all qualify; genuinely second-order or induction-flavoured conditions (McKinsey, Löb in general) do not. **R. Dyckhoff, S. Negri, "Geometrisation of first-order logic", Bulletin of Symbolic Logic 21(2):123–163, 2015** extends the reach in principle: every first-order theory has a geometric conservative extension. Survey: **S. Negri, "Proof theory for modal logic", Philosophy Compass 6(8):523–538, 2011.** The intuitionistic-modal ancestor is **A. Simpson's** Edinburgh PhD thesis (*The Proof Theory and Semantics of Intuitionistic Modal Logic*, 1994).
- **K. Brünnler, "Deep sequent systems for modal logic", Archive for Mathematical Logic 48(6):551–577, 2009** and **F. Poggiolesi, "The method of tree-hypersequents for modal propositional logic", in *Towards Mathematical Philosophy*, Trends in Logic, Springer, 2009; *Gentzen Calculi for Modal Propositional Logic*, Trends in Logic 32, Springer, 2011.** Nested sequents = trees of sequents (tree-hypersequents are notational variants); they give internal, label-free cut-free systems for the modal cube.
- **A. Avron, "The method of hypersequents in the proof theory of propositional non-classical logics", in *Logic: From Foundations to Applications*, Oxford University Press, 1996, pp. 1–32** (hypersequents originate with Avron 1987 and, independently, Pottinger 1983). Finite multisets of sequents with communication rules capture what single sequents cannot — S5, Gödel–Dummett LC, and, via §1.1, all of P₃.
- The maps between formalisms: **R. Goré, R. Ramanayake, "Labelled tree sequents, tree hypersequents and nested (deep) sequents", Advances in Modal Logic 9, College Publications, 2012** (nested = labelled restricted to trees); **A. Ciabattoni, R. Ramanayake, "Power and limits of structural display rules", ACM Transactions on Computational Logic 17(3), Article 17, 2016**; **A. Ciabattoni, R. Ramanayake, H. Wansing, "Hypersequent and display calculi — a unified perspective", Studia Logica 102(6):1245–1294, 2014.**

**What it settles — and doesn't.** Each formalism comes with a genuine uniform theorem: Negri's geometric scheme is the broadest single cut-elimination metatheorem in the field. The translation papers establish a rough hierarchy of generative power — sequent ⊂ hypersequent ⊂ nested ⊂ labelled ≈ display — with precise embeddings on overlapping fragments. But there is *no accepted master classification*: the hierarchy is a patchwork of pairwise translations, "internal vs. external" (label-free vs. semantics-importing) remains partly a philosophical distinction, and conservativity questions across formalisms are settled case-by-case. This subfield is exactly the "big mixed bag" of the complaint; Ciabattoni–Ramanayake(–Wansing) are the ones actively drawing the map.

### 1.4 Coalgebraic modal logic: the rank-1 metatheorem

- **D. Pattinson, "Coalgebraic modal logic: soundness, completeness and decidability of local consequence", Theoretical Computer Science 309(1–3):177–193, 2003.**
- **L. Schröder, "A finite model construction for coalgebraic modal logic", Journal of Logic and Algebraic Programming 73(1–2):97–110, 2007.**
- **L. Schröder, D. Pattinson, "Rank-1 modal logics are coalgebraic", Journal of Logic and Computation 20(5):1113–1147, 2010** (conference version STACS 2007).
- **L. Schröder, D. Pattinson, "PSPACE bounds for rank-1 modal logics", ACM Transactions on Computational Logic 10(2), Article 13, 2009.**
- **D. Pattinson, L. Schröder, "Cut elimination in coalgebraic logics", Information and Computation 208(12):1447–1468, 2010.**
- Survey: **C. Kupke, D. Pattinson, "Coalgebraic semantics of modal logics: an overview", Theoretical Computer Science 412(38):5070–5094, 2011.**

**What it settles.** Semantics: coalgebras for an endofunctor T on **Set**, modalities interpreted by predicate liftings. A logic is **rank-1** when its axioms put every variable under exactly one layer of modality. The theorems: every rank-1 logic *is* coalgebraic (it has a sound and strongly complete coalgebraic semantics, built canonically and finally from its own axioms — Schröder–Pattinson 2010), and **one-step completeness** — completeness of the rule set at the level of a single functor application, with variables ranging over subsets — automatically lifts to full completeness, cut-free sequent systems (Pattinson–Schröder 2010), the finite model property, and generic PSPACE decision procedures. This covers K, KD, graded, probabilistic, coalition/game logics and more, uniformly — a genuine "insert functor, receive metatheory" pipeline, the cleanest uniform metatheorem in modal logic. The boundary is equally crisp: **rank 1 only**. The 4 axiom □p→□□p, S4, GL — anything iterative — has rank ≥ 2 and falls outside; extensions (copointed functors for the T axiom, "Beyond rank 1" work, coalgebraic fixpoint logics) exist but lose the fully automatic guarantee. Note for lax logic: ○○A→○A is precisely a rank-2 axiom, so PLL, like S4, lives outside the automatic zone — its monad multiplication is *the* obstruction.

---

## 2. Categorical and type-theoretic presentations

### 2.1 Adjoint logic and mode theories

- **P. N. Benton, "A mixed linear and non-linear logic: proofs, terms and models", CSL 1994, Springer LNCS 933, pp. 121–135, 1995.** LNL: a symmetric monoidal adjunction F ⊣ G between a cartesian and a linear category; the exponential ! decomposes as G∘F. The template for everything below. (The monad-side counterpart is **P. N. Benton, P. Wadler, "Linear logic, monads and the lambda calculus", LICS 1996**, which connects LNL to Moggi's monads.)
- **J. Reed, "A judgmental deconstruction of modal logic", unpublished manuscript, 2009.** Decomposes □ and ◇ into adjoint pairs between judgmental layers; the direct ancestor of mode theories.
- **D. R. Licata, M. Shulman, "Adjoint logic with a 2-category of modes", LFCS 2016, Springer LNCS 9537, 2016.**
- **D. R. Licata, M. Shulman, M. Riley, "A fibrational framework for substructural and modal logics", FSCD 2017, LIPIcs 84, 25:1–25:22, 2017.**
- **K. Pruiksma, F. Pfenning, "A message-passing interpretation of adjoint logic", Journal of Logical and Algebraic Methods in Programming, 2021** (earlier PLACES 2019); manuscript **K. Pruiksma, W. Chargin, J. Reed, F. Pfenning, "Adjoint logic", CMU, 2018.**

**What it settles.** The unifying move: a **mode theory** — a 2-category (in LSR, a cartesian 2-multicategory) of modes — is the *parameter*. Propositions live at modes; each mode morphism α generates an adjoint pair of modal connectives F_α ⊣ U_α; 2-cells generate structural transformations (weakening, contraction, exchange become mode-theory data, so "substructural" and "modal" are the same phenomenon). Cut-elimination is proved **once**, for an arbitrary mode theory. Monads and comonads arise as the composites U∘F and F∘U — Benton's LNL is the one-adjunction instance, and lax logic's ○ is exactly the monad of a single adjunction: a *one-morphism mode theory* (one generating 1-cell with monad-structure 2-cells, or equivalently two modes with an adjoint generating pair). Assessment: this genuinely dissolves a large part of the "mixed bag" — dozens of previously separate calculi become instances — but the guarantee is about the *judgmental core* (cut-elimination, identity expansion). It does not by itself deliver decidability, complexity, semantic completeness for a given Kripke reading, or any logic-level invariant.

### 2.2 Multimodal type theory and normalisation-once

- **D. Gratzer, G. A. Kavvos, A. Nuyts, L. Birkedal, "Multimodal Dependent Type Theory", LICS 2020; journal version Logical Methods in Computer Science 17(3), 2021.** MTT: a dependent type theory parameterised by an arbitrary strict 2-category of modes; each modality μ becomes a type constructor ⟨μ|−⟩, semantically a (weak) *dependent right adjoint*. Canonicity is proved by gluing, uniformly in the mode theory.
- **D. Gratzer, "Normalization for multimodal type theory", LICS 2022** (extended version arXiv:2301.11842, in LMCS). Normalisation for MTT proved **once, for an arbitrary mode 2-category**, by a modal generalisation of synthetic Tait computability; corollaries include decidability of definitional equality (relative to decidability of the mode theory) and injectivity of type constructors.
- **R. Clouston, "Fitch-style modal lambda calculi", FoSSaCS 2018, Springer LNCS 10803, 2018.** The "locks" presentation of necessity; MTT's context locks generalise it.
- **F. Pfenning, R. Davies, "A judgmental reconstruction of modal logic", Mathematical Structures in Computer Science 11(4):511–540, 2001.** Dual-context □ and ◇ — and, importantly here, an explicit judgmental treatment of **lax truth**, exhibiting lax logic as a well-behaved judgmental fragment alongside S4.
- **G. A. Kavvos, "Dual-context calculi for modal logic", LICS 2017; extended version Logical Methods in Computer Science 16(3), 2020.** Systematises dual-context calculi for K, T, K4, S4 (and GL), with categorical semantics.

**How far is this "a satisfactory theory of modal logics"?** Gratzer's theorem is the strongest uniform metatheorem in the area: one proof, every mode theory, hence simultaneous normalisation for guarded recursion calculi, internalised parametricity, Fitch-style S4, and the rest. Three honest limits. (i) *Right-adjoint bias*: MTT modalities must be modelled as dependent right adjoints; monad-like modalities enter by decomposing through an adjunction between modes — fine for lax (Kleisli/Eilenberg–Moore decompositions exist), but left-adjoint-natively one needs Shulman's multimodal *adjoint* type theory (**M. Shulman, "Semantics of multimodal adjoint type theory", arXiv:2303.02572, 2023** [venue of record UNVERIFIED]). (ii) The mode theory is an *input*: nothing classifies which mode 2-categories are reasonable, and an undecidable mode theory poisons decidability downstream. (iii) It is a theory of *proof systems and their equational metatheory*, not of the lattice of logics: interpolation, FMP, admissibility, complexity are untouched. In short: it realises "satisfactory" for the judgmental/computational half of the subject, and is silent on the half in §3.

### 2.3 Where lax logic sits

- **H. B. Curry, "The elimination theorem when a modality is present", Journal of Symbolic Logic 17(4):249–265, 1952** — the lax modality's sequent rules avant la lettre.
- **R. Goldblatt, "Grothendieck topology as geometric modality", Zeitschrift für mathematische Logik und Grundlagen der Mathematik 27:495–529, 1981** — ○ as a nucleus / Lawvere–Tierney topology.
- **M. Fairtlough, M. Mendler, "Propositional lax logic", Information and Computation 137(1):1–33, 1997** — PLL: the single modality ○ with unit and multiplication, "possibility-like and necessity-like at once"; constraint Kripke semantics; FMP and decidability.
- **E. Moggi, "Computational lambda-calculus and monads", LICS 1989; "Notions of computation and monads", Information and Computation 93(1):55–92, 1991.**
- **P. N. Benton, G. M. Bierman, V. C. V. de Paiva, "Computational types from a logical perspective", Journal of Functional Programming 8(2):177–193, 1998** — Moggi's metalanguage *is* the Curry–Howard image of PLL; semantics: a strong monad on a cartesian closed category; strong normalisation and confluence proved.
- **N. Alechina, M. Mendler, V. de Paiva, E. Ritter, "Categorical and Kripke semantics for constructive S4 modal logic", CSL 2001, Springer LNCS 2142, 2001** — CS4 models: □ a monoidal comonad, ◇ a □-strong monad; PLL is exhibited as the degenerate case where the comonad is trivial, making precise the folklore reading of ○ as a fused ◇□.
- Survey of the nucleus/lax landscape: **T. Litak, "Constructive modalities with provability smack", in G. Bezhanishvili (ed.), *Leo Esakia on Duality in Modal and Intuitionistic Logics*, Springer, 2014.**

**Assessment.** Lax logic is the *minimal nontrivial instance* of every framework in §2: the one-morphism mode theory, the monad half of Benton's adjunction, Moggi's T, the nucleus of Goldblatt. Every general framework above should — and essentially does — subsume it; conversely PLL is a sharp test case because its rank-2 axiom keeps it *out* of the coalgebraic automatic zone (§1.4), and its N₂-flavoured axioms keep it well within reach of Negri-style labelled treatment and G4-style terminating calculi.

---

## 3. Cohering logic-level properties

### 3.1 Interpolation: Craig, Lyndon, uniform — and the obstruction theorem

*Definitions.* Craig: ⊢A→B implies ⊢A→I and ⊢I→B for some I in the shared vocabulary. Lyndon: additionally respecting polarity of variable occurrences. **Uniform**: the interpolant depends only on A and the shared vocabulary — equivalently, propositional quantifiers ∃p/∀p are definable; categorically, left/right adjoints to the substitution-inclusion, an unmistakably adjoint-flavoured strengthening.

- **A. M. Pitts, "On an interpretation of second order quantification in first order intuitionistic propositional logic", Journal of Symbolic Logic 57(1):33–52, 1992.** IPC has uniform interpolation, proved proof-theoretically via a terminating (Dyckhoff-style) calculus.
- **S. Ghilardi, M. Zawadowski, "Undefinability of propositional quantifiers in the modal system S4", Studia Logica 55(2):259–271, 1995.** **S4 has Craig but fails uniform interpolation** — the invariant genuinely separates. Their book, ***Sheaves, Games, and Model Completions*, Trends in Logic 14, Kluwer, 2002**, recasts uniform interpolation as existence of model completions / sheaf-duality — the categorical restatement.
- **M. Bílková, "Uniform interpolation and propositional quantifiers in modal logics", Studia Logica 85(1), 2007.** Pitts-style uniform interpolation for K and T; for GL, uniform interpolation goes back to **V. Yu. Shavrukov (Dissertationes Mathematicae 323, 1993)** [attribution split K/T vs GL per the published versions — the brief's "Bílková for K/GL" is approximately right but GL's priority is Shavrukov's].
- **R. Iemhoff, "Uniform interpolation and the existence of sequent calculi", Annals of Pure and Applied Logic 170(11), 2019**; companion **"Uniform interpolation and sequent calculi in modal logic", Archive for Mathematical Logic 58, 2019.** The universal-proof-theory result: any (intuitionistic) modal or intermediate logic possessing a *terminating* sequent calculus whose rules are **focused** (her term; "centered" appears in some secondary paraphrases) has uniform interpolation. **Contrapositive — the obstruction**: K4 and S4, lacking uniform interpolation, *cannot have any* terminating calculus of focused rules, no matter how ingenious. A semantic invariant thus bounds all possible proof systems of a given shape. Parallel programme: **A. Akbar Tabatabai, R. Jalali, "Universal proof theory: semi-analytic rules and Craig interpolation", arXiv:1808.06256** [journal venue UNVERIFIED].

**What it coheres.** This is the property doing exactly what the reader wants interpolation to do: it separates logics (S4 from K/GL/IPC), it has an algebraic/categorical avatar (§3.6, model completions), and via Iemhoff it *classifies calculi negatively* — the first genuinely load-bearing bridge from invariants back to the proof-theory zoo.

### 3.2 Admissible rules and unification type

*Definitions.* A rule is admissible if adding it derives no new theorems; unification type (unitary/finitary/infinitary/nullary) measures whether most general unifiers modulo the logic exist.

- **S. Ghilardi, "Unification in intuitionistic logic", Journal of Symbolic Logic 64(2):859–880, 1999**; **"Best solving modal equations", Annals of Pure and Applied Logic 102(3):183–198, 2000.** Projective formulas and finitary unification for IPC and the transitive modal logics; the engine behind everything else here.
- **R. Iemhoff, "On the admissible rules of intuitionistic propositional logic", Journal of Symbolic Logic 66(1):281–294, 2001.** The Visser rules form a basis for IPC's admissible rules.
- **E. Jeřábek, "Admissible rules of modal logics", Journal of Logic and Computation 15(4):411–431, 2005**; **"Independent bases of admissible rules", Logic Journal of the IGPL 16(3), 2008.** Bases for K4, GL, S4, Grz; decidability of admissibility for the transitive family.

**What it coheres.** Admissibility sees structure invisible at the theorem level: logics with identical theorems can differ in admissible rules, and *structural completeness* (all admissibles derivable) carves a classifiable subfamily. The frontier is honest and famous: for basic K, decidability of admissibility and the unification type remain open. Directly relevant here: **I. van der Giessen, *Uniform Interpolation and Admissible Rules: proof-theoretic investigations into (intuitionistic) modal logics*, PhD thesis, Utrecht University, 2022**, carries this whole programme into the intuitionistic-modal family including lax logic [thesis verified; per-chapter PLL claims not independently checked — the associated G4-style terminating calculus for PLL from the Iemhoff school is the natural base for such results; primary venue UNVERIFIED].

### 3.3 Disjunction property and Halldén completeness

DP: ⊢A∨B implies ⊢A or ⊢B. Halldén completeness: the same for *variable-disjoint* A, B (**S. Halldén, Journal of Symbolic Logic 16, 1951**; frame-gluing characterisation in **J. van Benthem, I. L. Humberstone, Notre Dame Journal of Formal Logic 24, 1983**). Both are classical cohering invariants — DP is the constructivity signature, Halldén completeness has meet-irreducibility-flavoured characterisations in the lattice of logics — but neither classifies as sharply as interpolation; the compendium treatment is **A. Chagrov, M. Zakharyaschev, *Modal Logic*, Oxford Logic Guides 35, Clarendon Press, 1997.**

### 3.4 Canonical formulas: coordinates for the lattice of logics

- **M. Zakharyaschev, "Canonical formulas for K4. Part I", Journal of Symbolic Logic 57(4):1377–1402, 1992; "Part II: Cofinal subframe logics", JSL 61(2):421–449, 1996.** Every normal extension of K4, and every superintuitionistic logic, is axiomatisable by canonical formulas — frame-combinatorial coordinates for the whole lattice; subframe and cofinal-subframe logics fall out as the well-behaved (FMP) bands.
- **G. Bezhanishvili, N. Bezhanishvili, "An algebraic approach to canonical formulas: intuitionistic case", Review of Symbolic Logic 2(3):517–549, 2009** (modal case in Studia Logica 99, 2011). Reworks Zakharyaschev's machinery through locally finite reducts and duality.
- **E. Jeřábek, "Canonical rules", Journal of Symbolic Logic 74(4):1171–1205, 2009.** Lifts the apparatus to multiple-conclusion *rule systems*, unifying §3.2 and §3.4: canonical rules axiomatise all rule systems over K4/IPC.
- **S. D. Melzer, *Canonical Formulas for the Lax Logic*, MSc thesis, ILLC, University of Amsterdam, MoL-2020-13, 2020** (supervised by N. Bezhanishvili). **Every extension of PLL is axiomatisable by lax canonical formulas**; introduces *steady* lax logics (the subframe-analogue — all with FMP, generated by subframe-closed classes) via nuclear Esakia duality, and proves a lax Dummett–Lemmon theorem. The Zakharyaschev-style classification *exists for the reader's own logic*.

**What it coheres.** Canonical formulas are the nearest thing to a periodic table: a complete, combinatorially indexed axiomatisation device for entire lattices of logics — with the honest restriction that the technology is native to transitive/superintuitionistic (and now nuclear/lax) settings; K itself resists.

### 3.5 Feasible interpolation: invariants meet complexity

- **J. Krajíček, "Interpolation theorems, lower bounds for proof systems, and independence results for bounded arithmetic", Journal of Symbolic Logic 62(2):457–486, 1997.**
- **P. Pudlák, "Lower bounds for resolution and cutting plane proofs and monotone computations", Journal of Symbolic Logic 62(3):981–998, 1997.**

**What it coheres.** If interpolants can be extracted from proofs in polynomial size (feasible interpolation), then proof-size lower bounds follow from circuit lower bounds — resolution and cutting planes fall to monotone-circuit bounds this way; conversely, strong systems (Frege and up) lack feasible interpolation under cryptographic assumptions. The same style transfers to modal and intuitionistic Frege systems (**P. Hrubeš, "Lower bounds for modal logics", JSL 72(3), 2007; "A lower bound for intuitionistic logic", APAL 146, 2007**). Interpolation is thus not merely a purity test: it is a *complexity-theoretic* invariant of calculi.

### 3.6 Amalgamation and Beth: Maksimova's paradigm

- **L. L. Maksimova, "Craig's theorem in superintuitionistic logics and amalgamable varieties of pseudo-Boolean algebras", Algebra i Logika 16(6):643–681, 1977** (English: Algebra and Logic 16:427–455). Craig interpolation in a superintuitionistic logic ⟺ the amalgamation property of the corresponding variety of Heyting algebras — and there are **exactly eight** such superintuitionistic logics (the count's inclusion of degenerate cases is convention-dependent; the definitive treatment is **D. M. Gabbay, L. Maksimova, *Interpolation and Definability: Modal and Intuitionistic Logics*, Oxford Logic Guides 46, OUP, 2005**).
- **L. L. Maksimova, "Interpolation theorems in modal logics and amalgamable varieties of topological Boolean algebras", Algebra and Logic 18(5):348–370, 1979.** For NExt S4 she pinned interpolation down to at most 37 candidates with six left open; the classification was completed only recently — the six open cases have interpolation, so **exactly 37** normal extensions of S4 have Craig interpolation (**Santschi–Vooijs, "Interpolation above S4", arXiv:2604.22020, 2026**, as reported in current surveys).
- **W. J. Blok, E. Hoogland, "The Beth property in algebraic logic", Studia Logica 83(1–3):49–90, 2006.** Beth definability ⟺ epimorphisms are surjective in the algebraic counterpart; a classical result going back to Kreisel (1960) [exact citation UNVERIFIED] gives Beth for *all* superintuitionistic logics — a lovely contrast: Beth is ubiquitous where Craig is vanishingly rare.

**What it coheres.** This is the model the reader is implicitly asking for: a logic-level property equals a category-shaped property of the algebraic semantics (amalgamation of spans; surjectivity of epis), and the resulting classifications are *finite lists* over infinite lattices. Uniform interpolation upgrades the correspondence to model completions and sheaf duality (Ghilardi–Zawadowski). Everything in §3.1 and §3.6 together says: interpolation-like invariants are the genuinely cohering ones because they are simultaneously (i) algebraically characterisable, (ii) rare enough to classify, and (iii) — since Iemhoff — obstructions on the space of possible calculi.

---

## 4. Closing assessment

**What could "a satisfactory theory" mean?** The field's actual shape suggests: a family of *uniform metatheorems parameterised by structured data*, plus a family of *invariants that classify logics and obstruct calculi*, with translation results knitting the parameter spaces together. Each framework in §1–§2 is exactly such a metatheorem — parameterised respectively by hierarchy level (N₂/P₃ + MacNeille closure), analytic-inductive shape (ALBA), geometric frame conditions (Negri), a rank-1 functor (Schröder–Pattinson), a mode 2-category (LSR; Gratzer). The "mixed bag" impression comes from the fact that these parameter spaces are heterogeneous and only partially inter-translatable. The honest frontiers: nothing classifies beyond P₃-ish levels or outside transitive settings; rank 1 is a hard wall for automatic coalgebraic metatheory; the labelled/nested/internal question lacks a master theorem; MTT-style results are right-adjoint-biased and say nothing about logic-level invariants; and proof *identity* (when are two derivations the same map?) — the categorical question par excellence — remains essentially untheorised for modal calculi. The most promising convergence is universal proof theory: theorems of the form "calculus of shape X exists ⟹ invariant P holds", which turn the §3 invariants into charts of what proof theory can *possibly* do. Lax logic is unusually well-placed: minimal mode theory (§2), canonical-formula classification (Melzer), FMP and terminating calculi, and open, well-posed questions (uniform interpolation for PLL; its exact place in the Iemhoff obstruction landscape).

**Reading order (most load-bearing first):**

1. **Ciabattoni–Galatos–Terui**, "Algebraic proof theory for substructural logics", *APAL* 163, 2012 — the classification backbone; read LICS 2008 first for the idea.
2. **Greco–Ma–Palmigiano–Tzimoulis–Zhao**, "Unified correspondence as a proof-theoretic tool", *JLC* 28, 2018 (with Kracht 1996 for lineage) — the display-side classification.
3. **Negri**, "Proof analysis in modal logic", *JPL* 34, 2005 — the broadest single cut-elimination metatheorem.
4. **Schröder–Pattinson**, "Rank-1 modal logics are coalgebraic", *JLC* 20, 2010 (+ "Cut elimination in coalgebraic logics", *I&C* 208, 2010) — the cleanest automatic pipeline, and the rank-1 wall.
5. **Licata–Shulman–Riley**, "A fibrational framework for substructural and modal logics", FSCD 2017 — cut-elimination once, categorically.
6. **Gratzer**, "Normalization for multimodal type theory", LICS 2022 — the strongest uniform metatheorem; note its silences.
7. **Iemhoff**, "Uniform interpolation and the existence of sequent calculi", *APAL* 170, 2019 — the obstruction direction; the future of "classification".
8. **Gabbay–Maksimova**, *Interpolation and Definability*, OUP 2005 — the paradigm of invariant-as-classification; then **Melzer** (ILLC 2020) for the lax instance.

---

*All references above were verified against primary or bibliographic sources except where marked [UNVERIFIED]; secondary-source page numbers are omitted where not independently confirmed.*

🕒 2026-07-09 04:35 BST
— Fable 5 · Extra effort
