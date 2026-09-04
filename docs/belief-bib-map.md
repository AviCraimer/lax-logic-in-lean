# belief.bib → paper-section map

*Companion to `docs/belief.bib` (compiled 2026-07-18, 115 entries + 4
normalisation-literature entries added after the same-day source check
(`Lindley2005`, `DoczkalSchwinghammer2009`, `Prawitz1971`, `deGroote2002`) =
119, large-first —
pruning is a later human step). Keys below are BibTeX keys in `belief.bib`.
Verification policy is recorded at the head of the `.bib` file: every entry was
checked against a publisher/primary record this session, or against one of the
repo's own verified literature digs (`iel-justification-lit.md`,
`realisability-modal-lit.md`, `nuclei-noncomplete-lit.md`,
`assembly-tower-lit.md`, `route-b-model.md`,
`surveys/nuclei-model-completions-monads.md`, `publication-routes.md`); the 13
entries with residual uncertainty carry `note = {UNVERIFIED: ...}` in the file.
27 entries carry a `Formal development:` note (Lean/Coq/Rocq/Agda mechanisation).*

## §1 Introduction — the six perspectives + the doxastic seventh

- The parent paper and its perspective list: `FairtloughMendler1997`,
  `FairtloughMendler1994` (hardware-verification origin).
- Curry's 1948 lectures: `Curry1950` (the lectures), `Curry1952` (the JSL paper
  where cut elimination meets the modality).
- Nuclei on (complete) Heyting algebras: `Macnab1981`, `Johnstone1982`,
  `PicadoPultr2012`.
- Kripke and J-space semantics: `Kripke1965`, `Goldblatt1981`, `Simpson1994`.
- Strong monads / computational type theory: `Moggi1991`,
  `BentonBiermanDePaiva1998`, `Kobayashi1997`, `PfenningDavies2001`.
- Constraint reading: `FairtloughMendler1997`, `FairtloughMendlerWalton1997`.
- Timing analysis of combinational circuits: `Mendler2000`.
- Doxastic/epistemic framing and logical omniscience owned as idealisation:
  `Hintikka1962`, `FaginHalpernMosesVardi1995`, `Stalnaker2006`.

## §2 The mechanised base

- The calculi and semantics being mechanised: `FairtloughMendler1997`
  (Definitions 3.1–3.2 verbatim), `Gentzen1935` (sequent calculus, cut
  elimination), `Kripke1965`.
- Term calculus and monadic laws: `Moggi1991`, `BentonBiermanDePaiva1998`.
- Strong normalisation by ⊤⊤-lifting: `LindleyStark2005` (flagged: artefact's
  `PLLTopTop.lean` appears to be the first mechanised ⊤⊤-lifting with sums;
  mechanisation benchmark neighbour `AbelEtAl2019`), `Lindley2005` (thesis:
  unrestricted sums via frame stacks, plus confluence and decidable
  convertibility for λml), `DoczkalSchwinghammer2009` (the sole prior
  mechanisation — Isabelle/HOL-Nominal, core calculus, no sums; AFP
  `Lam-ml-Normalization`). SN-for-λml prehistory (translation proofs):
  `BentonBiermanDePaiva1998` via `Prawitz1971`/`deGroote2002`
  permutative-conversion SN.
- Decidability via a contraction-free terminating calculus: `Dyckhoff1992`
  (G4ip template), `Iemhoff2024` (G4iLL — incomplete as published;
  artefact counterexample + repair), `Iemhoff2022` (the transfer theorem whose
  modal case fails), `Howe2001` (earlier PLL proof search).
- Proof-assistant substrate: `DeMouraUllrich2021`, `MathlibCommunity2020`.

## §3 Classical collapse; constructive richness

- Theorem 3.1 (every nucleus on a Boolean algebra is closed; N(B) ≅ B):
  `BeazerMacnab1979` (the published collapse), `Macnab1981`,
  `Simmons1980` / `Simmons2014` (when a single assembly is Boolean —
  scatteredness/Cantor–Bendixson), `AvilaBezhanishviliMorandiZaldivar2020`
  (modern proof + spatiality), `BezhanishviliGabelaiaJibladze2013`.
- Theorem 3.2 (open vs closed nuclei; infinite closed ◯-fragment):
  `Macnab1981` (the canonical open/closed/Boolean nuclei families),
  `Erne2022` + `ErnePicadoPultr2022` (nuclei on NON-complete Heyting algebras —
  the setting of the free algebra), `Nishimura1960` + `Rieger1949` (the free
  one-generator Heyting algebra is infinite), `BezhanishviliEtAlDiego2021`
  (nuclear implicative semilattices = algebras of the ∨-free lax fragment).
- Theorem 3.3 (context completeness, Curry's problem): `FairtloughMendler2002`,
  `Curry1950`, `Curry1952`.
- Assembly background if the tower is mentioned: `Simmons1978`, `Escardo2003`,
  `Plewe2000`, `Plewe2002`, `Isbell1972`, `DowkerPapert1966`,
  `NiefieldRosenthal1987`, `Wilson1994`, `Johnstone1990`, `Esakia1974`,
  `Esakia2019`, `BezhanishviliGhilardi2007`, `AvilaBezhanishviliMorandiZaldivar2021`,
  `BezhanishviliMelzer2025`.
- Idealisation remark (omniscience, introspection): `Hintikka1962`,
  `FaginHalpernMosesVardi1995`.

## §4–§6 Evidence, separations, completeness (the realisability tradition)

- The tradition the semantics extends: `Kleene1945` (number realisability),
  `Troelstra1973`, `Troelstra1998` (survey), `TroelstraVanDalen1988`,
  `VanOosten2008` (categorical side; PCAs), `Hyland1982` (effective topos).
- Kripke-indexed realisability (the ⊃-clause's ancestry): `Lipton1992`,
  `Fitting2005` (evidence functions with monotonicity),
  `MarinPadhiarShillito2026` (intuitionistic-base evidence models).
- Realiser-carrying worlds for lax specifically: `Valliappan2026` (the closest
  packaged artifact, Agda-checked; forward-confluence contrast is
  machine-checked in the artefact).
- ◯ as nucleus/local operator over realisability: `LeeVanOosten2013`,
  `Kihara2023`, `Nakata2026`, `Yamada2026`, `CohenGrunfeldKirstMiquey2025`
  (monad-parametrised realizability), `PavlovicHughes2020`.
- Classical end of the evidence-discipline spectrum: `Krivine2009`.
- §6.2 (Zorn traded for the decision procedure): `Zorn1935` (what is removed),
  `FairtloughMendler1997` §4 (the construction being finitised), `Gentzen1935`
  (the decidability-before-completeness pedigree, Remark 6.4), `Kripke1965`
  (the 1965 completeness it preceded), `Dyckhoff1992` + `Iemhoff2024` (the
  oracle's calculus).

## §7 The theory, run

- Proof terms and extraction: `Moggi1991`, `BentonBiermanDePaiva1998`,
  `PfenningDavies2001`.
- Confluence/normal forms for the η∘μ separation: `Newman1942` (Newman's
  lemma, mechanised in `PLLConfluence.lean`), `LindleyStark2005` (SN input),
  `Lindley2005` (paper-form confluence for λml, with η and without sums —
  the mechanised counterpart differs in both respects).
- Fig. 3 countermodels recovered by minimisation: `FairtloughMendler1997`.
- Frame-uniform vs frame-aware evidence remark: `Hintikka1962`.

## §8 Related work

- IEL/IEL⁻ and the conjecture PLL-◯ = IEL⁻ + idempotence:
  `ArtemovProtopopescu2016` (primary), `HagemeierKirst2022` (IEL mechanised in
  Coq — must be cited when claiming novelty for mechanised epistemic logic).
- Justification logic forces factivity (why the forgetful reading is not ◯):
  `Artemov1994`, `Artemov2001`, `Artemov2008`, `ArtemovFitting2019`,
  `ArtemovFittingSEP`, `Fitting2005`.
- Constraint and monadic readings compatible with the doxastic one:
  `FairtloughMendler1997`, `Moggi1991`, `BentonBiermanDePaiva1998`.
- Double-negation believer / continuation reading: `Goldblatt1981` (¬¬ as the
  archetypal geometric modality), `Krivine2009`, `Yamada2026`.
- Terminating-calculus route and the communicated counterexample:
  `Iemhoff2024`, `Iemhoff2022`.
- Other semantic studies of FM frames: `Zhao2023`, `AlechinaMendlerDePaivaRitter2001`,
  `MendlerScheele2011` (multimodal CK containing the lax modality).
- Multimodal/adjoint futures (two ◯'s and their join):
  `PruiksmaCharginPfenningReed2018`, `KavvosGratzer2023`,
  `GratzerKavvosNuytsBirkedal2021`, `HylandPlotkinPower2006`, `Beck1969`,
  `ZwartMarsden2022`, `Escardo2003` + `Pataraia1997` (joins of nuclei).

## §9 Method (mechanisation, publication, artefact)

- Mechanisation neighbours to situate the artefact:
  `FereeVanDerGiessenVanGoolShillito2024` (Coq, IJCAR 2024 Best Paper),
  `ShillitoVanDerGiessenGoreIemhoff2023` (Coq, iSL termination + cut
  elimination), `VanDerGiessenShillito2026` (Rocq, UI for CK/WK),
  `VanDerGiessen2022` (thesis: iK4/iS4 lack UI),
  `DeGrootShillitoClouston2025` (Coq, CK–IK semantics),
  `ValliappanRuchTomeCortinas2022` (Agda, modal NbE), `Valliappan2026` (Agda,
  lax), `HagemeierKirst2022` (Coq, IEL), `GattingerLean4PDL`,
  `FormalizedFormalLogic`, `AbelEtAl2019`, `StassenGratzerBirkedalMitten`.
- Toolchain and precedent for repo-as-artefact: `DeMouraUllrich2021`,
  `MathlibCommunity2020`, `BuzzardCommelinMassot2020`.
- The artefact itself (placeholder DOI to fill at Zenodo release):
  `BeliefArtefact`.
- Kleene–Brouwer well-foundedness (the fully constructive standalone):
  `Kechris1995`.

## §10 Open problems

- Uniform interpolation for PLL: `Iemhoff2024` (the claim with the gap),
  `Pitts1992` (the method), `FereeVanDerGiessenVanGoolShillito2024` (the
  mechanised-UI reference point), `VanDerGiessenShillito2026`.
- Axiomatisation of PLLᵘ: no direct literature — nearest are `Valliappan2026`
  and the constraint-algebra analysis in `FairtloughMendler2002`.
- Kleene-algebra instantiation of the table capacities: `Kleene1945`,
  `VanOosten2008` (K₁ as PCA).
- Tripos-level formulation: `VanOosten2008`, `Hyland1982`,
  `CohenGrunfeldKirstMiquey2025`, `LeeVanOosten2013`, `Kihara2023`.
- Model completion for nuclear Heyting algebras (unstudied; adjacent to the UI
  question): `GhilardiZawadowski2002`, `VanGoolMetcalfeTsinakis2017`,
  `KowalskiMetcalfe2019`, `Darniere2018`, `Ye2026`.

---

## Hidden-connection candidates

Non-obvious links noticed while compiling; none is currently cited in the
draft. Kept deliberately — decide explicitly rather than drop silently.

1. **Authorization logic's "says" is a principal-indexed lax/belief modality**
   (`Abadi2006`, `GargAbadi2008`). DCC's `L says T` is a monadic, non-factive,
   agent-flavoured modality with exactly the unit/bind discipline of ◯ — a
   published computational precedent for reading a lax monad as an *attitude of
   an agent*, and the "quarantining" of each principal's assertions is the
   access-control twin of §1's quarantined inconsistency. Strong candidate for
   one sentence in §8.

2. **Topological evidence models of belief** (`VanBenthemPacuit2011`,
   `BaltagBezhanishviliOzgunSmets2016`/`2022`). The classical evidence-logic
   tradition builds belief from evidence via interior-type operators on a
   *topology* — nucleus-adjacent machinery. Theorem 3.1 explains *why* they
   need topological structure: on the bare classical algebra every nucleus is
   closed, so evidence structure must live elsewhere. The paper's collapse
   theorem is a lens on an entire literature it does not currently mention.

3. **LT-topologies on the effective topos as oracles** (`LeeVanOosten2013`,
   `Kihara2023`, `Yamada2026`, `Nakata2026`). The candidate ◯'s over
   realisability are *classified*, and read as generalized oracles;
   Yamada's ¬¬-subtopos-equals-CPS result is a topos-theoretic instance of
   "classical belief is degenerate" — the §3 thesis realised inside a model.
   Also the natural home for the §10 tripos question, and Nakata's
   worlds-as-nuclei forcing lives one assembly floor up (belief about belief).

4. **The S4V bridge to Artemov–Protopopescu** (`ArtemovProtopopescu2016`
   §3.3: Gödel translation `Kp = □V□p` into a bimodal verification logic).
   Their verification modality V is lax-flavoured (□A → VA, with ¬□V⊥ for
   IEL); if V is essentially ◯ under that translation, it gives a citable
   *published* bridge for the PLL-◯ = IEL⁻ + idempotence conjecture of
   §8/§10. Needs checking against the primary text before use (flagged in
   `iel-justification-lit.md` §6.6). Related: a lax-◯ *realization theorem*
   (splitting ◯ into justification terms as LP splits □) appears to be open —
   `MarinPadhiarShillito2026` supplies the intuitionistic base it would need.

5. **Coherence failure vs the PLL model-completion question**
   (`KowalskiMetcalfe2019`, `VanGoolMetcalfeTsinakis2017`,
   `GhilardiZawadowski2002`). Coherence fails for K/KT/K4/S4 — the classical
   single-operator cousins of nuclear HAs — so the model completion of the
   variety of PLL-algebras is plausibly *refutable*, is unasked in the
   literature, and the §10 UI investigation is its proof-theoretic half. A
   concrete open problem the paper could claim/flag.

6. **Curry 1952 as ancestor of the repaired calculus** (`Curry1952`). The
   modality whose cut-elimination Curry analysed in 1952 is the same ◯ whose
   G4-style cut admissibility the artefact repairs in 2026; the historical
   arc (1948 lectures → F&M 1997 → Iemhoff 2024 → machine-checked repair)
   is worth a sentence in §8 or §9.

7. **Egli–Milner / powerdomain shape of the ∀∃ clause.** The modal clause
   (∀ futures ∃ constraint-witness) is the Egli–Milner-style two-quantifier
   combination familiar from powerdomains/weakest-precondition semantics; no
   entry included since no specific published identification was located —
   recorded here so the observation is not lost. (Nearest in-bib anchors:
   `Moggi1991`, `MendlerScheele2011`.)

8. **Fitch-style NbE for lax** (`ValliappanRuchTomeCortinas2022`,
   `Valliappan2026`): the Agda NbE line now covers K/T/4 and lax; the
   artefact's decision-procedure-driven fullness witnesses are a
   Kripke-logical-relations argument in the same family — a methodological
   kinship §9 could note when comparing mechanisation styles.
