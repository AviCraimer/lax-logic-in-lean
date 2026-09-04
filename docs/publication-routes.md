# Publication routes for the Belief-in-Lax-Logic work — research report

*Compiled 2026-07-18 by a web-research pass (every venue's existence and
current status checked as of mid-2026; unverifiable items flagged inline).
Audience: an unaffiliated author with prior conventional publications
(I&C 1997, TYPES 2000 LNCS) and a large Lean 4 + Mathlib artefact.*

## Critical time-sensitive findings

1. **arXiv endorsement policy changed (Dec 2025 / Jan 2026).** As of
   21 Jan 2026 an institutional email no longer suffices: a first-time
   submitter to a maths or CS category needs either prior co-authorship
   on an existing arXiv paper in that archive, or a **personal
   endorsement** from an established arXiv author in the field. No
   existing arXiv papers under "Fairtlough" were found, so a Path-2
   personal endorsement will be needed — a one-email problem, not a
   structural barrier: authors of recent arXiv papers in lax/
   intuitionistic modal proof theory qualify as endorsers, and Iemhoff's
   own papers (including arXiv:2209.08976, *Proof Theory for Lax Logic*)
   list endorsement links. The 1997/2000 publications make the case easy
   for whoever is asked. Budget time for this before anything that
   depends on an arXiv posting.

2. **LMCS requires prior CoRR (arXiv cs.LO) posting** before journal
   submission — so LMCS is gated on solving (1).

3. **ACM went mandatory-APC on 1 Jan 2026** (affects CPP and TOCL).
   Unaffiliated-author transitional rate for 2026 publications:
   ~$250 (member) / $350 (non-member) — verify the current figure for
   2027 papers before submitting.

4. **CPP 2027 has concrete deadlines**: abstracts 3 Sept 2026, full
   papers **10 Sept 2026** (strict), notification 10 Nov 2026;
   conference co-located with POPL, Mexico City, 11–12 Jan 2027. Scope
   explicitly includes proof assistants (Lean named) and mechanised
   metatheory; artifact evaluation customary. **The nearest well-matched
   archival deadline.**

## Journals for formalised mathematics

- **Annals of Formalized Mathematics** (afm.episciences.org) — real,
  new (founded 2024 by Rob Lewis and Filippo Nuccio; first volume July
  2025), **diamond OA**, requires a code artifact. Lived practice so far
  skews to "we formalised known theorem X"; new mathematics is not
  excluded. Distinct from Mizar's venerable *Formalized Mathematics*
  (still active, weaker cultural fit for Lean).
- **Journal of Formalized Reasoning** — **effectively defunct** (nothing
  after Vol. 13, Dec 2020). Do not target.
- **Journal of Automated Reasoning** (Springer) — active, strong fit,
  runs a **"Proof Pearls"** article type; zero-cost non-OA route exists
  (hybrid APC only if Gold OA wanted).
- **LMCS** — active, diamond OA, ~33 weeks to publication, good cs.LO
  fit; gated on arXiv (finding 2).
- **ACM TOCL** — viable but slower; APC point (finding 3).

## Philosophical-logic venues (for the belief argument)

- **Philosophical Logic** (philosophical-logic.org) — new diamond-OA
  journal founded Dec 2025 by the **entire resigned editorial board of
  Springer's Journal of Philosophical Logic** (publisher: Open Library
  of Humanities; publishing since June 2026; eds.-in-chief Holliday,
  Icard, Poggiolesi; board includes Bílková, Ciardelli, Korbmacher,
  Kocurek, Yanjing Wang). Scope is JPL's — modal/epistemic/constructive
  logics, belief — a near-perfect match. Risk: one article old.
- **Journal of Philosophical Logic** (Springer) — continues under a
  reconstituted board; no author fee on the subscription route; watch
  how the editorial identity settles.
- **Studia Logica** — active; **Iemhoff published the adjacent G4i work
  here (2022)** — the natural home for the corrective note's audience;
  free non-OA route.
- **Review of Symbolic Logic**, **NDJFL**, **Archive for Mathematical
  Logic** — all active, good technical fits, standard no-fee
  subscription routes (NDJFL fee status unconfirmed — ask).

## Conferences

- **CPP 2027** — see finding 4. LIPIcs-style OA economics do not apply
  (ACM venue; APC per finding 3).
- **ITP** — 2026 edition is at FLoC (July 2026, past); **ITP 2027 CFP
  not yet out** — watch itp-conference.github.io; proceedings are
  Dagstuhl **LIPIcs: no author-side APC at all** — the cleanest
  zero-cost archival route when the CFP appears.
- **IJCAR** — biennial; next slot 2028 (2027 is a CADE year).
- **TABLEAUX 2027** — expected but unannounced; Iemhoff's community.
- **AiML** — 2026 edition just ran (Amsterdam); biennial → 2028; from
  2026 its proceedings are EPTCS (no APC). Lists "constructive and
  intuitionistic modal logics" and "belief" among its topics.

## Preprint and artefact norms

- **Zenodo + GitHub release → DOI** (CERN-backed): the standard way to
  make the Lean repository citable; add `CITATION.cff`. No affiliation
  needed.
- **Precedents for citing a Lean repo in a refereed paper**: Buzzard–
  Commelin–Massot, *Formalising perfectoid spaces* (CPP 2020); the
  Mathlib paper (CPP 2020); the Liquid Tensor Experiment (repo + short
  write-up, arXiv:2309.14870); the ongoing FLT project ("cite the repo
  now, paper later" is accepted practice in this community).
- **Lean Together** — annual community workshop (Jan 2026 edition ran,
  virtual, free): visibility and feedback, not an archival venue. No
  Lean-FRO journal exists; Mathlib contribution is credit, not a paper.

## Ranked recommendation

**(a) The main paper.** Split the work:
1. Technical core (evidence semantics, separations, completeness,
   Zorn-free canonical model, decidability) → **JAR (Proof Pearls)** or
   **LMCS** (after arXiv endorsement); with **CPP 2027 (10 Sept 2026)**
   as the fast conference-length route — CPP-then-journal is the normal
   pattern (exactly the perfectoid-spaces trajectory).
2. The belief/epistemology argument as a companion conceptual paper →
   **Philosophical Logic** (diamond OA, near-perfect scope) or, more
   conservatively, **Studia Logica** / the refounded **JPL**.

**(b) The Iemhoff-counterexample note.**
1. Default: **fold into the decidability/proof-theory paper as a
   section** — the normal way such corrections circulate (a 2024
   Springer book chapter has no erratum mechanism).
2. Stand-alone citable note: **Studia Logica** first (her adjacent 2022
   paper is there), **Journal of Logic and Computation** second.
3. Immediate: **arXiv note + direct communication to Iemhoff** — fast,
   low-stakes, and she is active in exactly this sub-field.

## Not verified (do not treat as settled)

ACM APC for 2027 papers; NDJFL author-fee status; RSL's OA APC;
TABLEAUX 2027 and ITP 2027 CFPs (pattern-based inference only); AFM's
full board membership.
