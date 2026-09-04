# Typesetting options for the PLL companion paper: Verso vs LaTeX

**Purpose.** We have mechanised essentially all of Fairtlough–Mendler 1997
("Propositional Lax Logic", *Information and Computation*) and drafted a
~600-line companion paper at `docs/pll-companion-paper.md`. This asks
whether [Verso](https://github.com/leanprover/verso) is mature enough in
mid-2026 to typeset that paper with **checked** Lean code as a first-class
feature, or whether LaTeX (with some bolt-on checking) is the safer route
for an *Information and Computation*-style journal submission.

**Date-stamp.** Version numbers, star/issue counts and "latest release"
claims below were gathered **2026-07-07** via the GitHub API and primary
sources. Verso moves fast (see §2.5), so treat anything more specific than
"mid-2026" as liable to be stale within weeks. Claims resting only on a web
search summary (not something I fetched and read directly) are flagged.

---

## 1. What's actually in this repo today

- `lakefile.toml` depends on Verso as `rev = "main"` — a **floating
  branch**, not a tagged release. `lake-manifest.json` currently resolves
  that to Verso commit
  [`ce4108e2`](https://github.com/leanprover/verso/commit/ce4108e2edf3ff980484425aa41d946c5549d16d)
  (2025-07-04), a year-old lock on a moving target.
- `lean-toolchain` pins `v4.22.0-rc3`. Verso tags a release for essentially
  every Lean release/RC, and a Verso tag named
  [`v4.22.0-rc3`](https://github.com/leanprover/verso/releases/tag/v4.22.0-rc3)
  exists, cut 2025-07-04 — the same day as the manifest's floating commit.
  **An exact-match tagged release already exists but isn't being used**
  (see §5, first step).
- `LaxLogic/VersoText.lean` is a 5-line stub (`import Verso` +
  `#doc (Test) "Hello, Verso!" =>`). `lake build LaxLogic.VersoText`
  **fails**: `unknown constant 'Test'`. This is not a Verso breakage —
  `import Verso` itself compiles fine against the pinned toolchain; the
  stub just never defined/opened a genre (real docs need `import
  VersoManual` + `open Verso.Genre Manual` before `#doc (Manual) ... =>`
  works). The stub was never finished and currently tells us nothing about
  Verso's viability.
- `LaxLogic/VersoText.md` (437 bytes) is disconnected prose, not imported
  by anything — a sketch of hoped-for features (LaTeX-style math,
  cross-refs), not a working demo.
- No `.tex`/`.bib`/`.cls`/`.sty` files exist anywhere in this repo outside
  dependency caches; the legacy 1997 LaTeX sources live elsewhere on disk.
- `docs/pll-companion-paper.md` is 593 lines with a full paper skeleton
  (Abstract, ten numbered sections incl. 8a–8d, Engineering Lessons, Future
  Work, Acknowledgements, References) — the actual manuscript to typeset.

---

## 2. State of Verso, mid-2026

### 2.1 What it is

Verso is [David Thrane Christiansen](https://davidchristiansen.dk/)'s
documentation system, developed full-time under the Lean FRO. Verso
documents *are* Lean source files (a Markdown-like concrete syntax that
elaborates as Lean), so prose containing Lean code or embedded proofs is
checked by the real elaborator at build time — a structural guarantee, not
a CI convention. Primary sources: [repo](https://github.com/leanprover/verso),
[project site](https://verso.lean-lang.org/),
[user manual](https://verso-user-manual.netlify.app/).

### 2.2 Genres and who uses them

The genre system is extensible; genres in the main repo are `verso-manual`
(long-form docs/books), `verso-blog`, `verso-tutorial`, plus "literate"
doc-comment extractors. Two more live in sibling repos:
[`verso-blueprint`](https://github.com/leanprover/verso-blueprint) (proof
blueprints; repo created 2026-02-22, under 5 months old) and
[`verso-slides`](https://github.com/leanprover/verso-slides). **There is no
dedicated "paper"/"article" genre.** Manual — the genre with sectioning,
cross-refs and a real bibliography (§2.3) — is the closest fit, and is what
real production documents use: the
[Lean reference manual](https://lean-lang.org/doc/reference/latest/),
[Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/),
[Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/),
*Mathematics in Lean*, and Terence Tao's
[*Analysis I: A Lean Companion*](https://terrytao.wordpress.com/2025/05/31/a-lean-companion-to-analysis-i/)
(announced 2025-05-31). Real, credible, non-toy usage — but all of it
**HTML** output (§2.4).

### 2.3 Bibliography / citations

A real citation system exists in
[`VersoManual/Bibliography.lean`](https://github.com/leanprover/verso/blob/main/src/verso-manual/VersoManual/Bibliography.lean):
a typed `Citable` union (`InProceedings | Thesis | ArXiv | Article`, rich
fields for title/authors/year/venue/pages/url), citation styles matching
`citet`/`citep`/`citehere`, and renderers to **both** HTML and TeX
(`bibHtml`/`bibTeX`). Materially comparable to natbib/BibTeX. The catch:
**no `.bib` importer** — entries are Lean values in an imported module,
which the source comments describe as playing a role "similar to a `.bib`
file in LaTeX." Porting `references.bib` means transcribing it (mechanical
but not automatic).

### 2.4 PDF / TeX output — the nuanced part

- A real `Verso.Output.TeX` backend exists, and Manual has a first-class
  `emitTeX : Bool` switch, exercised in Verso's own test suite
  (`emitTeX := true` in `src/tests/TestMain.lean`).
- **Every real production document sets it to `false`**: the reference
  manual's `Main.lean`, and the official `package-manual` and `textbook`
  starter templates. The Lean FRO's own flagship manual ships HTML only,
  despite the TeX plumbing existing in the same codebase.
- The issue tracker shows live-but-incomplete work: open
  [#518](https://github.com/leanprover/verso/issues/518) ("placeholder
  text for missing `toTex` implementations" — some elements have *no* TeX
  renderer yet), recently-closed
  [#717](https://github.com/leanprover/verso/issues/717) ("bugs in TeX
  output"), [#666](https://github.com/leanprover/verso/issues/666)/[#616](https://github.com/leanprover/verso/issues/616)
  (more TeX coverage for FPiL/TPiL), plus an open RFC
  [#811](https://github.com/leanprover/verso/issues/811) for a parallel
  Typst backend — evidence TeX output is still being actively built out,
  not treated as finished.
- The one **working end-to-end PDF pipeline** is `verso-blueprint`'s
  `lake exe blueprint-gen --pdf` (emits TeX, shells to `lualatex`). But
  that tool is new, built for whole-project dependency/`sorry` tracking,
  not a single polished paper, and its PDF isn't an `elsarticle`-conformant
  submission artifact.

**Bottom line:** Verso can emit TeX for parts of a document and can produce
a PDF end-to-end via separate blueprint tooling, but nobody — including its
own authors, for their own flagship manual — yet uses it for a polished,
submittable PDF. Betting a paper on this path means being the first real
test case.

### 2.5 Stability, versioning, pain points

Versioning tracks Lean's own release train, not independent semver. Latest
formal [GitHub Release](https://github.com/leanprover/verso/releases/tag/v4.29.0)
is `v4.29.0` (2026-03-30) — a few Lean releases behind current (Lean itself
reached [4.30.0](https://lean-lang.org/doc/reference/latest/releases/v4.30.0/)
on 2026-05-26; a later reference-manual version was mentioned in a search
summary I did not independently verify). Matching tags past `v4.29.0` exist
in git, just not all cut as Releases — tracking bleeding-edge Lean means
tracking tags/`main`, not "the latest release." The README states the
project moves at "rapid pace" and asks contributors to coordinate first — a
direct churn signal from the maintainer. Cross-document linking is marked
"Experimental." No independent academic paper describes Verso's design.
Repo health as of 2026-07-07: created 2023-12-06, 359 stars, 117 forks, 77
open issues, 26 contributors, pushed today — real and active, not settled.

---

## 3. LaTeX + checked Lean code: the alternatives

**Cosmetic highlighting only (no checking, by design).** Confirmed via the
[official Lean guidance page](https://lean-lang.org/documentation/latex-syntax-highlighting/):
`lstlean.tex` (a `listings` style [shipped in the Lean 4 repo](https://github.com/leanprover/lean4/blob/master/doc/latex/lstlean.tex),
simple but weak on Unicode) and `minted` (wraps Pygments, which has a
`lean4` lexer since 2.18; full Unicode via XeLaTeX/LuaLaTeX but needs
`--shell-escape`). A [Zulip thread](https://leanprover-community.github.io/archive/stream/113488-general/topic/Latexing.20Lean.html)
documents this being genuinely painful (naive setups → "thousands" of
compile errors), with the aside that Lean proofs are "not really intended
for consumption anywhere other than in a Lean-aware editor" — precisely the
gap Verso exists to close.

**[`leanblueprint`](https://github.com/PatrickMassot/leanblueprint)**
(PatrickMassot) is plasTeX-based (a Python LaTeX→HTML processor, not raw
pdfLaTeX), providing `\uses{}`/`\leanok`/`\notready` macros and a
Graphviz-rendered dependency graph. Its `print.tex` PDF mode works by
stubbing the web-only macros to no-ops and falling back to plain LaTeX —
it doesn't check that a labelled statement's text matches what the Lean
declaration actually says; `\leanok` is a marker a human or script sets, not
an automatic re-verification. It's a *project tracker* (Liquid Tensor
Experiment, PFR, FLT), not a paper typesetter. Last pushed 2025-12-23, 34
open issues, not archived — mature/stable, not abandoned. `verso-blueprint`
is a newer, Verso-native reimagining of the same idea.

**The gap:** no adopted, off-the-shelf tool extracts code blocks from
`.tex` and checks them against a real project (the brief's "simple
approach"). Most LaTeX+Lean papers appear to simply trust the author to
keep pasted code in sync by hand.

**The better primitive: SubVerso, standalone.** Verso's underlying
extraction/highlighting library, [SubVerso](https://github.com/leanprover/subverso),
has its own CLI (`subverso-extract-mod`, `subverso-helper`) usable outside
a full Verso document. It elaborates real `.lean` source and emits JSON
with accurate highlighting, defined names, proof states, and named "anchor"
regions. This inverts the usual failure mode: generate small `.tex`
snippets *from* the real, checked source as a build step and `\input{}`
them, rather than hand-pasting Lean text into `.tex` and hoping it stays
truthful. No pre-packaged "SubVerso → TeX" renderer exists, so this needs
custom scripting (§5) — but the hard part, real checked extraction, already
exists.

---

## 4. Comparison table

| Approach | Code actually checked? | Submittable PDF today? | Bibliography | Maturity (mid-2026) | Setup effort here |
| --- | --- | --- | --- | --- | --- |
| **Verso Manual genre → HTML** | Yes, genuinely | No (HTML only in every prod. use found) | Native, typed, HTML+TeX renderers | Proven for books/manuals; no paper genre | ~1–3 days for one real page (stub redone) |
| **`verso-blueprint`** | Partially (declaration existence, not prose-statement equivalence) | Yes via `lualatex`, but project-blueprint shaped | Not bibliography-focused | Very new (<5 months) | Unclear; mismatched to a single paper |
| **Plain LaTeX + `lstlean`/`minted`** | No — cosmetic only | Yes, exactly what journals expect | Real BibTeX/natbib | Old, stable, painful Unicode | Low, but zero checking gain |
| **LaTeX + `leanblueprint`** | No — existence/label tracking only | Yes via print template (→ plain LaTeX) | Real BibTeX/natbib | Mature, built for multi-file projects | Medium; mismatched use case |
| **LaTeX + SubVerso-extraction hybrid (recommended)** | Yes — generated from real elaborated source | Yes — ordinary `elsarticle` LaTeX | Real BibTeX/natbib (reuse 1997 `.bib`) | Glue code needed, but every underlying piece is mature | Medium once, then near-zero marginal |

---

## 5. Recommendation for this paper

*Information and Computation* (Elsevier) explicitly recommends
`elsarticle.cls` + BibTeX and requires editable `.tex`/`.bbl`/`.bst`/`.bib`
files at submission — confirmed from the
[journal's guide for authors](https://www.sciencedirect.com/journal/information-and-computation/publish/guide-for-authors)
and [Elsevier's LaTeX instructions](https://www.elsevier.com/researcher/author/policies-and-guidelines/latex-instructions).
The submission artifact must be LaTeX, full stop — that fixes the shape of
the recommendation.

**Don't make Verso's TeX/PDF path the critical path.** It's real but
unfinished by its own authors' usage (§2.4), still shifting API-wise, and
its native bibliography doesn't emit `.bib`/`.bbl`, so it wouldn't satisfy
"BibTeX to generate your bibliography" without an export layer that doesn't
exist. Becoming the first serious paper-genre test case for Verso's TeX
backend is a bad trade against a journal deadline.

**Do use Verso in parallel** for what it's already proven: publish the
paper's content as a real, checked, cross-linked HTML book (Manual genre)
— the same genre behind the reference manual, TPiL, FPiL and Tao's
*Analysis I*. A live checked companion to the mechanisation, linked from
the PDF, off the submission critical path, low-risk because it's exactly
Verso's validated use case.

**For the submission: LaTeX + the SubVerso-extraction hybrid** (§3, §4
last row). Start from the legacy 1997 sources (reuse the journal macros
and ideally the original `.bib`), port `docs/pll-companion-paper.md`
section by section, and replace each Lean snippet with a generated
`\input{}`: mark the region in the real `.lean` source with a SubVerso
anchor comment, run `subverso-extract-mod` to pull checked/highlighted
JSON, render it to a `.tex` fragment (plain `verbatim` is a fine v1;
token-coloured output is a stretch goal), and wire generation into CI so a
broken proof breaks the build. That delivers the checked-code
differentiator without depending on Verso's least-mature subsystem.

### Effort estimate (order of magnitude)

- **LaTeX-from-1997-sources, cosmetic code, no checking**: ~1–2 weeks, but
  no checked-code differentiator over what was possible in 1997.
- **+ SubVerso-extraction hybrid** (recommended): +3–5 days up front to
  get one anchor extracting, write the JSON→TeX renderer, wire it into
  CI/`lake`; each further snippet is then nearly free.
- **Verso as the actual submission pipeline**: not recommended now;
  realistically 1–2+ months contributing to Verso's own TeX backend (in
  coordination with its maintainer, per the README), with no guarantee of
  an `elsarticle`-conformant result. Revisit in 12–18 months.
- **Verso HTML companion** (parallel, non-blocking): ~1 day to turn the
  broken stub into one real page; a few more days to build out, reusing
  the extraction plumbing above.

### First steps, in order

1. **Fix the dependency pin**: `rev = "main"` → `rev = "v4.22.0-rc3"` in
   `lakefile.toml` (exact match to `lean-toolchain`). One line, zero risk.
2. **Redo the Verso spike properly**, half a day, timeboxed: `import
   VersoManual`, `open Verso.Genre Manual`, a real `#doc (Manual) =>`
   block and a `Main.lean` calling `manualMain` (mirror
   `test-projects/package-manual` in the Verso repo). Get one real page
   with one checked snippet and one citation rendering to HTML.
3. **Decide the bibliography source of truth**: reuse/refresh the 1997
   `references.bib` as canonical; treat Verso `Citable` entries as a
   ported mirror, not a second original.
4. **Prototype the extraction pipeline on 2–3 real snippets** from
   `docs/pll-companion-paper.md` before committing to it for the whole
   paper — front-load the step most likely to surprise.
5. **Start the LaTeX shell from the legacy 1997 sources**, not from
   scratch; port section-by-section using `docs/pll-companion-paper.md` as
   the outline (its §8 "correspondence with Fairtlough–Mendler 1997"
   already maps onto this task).
6. Only after 1–4 work: build out the HTML companion further, and treat
   any future Verso paper genre (or a matured `emitTeX`) as a possible
   *replacement* for step 5's pipeline, not a prerequisite for it.

---

## 6. Honest uncertainty

- The extraction pipeline's "days-scale" effort is a reasoned guess from
  reading SubVerso's CLI surface, not a measurement.
- The exact Lean version the reference manual currently targets comes only
  from a web-search summary, not a primary source I opened myself.
- The "LCNF visibility checker" breaking-change item (§2.5) is from search
  results, not a primary source I re-read directly — indicative of the
  *kind* of churn to expect, not a verified incident report.
- This is a one-week snapshot of a project that moves at "rapid pace." The
  qualitative conclusion (real infrastructure, not yet trusted for
  production PDF even by its own authors) should hold for a while; specific
  issue numbers and release tags will age fast.
