# Fresh-session prompt: semantic uniform interpolation for PLL

*(Paste this as the opening message of a new session, or tell the session
to read this file. Written 2026-07-18, end of the long g4ill/semantic-UI
session.)*

---

Mission: **uniform interpolation for PLL by the semantic
(bisimulation-quantifier) route — prove definability.** Work from `main`
in `/Users/matthew/Lean/Sources/lax-logic-in-lean` (no worktree).

## Read first, in this order

1. Memory: `communication-register` (register rules — hard requirement:
   standard proof-theoretic language only, lemmas as displayed formulas,
   PROVED/REFUTED/OPEN kept distinct), `machine-checked-mandate`,
   `onevar-descent-probe` (tail = live state of both UI routes).
2. `docs/semantic-ui-route.md` — the plan, all results so far, the
   hazards, and the three routes (syntactic cascade / semantic
   definability / finite-support constraint transfer).
3. `LaxLogic/PLLSemUI.lean` — compiles with EXACTLY two `sorry`s
   (`semEx_definable`, `semAll_definable`). Everything else is PROVED:
   A-bisimulation (i- and m-zigzag + fallibility) and forcing
   invariance; the four Pitts adjunction theorems via the choice-free
   `completeness` (so ANY spec-satisfier IS the uniform interpolant —
   UI ⟺ definability alone); `redecorate` (the universal p-variant
   constructor) with base + compositional cases; the 1-pv amalgamation
   obstruction (`semEx_and_pointwise_fails`); the first modal values
   ∃p.¬p = ⊤, ∀p.¬p = ⊥, ∃p.◯p = ⊤, **∀p.◯p = ◯⊥**; the p-free
   fixpoints and surjectivity onto RN(◯,{}).
4. For the syntactic route and tooling: `PROGRESS.md` (repo root),
   `docs/belief-in-lax-logic-handover.md` addendum §A4/§A5/§A8, task
   list #9/#31/#33.

## The work, in Matthew's priority order

**1. Definability at ONE variable.** For every M with atoms ⊆ {p},
construct a closed formula meeting `IsSemEx`/`IsSemAll`. Engine: the
finite canonical model (`PLLFinComp.lean`, closure-total triples
(Γ, Δ, Θ)); candidate interpolant = finite disjunction of promise-aware
world descriptions (the `¬◯(⋁Θ)` conjunct carries the ◯-behaviour).
Matthew's proposed induction: lattice-height / lex-coordinate walk over
the RN-style lattice; note ∀p is meet-preserving (`semAll_and`), hence
determined by its values on meet-irreducible elements — compute
level-by-level. TEST CANDIDATES COMPUTATIONALLY FIRST: harnesses
`wip/lattice_cmp.lean` (closed-fragment oracle `entails`/`equiv`) and
`wip/slick_probe.lean` (canon-as-you-go); the two-sided oracle gives
kernel-checked proof terms (`G4cTm`/`prove`, `PLLG4Term.lean`) and
certified countermodels with diagrams (`PLLCountermodelEmit.lean`,
`PLLDiagram.lean`) — a failed candidate returns a three-world picture of
why.

**2. The essential-fibre conjecture (NEW, sharp, small).** Say p is
*essential* in M if M is not PLL-equivalent to any p-free formula.
First exercises (each a few lines, from the spec + completeness):

   * `IsSemAll p M truePLL → ⊢ M` — hence ⊤ is NEVER an essential
     ∀p-value (∀p.M ≅ ⊤ forces M valid forces M ≅ ⊤).
   * Dually: `IsSemEx p M falsePLL → M ≅ ⊥` — ⊥ is never an essential
     ∃p-value.

   Then the CONJECTURE (Matthew, 2026-07-18): the essential ∀p-image is
   exactly RN(◯,{}) ∖ {⊤}, dually the essential ∃p-image is
   RN(◯,{}) ∖ {⊥}. Data: ⊥ = ∀p.p, ◯⊥ = ∀p.◯p (both proved, p
   essential). Next data points to compute before generalising:
   ¬◯⊥, ◯¬◯⊥, ¬¬◯⊥, the RN-ladder rungs. Prove or refute; either
   outcome is a publishable structure theorem about the quantifiers.

**3. If blocked on 1:** the machine-checked amalgamation obstruction
(incompatible decorations: p := univ vs p := F) is the guide to the
right description shape. And route C — the finite-support constraint
transfer (per-instance finite S_φ via Lemma 7's per-model constraints,
`docs/semantic-ui-route.md` §3(c)) — is entirely unexplored.

## Rules

* Machine-checked mandate: nothing claimed as proved without a
  sorry-free, `#print axioms`-clean Lean proof; unproven = OPEN /
  conjecture, said so.
* Register: standard terminology only; no invented jargon; displayed
  formulas.
* Git: work on `main`; push with explicit refspec `origin main:main` to
  the fairflow fork ONLY (upstream = AviCraimer's parent repo, never
  push there); a sister session also pushes to main — fetch before
  pushing, rebase small doc/wip commits if needed.
* Long-running probes: `def main` + `lake env lean --run file.lean`
  (`#eval` buffers all IO until completion — silent hangs). Never feed
  raw (unsimplified) interpolants to the search oracle: formula weight
  sets the search-space cap.
* The structural picture worth keeping in view: ∃p ⊣ inclusion ⊣ ∀p —
  incl∘∀p is an interior (meet-preserving) comonad, incl∘∃p a closure
  (join-preserving) monad on the free one-variable lax algebra, common
  fixpoints = RN(◯,{}); in a project about nuclei, the propositional
  quantifiers are themselves a nucleus/co-nucleus pair on the free
  algebra. This belongs in whichever paper UI lands in.
