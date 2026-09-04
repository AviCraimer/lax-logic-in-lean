# The G4iLL′ admissibility ladder: state and design (2026-07-08)

Target: contraction and cut admissible in `G4p`, then completeness
`SC → G4p` by plain induction on `SCh` — all structural, no
well-founded sequent order.

## Proven (sorry-free)

| brick | file | method |
|---|---|---|
| exchange, weakening, `G4 ⊆ G4p`, `toSC` | `PLLG4P` | structural |
| master inversion (9 inversions), `impR_inv` | `PLLG4PInv` | one traversal |
| identity `A, Γ ⊢ A`, telescoped MP | `PLLG4PAdm` | weight induction |
| `Spine` + lifts | `PLLG4PStr` | trivial |
| **`weak_Imp`** (D–N 4.1, *all* antecedents incl. `◯`) | `PLLG4PStr` | induction on the first derivation; each ending feeds one L⊃-rule |
| **`impLImp_dup`** (D–N 4.2, folded form) | `PLLG4PStr` | structural; principal case closed by `weak_Imp` |

## Remaining bricks and their true dependency graph

Notation: `S(F)` = self-absorbing weak implication for `F = ◯D→B`
(`Γ,F ⇒ ◯D` and `Γ,B ⇒ E` give `Γ,F ⇒ E`); `C(A)` = contraction;
`K(A)` = additive cut; `ABS(◯X)`/`OStr` = absorb/strengthen a boxed
hypothesis (`◯X ⇒ X` in context).

Verified case analyses (on paper, twice):

* `S(F)`: all cases close *structurally* — the kept implication is
  exactly what the `L◯→′`/`laxL` cases need — **except** a right rule
  at the spine's non-`◯` bottom `b`, which closes via `K(b)` with
  `w(b) < w(F)` (right premise manufactured from `identity` +
  `Spine.lift` + `weak_Imp`).  So `S(F) ⇐ K(<w F)`.
* `C(A)`: IPC-principal cases via inversions + `impLImp_dup` +
  smaller `C` (Dyckhoff–Negri verbatim).  Both `◯`-principal cases and
  both `F`-principal-with-spectator cases close via `S(w A)` and
  `K(w A)` — same weight, so `C(w) ⇐ S(w), K(w), C(<w)`.
* `K(A)`: principal ∧/∨/⊃/`R◯→` cases: smaller cuts only (additive —
  no context merging, no contraction except an easy standalone
  atom-contraction at the `init` case).  **The knot**: cut formula
  principal-right in `L◯→′`, and more generally pushing a cut into
  `L◯→′`'s first premise, requires transporting the *left* derivation
  across a box-opening (`Γ ∋ ◯X` versus premise context `∋ X`) — i.e.
  `OStr` applied to the left derivation.  And `OStr`'s own `L◯→′` case
  *is* an instance of `S(F₂)` for a context implication `F₂` of
  **unrelated weight**.  So the naive stratification
  `K(w) ⇐ C(<w), OStr ⇐ S(arbitrary) ⇐ K(<arbitrary)` is not obviously
  well-founded: the `F₂`-population comes from contexts, which the kept
  implication keeps re-supplying.

## Design revision 2 (2026-07-08, evening): the knot dissolves

Re-deriving the `K`-cases exposed that every appeal to `OStr`/`S`
inside cut has the same root: a rule premise whose context has *lost*
material (`◯χ` traded for `χ`) that the transported derivation still
needs.  The fix is to stop consuming boxes altogether — make **both**
box rules keep their box:

    Γ, ◯χ, χ ⇒ ◯B                            Γ, ◯χ, ◯φ→ψ, χ ⇒ ◯φ    Γ, ◯χ, ψ ⇒ Δ
    -------------- laxL″                     ------------------------------------- L◯→″
    Γ, ◯χ ⇒ ◯B                                        Γ, ◯χ, ◯φ→ψ ⇒ Δ

(`laxL″` is *exactly* G3iLL's `L◯`; `L◯→″` keeps both the implication
and the box in its first premise.)  Consequences, each checked at the
case level:

1. boxed-vs-unboxed absorption never arises: contraction's
   `◯`-principal cases are purely structural (the two copies always
   travel together — the minimal form of the iSL `⊗`-insight);
2. `OStr`/`ABS` drop out of the ladder entirely (the completeness
   simulation of `SC.laxL` becomes a direct `laxL″` rebuild);
3. every rule's premise context now contains the conclusion context
   minus at most a *decomposed* principal — so cut's parametric
   transports are inversions (for decomposed principals) or pure
   weakenings (box rules only add), never a box-crossing;
4. the dependency graph is acyclic by weight levels:
   `atomC → K_w (⇐ K_{<w}) → S_w (⇐ K_{<w}) → C_w (⇐ S_w, C_{<w})`;
5. remaining cost: `K`'s principal-left recursions transport the right
   derivation by weakening, which a `Prop`-valued structural induction
   cannot absorb — so the calculus gets a **height index**
   (`G4h : Nat → …` with `G4p″ := ∃ n, G4h n …`, the repo's own
   `SCh`/`SC` pattern) and height-preserving `perm`/`weaken`/`Inv`,
   after which `K` and `C` run on the classical
   (weight, height)-lexicographic measures.

`G4p″` has a tidy description: **G3iLL plus Dyckhoff's implication
splitting, with maximal retention in the two lax-implication rules.**
Termination is unaffected as a deferral (naive search now loops even
more freely, but decidability was always a separate discipline —
Bílková order or strategy-bounded search on the cut-free system).

## Superseded candidate resolutions (kept for the record)

1. **Height-index the calculus** (`G4pH : Nat → …`, the `SCh` pattern
   already used in this repo): port perm/weaken/inversions
   height-preservingly, then run the classical
   (weight, height/level)-lexicographic inductions.  This gives the
   parametric cut cases for free, but the `OStr`-inside-cut transport
   is *still* not height-preserving (its `S`-uses go through `K`), so
   heights alone do not cut the knot — they only clean up the
   push-cases.  Worth doing regardless if 2 fails.
2. **Subformula-bounded joint induction**: all formulas ever passed to
   `S`/`C`/`K`/`OStr` in a ladder run lie in the subformula closure of
   the original inputs; the `F₂`-chains consumed by `S` strictly
   descend in `K`-weight *within each branch* (`S(F₂)` only spawns
   `K(b)` for `b` a proper subformula of `F₂`).  A candidate global
   measure: the *multiset of weights of all cut/self/contraction
   obligations*, under Dershowitz–Manna — each ladder step replaces an
   obligation by finitely many strictly lighter ones **except** the
   `K → OStr → S(F₂)` step, which must be shown to consume something
   else (the box `◯X` that `OStr` opens — a Bílková-flavoured
   component).  This is where the remaining design work is.
3. **Avoid `OStr` inside `K`** by changing the cut statement to build
   in box-transport ("cut under a stack of openings":
   from `Γ ⊢ A` and `A :: openings(Γ) ⊢ C` conclude `openings(Γ) ⊢ C`)
   — a `⊗`-flavoured strengthening imitating G4iSLt's `open_boxes_R`,
   which is what made *their* cut go through.  Needs care to state so
   that it is provable for single-box openings.

The incompleteness discovery means none of this has a published
blueprint — G4iSLt's escape (⊗-opening + Löb diagonal) is structurally
unavailable for lax.  Next session: attempt 2, falling back to 3+1.

## Design revision 3 (2026-07-09): `R◯→` keeps its context — contraction lands, cut-free

Writing the general-contraction case table *in Lean* exposed a case the
revision-2 paper analysis had missed: a doubled `◯φ→ψ` whose visible
copy is fired by `R◯→` (old premise 1 `Δ ⇒ φ` — the rule *consumes*
the implication).  The inverted premises `ψ,Γ ⇒ φ` and `ψ,Γ ⇒ E` do
**not** suffice to rebuild `◯φ→ψ,Γ ⇒ E`: with `j = id`, `φ := p`,
`ψ := p∧q`, `E := q` the required inference fails in a Heyting algebra
with nucleus — no proof was being overlooked, the rule shape itself was
the obstacle (with the consuming rule, this case genuinely needs the
self-absorption lemma `S`, as the pre-revision analysis had said).

Fix, same medicine as revision 2: `R◯→″`'s first premise keeps the
whole conclusion context — G3's `L⊃` premise-1 discipline:

    Γ, ◯φ→ψ ⇒ φ    Γ, ψ ⇒ Δ
    ------------------------ R◯→″
    Γ, ◯φ→ψ ⇒ Δ

Sound (a weakening of the old premise), `toSC` *simplifies* (premise 1
is already G3-shaped), and the whole `G4h` tower re-compiled after six
one-line edits.  With it:

* **Contraction is proved, cut-free** (`PLLG4HCtr.lean`,
  `G4c.contract`): outer weight induction, inner structural induction.
  Principal cases: inversion of the surviving copy + strictly lighter
  contractions (∧, ∨, `p⊃`, `⊥⊃`, `∧⊃`, `∨⊃`); `⊃⊃` by the
  Dyckhoff–Negri recipe (`impLImp_dup`, three lighter contractions,
  re-abstraction); all three lax rules close by the *inner* induction
  because their premises now carry both copies.  `S` has dropped out of
  contraction entirely.
* The ladder reorders to the classical Dyckhoff–Negri shape:
  `atomC → C (cut-free) → K(w) (⇐ K(<w), C, exfalso, cut_atom) →
  completeness`.
* `K`'s case table after re-tabulation under revision 3 — two former
  hard spots and one still open:
  1. `⊃⊃` parametric-right, premise-1 transport (the residue `B→D` is
     not an inversion piece) — **solved**: cut at the enlarged context,
     then `impR_inv` + `impLImp_dup` + `C` (now closed) + `impR`
     re-abstraction.
  2. cut formula principal-right in `R◯→″` — **now classical**:
     premise 1 keeps the cut formula, so a structural cut cleans it,
     then two strictly-smaller-weight cuts finish.
  3. **open**: cut formula `◯X` serving as the *box witness* `hX` of an
     `L◯→″` instance whose implication `F₂` has unrelated weight — the
     self-absorption flavour survives exactly here and nowhere else.
     Candidate escapes: (a) an `S`-interleave under a
     subformula-bounded measure; (b) generalising `L◯→″`'s witness side
     condition (derived box instead of present box); (c) a cut
     statement carrying a box-witness oracle.  Next design session.

## K's full architecture (2026-07-09 afternoon): the open case dissolves modulo one lemma

Re-deriving the case table for implementation sharpened the one open
spot to a single clean obligation.  Extract:

    SelfAbsorb : ∀ {Γ l₀ A₁ B₁ E},
      Γ.Perm (◯A₁→B₁ :: l₀) → G4c Γ ◯A₁ → G4c (B₁ :: l₀) E → G4c Γ E

("an implication whose antecedent-box is derivable *in its own
presence* may fire") — semantically valid in every nuclear algebra:
from f∧γ ≤ jA₁ and f∧jA₁ ≤ B₁ get f∧γ ≤ B₁∧⋀l₀ ≤ E.  Then
`cut_of_selfAbsorb (hS : SelfAbsorb)` closes on (weight, height-sum):

* **Right-primary case analysis** (d₂'s last rule), as in `cut_atom`.
  Parametric cases: hp-inversion transports, verbatim.  `L→→`
  premise 1: the enlarged-context cut + `impR_inv`/`impLImp_dup`/
  contraction repair, verbatim from `cut_atom`.
* **`Lp→` side atom = cut copy** ⟹ the cut formula is atomic ⟹
  delegate the whole cut to `cut_atom` (one line; the switching
  induction lives there).
* **Principal cases** (cut formula = the fired principal, per
  connective): if d₁ ends with the matching right rule — the
  classical smaller-weight reductions.  Otherwise d₁ ends `botL` or a
  Perm-left rule (its `laxL` ending is shape-impossible: these
  principals are unboxed) — push left: cut d₁'s goal-`A` premises
  against the *whole reassembled* d₂ transported by hp-inversion at
  d₁'s principal (strictly smaller height sum), auxiliary premises
  verbatim, rebuild d₁'s rule at goal `E`.
* **Boxed cut formula used as a box** — two spots:
  1. `laxL` of d₂ with the membership on the copy (`A = ◯A₁`, goal
     `◯B`-shaped): left-analyse d₁.  `laxR` ending: two cuts (same
     weight smaller heights, then `A₁ < w`).  `laxL` ending: push
     left and rebuild — legitimate *because the goal is boxed*.
     Other left endings: standard pushes.
  2. `L◯→″` of d₂ with `hX` on the copy (`A = ◯X`, `E` arbitrary) —
     the formerly-open case.  Two keys: (i) the second premise
     transports by plain `Inv.impLax` at the *implication* `F` — no
     box crossing — giving `q_b : B₁, l₀ ⇒ E`; (ii) the missing
     `Γ ⇒ ◯A₁` is a **boxed-goal** cut of `d₁ : Γ ⇒ ◯X` against the
     *synthetic* right derivation `laxL(hX)(da) : ◯X, Γ ⇒ ◯A₁` at
     height `n₀+1` — run d₁'s left-analysis directly against it:
     `laxR` ending gives the two-cut route through `da` at `m + n₀`
     (strict); `laxL` and other left endings push at `(m-1) + n`
     (strict) and rebuild *because this subgoal is boxed*.  Then
     `hS hΓ (Γ ⇒ ◯A₁) q_b` closes.

**IMPLEMENTED AND KERNEL-CHECKED (same day, `PLLG4HCut.lean`):**
`G4c.cut_of_selfAbsorb : SelfAbsorb → (weight, height-sum) cut`, with
wrapper `G4c.cut'`, plus the new hp right-inversion `andR_inv` that
eliminated the push-tables from all implication-shaped principals.
First compile.  So: **cut is fully proved, conditional on `SelfAbsorb` alone** — no
interleaved measure, no `S`-tower.  `SelfAbsorb` itself is the old
`S`, now isolated: prove it standalone (its bottom cases want cut at
weights related to `F`, i.e. the genuine mutual knot survives only
here, in one lemma), or find the direct induction.  Either way the
conditional theorem pins every other obligation as discharged.

Completeness `SC → G4p` is then a plain induction on `SCh` (`impL` via
`K` + MP; `laxL` via `ABS`/`C`; the rest via inversions/identity), and
`G4p ≡ SC ≡ PLL` follows with `toSC`.  Termination of `G4p`
(decidability, F&M Thm 2.8) is a separate question: every rule premise
except `L◯→′`'s first is DM-decreasing; that premise strictly decreases
the *boxed-antecedent multiset* while trading the succedent for `◯φ` —
a lex/Bílková combination or a strategy-completeness argument is
needed, and weak termination + a complete strategy suffices.

## THE LADDER IS COMPLETE (2026-07-09, evening)

`SelfAbsorb` is **proved outright** (`PLLG4HCut.selfAbsorb_aux`), by
plain structural induction on the `◯A`-derivation — no cut, no
measure.  The resolution is poetic: the `laxL` ending that walled
every previous attempt is *exactly the firing shape of `L◯→″`* — the
box-witness rule Iemhoff introduced because of Howe's duplication
absorbs the opened premise verbatim (revision 2 having kept the full
context in it), and a `laxR` ending feeds `R◯→″` the same way
(revision 3).  If the implication is fired inside the derivation, its
own first premise is again a verbatim firing input.  Everything else
is parametric, the side derivation transported by hp-inversion.

Hence, unconditional and kernel-checked, each with pinned axiom audits
(`[propext, Quot.sound]` — choice-free since the 2026-07-17 axiom-hygiene
pass, no `sorryAx`):

    G4c.cut            : G4c Γ A → G4c (A::Γ) E → G4c Γ E
    G4c.completeness   : SC Γ C → G4c Γ C
    G4c.equiv_sc/nd/tm : G4c = SC = LaxND = Tm-inhabitation

Together with `PLLG4Gap.lean` (G4 ⊊ SC): **G4iLL″ is a complete
cut-free calculus for PLL with all structural rules admissible**,
obtained from Iemhoff's G4iLL by exactly three retention repairs.
The proof-theoretic half of F&M Theorem 2.8 is mechanised end to end;
what remains for decidability is the termination/strategy discipline
(Bílková-style order or strategy-bounded search), now over a calculus
that is *known* complete.
