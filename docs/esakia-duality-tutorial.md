# Esakia duality — a working tutorial

For Matthew, 2026-07-18. Register: standard order-topology/modal-logic
language; displayed definitions; pointers into this repo's threads (RN
lattice, nuclei/assembly, finite countermodels) where they connect.

---

## 0. Is it in Johnstone's *Stone Spaces*?

**Almost, but not by name.** What Johnstone develops:

* **Stone duality** for Boolean algebras — Chapter II.
* **Priestley duality** for bounded distributive lattices — the "ordered
  Stone spaces" section of Chapter II (§II.4): DL ⟷ Priestley spaces.
* The **frame/locale side** (Heyting algebras qua frames, opens of
  locales) — Chapters I–II — and **spectral spaces** for distributive
  lattices (the Stone-topology route, equivalent to Priestley's) in the
  coherent-locale chapters.

What he does **not** develop is the duality *for Heyting algebras as
such* — i.e. Esakia duality — as a named theory; the Heyting case
surfaces only in passing/exercises. The good news: Esakia duality is
exactly **Priestley duality + one extra condition**, so with *Stone
Spaces* §II.4 in hand the step is short, and this tutorial is that step.

Standard dedicated sources, in reading order:
1. **L. Esakia, "Topological Kripke models"**, Soviet Math. Dokl. 15
   (1974) — the original announcement.
2. **L. Esakia, *Heyting Algebras: Duality Theory*** (Russian 1985;
   English translation, Springer Trends in Logic 50, 2019, eds.
   G. Bezhanishvili & W. Holliday) — THE book; short and readable.
3. **Davey & Priestley, *Introduction to Lattices and Order*** —
   Priestley duality gently (background).
4. **Chagrov & Zakharyaschev, *Modal Logic*** ch. 8 — the same objects as
   "descriptive frames" (general-frame language, no topology vocabulary).
5. **Gehrke & van Gool, *Topological Duality for Distributive Lattices:
   Theory and Applications*** (CUP 2024) — modern textbook treatment with
   a Heyting/Esakia chapter.
6. For the **nucleus** refinement (our assembly thread): Bezhanishvili,
   Bezhanishvili, Moraschini et al. on *nuclear* Esakia spaces
   (arXiv:1906.03636), already cited in `docs/assembly-tower-lit.md`.

---

## 1. The three dualities in one table

| algebra | dual space | morphisms (spatial side) |
|---|---|---|
| Boolean algebras | Stone spaces (compact Hausdorff, zero-dim.) | continuous maps |
| bounded distributive lattices | Priestley spaces | continuous order-preserving maps |
| **Heyting algebras** | **Esakia spaces** | **continuous p-morphisms** |

Each column restricts the previous one: BA ⊂ DL as algebras with the
discrete order on the spectrum; HA ⊂ DL with the *Esakia condition* on
the spectrum and *p-morphisms* (not merely order-preserving maps) as the
dual maps.

## 2. Priestley spaces (the §II.4 objects, fixed notation)

> **Definition.** A *Priestley space* is a compact ordered topological
> space (X, τ, ≤) satisfying the *Priestley separation axiom*: whenever
> x ≰ y there is a **clopen up-set** U with x ∈ U and y ∉ U.

Duality (Priestley 1970): the dual of a bounded distributive lattice L is
the set of prime filters of L, ordered by ⊆, topologised by the subbasis
{ â : a ∈ L } ∪ { X ∖ â : a ∈ L } where â = {prime filters containing a}.
Conversely the lattice dual to X is

> ClopUp(X) = the lattice of clopen up-sets of X, with ∩, ∪, ∅, X.

L ≅ ClopUp(X_L) via a ↦ â, and X ≅ X_{ClopUp(X)}.

## 3. Esakia spaces: one extra axiom

A Heyting algebra is a distributive lattice with ⊃; the dual must have
enough structure to *compute* ⊃ from ∩/∪. That is exactly one condition:

> **Definition (Esakia space).** A Priestley space (X, τ, ≤) is an
> *Esakia space* if for every **clopen** U ⊆ X the down-set
>   ↓U = { x : ∃u ∈ U, x ≤ u }
> is again **clopen**.

(Priestley gives ↓U closed for closed U; the strengthening is that
clopens have clopen down-sets.)

> **Theorem (Esakia duality).** The category of Heyting algebras with
> Heyting homomorphisms is dually equivalent to the category of Esakia
> spaces with continuous p-morphisms. The algebra dual to X is
> ClopUp(X) with
>
>   U ⊃ V := X ∖ ↓(U ∖ V),      ¬U = X ∖ ↓U,
>
> and the Esakia condition is exactly what makes U ⊃ V clopen.

**Morphisms.** A *p-morphism* (bounded morphism) f : X → Y is
order-preserving with the back condition: f(x) ≤ y′ implies ∃x′ ≥ x with
f(x′) = y′. Continuous p-morphisms dualise Heyting homomorphisms.
(Plain order-preserving continuous maps only dualise *lattice*
homomorphisms — this is where HA-duality genuinely differs from
DL-duality, not just in the objects.)

## 4. The logician's dictionary

* An Esakia space is the same thing as a **descriptive intuitionistic
  Kripke frame**: worlds = points, accessibility = ≤, admissible
  valuations = clopen up-sets. Completeness of IPC w.r.t. descriptive
  frames is duality restated.
* **Finite case:** the topology trivialises — finite Esakia spaces are
  exactly **finite posets**, and the duality restricts to: finite Heyting
  algebras ⟷ finite posets (algebra = the up-sets of the poset). This is
  the bridge between our algebra computations and the `FinCM` finite
  countermodels: a finite countermodel's frame *is* the dual poset of a
  finite Heyting algebra.
* **Open subsets vs. filters:** up-sets of the dual ↔ filters; closed
  up-sets ↔ theories (the prime ones are the points). The
  `PLLCountermodelEmit` construction (worlds = prime G4c-closed
  theories, order = ⊆) is a hand-built finite fragment of the dual-space
  construction.

## 5. Where our threads plug in

* **The Rieger–Nishimura lattice.** RN = the free Heyting algebra on one
  generator; its Esakia dual is the *RN Esakia space* — the ω-comb/fan
  whose finite levels are the duals of the finite RN truncations. The
  one-variable universal model (`rnModel`, `wip/lax_infinite.lean` /
  `PLLLaxInfinite`) is its point-set skeleton. Cantor–Bendixson rank of
  this space is the invariant the assembly-tower thread wants
  (Simmons: assembly-stopping ordinal = CB rank, on frames).
* **Nuclei.** On the dual side a nucleus on a Heyting algebra H
  corresponds to a distinguished ("nuclear") subset of the Esakia space
  of H — the concrete computational handle for N(H) (the arXiv:1906.03636
  route). This is how one would *compute* N(RN) level-by-level: work on
  the dual posets of the RN truncations.
* **PLL frames.** Our constraint models (Rᵢ, Rₘ, fallible worlds) are the
  Kripke face; a descriptive/Esakia treatment of *lax* logic = Esakia
  spaces with the extra Rₘ-structure dualising ◯ — the natural setting
  for any future "Esakia duality for nuclear HAs applied to PLL" section
  in a paper.

## 6. Proof sketches worth internalising (both two-liners)

* *Why ⊃ needs the Esakia condition:* in any Priestley space,
  a ⊃ b must be the largest clopen up-set whose meet with a lies in b;
  the candidate is X ∖ ↓(â ∖ b̂), an up-set which is clopen iff
  ↓(clopen) is clopen.
* *Why finite = posets:* finite + Hausdorff-like separation forces the
  discrete topology; all subsets clopen, so the conditions trivialise and
  only the order remains.

---

*Cross-references:* `docs/assembly-tower-lit.md` (assembly/CB-rank),
`docs/nuclei-noncomplete-lit.md` (off-frame N(H)),
`docs/surveys/nuclei-model-completions-monads.md` (model completions,
joins of nuclei, monad coproducts).
