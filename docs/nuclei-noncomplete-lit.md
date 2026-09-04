# The algebra of nuclei on a non-complete Heyting algebra

*Literature dig, 2026-07-14. Question: for a Heyting algebra `H` that is **not** complete
(not a frame), what is the exact algebraic structure of the set `N(H)` of nuclei
( = Macnab's "modal operators" = interpretations of the lax modality `◯`), ordered
pointwise? Does it have a Heyting implication `⊃`? Binary joins? Is it a Heyting
algebra at all?*

Throughout, a **nucleus** on a meet-semilattice `A` (with top `⊤`) is a self-map `j` with

```
    a ≤ j a,        j (j a) = j a,        j (a ∧ b) = j a ∧ j b.
```

`N(H)` denotes the set of all nuclei on `H`, ordered pointwise
(`j ≤ k  ⇔  ∀a. j a ≤ k a`). Macnab and Beazer–Macnab call these *modal operators*;
in point-free topology they are *nuclei*; in Fairtlough–Mendler lax logic they are exactly
the algebraic interpretations of `◯`, and `(A, ∧, →, j)` — an implicative semilattice with
one distinguished nucleus — is the algebraic semantics for the `∨`-free fragment of PLL
(Bezhanishvili–Bezhanishvili–Carai–Gabelaia–Ghilardi–Jibladze, below).

---

## Crisp answer (foregrounded)

**For a general, non-complete `H` the reliably-guaranteed structure of `N(H)` is a
*bounded meet-semilattice*, and nothing more: neither the Heyting implication `⊃` of
nuclei nor the binary join `∨` of nuclei is guaranteed to exist.** Precisely:

- **Meets are pointwise and always exist** (finite case): `(j ∧ k) a = j a ∧ k a` is again a
  nucleus. Bottom `⊥ = id` (the identity nucleus); top `⊤ =` the constant map `a ↦ 1`.
  So `N(H)` is *always* a bounded meet-semilattice. **[ESTABLISHED]**

- **The join `j ∨ k` and the implication `j ⊃ k` are both "extremal-fixpoint"
  constructions** — the *least nucleus above* an auxiliary prenucleus, resp. the *greatest
  nucleus below* an auxiliary weak nucleus — and **Erné (2022) proves that specific
  completeness properties of `H` are *necessary and sufficient* for these to exist.**
  Hence off completeness they can genuinely fail: `N(H)` need **not** be a lattice, and
  need **not** be an implicative semilattice, so **in general it is *not* a Heyting
  algebra.** **[ESTABLISHED — Erné 2022; see Q2]**

- **The complete case is the good case.** `H` complete `⇔` `H` a frame; then `N(H)` *is* a
  frame (the *assembly* of `H`), hence a complete Heyting algebra with both `⊃` and all
  joins. Meets stay pointwise; joins are **not** pointwise (a pointwise sup of closure
  operators is not idempotent) but are computed as least fixed points of prenuclei
  (Escardó/Pataraia). Dually `N(H) ≅ S(H)^op`, the coframe of sublocales. **[ESTABLISHED]**

- **What *does* survive to the non-complete setting** is the *representation*, not the
  Heyting structure: `N(H)` is isomorphic to the poset of **nuclear ranges** — the
  closure ranges that are total subalgebras (`l`-ideals) — ordered by *dual* inclusion
  (Erné 2022). This is the non-complete analogue of "nuclei ≅ sublocales". **[ESTABLISHED]**

**Macnab verdict.** I could **not** obtain Macnab (1981) or Beazer–Macnab (1979) directly —
Springer, zbMATH, MathSciNet, ScienceDirect, PhilArchive and the Hannover repository all
blocked automated access (paywall / 403). I therefore have **no verbatim Macnab theorem
statement**, and I do **not** assert one. What I *can* source is what Macnab is *credited
with* by authors who did reach him — chiefly **Erné (2022)**, who builds directly on Macnab
and cites both his papers. On that (CONFIRMED-secondary) evidence Macnab's contribution is a
body of "substantial results on nuclei in the **non-complete** setting … on Heyting
algebras," including the decomposition result in Q1 below — **but Erné, like everyone else I
reached, describes the *total* structure of the nuclei only as a *semilattice*, never as a
Heyting algebra.** No source I reached asserts "`N(H)` is a Heyting algebra for arbitrary
`H`." See the candor note at the end.

---

## Q1 — Macnab 1981: the main structural theorem

**Reference (CONFIRMED to exist; NOT directly accessed):**
D. S. Macnab, *Modal operators on Heyting algebras*, **Algebra Universalis 12** (1981),
no. 1, 5–29, `doi:10.1007/BF02483860`. Preceded by his thesis: D. S. Macnab, *An algebraic
study of modal operators on Heyting algebras with applications to topology and
sheafification*, Ph.D., University of Aberdeen, 1976. (Both appear verbatim in Erné's
reference list, [33] and [32] respectively.)

**Status of the theorem statement: UNVERIFIED (paywalled).** I did not reach the paper, a
zbMATH/MR review, or any source quoting a numbered Macnab theorem verbatim. I will *not*
fabricate one. Everything below is *attributed to the secondary source that states it*.

**What Macnab is credited with (CONFIRMED via Erné 2022, who cites Macnab [32,33]):**

- Nuclei on Heyting algebras "are also referred to as *modal operators* (Beazer and Macnab
  [4], Macnab [32,33])." Macnab's three canonical nuclei carry the notation `v_a, u_a, w_a`
  (Erné/ÁBMZ/the survey all record that the operators
  `o_a(x)=a→x` (open), `c_a(x)=a∨x` (closed), `b_a(x)=(x→a)→a` (relatively dense /
  "boolean") "were first considered in [Simmons 78, Beazer–Macnab 79, Macnab 81]").

- "The tools of r- and l-morphisms provide extensions of results from the realm of
  frames/locales to arbitrary Heyting algebras or even to implicative semilattices.
  Sometimes the existence of certain joins or meets is indispensable. **But one also finds
  substantial results on nuclei in the non-complete setting, for example in the work of
  Macnab [32,33] on Heyting algebras**" (Erné 2022, §1).

- The one *specific* Macnab result Erné singles out (Erné 2022, §1, citing Macnab [33]): the
  basic open `l`-ideals `𝔞a = {a→x | x∈A}` and basic closed `l`-ideals `𝔠a = {x | x≥a} = ↑a`
  "**together generate `𝒩A` via joins of finite meets if `A` is a Heyting algebra [33].**"
  This is the non-complete analogue of the frame fact "every sublocale is a meet of binary
  joins of open and closed sublocales" (survey Cor. 4.14). Note this is a *generation*
  statement about a specific family; **it is not the same as, and Erné does not upgrade it
  to, "`N(H)` is a Heyting algebra."**

**Does Macnab prove `N(H)` is a Heyting algebra, and does the construction need
completeness?** On the sources I reached: the *meet* semilattice structure needs nothing
(finite pointwise meets); the *join* and *implication* need completeness (Q2). Erné's
uniform verdict for the general (implicative-semilattice, hence non-complete) case is
**"the nuclei form a semilattice `𝒩A`"** — a meet-semilattice — and I found **no** source,
Macnab-derived or otherwise, claiming a full Heyting-algebra structure on `N(H)` for
arbitrary non-complete `H`. I cannot exclude that Macnab proved something sharper for the
special case where `H` is a Heyting algebra (finite joins present) than for a bare
implicative semilattice; that residual gap is exactly the part I could not close without the
paper. **[Honest limit — see candor note.]**

**A single-equation characterisation attributed to Macnab (UNVERIFIED):** secondary mentions
state that Macnab characterised nuclei by one identity, quoted as `x → j y = j x → j y`. I
saw this only in a search snippet, reached no primary source for it, and do not rely on it.
(Erné's own one-line characterisation of a *closure* operation is the adjunction
`x ≤ j y ⇔ j x ≤ j y`, his equation (C) — that is the closure-operator condition, not the
nucleus-specific identity.)

---

## Q2 — Join and implication of nuclei off-frame

### The frame (complete) case — fully established, multiply sourced

For a frame `L`:

- `N(L)` is a **frame**, the *assembly* of `L` (Simmons 1978, p. 242). Equivalently
  `N(L) ≅ S(L)^op`, where `S(L)` (sublocales, ordered by inclusion) is a *coframe*
  (Bezhanishvili–Melzer survey, Def. 4.1, Thm. 4.4; Picado–Pultr, *Frames and Locales*,
  Ch. III). Being a frame, `N(L)` is a complete Heyting algebra, so `⊃` and all joins exist.

- **Meets are pointwise**; **the top** is `a ↦ 1` and **the bottom** is `id`
  (ÁBMZ §2, verbatim: "Finite meets are defined in `N(L)` componentwise, the bottom `⊥` is
  the identity nucleus, and the top `⊤` is the nucleus sending every element of `L` to 1.").

- **Joins are NOT pointwise.** "Calculating joins in `N(L)` is more involved"
  (ÁBMZ §2, citing Johnstone *Stone Spaces* II.2.5). The obstruction: a pointwise join of
  closure operators is **not idempotent**. The resolution (Escardó, *Joins in the Frame of
  Nuclei*, Appl. Categ. Structures **11** (2003), no. 2, 117–124): **prenuclei**
  (inflationary, finite-meet-preserving maps) *are* closed under composition and pointwise
  *directed* joins, so a join of nuclei is the **least fixed point of an inflationary
  operator on prenuclei**, obtained by Pataraia's fixed-point theorem. Directed joins /
  least fixed points are exactly what require completeness.

- Every nucleus decomposes: `j = ⋀ { w_{ja} | a ∈ L }` with `w_a(x) = (x→a)→a`
  (ÁBMZ §2, citing Simmons); dually every sublocale is a meet of binary joins of open and
  closed sublocales (survey Cor. 4.14). `a ↦ u_a` (or `a ↦ c_a`) embeds `L` into `N(L)`,
  giving the assembly tower `L ↪ N(L) ↪ N²(L) ↪ ⋯`.

### The non-complete case — the decisive source is Erné 2022

**M. Erné, *Nuclear ranges in implicative semilattices*, Algebra Universalis 83:18 (2022),
`doi:10.1007/s00012-022-00768-3`, open access (CC-BY). [CONFIRMED — full text read.]**
This is *the* paper for the non-complete question; it and its announced successor
("*Assemblies of implicative semilattices*", preprint) set out to "extend, as far as
possible, results on nuclei and their ranges to the **non-complete setting of implicative
semilattices**." Verbatim from the abstract:

> "A nucleus on a meet-semilattice `A` is a closure operation that preserves binary meets.
> **The nuclei form a semilattice `𝒩A` that is isomorphic to the system `𝒩A` of all nuclear
> ranges, ordered by dual inclusion.** The nuclear ranges are those closure ranges which are
> total subalgebras (`l`-ideals). Nuclei have been studied intensively in the case of
> **complete** Heyting algebras. We extend, as far as possible, results on nuclei and their
> ranges to the non-complete setting of implicative semilattices … **Certain completeness
> properties are necessary and sufficient for the existence of a least nucleus above a
> prenucleus or of a greatest nucleus below a weak nucleus.**"

Reading the two highlighted sentences against the definitions of the lattice operations:

1. **`N(H)` is a (bounded) meet-semilattice — always.** Erné's headline structure is a
   *semilattice*, deliberately not "lattice" or "Heyting algebra". Finite meets are pointwise
   (his §2, `A_{j∧k}`-type computations); the isomorphism to nuclear ranges is order-*dual*.

2. **Binary joins of nuclei are completeness-gated.** The join `j ∨ k` is the *least nucleus
   above* the inflationary map generated by `j, k`; Erné's Theorem 2.7 makes the existence of
   the "least closure operation `ḡ` above a preclosure `g`" equivalent to an
   `l`-completeness condition on `H`, and the abstract states this equivalence is **necessary
   and sufficient**. "Necessary" means there are non-complete `H` where the least nucleus —
   hence the join — **fails to exist**. So `N(H)` is **not a lattice** in general.

3. **The implication `⊃` of nuclei is likewise completeness-gated.** `j ⊃ k` is a *greatest
   nucleus below* a suitable weak nucleus; existence of the "greatest closure `g°` below a
   weak closure `g`" is again governed by an `l`-completeness condition (Erné Prop. 2.6(3),
   Thm. 2.7, and the abstract's "greatest nucleus below a weak nucleus"). So `⊃` is **not
   guaranteed** either, and `N(H)` need not even be an implicative semilattice.

4. **Framework.** Erné treats an implicative semilattice as `(A, ∧, ⊤, α)` with
   `α_a = (a → −)` the residual of `λ_a = (a ∧ −)`; the frames/locales are exactly the
   *complete* implicative semilattices. Nuclear ranges = `l`-ideals that are closure ranges =
   the non-complete generalisation of *sublocales*; morphisms are r-/l-morphisms
   (residuated top-preserving `∧`-homs and their adjoints) which "transport nuclear ranges
   and preserve implicativity." The companion paper does the morphism theory:
   **M. Erné, J. Picado, A. Pultr, *Adjoint maps between implicative semilattices and
   continuity of localic maps*, Algebra Universalis 83:19 (2022),
   `doi:10.1007/s00012-022-00767-4`** (Coimbra preprint 21-28, freely available)
   **[CONFIRMED — read]**, which states plainly: "In the complete case of frames/locales, the
   r-domains are the subframes, whereas the l-domains are the sublocales. In our general
   setting, they are still nothing but the **ranges of nuclei**."

**Corroborating warning from the frame side.** ÁBMZ (below) give Example 4.7: on a general
(non-frame) Esakia space, the *intersection* of two nuclear sets need not be nuclear — the
dual symptom that the lattice operation on nuclei matching it (a join of nuclei) has no naive
description once completeness (extremal order-disconnectedness) is dropped.

**Net answer to Q2.** For non-complete `H`: **the binary join of two nuclei need not exist,
and the Heyting implication `⊃` of two nuclei need not exist**; both are extremal-fixpoint
constructions whose existence Erné pins to necessary-and-sufficient completeness conditions.
The unconditional structure is a bounded **meet-semilattice**; the surviving positive
statement is the representation `N(H) ≅ {nuclear ranges, dual inclusion}`. `N(H)` is a
Heyting algebra (indeed a frame) exactly in the complete case.

---

## Q3 — `N(B) ≅ B` and the Boolean case

### Beazer–Macnab, stated precisely

**Reference (CONFIRMED to exist; NOT directly accessed):** R. Beazer and D. S. Macnab,
*Modal extensions of Heyting algebras*, **Colloquium Mathematicum 41** (1979), no. 1, 1–12.
*(Citation caution: Erné's list [4] mis-records this as "Modal operators on Heyting
algebras … Coll. Math. XVI"; the ÁBMZ list and the standard record agree on the title
*Modal extensions…* and volume **41**. Same authors, year, pages 1–12.)*

**The result, as restated by a source that reached it (ÁBMZ §1, verbatim):**

> "Beazer and Macnab [1] proved that **if `L` is boolean, then `N(L)` is isomorphic to `L`**,
> and gave a necessary and sufficient condition for `N(L)` to be boolean."

This is stated in the **frame** setting (ÁBMZ work throughout with frames), so "`L` boolean"
there means a **Boolean frame = complete Boolean algebra**. The sharp "iff" refinement is
theirs plus ÁBMZ Thm. 7.14: *for a spatial frame `L`, `N(L)` is boolean `⇔` `N(L)` is a
complete atomic Boolean algebra `⇔` the space `Y_L` is scattered.* The canonical embedding
`L ↪ N(L)` is an isomorphism iff every nucleus is open, i.e. iff `L` is a Boolean frame.

### What about a NON-complete Boolean algebra `B`?

Here the completeness worry of Q2 **evaporates**, and `N(B) ≅ B` for **any** Boolean algebra,
complete or not. This is elementary and finitary; I give the argument because I could not
confirm from Beazer–Macnab's own text whether their hypothesis was "complete Boolean" or
"any Boolean". **[This derivation is my own inference, clearly marked — but it is standard and
self-contained; it uses only the Boolean law `x ∨ ¬x = 1` and the nucleus axioms.]**

Let `j` be any nucleus on a Boolean algebra `B`, and put `a := j 0`. For every `x`:

```
    j x  =  j x ∧ 1  =  j x ∧ (x ∨ ¬x)  =  (j x ∧ x) ∨ (j x ∧ ¬x)
         =  x ∨ (j x ∧ ¬x).
```

Now `j` preserves binary meets, so `j x ∧ j(¬x) = j(x ∧ ¬x) = j 0 = a`, whence
`j x ∧ ¬x ≤ j x ∧ j(¬x) = a` (using `¬x ≤ j(¬x)`). Combined with `a = j 0 ≤ j x` and
`x ≤ j x`, this gives

```
    j x  =  x ∨ (j x ∧ ¬x)  ≤  x ∨ a  ≤  j x,     i.e.   j x = a ∨ x = c_a(x).
```

So **every nucleus on a Boolean algebra is a closed nucleus** `c_a`, `a = j0`. The map
`c : B → N(B)`, `a ↦ c_a`, is injective (`c_a(0)=a`), order-reflecting, and surjective, with
`c_a ∧ c_b = c_{a∧b}` and (as an order-iso onto `N(B)`) `c_a ∨ c_b = c_{a∨b}`. Hence:

- **`N(B) ≅ B` for every Boolean algebra `B`, complete or not** — as Boolean algebras, a
  fortiori as Heyting algebras. So `N(B)` *is* a well-defined Heyting algebra here, and it is
  just `B` again; the assembly tower collapses at the first step.
- On a Boolean algebra open = closed: `u_a(x) = a → x = ¬a ∨ x = c_{¬a}(x)`, and
  `w_a(x) = (x→a)→a = a ∨ x = c_a(x)`. All three canonical families coincide, matching Erné's
  remark that his `𝔞a`, `𝔟a`, `𝔠a` collapse and that the "boolean" `l`-ideals `𝔟a` are meet-
  dense in `𝒩A` and are exactly the `l`-ideals that are Boolean lattices.
- Note the join `c_a ∨ c_b = c_{a∨b}` is **not** the pointwise join of the closure operators
  `c_a, c_b` (that is not idempotent); it just tracks `a ∨ b` in `B`. The Q2 non-pointwise-
  join phenomenon is present but harmless because the answer is forced back onto `B`.

**Sourcing of Q3:** the collapse `N(B) ≅ B` is ESTABLISHED (Beazer–Macnab, restated by ÁBMZ);
its extension to *non-complete* `B` is the elementary argument above (my inference, standard).
I did not find a source that explicitly asserts `N(B) ≅ B` for *incomplete* `B` in print, nor
one that contradicts it; given the one-line proof I am confident it is correct and folklore.

---

## References

Tag key: **[C]** = I reached the source (or a source that quotes it) directly;
**[U]** = located/cited but the *content claim* rests on a secondary mention only.

Primary targets of the question
- **[U]** D. S. Macnab, *Modal operators on Heyting algebras*, Algebra Universalis **12**
  (1981) 5–29, `doi:10.1007/BF02483860`. *Paywalled; not accessed. All Macnab claims here are
  attributed to Erné 2022 / ÁBMZ, who cite him.*
- **[U]** D. S. Macnab, *An algebraic study of modal operators on Heyting algebras with
  applications to topology and sheafification*, Ph.D. thesis, University of Aberdeen, 1976.
- **[U]** R. Beazer, D. S. Macnab, *Modal extensions of Heyting algebras*, Colloquium
  Mathematicum **41** (1979) 1–12. *Not accessed; result quoted via ÁBMZ.*

Sources actually read (the load-bearing ones)
- **[C]** M. Erné, *Nuclear ranges in implicative semilattices*, Algebra Universalis **83**:18
  (2022), `doi:10.1007/s00012-022-00768-3` (open access, CC-BY). *Full text read — the
  decisive source for the non-complete case: nuclei form a meet-semilattice `𝒩A ≅` nuclear
  ranges by dual inclusion; join/implication existence is completeness-gated (necessary and
  sufficient).*
- **[C]** M. Erné, J. Picado, A. Pultr, *Adjoint maps between implicative semilattices and
  continuity of localic maps*, Algebra Universalis **83**:19 (2022),
  `doi:10.1007/s00012-022-00767-4`; free preprint: `www.mat.uc.pt/preprints/ps/p2128.pdf`
  (Coimbra 21-28). *Read — ranges of nuclei = l-domains generalise sublocales off-frame.*
- **[C]** F. Ávila, G. Bezhanishvili, P. J. Morandi, A. Zaldívar, *When is the frame of nuclei
  spatial: a new approach*, `arXiv:1906.03636`. *Read — pointwise meets, top `a↦1`, bottom
  `id`, "joins more involved"; Beazer–Macnab restatement; Esakia-dual `N(L) ≅ N(X_L)`;
  Example 4.7 (intersection of nuclear sets need not be nuclear off-frame).*
- **[C]** G. Bezhanishvili, S. D. Melzer, *Priestley perspective on pointfree topology*,
  `arXiv:2511.01426` (2025). *Read §2, §4 — `S(L)` coframe, `N(L)` assembly/frame, Thm. 4.4
  duality; Rem. 4.11 attributes `o_a,c_a,b_a` to [Simmons 78, Beazer–Macnab 79, Macnab 81].*
- **[C]** G. Bezhanishvili, N. Bezhanishvili, L. Carai, D. Gabelaia, S. Ghilardi, M. Jibladze,
  *Diego's Theorem for nuclear implicative semilattices*, `arXiv:2001.11060` (Indag. Math.
  2021). *Read intro — nucleus on an implicative semilattice; every Heyting algebra is an
  implicative semilattice but not conversely (implicative semilattice + joins = Heyting
  algebra); nuclear implicative semilattices = algebraic semantics for the `∨`-free fragment
  of Fairtlough–Mendler Lax Logic.*
- **[C]** M. H. Escardó, *Joins in the frame of nuclei*, Appl. Categ. Structures **11** (2003)
  117–124. *Content (joins = least fixed points of prenuclei via Pataraia; pointwise join of
  closure operators not idempotent) confirmed via abstract/summary; full text not opened.*

Cited but not reached (content via the [C] sources above)
- **[U]** G. Bezhanishvili, S. Ghilardi, *An algebraic approach to subframe logics.
  Intuitionistic case*, Ann. Pure Appl. Logic **147** (2007) 84–100. *(= ÁBMZ [5]: nuclei on
  a Heyting algebra `↔` special closed "nuclear" subsets of the Esakia space; Thms 30, 34.)
  ScienceDirect blocked the fetch.*
- **[U]** H. Simmons, *A framework for topology*, Logic Colloquium '77, Stud. Logic Found.
  Math. **96**, North-Holland (1978) 239–251. *(Assembly; `j = ⋀ w_{ja}` decomposition.)*
- **[U]** P. T. Johnstone, *Stone Spaces*, CUP (1982), II.2. *(Assembly, joins hard.)*
- **[U]** J. Picado, A. Pultr, *Frames and Locales: topology without points*, Birkhäuser
  (2012), Ch. III. *(`S(L)` coframe; `N(L)` assembly; booleanization.)*
- **[U]** P. Köhler, *Brouwerian semilattices*, Trans. AMS **268** (1981) 103–126; W. C.
  Nemitz, *Implicative semi-lattices*, Trans. AMS **117** (1965) 128–142. *(Foundations of the
  non-complete "implicative semilattice" setting; total subalgebras = `l`-ideals.)*
- **[U]** M. Erné, *Assemblies of implicative semilattices*, preprint (the announced sequel to
  the 2022 paper; the direct study of the algebraic structure of `𝒩A`). *Not located online.*

### Notes on access
Springer article pages and OA PDFs (Erné 2022) redirect the WebFetch fetcher to an IdP
cookie handshake; the CC-BY PDF was retrievable only by following redirects with `curl`
(`link.springer.com/content/pdf/10.1007/s00012-022-00768-3.pdf`). zbMATH, MathSciNet,
academia.edu, ScienceDirect, PhilArchive and `repo.uni-hannover.de` all returned 403 to both
WebFetch and `curl`, which is why Macnab and Beazer–Macnab remain **[U]**.

### Candor note on confidence
- The **frame case** (Q2 first half) and the **Boolean collapse** (Q3) are solid: multiply
  sourced and, for the Boolean case, backed by a one-line finitary proof.
- The **non-complete headline** ("meet-semilattice; `⊃` and `∨` are completeness-gated and can
  fail; not a Heyting algebra in general") rests on Erné 2022, read in full — high confidence.
- The **one genuine gap** is a *verbatim Macnab theorem*. I did not see Macnab's own statements
  and cannot rule out that for a Heyting-algebra base (as opposed to a bare implicative
  semilattice) Macnab established more join/implication structure than Erné's general
  "semilattice" verdict advertises. If a definitive `N(H)`-is/*isn't*-a-Heyting-algebra ruling
  for arbitrary non-complete `H` is needed, the two documents to obtain are **Macnab 1981**
  and **Erné's sequel "Assemblies of implicative semilattices"** — neither reachable here.
