# Review pack: the G4iLL incompleteness claim

*Prepared 2026-07-08, worktree `g4ill`. Purpose: everything needed to
check the claim against Iemhoff's papers as written, before any
correspondence. Every Lean item cited here is committed and sorry-free;
the pencil-and-paper items are labelled as such.*

The claim being reviewed:

> **Claim.** The sequent `◯((◯p→r)→◯p), ◯p→r ⇒ r` is derivable in
> G3iLL but not in G4iLL (Iemhoff, *Proof Theory for Lax Logic*,
> Fig. 2.3 = published Fig. 8.3). Hence Corollary 1/8.1 there is false,
> as is Theorem 1 of arXiv:2011.11847v1 (whose hypotheses G4iLL
> satisfies). Moreover `◯((◯p→r)→◯p), ◯p→r, ◯p→r ⇒ r` (two copies)
> **is** G4iLL-derivable, so contraction is not admissible in G4iLL —
> which is the hypothesis the published version of the general theorem
> (Studia Logica 110 (2022), Thm 3.4) added, so the published theorem
> does not apply to lax logic either.

Abbreviations throughout: `F′ := ◯p→r`, `G′ := F′→◯p`, and the
`⊥`-variant `F := ◯⊥→⊥`, `G := F→◯⊥`.

---

## 1. What is machine-checked, and with what trust base

| # | Statement | Artifact | Checked by |
|---|-----------|----------|------------|
| 1 | `SC [◯G′, F′] r` (G3-derivability) | `theorem sep_SC` in `LaxLogic/PLLG4Gap.lean` | **Lean kernel** (an explicit derivation term; axioms: `propext, Quot.sound` — choice-free since the 2026-07-17 hygiene pass) |
| 2 | `¬ G4 [◯G′, F′] r` (G4-underivability) | **`theorem sep_not_G4`**, same file (§7 item 1 is DONE); the `decide … = false` guard remains as an independent second witness | **Lean kernel** — an explicit inversion proof, axiom audit pinned at build time: **`[propext]` only**. Packaged with row 1 as `theorem sc_but_not_G4`. |
| 3 | `G4 [◯G′, F′, F′] r` (two copies derivable) | `decide … = true`, same file | compiled evaluation (a hand derivation also exists, §6, usable as a kernel-checked term on request) |
| 4 | `G4 [◯G′, F′] ◯p` (control: the boxed detour exists) | `decide … = true` | compiled evaluation |
| 5 | All of 1–4 for the `⊥`-variant `◯G, F ⇒ q` | same file | as above |
| 6 | The nucleus countermodel computations (§5) | — | **pencil and paper** (5-minute check; *not* load-bearing for 1–3) |

On the trust base of rows 2–4: the `Decidable` instance is not an
oracle. Its ingredients are three **kernel-checked theorems** about the
enumeration `succs` of backward rule instances
(`LaxLogic/PLLDecide.lean`):

```lean
theorem succs_sound    : inst ∈ succs Γ C → (∀ s ∈ inst, G4 s.1 s.2) → G4 Γ C
theorem succs_complete : G4 Γ C → ∃ inst ∈ succs Γ C, ∀ s ∈ inst, G4 s.1 s.2
theorem succs_dec      : inst ∈ succs Γ C → s ∈ inst →
                           Multiset.IsDershowitzMannaLT (smeasure s) (smeasure (Γ,C))

def decideG4 : ∀ s : Sequent, Decidable (G4 s.1 s.2) :=
  WellFounded.fix (InvImage.wf smeasure Multiset.wellFounded_isDershowitzMannaLT) …
```

`succs_complete` is the crucial one: *every* G4 derivation ends with an
enumerated instance, so exhaustive backward search is a decision
procedure, and `succs_dec` makes it terminate. The only trust added on
top of the kernel is that Lean's compiler correctly executes
`decideG4` at the two arguments (`WellFounded.fix` does not ι-reduce in
the kernel, so `by decide` is unavailable — this is the standard
situation for verified deciders). If we want to remove even that, §7
sketches a hand-written kernel-checked `¬ G4 [◯G′, F′] r`; the search
tree is small.

Row 1 chains into the rest of the mechanisation:
`SC_to_ND`/`ND_to_SC` (`PLLSequent.lean:546,578`, F&M Lemma 2.7) make
the G3-witness an ND-derivation, hence sound for the mechanised F&M
semantics — the sequent really is a PLL-validity (independently proved
by hand in §5.1).

## 2. Faithfulness: her calculus vs. our Lean inductives

Sources: arXiv:2209.08976 Fig. 2.1–2.3, identical to Figs. 8.1–8.3 of
the published chapter (checked against both PDFs; the extraction agent
confirmed the published figures verbatim). Her caption: *"G3iLL is G3ip
plus R◯ and L◯, G4iLL is G4ip plus all four rules."* Her sequents:
finite **multisets**, single succedent with **at most one** formula;
`⊥` is *not* an atom; weight `w(∧)=+2`, `w(∨)=w(→)=+1`, `w(◯)=+1`
(ours: `PLLFormula.weight`, identical including `w(⊥)=1`).

### G4iLL (her Fig. 2.3/8.3 notation) vs `inductive G4` (`PLLG4.lean:87`)

| Her rule | Her premises / conclusion | Our constructor |
|---|---|---|
| Ax | `Γ, p ⇒ p` (p an atom) | `init (h : prop a ∈ Γ) : G4 Γ (prop a)` |
| L⊥ | `Γ, ⊥ ⇒ Δ` | `botL (h : ⊥ ∈ Γ) : G4 Γ C` |
| R∧ | `Γ⇒φ`, `Γ⇒ψ` / `Γ⇒φ∧ψ` | `andR` |
| L∧ | `Γ,φ,ψ⇒Δ` / `Γ,φ∧ψ⇒Δ` | `andL (h : Γ.Perm (φ∧ψ :: Δ))`, premise `φ::ψ::Δ ⊢ C` |
| R∨ᵢ | `Γ⇒φᵢ` / `Γ⇒φ₀∨φ₁` | `orR1`, `orR2` |
| L∨ | two premises | `orL` |
| R→ | `Γ,φ⇒ψ` / `Γ⇒φ→ψ` | `impR` |
| Lp→ | `Γ,p,φ⇒Δ` / `Γ,p,p→φ⇒Δ` (p an atom) | `impLProp (h : Γ.Perm ((p→φ)::Δ)) (ha : p ∈ Δ)`, premise `φ::Δ ⊢ C` |
| L∧→ | `Γ,φ→(ψ→γ)⇒Δ` / `Γ,(φ∧ψ)→γ⇒Δ` | `impLAnd` |
| L∨→ | `Γ,φ→γ,ψ→γ⇒Δ` / `Γ,(φ∨ψ)→γ⇒Δ` | `impLOr` |
| L→→ | `Γ,ψ→γ ⇒ φ→ψ` and `Γ,γ⇒Δ` / `Γ,(φ→ψ)→γ⇒Δ` | `impLImp`, premises `(ψ→γ)::Δ ⊢ φ→ψ` and `γ::Δ ⊢ C` |
| R◯ | `Γ⇒φ` / `Γ⇒◯φ` | `laxR` |
| L◯ | `Γ,ψ⇒◯φ` / `Γ,◯ψ⇒◯φ` | `laxL (h : Γ.Perm (◯ψ::Δ))`, premise `ψ::Δ ⊢ ◯φ` |
| **R◯→** | `Γ⇒φ` and `Γ,ψ⇒Δ` / `Γ,◯φ→ψ⇒Δ` | `impLLax (h : Γ.Perm ((◯φ→ψ)::Δ))`, premises `Δ ⊢ φ` and `ψ::Δ ⊢ C` |
| **L◯→** | `Γ,χ⇒◯φ` and `Γ,◯χ,ψ⇒Δ` / `Γ,◯χ,◯φ→ψ⇒Δ` | `impLLaxLax (h : Γ.Perm ((◯φ→ψ)::◯χ::Δ))`, premises `χ::Δ ⊢ ◯φ` and `ψ::◯χ::Δ ⊢ C` |

Interpretation points, each with its resolution:

1. **Multisets vs lists.** Her contexts are multisets; ours are lists
   with every left rule locating its principal through a permutation
   hypothesis, and exchange proven (`G4.perm`, `PLLG4.lean:143`). The
   two presentations derive the same sequents up to `List.Perm`, which
   is definitionally the multiset quotient.
2. **Empty succedents.** Her `Δ` may be empty; our succedent is a
   formula. Inspecting her rules top-down: no rule with a nonempty
   succedent in the conclusion has an empty succedent in any premise
   (the L-rules and R◯→/L◯→ carry `Δ` through; premise 1 of R◯→/L◯→
   has succedent `φ`/`◯φ`; the R-rules and Ax/L⊥ likewise). So every
   derivation of a nonempty-succedent sequent stays nonempty, and our
   formalisation is faithful for such sequents. The separating sequent
   has succedent `r`.
3. **One deliberate extra rule, in the safe direction.** Our `impLBot`
   (`Γ,⊥→ψ ⇒ Δ` from `Γ ⇒ Δ`) has no counterpart in her G4ip: with
   `⊥` not an atom, her calculus simply has **no** left rule for a
   `⊥→ψ` antecedent (harmless for completeness, `⊥→ψ` being inert).
   Thus our `G4` derives *at least* everything her G4iLL does, rule
   instance for rule instance. Underivability verdicts (`false`)
   therefore transfer **a fortiori** to her calculus; and the positive
   derivations relevant here (rows 3–4, and §6) use no `impLBot`, so
   they are literally derivations in her calculus too.
4. **Lp→ keeps its atom** (her `Γ,p,…`): ours keeps `p ∈ Δ` ✓.
   **L◯→ needs a separate box occurrence** `◯χ` besides the
   implication: ours exposes both through the `Perm` (an implication
   cannot unify with `◯χ`) ✓.

### G3iLL vs `inductive SCh` (`PLLSequent.lean:30`)

Her G3iLL = G3ip + R◯ + L◯, additive, principal formulas **kept** in
the context. Ours (`SC Γ C := ∃ n, SCh n Γ C`) keeps principals via
membership hypotheses — e.g.

```lean
| impL (h : A.ifThen B ∈ Γ) : SCh n Γ A → SCh n (B :: Γ) C → SCh (n+1) Γ C
| laxL (h : A.somehow ∈ Γ)  : SCh n (A :: Γ) (B.somehow) → SCh (n+1) Γ (B.somehow)
```

matching her `L→` (`Γ,φ→ψ⇒φ` and `Γ,ψ⇒Δ` / `Γ,φ→ψ⇒Δ` — the
implication present in premise 1 via `h`) and `L◯` (`Γ,ψ⇒◯φ` /
`Γ,◯ψ⇒◯φ` — with `◯ψ` kept, which only makes our premise *stronger*
than hers; our witness never needs the kept copy, see §4). Heights
`n` are our device for the cut proof; `SC` erases them.

## 3. The G3 witness, in full

`PLLG4Gap.lean`, kernel-checked. Written with her rule names:

```
                                        ————————————————— Ax
                                        ◯p, …, F′ ⇒ ◯p          ————————————— Ax
                                        (premise of L→ on F′)    r, ◯p, … ⇒ r
                                        —————————————————————————————————————— L→ (on F′)   ②
                    ————————————————————————————
                    ◯p, G′, ◯G′, F′ ⇒ r
              ——————————————————————————— R→
              G′, ◯G′, F′ ⇒ F′                 ◯p, G′, ◯G′, F′ ⇒ ◯p  (Ax)
              ———————————————————————————————————————————————————————— L→ (on G′)
                            G′, ◯G′, F′ ⇒ ◯p
                            ————————————————— L◯ (on ◯G′)
                            ◯G′, F′ ⇒ ◯p                    r, ◯G′, F′ ⇒ r  (Ax)
                            ——————————————————————————————————————————————— L→ (on F′)   ①
                                          ◯G′, F′ ⇒ r
```

The two `L→`-inferences on `F′` (① outside the box-opening, ② inside
it) are the point: **one multiset occurrence of `F′` is used twice**,
which G3's context-keeping left rules provide and G4's
context-consuming `R◯→`/`L◯→` do not. This is Howe's duplication
pattern (MSCS 11(4), 2001, §5) — his sequent
`B ⊃ ((◦A⊃C) ⊃ ◦A), ◦B, ◦A⊃C ⇒ C` is ours with the box packaged as
`◯G′` — for the formula class he identified: the `◯`-antecedent
implication itself.

## 4. Why no G4 derivation exists (the argument the decider mechanises)

Goal sequent `S₀ = (◯G′, F′ ⇒ r)`. Enumerate the rule instances with
conclusion `S₀` (this is `succs [◯G′, F′] r`, and `succs_complete`
says the enumeration is exhaustive):

* right rules / Ax: goal `r` is an atom not in the context — none.
* L⊥: no `⊥` in the context — none.
* rules on `◯G′`: it is a `◯`-formula, so only `L◯` (needs a `◯`-goal;
  goal is `r`) — none — or serving as the box of an `L◯→` instance.
* rules on `F′ = ◯p→r`: antecedent is a `◯`-formula, so exactly
  * **R◯→**: premises `(◯G′ ⇒ p)` and `(r, ◯G′ ⇒ r)`;
  * **L◯→** (box `◯G′`): premises `(G′ ⇒ ◯p)` and `(r, ◯G′ ⇒ r)`.

So `S₀` is derivable iff `(◯G′ ⇒ p)` or `(G′ ⇒ ◯p)` is. Both are
**invalid** (§5.2), hence underivable by soundness. ∎ (informally)

The decider does not use soundness: it recursively explores those two
premises' own instances until the finite DM-bounded search closes — and
returns `false`. The countermodel below is therefore *explanatory*
(it says **why** the search must fail), while the verdict itself is
independent of it.

## 5. The nucleus countermodel — precisely what it does and doesn't do

PLL's algebraic semantics: a Heyting algebra `H` with a **nucleus**
`j` (inflationary, idempotent, meet-preserving) interpreting `◯`
(Fairtlough–Mendler 1997 §3; Goldblatt 1981). Soundness of PLL — hence
of `SC` via `SC_to_ND`, hence of `G4` via `G4.toSC` — for this
semantics is classical; note it is *not* currently formalised in the
repo (the repo's mechanised semantics is the F&M Kripke one), and none
of the machine-checked rows in §1 depend on it.

### 5.1 The separating sequent is valid (so G4 *misses* it; SC does not overshoot)

In **any** `(H, j)` and any valuation, write `f = ⟦F′⟧ = jp → r` and
`g = ⟦G′⟧ = f → jp`, where `jp := j(⟦p⟧)`, `r := ⟦r⟧`. Then:

1. `jg ∧ f ≤ jg ∧ jf = j(g ∧ f)` (inflation on `f`, meet-preservation);
2. `g ∧ f ≤ jp` (modus ponens in `H`), so `j(g ∧ f) ≤ j(jp) = jp`;
3. hence `jg ∧ f ≤ jp ∧ f = jp ∧ (jp → r) ≤ r`. ∎

Four lines, any nucleus algebra: `◯G′ ∧ F′ ≤ r`. (Proof-theoretic
double-check: the §3 derivation plus `SC_to_ND`.)

### 5.2 The two G4 premises are invalid (the concrete countermodel 𝔄)

Take the 3-chain `H = {0 < m < 1}` (Heyting: `x→y = 1` if `x ≤ y`,
else `y`) with

```
j0 = m,   jm = m,   j1 = 1.
```

`j` is a nucleus: inflationary (`0≤m`, `m≤m`, `1≤1`); idempotent;
meet-preserving on a chain reduces to monotonicity plus the three pair
checks `j(0∧m)=m=j0∧jm`, `j(0∧1)=m=j0∧j1`, `j(m∧1)=m=jm∧j1`. ✓

Valuation `v(p) = v(r) = 0`. Compute:

| formula | value |
|---|---|
| `◯p` | `j0 = m` |
| `F′ = ◯p→r` | `m→0 = 0` |
| `G′ = F′→◯p` | `0→m = 1` |
| `◯G′` | `j1 = 1` |

* premise of R◯→: `◯G′ ⇒ p` — `1 ≤ 0` **fails**;
* premise of L◯→: `G′ ⇒ ◯p` — `1 ≤ m` **fails**.

(Consistency check of §5.1 in 𝔄: `⟦◯G′∧F′⟧ = 1∧0 = 0 ≤ 0 = ⟦r⟧` ✓ —
the endsequent is *not* refuted, as it must not be.)

**Status:** these are pencil-and-paper computations, deliberately small
enough to verify by hand in minutes. They played two roles: (i) they
are how the counterexample was *found* — while designing the
contraction-admissibility induction, the case that would not close
required exactly a premise of the shape `(G′ ⇒ ◯p)` to be derivable,
and 𝔄 showed it need not be; (ii) they explain §4. They are **not**
part of the machine-checked chain, which rests on §1 rows 1–2 only.

## 6. Contraction inadmissibility: the two-copy derivation

`decide (G4 [◯G′, F′, F′] r) = true` (build-time guard). The
derivation found — writable by hand, and using only rules of *her*
calculus (no `impLBot`):

```
L◯→ on F′ (copy 1) with box ◯G′:
  premise 1:  G′, F′ ⇒ ◯p
     by L→→ on G′ = (◯p→r)→◯p:
       premise 1:  r→◯p, F′ ⇒ ◯p→r
          by R→ then L◯→ on F′ with box ◯p:   (uses copy 2, inside)
            premise 1:  p, r→◯p ⇒ ◯p          (R◯, Ax)
            premise 2:  r, ◯p, r→◯p ⇒ r       (Ax)
       premise 2:  ◯p, F′ ⇒ ◯p                (Ax)
  premise 2:  r, ◯G′, F′ ⇒ r                  (Ax)
```

One copy is consumed outside, one inside — the two rule applications
that G3 funds from a single occurrence. With the single-copy verdict
`false`, this machine-checks that **the contraction rule is not
admissible in G4iLL**. Consequences: (i) the *published* general
theorem (SL 110 (2022) Thm 3.4, which added "closed under contraction"
to the G4iX hypotheses after refereeing) does not apply to G4iLL;
(ii) the *unpatched* theorem (arXiv v1 Thm 1 = lax paper Thm 2/8.2,
which requires closure under weakening only) is refuted outright,
since G4iLL satisfies all its stated hypotheses (nonflat ✓, G3iLL
closed under the structural rules ✓ = her Lemma 1, terminating in
`≪_w` ✓ = her Fact 1) yet derives strictly less than G3iLL.

## 7. Hardening options before correspondence

1. **Kernel-checked underivability** (removes the compiled-evaluator
   trust): hand-write `theorem : ¬ G4 [◯G′, F′] r` by case analysis on
   the derivation (the `Perm`-hypothesis design plus `perm_cons_cases`
   makes the inversion mechanical; the search tree of §4 is shallow —
   estimate 100–200 lines). Recommended; can be done on request.
2. **Named-theorem packaging** of the decider verdicts via
   `native_decide` (same trust base as `#eval`, but citable as
   `theorem`s; adds the `ofReduceBool` axiom — should be disclosed).
3. Formalising the nucleus semantics + 𝔄 would let §5 be
   machine-checked too, but adds no strength to the separation itself
   (§4's exhaustion is already mechanised in verified generality by
   the decider); park unless wanted for the note.

## 8. Version history of the theorem (for the correspondence)

* arXiv:2011.11847**v1** (Nov 2020): Thm 1, G4iX closed under
  **weakening**; modal case's exhibited `R→`-instance silently drops
  the second copy of `◯φ→ψ`.
* **Studia Logica 110:1493–1506 (2022)** (accepted May 2022; the arXiv
  was never updated): Thm 3.4 adds "**and contraction**"; the modal
  case now derives `Γ, ◯φ→ψ, ◯φ→ψ ⇒ Δ` and contracts. (Residual
  concern even there: it asserts `Sᵢ ≪ S` where the instance's
  conclusion is the doubled `S⁺`, and `S ≪ S⁺`; so `Sᵢ ≪ S` needs an
  argument the text doesn't give.)
* *Proof Theory for Lax Logic*: arXiv:2209.08976v1 (Sept 2022, v1
  only) **and** the published de Jongh chapter (2024) both state the
  theorem in the **unpatched** form (weakening only, cited as
  "accepted for publication"), and prove no contraction admissibility
  for G4iLL before invoking it (Cor. 1 = Cor. 8.1).
* Related self-flag: van der Giessen–Iemhoff, arXiv:2011.10383v2
  ("Corrected version at July 14, 2022"), Remark 1: the direct
  contraction claim for G4iGL□ (NDJFL 2021, Lemma 4.1) "might be
  wrong". The iSL/iGL equivalence proofs themselves are direct
  inductions (Bílková-style order), not the general theorem, and
  their `→SL`/`→GL` rules retain what L◯→ discards (the implication
  itself, resp. the unboxed context), so they are structurally immune
  to this counterexample shape.
