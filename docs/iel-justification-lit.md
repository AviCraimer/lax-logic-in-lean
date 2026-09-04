# Positioning PLL belief against Intuitionistic Epistemic Logic and Justification Logic

*Literature dig, 2026-07-15. Question: where does Propositional Lax Logic's `◯`,
read as "is believed", sit relative to its closest published neighbours — Artemov
& Protopopescu's Intuitionistic Epistemic Logic (IEL) and Artemov's Justification
Logic? Which axioms are shared, which distinguish them, and is the "evidence"
reading of `◯` supported by justification logic?*

Tag key: **VERIFIED** = read in a primary source (location given); **MY-INFERENCE**
= sound derivation not stated verbatim in a source; **CONJECTURE** = believed
true, to be machine-checked; **UNVERIFIED** = cited but the source was not reached.

---

## Crisp answer (foregrounded)

- **The nearest published neighbour of `◯` is A&P's `IEL⁻` — their "logic of
  intuitionistic beliefs" — not full `IEL`.** `IEL⁻` is intuitionistic logic +
  distribution `K(A→B)→(KA→KB)` + co-reflection `A→KA`, and it *leaves `K⊥`
  consistent* — the exact analogue of PLL's non-trivial `◯⊥`. **[VERIFIED, A&P Def 1]**

- **`◯` and `IEL⁻`-`K` agree** on co-reflection `A→□A`, distribution/normality,
  necessitation, `∧`-preservation, and **non-factivity** (`□⊥` consistent). They
  differ in **exactly one** law:

  > **idempotence.** `◯◯A ⊣⊢ ◯A` (PLL `◯` is a monad / nucleus). A&P's `K`
  > validates only `KA → KKA`; the converse `KKA → KA` is **not** a theorem of
  > `IEL⁻` or `IEL`. **[VERIFIED positive dir. (Prop 1.5); converse MY-INFERENCE + countermodel]**

- **Cleanest framing (CONJECTURE, machine-check both inclusions):**
  > `PLL-◯  =  IEL⁻  +  idempotence ◯◯A → ◯A`.
  > `◯` is A&P's belief modality *made idempotent*.

- **Distribution / normality is NOT a distinguishing feature.** Correcting the
  handover's "distribution NO (not normal)": `◯` **does** validate
  `◯(A→B)→(◯A→◯B)` — a nucleus preserves finite meets, so K holds. This is now
  machine-checked on the `◯` side (`nucleus_himp_le`, `wip/belief_normality.lean`,
  axioms clean) and derivable syntactically from PLL's own `◯S` + functoriality.

- **`◯` vs full `IEL` (knowledge).** `IEL = IEL⁻ + KA→¬¬A` (intuitionistic
  factivity, ≡ `¬K⊥`, "knowledge is consistent"). `◯` has no factivity: `◯⊥` is
  consistent. This is the **belief-vs-knowledge** line. **[VERIFIED, A&P Def 2, Thm 1]**

- **Justification logic does NOT fit `◯` off the shelf.** The standard forgetful
  projection `□F := ∃t.(t:F)` over the Logic of Proofs `LP` yields an **S4 box** —
  *factive* (`□A→A`) and *without* co-reflection: the reverse profile to `◯`. An
  evidential reading of `◯` needs a **non-factive** justification logic. **[VERIFIED, SEP]**

---

## Sources actually read

- **A&P** — S. Artemov, T. Protopopescu, *Intuitionistic Epistemic Logic*,
  **Review of Symbolic Logic 9(2)** (2016) 266–298; **arXiv:1406.1582v4** (19 Jan
  2016). Pages 1–22 read directly. All A&P formulas below are from that text. **[VERIFIED]**
- **SEP** — S. Artemov, M. Fitting, *Justification Logic*, Stanford Encyclopedia
  of Philosophy. **[VERIFIED]**
- Repo cross-check (PLL's own axioms): `LaxLogic/PLLAxiom.lean`,
  `PLLTheorems.lean`, `PLLHilbert.lean`, `PLLDemos.lean`. **[VERIFIED]**

---

## 1. The systems `IEL⁻` and `IEL` (A&P §3)

**Definition 1 — `IEL⁻`**, *"the logic of intuitionistic beliefs"*. **[VERIFIED]**

> Axioms: (1) axioms of propositional intuitionistic logic; (2) `K(A→B) → (KA→KB)`
> *(distribution)*; (3) `A → KA` *(co-reflection)*.  Rule: Modus Ponens.

**Definition 2 — `IEL`**, *"the logic of intuitionistic knowledge"* (equivalently
*"of provably consistent intuitionistic beliefs"*). **[VERIFIED]**

> `IEL := IEL⁻ + KA → ¬¬A`  *(A&P's name: intuitionistic reflection)*.

Point by point (all **[VERIFIED]**, A&P §3):

- **Distribution / normality** `K(A→B)→(KA→KB)`: **primitive axiom**, both systems (Def 1.2).
- **Strength** `KA∧KB→K(A∧B)`: not primitive but a **theorem** — Prop 2, `⊢ K(A∧B) ↔ (KA∧KB)`.
- **Necessitation** `⊢A ⇒ ⊢KA`: **derivable**, not primitive (only rule is MP) — Prop 1.1.
- **Co-reflection** `A→KA`: Def 1.3.
- **Intuitionistic factivity** `KA→¬¬A`: the single axiom `IEL` adds to `IEL⁻` (Def 2).
  `IEL⁻` does **not** prove it.
- **`IEL⁻` vs `IEL`:** the one axiom `KA→¬¬A`. Thm 1: `IEL` further proves `¬K⊥`,
  `¬(KA∧¬A)`, `¬A→¬KA`, `¬¬(KA→A)`, and `IEL⁻ +` any one of these `= IEL`; so
  equivalently `IEL = IEL⁻ + ¬K⊥`. Thm 3: `IEL⁻ ⊊ IEL` (strict). Both **reject**
  classical reflection — Thm 5: `⊬ KA→A` in both; Thm 11: the reflection *rule*
  `⊢KA ⇒ ⊢A` is admissible in both.
- A&P also record (Prop 1.4) that their logic is *"a normal intuitionistic modal
  logic"*, and (Prop 1.5) positive/negative introspection `⊢KP→KKP`, `⊢¬KP→K¬KP`.

## 2. "Belief" = co-reflection without factivity = `IEL⁻` (A&P's own reading)

A&P explicitly treat the co-reflective-but-non-factive modality as *belief*. **[VERIFIED]**

- p. 4: *"The basic intuitionistic logic of belief `IEL⁻` is given by the
  epistemic closure principle … along with the adoption of co-reflection `A→KA` …
  In `IEL⁻`, theoretically, false beliefs are not a priori ruled out."*
- §4.1 "Modeling Knowledge vs. Belief" (p. 22): the "all swans are white" model
  `M₄` is an `IEL⁻`-model with `1⊩Kp` but `1⊮¬¬p` — *"a mere belief … only a
  belief because the situation in which p does not hold was not considered
  epistemically possible."* Contrasted with the `IEL`-model `M₃` (knowledge).
- §3.1: `IEL` *"does not distinguish intuitionistic knowledge from intuitionistic
  provably consistent belief, just like … S5 does not distinguish knowledge from
  true belief."*

Because `¬K⊥` is exactly what must be **added** to reach `IEL`, `IEL⁻` leaves `K⊥`
consistent — structurally the closest published match to PLL's `◯⊥ ≠ ⊤`.

## 3. Justification logic forces factivity (SEP, §1.2, §4)

- **Forgetful projection:** replace each `t:F` by `□F`; existential reading
  `□F := ∃t.(t:F)`. **[VERIFIED]**
- **Logic of Proofs** `LP := JT + Positive Introspection`, where `JT` contains the
  **Factivity Axiom `t:F → F`** and positive introspection `t:F → !t:(t:F)`. **[VERIFIED]**
- **Realization:** `LP` is the explicit counterpart of **S4**; the forgetful
  projection of `LP` is `S4`. (Artemov, *The Logic of Proofs*, APAL 1994; *The
  Logic of Justification*, RSL 1(4) 2008.) **[VERIFIED]**
- **S4 is factive:** `□F→F`, `□F→□□F` (SEP §1.2). **[VERIFIED]**
- **Consequence:** the modality from the `LP→S4` forgetful projection is an S4
  box — factive (`□F→F`), and with **no** co-reflection (`A→□A` is not S4-valid).
  So `◯M := ∃t.(t:M)` built on `LP` would force `◯M → M`, the reverse profile to
  `◯`. **[factivity VERIFIED; "reverse profile" MY-INFERENCE]**

To read `◯` as "evidence exists" one must drop `LP`'s factivity `t:F→F` and use a
**non-factive** justification logic. A&P gesture at a justification counterpart of
`IEL` (arXiv:1406.1582 §3.3, fn 22); see also Su & Sano, and Lurie. **[UNVERIFIED —
these specific sources not reached; confirm before citing]**

---

## 4. Comparison table

| property | **PLL `◯`** | **IEL `K`** | **forgetful-JL `□` (`LP→S4`)** |
|---|---|---|---|
| co-reflection `A→□A` | YES *(given)* | **YES** — Def 1.3 | NO — MY-INF. (S4 lacks it) |
| reflection `□A→A` | NO *(given)* | **NO** — Thm 5 | **YES** — S4/`LP` factivity |
| intuitionistic factivity `□A→¬¬A` | NO (`◯⊥` consistent) | **`IEL` YES / `IEL⁻` NO** — Def 2 | YES — MY-INF. (from `□A→A`) |
| distribution `□(A→B)→(□A→□B)` | **YES** — machine-checked `nucleus_himp_le`; repo `◯S`+functor | **YES** — Def 1.2 | **YES** — S4 normal |
| necessitation `⊢A⇒⊢□A` | YES, from `◯R` *(given)* | YES, derived — Prop 1.1 | YES, primitive |
| idempotence `□□A↔□A` | **YES** (`◯M`+unit) | **NO** — only `KA→KKA` (Prop 1.5); converse MY-INF.+ctrmodel | YES (S4 = T+4) |
| intended reading | idealised **evidential belief** | verification **knowledge**(`IEL`)/**belief**(`IEL⁻`), BHK | **provability** / "∃ proof" (S4) |

*Idempotence countermodel (MY-INFERENCE, sound by A&P Thm 2, semantics Def 3/4,
`u⊩KA ⇔ ∀v∈E(u). v⊩A`):* take `E(u)={v₀}`, `E(v₀)=∅`, `p` false everywhere; then
`v₀⊩Kp` vacuously so `u⊩KKp`, but `u⊮Kp`. Non-emptiness of `E` extends it to an
`IEL`-model. So `KKA→KA` fails.

---

## 5. Bottom line and framing options

**(a) Is PLL `◯` the same as IEL `K`?** Different, and the mapping is precise.
`◯` is *not* full `IEL`-`K` (that is intuitionistically factive: `¬K⊥`,
`KA→¬¬A` — knowledge). `◯` lines up with the **belief** system `IEL⁻`, but is
*not identical* to it either: they agree on co-reflection, distribution,
necessitation, `∧`-preservation and non-factivity, and **differ in idempotence**.

- **Sharpest fact, `◯` vs `IEL⁻` (the two belief systems):** idempotence. `◯` is a
  monad/nucleus, `◯◯A ⊣⊢ ◯A`; A&P's `K` validates only `KA→KKA` (Prop 1.5).
- **Sharpest fact, `◯` vs full `IEL` (belief vs knowledge):** `◯⊥` consistent,
  whereas `¬K⊥` is an `IEL` theorem (Thm 1.1).
- **Cleanest one-line positioning (CONJECTURE):** `PLL-◯ = IEL⁻ + idempotence
  ◯◯A→◯A`. A&P's Prop 2 already gives strength in `IEL⁻`, so the only thing `◯`
  adds over `IEL⁻` is multiplication.

**(b) Does the justification "evidence" reading fit `◯`?** Not the standard (`LP`)
one — it forces factivity `◯M→M` and lacks co-reflection. A non-factive
justification logic is required (citation to confirm).

## 6. Open questions for Matthew

1. **Handover correction (settled).** "◯ non-normal / distribution NO" is false;
   distribution holds and is machine-checked (`nucleus_himp_le`). Non-normality
   cannot be the `◯`-vs-IEL distinction; use **idempotence** (vs `IEL⁻`) and
   **factivity** (vs `IEL`).
2. **Machine-check the positioning** `PLL-◯ = IEL⁻ + (◯◯A→◯A)` (both inclusions)?
   Would give the clean one-line framing. Currently CONJECTURE.
3. **Machine-check the idempotence gap** `IEL, IEL⁻ ⊬ KKA→KA` (formalise the
   countermodel above) if you want to cite it as the sharp `◯`-vs-`K` difference.
4. **Framing choice:** position `◯` against `IEL⁻` (belief), not `IEL` (knowledge)
   — A&P's own reading of `IEL⁻` — carrying the idempotence caveat?
5. **Evidence reading:** invoke justification logic at all? If yes, a *non-factive*
   JL only, and verify a specific citation (A&P §3.3 fn 22 / Su–Sano / Lurie).
6. **Deeper link (UNVERIFIED, worth checking):** A&P's §3.3 Gödel translation reads
   `Kp` as `□V□p` in a bimodal *logic of verification* `S4V`, with `V` a lax-style
   verification modality (`□A→VA`, and `¬□V⊥` for `IEL`). Is `V` essentially PLL's
   `◯` under that translation? A potential citable bridge to A&P.

---

## References

- **[VERIFIED]** S. Artemov, T. Protopopescu, *Intuitionistic Epistemic Logic*,
  Review of Symbolic Logic **9**(2) (2016) 266–298; arXiv:1406.1582v4.
- **[VERIFIED]** S. Artemov, M. Fitting, *Justification Logic*, Stanford
  Encyclopedia of Philosophy.
- **[VERIFIED]** S. Artemov, *The Logic of Proofs*, Ann. Pure Appl. Logic (1994);
  *The Logic of Justification*, Review of Symbolic Logic **1**(4) (2008) — via SEP.
- **[UNVERIFIED]** Su & Sano; Lurie — justification counterparts of IEL (A&P
  §3.3 fn 22). Not reached; confirm before citing.
- Machine-checked support (this repo): `wip/belief_normality.lean`
  (`nucleus_himp_le`, `nucleus_top`), `wip/belief_boolean_collapse.lean`.
