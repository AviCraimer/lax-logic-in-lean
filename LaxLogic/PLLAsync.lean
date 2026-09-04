import LaxLogic.PLLTimingLookahead
import LaxLogic.PLLSearch

/-!
# Two asynchronous elements: the C-element and the arbiter

The adders of `PLLTimingRipple.lean` / `PLLTimingLookahead.lean` are
combinational: every output is a function of the inputs, and the whole content
is *when* it settles.  The two remaining circuits of the case-study list are
asynchronous, and between them they exhibit one law of the modality that
**holds** and one that **fails**.

* The **C-element** (Muller's rendezvous element) waits for *both* inputs to
  agree.  Logically it is the meet law `◯A ∧ ◯B ⊢ ◯(A ∧ B)`, which is
  derivable in PLL.  Its canonical derivation is *sequential* — two `bind`s,
  so `μ = +` charges `δa + δb` — while the element realises the same law in
  *parallel*, `σ = max`, charging `max(δa, δb) + δ_C`.  The C-element is thus
  a cheaper realisation of a derivable law, and `cElem_beats_sequential` says
  exactly when it pays: iff `δ_C < min(δa, δb)`.

* The **arbiter** grants one of two competing requests.  It believes that
  *some* grant occurs, `◯(g₁ ∨ g₂)`, without believing of either grant that it
  occurs: under contention nothing in the inputs determines which way the
  resolution falls.  That is precisely the failure of `◯`-distribution over
  `∨`, and it is refuted here by a three-world model read as the arbiter
  itself (`arbiter_no_distribution`).  The reason is structural: mutual
  exclusion means the two grant-futures never reconverge, so the frame is not
  mutually confluent (`arbiter_not_confluent`) --- and by
  `PLLConfluentComplete.derivU_iff_confluent_valid`, mutually confluent frames
  are *exactly* the models of PLL + the distribution scheme.  Mutual exclusion
  is the circuit-level reason the scheme fails.

So `∧` is the rendezvous and `∨` is the arbitration: the modality distributes
over the first and not over the second, and each has a circuit that says why.

## Provenance (tools vs proofs)

Both facts were **found** with `PLLND.Search.decide` (`PLLSearch.lean`), the
efficient searcher, not with the verified decision procedure, whose fuel bounds
make it unusable for search.  Search is untrusted; what is kept is its
certificate.  The `#guard` lines below re-run the search at compile time, and
the theorems stand on kernel-checked artefacts: a transcribed proof term for
the C-element, and for the arbiter a pinned finite model discharged through the
verified checker (`FinCM.not_provable_of_check`, `by decide`).  A wrong search
could only have failed to find these; it could not have produced them.
-/

open PLLFormula

namespace PLLND
namespace Async

/-! ## 1. The C-element: rendezvous, and the meet law -/

abbrev pa : PLLFormula := prop "a"
abbrev pb : PLLFormula := prop "b"

/-- Input `a` settled. -/
abbrev Sa := somehow pa
/-- Input `b` settled. -/
abbrev Sb := somehow pb
/-- Both inputs settled --- the C-element's conclusion. -/
abbrev Sab := somehow (pa.and pb)
/-- The C-element's output node. -/
abbrev Sc := somehow (prop "c")

/-- **The meet law as a proof term**: `◯a, ◯b ⊢ ◯(a ∧ b)`.  Run the belief in
`a`, then under its constraint run the belief in `b`, then return the pair.
Two `bind`s and a `val` --- the derivation is sequential. -/
def cElemTm : Tm [Sa, Sb] Sab :=
  .bind (.var .here)
    (.bind (.var (.there (.there .here)))
      (.val (.pair (.var (.there .here)) (.var .here))))

/-- Curry–Howard certificate: the rendezvous law is a genuine PLL derivation. -/
example : Nonempty (LaxND [Sa, Sb] Sab) := ⟨cElemTm.toND⟩

-- The searcher agrees, at compile time: the meet law is provable.
#guard (match Search.decide {} [Sa, Sb] Sab with | .proved _ => true | _ => false)

-- and so is its converse, `◯(a ∧ b) ⊢ ◯a ∧ ◯b` --- `◯` distributes over `∧`.
#guard (match Search.decide {} [Sab] (Sa.and Sb) with | .proved _ => true | _ => false)

/-- The rendezvous environment: inputs settled at `δa` and `δb`. -/
def envMeet (δa δb : ℕ) : Env (M := ℕ) B [Sa, Sb] :=
  ((δa, ()), ((δb, ()), PUnit.unit))

/-- **The derivation is sequential**: the canonical proof of the meet law pays
`μ = +` at each `bind`, so it extracts `δa + δb` --- believe `a`, *then*
believe `b`. -/
theorem cElem_sequential (δa δb : ℕ) :
    (cElemTm.eval (· + ·) 0 B (envMeet δa δb)).1 = δa + δb := rfl

/-! ### The element itself: the same law, in parallel

As a piece of hardware the C-element is a two-input cell, so its denotation
carries `σ = max`: it waits for the later input and adds its own delay. -/

/-- The one-gate netlist `[C : ◯a ⊃ ◯b ⊃ ◯c, ◯a, ◯b]`. -/
abbrev Γc : List PLLFormula := [Sa.ifThen (Sb.ifThen Sc), Sa, Sb]

/-- The C-element applied to its two inputs: `Γc ⊢ ◯c`. -/
def cGateTm : Tm Γc Sc :=
  .app (.app (.var .here) (.var (.there .here))) (.var (.there (.there .here)))

example : Nonempty (LaxND Γc Sc) := ⟨cGateTm.toND⟩

/-- The gate environment: a C-element of delay `δC`, inputs settled at `δa`,
`δb`. -/
def envC (δC δa δb : ℕ) : Env (M := ℕ) B Γc :=
  (gate2 δC, ((δa, ()), ((δb, ()), PUnit.unit)))

/-- **The element is parallel**: `max(δa, δb) + δ_C` --- it waits for the later
input, not for one input after the other. -/
theorem cElem_parallel (δC δa δb : ℕ) :
    (cGateTm.eval (· + ·) 0 B (envC δC δa δb)).1 = max δa δb + δC := rfl

/-- **When the rendezvous pays.**  The C-element realisation beats the
sequential derivation exactly when the element's own delay is below the
*faster* input's settling time.  (With `δ_C = 0` it is never worse, since
`max x y ≤ x + y`.) -/
theorem cElem_beats_sequential (δC δa δb : ℕ) :
    max δa δb + δC < δa + δb ↔ δC < min δa δb := by omega

/-- Nominal C-element delay (ps), of the same order as the other cells. -/
def dC : ℕ := 90

/-- With both inputs settling at `200 ps`, the rendezvous costs `290 ps` where
the sequential derivation would charge `400 ps`. -/
example : (cGateTm.eval (· + ·) 0 B (envC dC 200 200)).1 = 290 := by decide

example : (cElemTm.eval (· + ·) 0 B (envMeet 200 200)).1 = 400 := by decide

/-! ## 2. The arbiter: choice, and the failure of `∨`-distribution -/

abbrev g1 : PLLFormula := prop "g1"
abbrev g2 : PLLFormula := prop "g2"

/-- "Some grant is issued." -/
abbrev Ogrant := somehow (g1.or g2)
/-- "Grant 1 is issued, or grant 2 is issued." -/
abbrev OgOrOg := (somehow g1).or (somehow g2)

/-- **The arbiter as a finite constraint model.**  World `0` is *contention*:
both requests are up and the arbiter has not resolved.  Worlds `1` and `2` are
the two resolutions, granting `g₁` and `g₂` respectively.  They are
`Rᵢ`-incomparable and neither is `Rₘ`-reachable from the other: **mutual
exclusion is exactly the absence of a reconvergent world**.  (This is the
split model of \[F&M 1997, Fig. 3\], read as a circuit.) -/
def arbiterM : FinCM :=
  { n := 3
    ri := [(0,0),(0,1),(0,2),(1,1),(2,2)]
    rm := [(0,0),(0,1),(0,2),(1,1),(2,2)]
    fall := []
    val := [(1, "g1"), (2, "g2")] }

-- The searcher refutes `∨`-distribution at compile time.
#guard (match Search.decide {} [Ogrant] OgOrOg with | .refuted _ _ _ => true | _ => false)

-- It stays refuted with mutual exclusion added as a premise: the failure is
-- not an artefact of allowing both grants at once.
#guard (match Search.decide {} [Ogrant, (g1.and g2).ifThen .falsePLL] OgOrOg with
        | .refuted _ _ _ => true | _ => false)

/-- **Under contention some grant is believed.** -/
theorem arbiter_believes_grant : FinCM.forceB arbiterM 0 Ogrant = true := by decide

/-- **But neither grant is believed.**  No constraint discharges to `g₁` along
every future --- the `g₂`-resolution is a future in which it never does. -/
theorem arbiter_denies_g1 : FinCM.forceB arbiterM 0 (somehow g1) = false := by decide

theorem arbiter_denies_g2 : FinCM.forceB arbiterM 0 (somehow g2) = false := by decide

/-- **The arbiter refutes `◯`-distribution over `∨`**, through the verified
checker: believing that *a* grant occurs does not amount to believing, of some
particular grant, that it occurs. -/
theorem arbiter_no_distribution : ¬ Nonempty (LaxND [Ogrant] OgOrOg) :=
  FinCM.not_provable_of_check (M := arbiterM) (w := 0) (by decide)

/-! ### Why: mutual exclusion is non-confluence -/

/-- Mutual confluence as a decidable check on a finite model, mirroring
`PLLFrames.MutuallyConfluent`: from `x`, an `Rₘ`-step to `w` and an `Rᵢ`-step
to `v` must close at some `u` with `w Rᵢ u` and `v Rₘ u`. -/
def mutConfluentB (M : FinCM) : Bool :=
  (List.range M.n).all fun x => (List.range M.n).all fun w =>
    (List.range M.n).all fun v =>
      !(M.rmB x w && M.riB x v) ||
        (List.range M.n).any fun u => M.riB w u && M.rmB v u

/-- Sanity: the one-point model is mutually confluent. -/
example : mutConfluentB ⟨1, [(0,0)], [(0,0)], [], []⟩ = true := by decide

/-- **The arbiter frame is not mutually confluent.**  From contention, the
`Rₘ`-step granting `g₁` and the `Rᵢ`-step to the `g₂`-resolution have no common
future: that is mutual exclusion.  Since mutually confluent frames are exactly
the models of PLL + the distribution scheme
(`PLLND.ConfluentU.derivU_iff_confluent_valid`), this non-confluence *is* the
reason `arbiter_no_distribution` holds. -/
theorem arbiter_not_confluent : mutConfluentB arbiterM = false := by decide

/-! ## Axiom audits — measured and pinned on creation (2026-07-20)

The two extractions are `rfl`, hence axiom-free.  Everything on the arbiter
side --- the forcing facts, the refutation, and the non-confluence --- is
`decide` over finite data and comes out **choice-free** `[propext, Quot.sound]`,
the same tier as the other pinned countermodel certificates.  Only the
`min`/`max` arithmetic of `cElem_beats_sequential` reaches clean-classical. -/

/-- info: 'PLLND.Async.cElem_sequential' does not depend on any axioms -/
#guard_msgs in
#print axioms cElem_sequential

/-- info: 'PLLND.Async.cElem_parallel' does not depend on any axioms -/
#guard_msgs in
#print axioms cElem_parallel

/--
info: 'PLLND.Async.cElem_beats_sequential' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cElem_beats_sequential

/-- info: 'PLLND.Async.arbiter_believes_grant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arbiter_believes_grant

/-- info: 'PLLND.Async.arbiter_no_distribution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arbiter_no_distribution

/-- info: 'PLLND.Async.arbiter_not_confluent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms arbiter_not_confluent

end Async
end PLLND
