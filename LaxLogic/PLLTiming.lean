import LaxLogic.PLLConstraints

/-!
# Proofs-as-delays: the `(ℕ, 0, +, max)` timing algebra and Mendler's `CIRC`

This file executes Phase 2 of the timing constraint-extraction programme
(see `wip/timing-extraction-proposal.md`).  It upgrades the *single*-operation
extractor of `PLLConstraints.lean` to the **two**-operation delay algebra that
Mendler's "proofs-as-delays" reading demands, and reproduces the canonical
example — `CIRC` of *Timing Analysis of Combinational Circuits in
Intuitionistic Propositional Logic* (Mendler, **FMSD 17(1):5–37, 2000**), §7 —
with its reconvergent-fanout / false-path punchline.

## The two operations (the design step)

Mendler evaluates an `LJ`/PLL proof in the strong monad `T A = ℕ × A` with

* unit         `η a       = (0, a)`         — a wire, delay `0`   (`◯R`);
* multiplication `μ (n₁,n₂,a) = (n₁+n₂, a)` — **sequential** composition, `+` (`◯M`);
* tensorial strength `σ = max`              — **parallel** merge / reconvergence (`◯S`).

"Both `+` and `max` [are] essential."  The existing extractor
(`PLLConstraints.Tm.eval`) is *parametric* in one binary `op`, instantiated as
`+` **or** `max`.  A series chain only ever needs one of them, so the toy
there is degenerate.  A **reconvergent** circuit needs both **in the same
evaluation**.  The least-invasive resolution (proposal §4) — and the one taken
here — is:

* keep `op = (· + ·)`, `e = 0` for the object-level `bind`  (this *is* `μ`);
* put the `max` inside the **multi-input gate denotations** (this *is* `σ`):
  a `k`-input gate emits `max (ready-times of inputs) + δ_gate`.

Nothing in `PLLConstraints.lean` is modified: we import it and instantiate
`Tm.eval` at `(ℕ, +, 0)`, supplying gate denotations that carry the `max`.
The `Prop`/`Type` Curry–Howard bridge `Tm.toND` certifies every proof term
below is a genuine PLL derivation.

## `CIRC` (Mendler FMSD 2000, §7)

`c = (a ∨ b) ∧ ¬b`, built from three gates

* `OR (a, b) = d`   `INV (b) = e`   `AND (d, e) = c`

with `b` fanning out to `OR` and `INV` and **reconverging** at `AND`.  The
rising stabilisation bound is `δ_CIRC↑ = max(δ_OR, δ_INV) + δ_AND` — genuinely
a `max`, unlike the series toy.  The punchline (below): on the input class that
holds `a = 1`, the `OR → AND` path is **not sensitisable** (`d = a ∨ b = 1` is
stable), so the proof for that class never traverses `OR`, and the extracted
bound `δ_INV + δ_AND` is **strictly below** the topological longest path
`max(δ_OR, δ_INV) + δ_AND`.  A proof only traverses real logical dependencies,
so a non-sensitisable path is absent from its constraint set *for free*.
-/

open PLLFormula

namespace PLLND

/-! ## The timing monad `T A = ℕ × A` over the algebra `(ℕ, 0, +, max)`

We run `Tm.eval` at `op = (· + ·)` (Mendler's `μ`) and `e = 0` (his `η`).
The realiser layer is trivial (`base = fun _ => Unit`): we track *only* the
stabilisation bound `ℕ`, which is exactly what constraint extraction is for.
`sem (◯φ) = ℕ × sem φ`, so a `◯`-signal is a delay paired with its (trivial)
realiser. -/

/-- Trivial realiser layer: we track delays, not values (`T A = ℕ × A` with
`A` collapsed to `Unit`). -/
abbrev B : String → Type := fun _ => Unit

/-- The delay-carrying denotation of a **1-input** gate with delay `δ`:
output ready-time is `input + δ`.  (A `◯`-consuming generalisation of
`PLLConstraints.gate`, which consumes an *unlifted* input.) -/
def gate1 {x y : String} (δ : ℕ) :
    sem (M := ℕ) B ((somehow (prop x)).ifThen (somehow (prop y))) :=
  fun p => (p.1 + δ, ())

/-- The delay-carrying denotation of a **2-input** gate with delay `δ`:
output ready-time is `max (inputs) + δ`.  **This is where `σ = max` lives** —
the reconvergent merge the single-`op` toy could not express. -/
def gate2 {x y z : String} (δ : ℕ) :
    sem (M := ℕ) B
      ((somehow (prop x)).ifThen ((somehow (prop y)).ifThen (somehow (prop z)))) :=
  fun p q => (max p.1 q.1 + δ, ())

/-! ## `CIRC` natively in `Tm`

Signal atoms `a b c d e`; `◯x = somehow (prop x)` is the ready-time of `x`.
Gate hypotheses (proposal §3):

* `gOR  : ◯a ⊃ ◯b ⊃ ◯d`   `gINV : ◯b ⊃ ◯e`   `gAND : ◯d ⊃ ◯e ⊃ ◯c`

and we derive `◯a ⊃ ◯b ⊃ ◯c` — "given the inputs' ready-times, the output is
ready (under the extracted delay constraint)". -/

abbrev Oa := somehow (prop "a")
abbrev Ob := somehow (prop "b")
abbrev Oc := somehow (prop "c")
abbrev Od := somehow (prop "d")
abbrev Oe := somehow (prop "e")

/-- The gate netlist as a context `Γ = [gOR, gINV, gAND]`. -/
abbrev ΓCIRC : List PLLFormula :=
  [Oa.ifThen (Ob.ifThen Od), Ob.ifThen Oe, Od.ifThen (Oe.ifThen Oc)]

/-- **`CIRC↑` as a `Tm` proof term**: `Γ ⊢ ◯a ⊃ ◯b ⊃ ◯c`, i.e.
`gAND (gOR a b) (gINV b)`.  `b` fans out to `gOR` and `gINV` and reconverges
at `gAND`. -/
def circUp : Tm ΓCIRC (Oa.ifThen (Ob.ifThen Oc)) :=
  -- after the two `lam`s the context is `[◯b, ◯a, gOR, gINV, gAND]`
  .lam (.lam
    (.app
      (.app (.var (.there (.there (.there (.there .here)))))        -- gAND
        (.app (.app (.var (.there (.there .here)))                  -- gOR
                    (.var (.there .here)))                          --   applied to ◯a
              (.var .here)))                                        --   and ◯b   ↦ ◯d
      (.app (.var (.there (.there (.there .here))))                 -- gINV
            (.var .here))))                                         --   applied to ◯b ↦ ◯e

/-- Curry–Howard certificate: `circUp` really is a PLL derivation. -/
example : Nonempty (LaxND ΓCIRC (Oa.ifThen (Ob.ifThen Oc))) := ⟨circUp.toND⟩

/-- The gate environment for `CIRC`, parametric in the three gate delays. -/
def envCIRC (δOR δINV δAND : ℕ) : Env (M := ℕ) B ΓCIRC :=
  (gate2 δOR, (gate1 δINV, (gate2 δAND, PUnit.unit)))

/-! ### Extraction

Evaluating the proof term at `(ℕ, +, 0)` with the `max`-carrying gate
denotations *computes* the stabilisation bound.  We keep the gate delays and
the input ready-times symbolic; the raw output is the composite delay **by
`rfl`** — the kernel reads the constraint straight off the proof term. -/

/-- **Raw symbolic extraction, by `rfl`.**  With inputs `a, b` ready at times
`δa, δb`, `CIRC↑` extracts the composite delay
`max (max δa δb + δ_OR) (δb + δ_INV) + δ_AND` — Mendler's symbolic delay
*table* `T_OR, T_INV, T_AND` composed, computed by the kernel from the proof
term. -/
theorem circUp_extract (δOR δINV δAND δa δb : ℕ) :
    (circUp.eval (· + ·) 0 B (envCIRC δOR δINV δAND) (δa, ()) (δb, ())).1
      = max (max δa δb + δOR) (δb + δINV) + δAND := rfl

/-- **The rising bound.**  With inputs available at time `0`, the extracted
bound is exactly Mendler's `δ_CIRC↑ = max(δ_OR, δ_INV) + δ_AND` — genuinely a
`max` over the two reconvergent branches. -/
theorem circUp_rising (δOR δINV δAND : ℕ) :
    (circUp.eval (· + ·) 0 B (envCIRC δOR δINV δAND) (0, ()) (0, ())).1
      = max δOR δINV + δAND := by
  show max (max 0 0 + δOR) (0 + δINV) + δAND = max δOR δINV + δAND
  omega

/-- Concrete evaluation at a nominal sky130 operating point (numbers justified
at `dOR/dINV/dAND` below): the rising bound is `210 ps`. -/
example : (circUp.eval (· + ·) 0 B (envCIRC 120 40 90) (0, ()) (0, ())).1 = 210 := by
  decide

/-! ## Both operations in one evaluation: `+` on `bind`, `max` in a gate

The extraction above already contains both `+` (each gate's own delay) and
`max` (each 2-input gate's merge) in a single `rfl`.  To exhibit the
**object-level `bind`** paying `μ = +` *on top of* a gate's `σ = max` — the
exact split the proposal names — here is a 2-input gate feeding a buffer via
`bind`.  The buffer is `PLLConstraints.gate` (an *unlifted*-input germ), so the
sequential composition genuinely routes through `bind`. -/

abbrev Ow := somehow (prop "w")

/-- `Γ = [g : ◯x ⊃ ◯y ⊃ ◯z, buf : z ⊃ ◯w] ⊢ ◯x ⊃ ◯y ⊃ ◯w`, i.e.
`λ x y. bind (g x y) (λ z. buf z)`.  The `bind` is Mendler's `μ`. -/
def gateThenBuf : Tm [Od.ifThen (Oe.ifThen Oc), (prop "c").ifThen Ow]
    (Od.ifThen (Oe.ifThen Ow)) :=
  -- after two `lam`s: `[◯e, ◯d, g, buf]`; under the `bind` binder prepend `c`
  .lam (.lam
    (.bind
      (.app (.app (.var (.there (.there .here)))   -- g
                  (.var (.there .here)))           --   ◯d
            (.var .here))                          --   ◯e   ↦ ◯c
      (.app (.var (.there (.there (.there (.there .here)))))  -- buf (shifted under bind)
            (.var .here))))                         --   applied to c ↦ ◯w

/-- **`μ = +` on `bind`, `σ = max` in the gate, one evaluation.**  The gate
emits `max δd δe + δ_G` (its `σ` then its own delay); the `bind` then adds the
buffer's `δ_BUF` — the outer `+` is the object-level monad multiplication. -/
theorem gateThenBuf_extract (δG δBUF δd δe : ℕ) :
    (gateThenBuf.eval (· + ·) 0 B
        (gate2 δG, (gate δBUF (fun _ => ()), PUnit.unit)) (δd, ()) (δe, ())).1
      = max δd δe + δG + δBUF := rfl

/-! ## The false-path punchline (in miniature)

`c = (a ∨ b) ∧ ¬b` classically equals `a ∧ ¬b`.  On the **input class `a = 1`**
the `OR` output `d = a ∨ b = 1` is *stable* — independent of any transition on
`b` — so `◯d` is available immediately and the `OR → AND` path carries no
fresh delay.  The correct per-class proof therefore takes `◯d` as a hypothesis
and **never mentions `gOR`**: the reconvergent `OR` branch is literally absent
from the derivation, hence from its constraint set.

This is Mendler's per-transition/per-input observation (FMSD §7; F&M eqs.
15–16): the bound "may be smaller than the topological delay, i.e. the longest
path." -/

/-- The `a = 1` netlist: `◯d` is *given* (stable, since `a = 1`), so `gOR` is
gone.  `Γ = [gINV, gAND, ◯d, ◯b]`. -/
abbrev Γa1 : List PLLFormula :=
  [Ob.ifThen Oe, Od.ifThen (Oe.ifThen Oc), Od, Ob]

/-- **`CIRC↑` on the `a = 1` class**: `Γ ⊢ ◯c`, i.e. `gAND d (gINV b)`.
Note the total absence of `gOR` — the false path is not in the term. -/
def circUp_a1 : Tm Γa1 Oc :=
  -- context `[gINV, gAND, ◯d, ◯b]`
  .app
    (.app (.var (.there .here))                 -- gAND
          (.var (.there (.there .here))))       --   ◯d  (given: a = 1 pins it)
    (.app (.var .here)                          -- gINV
          (.var (.there (.there (.there .here)))))  --   ◯b   ↦ ◯e

/-- Certificate that the `a = 1` case is a genuine PLL derivation. -/
example : Nonempty (LaxND Γa1 Oc) := ⟨circUp_a1.toND⟩

/-- The `a = 1` environment (no `gOR`). -/
def envA1 (δINV δAND δd δb : ℕ) : Env (M := ℕ) B Γa1 :=
  (gate1 δINV, (gate2 δAND, ((δd, ()), ((δb, ()), PUnit.unit))))

/-- **Raw extraction on the `a = 1` class, by `rfl`**: `max δd (δb + δ_INV) +
δ_AND`.  Only the `INV → AND` branch contributes a fresh delay; `δd` enters
merely as an already-stable input. -/
theorem circUp_a1_extract (δINV δAND δd δb : ℕ) :
    (circUp_a1.eval (· + ·) 0 B (envA1 δINV δAND δd δb)).1
      = max δd (δb + δINV) + δAND := rfl

/-- With `d` already stable (ready `0`) and `b` ready `0`, the `a = 1` bound is
`δ_INV + δ_AND` — a single reconvergent branch. -/
theorem circUp_a1_bound (δINV δAND : ℕ) :
    (circUp_a1.eval (· + ·) 0 B (envA1 δINV δAND 0 0)).1 = δINV + δAND := by
  show max 0 (0 + δINV) + δAND = δINV + δAND
  omega

/-! ### Concrete numbers — nominal sky130 (`sky130_fd_sc_hd`) operating point

Illustrative single scalars per gate/transition (proposal §5: sky130 Liberty
NLDM tables are 2-D in load/slew; we pin a nominal corner — typical process,
nominal `1.8 V`, `25 °C` — and read one representative rising propagation
delay per cell).  Values in picoseconds, rounded, on the order the PDK reports
(tens–low-hundreds of ps):

* `dINV = 40`   — `sky130_fd_sc_hd__inv_1`   (≈ 0.03–0.05 ns)
* `dOR  = 120`  — `sky130_fd_sc_hd__or2_1`   (OR2 = NOR+INV internally, slower)
* `dAND = 90`   — `sky130_fd_sc_hd__and2_1`  (AND2 = NAND+INV)

These are *illustrative, not sign-off STA* (proposal §5): the contribution is
the extraction mechanism and the false-path observation, kernel-checked. -/

/-- `sky130_fd_sc_hd__inv_1` nominal rising delay (ps). -/
def dINV : ℕ := 40
/-- `sky130_fd_sc_hd__or2_1` nominal rising delay (ps). -/
def dOR : ℕ := 120
/-- `sky130_fd_sc_hd__and2_1` nominal rising delay (ps). -/
def dAND : ℕ := 90

/-- **The topological longest path** (structural, sensitisation-blind): the
longest input→`c` path is through `OR` or `INV`, both terminating at `AND`, so
`δ_topo = max(δ_OR, δ_INV) + δ_AND`.  This is what naive STA reports; it equals
the *full* `CIRC↑` bound (`circUp_rising`). -/
def dTopo : ℕ := max dOR dINV + dAND

/-- The topological longest path is `210 ps`. -/
example : dTopo = 210 := by decide

/-- The `a = 1` data-dependent bound is `130 ps`. -/
example : (circUp_a1.eval (· + ·) 0 B (envA1 dINV dAND 0 0)).1 = 130 := by decide

/-- **The false-path punchline, kernel-checked.**  The delay extracted from
the `a = 1` proof (`130 ps`, `= δ_INV + δ_AND`) is **strictly below** the
topological longest path (`210 ps`, `= max(δ_OR, δ_INV) + δ_AND`): the
non-sensitisable `OR → AND` path is absent from the proof's constraint set, so
extraction beats topological STA by recognising the false path — *for free*. -/
theorem falsePath_beats_topological :
    (circUp_a1.eval (· + ·) 0 B (envA1 dINV dAND 0 0)).1 < dTopo := by decide

/-- The gap is exactly the sensitisation saving `δ_OR - δ_INV = 80 ps`. -/
example : dTopo - (circUp_a1.eval (· + ·) 0 B (envA1 dINV dAND 0 0)).1 = 80 := by decide

/-! ## Axiom audits (repo discipline: `#guard_msgs` + `#print axioms`)

The extraction theorems are `rfl`/`decide`/`omega`; none appeals to
classical choice.  `decide`/`rfl` results are axiom-free; `omega` introduces
only propositional extensionality.  Pinned below. -/

/-- info: 'PLLND.circUp_extract' does not depend on any axioms -/
#guard_msgs in
#print axioms circUp_extract

/-- info: 'PLLND.circUp_a1_extract' does not depend on any axioms -/
#guard_msgs in
#print axioms circUp_a1_extract

/-- info: 'PLLND.falsePath_beats_topological' does not depend on any axioms -/
#guard_msgs in
#print axioms falsePath_beats_topological

/-- info: 'PLLND.circUp_rising' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms circUp_rising

end PLLND
