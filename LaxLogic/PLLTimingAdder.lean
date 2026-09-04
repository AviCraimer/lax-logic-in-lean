import LaxLogic.PLLTiming

/-!
# The carry-skip adder slice: the false path at "tens of gates"

Phase 2, deliverable 2 (see `wip/timing-extraction-proposal.md`, candidate B).
The 2–4-bit **carry-skip (carry-bypass) adder** is *the* textbook false-path
example: its longest **topological** carry path — ripple through a block **and**
then take the skip multiplexer — is **never sensitisable**, so topological STA
over-estimates the true critical delay.  We reproduce this with the same
`(ℕ, 0, +, max)` extractor as `PLLTiming.lean`.

## Why the ripple-and-skip path is false

A `k`-bit block with block-propagate `P = p₀ ∧ … ∧ p_{k-1}` and a skip mux
`cout = P ? cin : cripple`:

* for `cin` to ripple all the way to `cripple`, **every** bit must propagate,
  i.e. `P = 1`;
* but if `P = 1` the mux selects the **bypass** `cin`, *not* `cripple`.

So the path `cin → ripple → cripple → mux → cout` needs `P = 1` **and** `P = 0`
simultaneously — a contradiction.  It is a **false path**.  The true critical
carry delay is the max of the *sensitisable* paths, dominated by the short
`cin → mux` bypass and the `P`-tree, never the full ripple.

## What is mechanised

Two `Tm` proof terms over an explicit 4-bit netlist, both extracting bounds by
`rfl`/`omega`, plus the strict inequality by `decide`:

* `rippleTm`   — the ripple sub-chain `◯cin ⊃ … ⊢ ◯c₄`, extracting the long
  ripple bound `4·δ_carry` (the sub-path the false path rides on);
* `coutSkip`   — the correct **all-propagate (`P = 1`) skip** derivation
  `⊢ ◯cout`, extracting `2·δ_and + δ_mux` — it routes `cin` through the mux
  bypass and **never touches the ripple chain**, so the false path is absent by
  construction;
* `skip_beats_topological` — `2·δ_and + δ_mux  <  4·δ_carry + δ_mux`
  (`280 < 580 ps`) on nominal sky130 numbers, by `decide`.
-/

open PLLFormula

namespace PLLND

/-! ## Netlist atoms (`◯x = ready-time of signal x`) -/

abbrev Ocin  := somehow (prop "cin")
abbrev Oc1   := somehow (prop "c1")
abbrev Oc2   := somehow (prop "c2")
abbrev Oc3   := somehow (prop "c3")
abbrev Oc4   := somehow (prop "c4")     -- = cripple (block ripple output)
abbrev Op0   := somehow (prop "p0")
abbrev Op1   := somehow (prop "p1")
abbrev Op2   := somehow (prop "p2")
abbrev Op3   := somehow (prop "p3")
abbrev Oq0   := somehow (prop "q0")     -- p0 ∧ p1
abbrev Oq1   := somehow (prop "q1")     -- p2 ∧ p3
abbrev Opp   := somehow (prop "pp")     -- P = block propagate = q0 ∧ q1
abbrev Ocout := somehow (prop "cout")

/-! ## The ripple sub-chain `⊢ ◯c₄`

Four ripple-carry stages `csᵢ : ◯cᵢ ⊃ ◯pᵢ ⊃ ◯cᵢ₊₁`, each a 2-input gate
paying `max(inputs) + δ_carry`.  The chain is pure application over a flat
context — no binder, so no de Bruijn shifting. -/

abbrev Γripple : List PLLFormula :=
  [ Ocin.ifThen (Op0.ifThen Oc1),      -- cs0
    Oc1.ifThen  (Op1.ifThen Oc2),      -- cs1
    Oc2.ifThen  (Op2.ifThen Oc3),      -- cs2
    Oc3.ifThen  (Op3.ifThen Oc4),      -- cs3
    Ocin, Op0, Op1, Op2, Op3 ]

/-- `cin` rippled through the 4-stage carry chain: `Γ ⊢ ◯c₄`. -/
def rippleTm : Tm Γripple Oc4 :=
  let cs0 : Tm Γripple _ := .var .here
  let cs1 : Tm Γripple _ := .var (.there .here)
  let cs2 : Tm Γripple _ := .var (.there (.there .here))
  let cs3 : Tm Γripple _ := .var (.there (.there (.there .here)))
  let cin : Tm Γripple _ := .var (.there (.there (.there (.there .here))))
  let p0  : Tm Γripple _ := .var (.there (.there (.there (.there (.there .here)))))
  let p1  : Tm Γripple _ := .var (.there (.there (.there (.there (.there (.there .here))))))
  let p2  : Tm Γripple _ := .var (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let p3  : Tm Γripple _ := .var (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let c1 := Tm.app (.app cs0 cin) p0
  let c2 := Tm.app (.app cs1 c1) p1
  let c3 := Tm.app (.app cs2 c2) p2
  Tm.app (.app cs3 c3) p3

/-- Curry–Howard certificate for the ripple chain. -/
example : Nonempty (LaxND Γripple Oc4) := ⟨rippleTm.toND⟩

/-- The ripple environment: four carry gates (delay `δc`) and the inputs
(`cin` and the `pᵢ`) ready at their given times. -/
def envRipple (δc : ℕ) (tcin tp0 tp1 tp2 tp3 : ℕ) : Env (M := ℕ) B Γripple :=
  (gate2 δc, (gate2 δc, (gate2 δc, (gate2 δc,
    ((tcin, ()), ((tp0, ()), ((tp1, ()), ((tp2, ()), ((tp3, ()), PUnit.unit)))))))))

/-- **Raw ripple extraction, by `rfl`**: the fully-associated `max`/`+` chain. -/
theorem ripple_extract (δc tcin tp0 tp1 tp2 tp3 : ℕ) :
    (rippleTm.eval (· + ·) 0 B (envRipple δc tcin tp0 tp1 tp2 tp3)).1
      = max (max (max (max tcin tp0 + δc) tp1 + δc) tp2 + δc) tp3 + δc := rfl

/-- **The ripple bound.**  With `cin` and every `pᵢ` ready at `0`, the block
ripple output `c₄` is ready at `4·δ_carry` — the long sub-path the false path
rides on. -/
theorem ripple_bound (δc : ℕ) :
    (rippleTm.eval (· + ·) 0 B (envRipple δc 0 0 0 0 0)).1 = 4 * δc := by
  show max (max (max (max 0 0 + δc) 0 + δc) 0 + δc) 0 + δc = 4 * δc
  omega

/-! ## The all-propagate (`P = 1`) skip derivation `⊢ ◯cout`

Block-propagate `P = (p₀ ∧ p₁) ∧ (p₂ ∧ p₃)` via a balanced AND-tree, then the
skip mux `muxSkip : ◯cin ⊃ ◯P ⊃ ◯cout`.  In the `P = 1` class the mux bypasses
the ripple entirely (`cout = cin`), so **`rippleTm`'s chain never appears in
this derivation** — the false path is gone by construction. -/

abbrev Γskip : List PLLFormula :=
  [ Op0.ifThen (Op1.ifThen Oq0),        -- a01 : p0 ∧ p1
    Op2.ifThen (Op3.ifThen Oq1),        -- a23 : p2 ∧ p3
    Oq0.ifThen (Oq1.ifThen Opp),        -- aP  : P = q0 ∧ q1
    Ocin.ifThen (Opp.ifThen Ocout),     -- muxSkip : P ? cin : _
    Ocin, Op0, Op1, Op2, Op3 ]

/-- The skip carry-out `Γ ⊢ ◯cout`: `muxSkip cin (aP (a01 p0 p1) (a23 p2 p3))`.
The ripple carries `c₁ … c₄` are absent — the bypass path only. -/
def coutSkip : Tm Γskip Ocout :=
  let a01 : Tm Γskip _ := .var .here
  let a23 : Tm Γskip _ := .var (.there .here)
  let aP  : Tm Γskip _ := .var (.there (.there .here))
  let mux : Tm Γskip _ := .var (.there (.there (.there .here)))
  let cin : Tm Γskip _ := .var (.there (.there (.there (.there .here))))
  let p0  : Tm Γskip _ := .var (.there (.there (.there (.there (.there .here)))))
  let p1  : Tm Γskip _ := .var (.there (.there (.there (.there (.there (.there .here))))))
  let p2  : Tm Γskip _ := .var (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let p3  : Tm Γskip _ := .var (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let q0 := Tm.app (.app a01 p0) p1
  let q1 := Tm.app (.app a23 p2) p3
  let pp := Tm.app (.app aP q0) q1
  Tm.app (.app mux cin) pp

/-- Curry–Howard certificate for the skip derivation. -/
example : Nonempty (LaxND Γskip Ocout) := ⟨coutSkip.toND⟩

/-- The skip environment: three AND gates (delay `δa`), the mux (delay `δm`),
and inputs ready at their given times. -/
def envSkip (δa δm : ℕ) (tcin tp0 tp1 tp2 tp3 : ℕ) : Env (M := ℕ) B Γskip :=
  (gate2 δa, (gate2 δa, (gate2 δa, (gate2 δm,
    ((tcin, ()), ((tp0, ()), ((tp1, ()), ((tp2, ()), ((tp3, ()), PUnit.unit)))))))))

/-- **Raw skip extraction, by `rfl`**: the mux merges `cin` with the
`P`-tree's output. -/
theorem coutSkip_extract (δa δm tcin tp0 tp1 tp2 tp3 : ℕ) :
    (coutSkip.eval (· + ·) 0 B (envSkip δa δm tcin tp0 tp1 tp2 tp3)).1
      = max tcin (max (max tp0 tp1 + δa) (max tp2 tp3 + δa) + δa) + δm := rfl

/-- **The skip bound.**  With `cin` and every `pᵢ` ready at `0`, the
all-propagate carry-out is ready at `2·δ_and + δ_mux` — the balanced `P`-tree
(`2·δ_and`) followed by the mux.  No ripple term. -/
theorem coutSkip_bound (δa δm : ℕ) :
    (coutSkip.eval (· + ·) 0 B (envSkip δa δm 0 0 0 0 0)).1 = 2 * δa + δm := by
  show max 0 (max (max 0 0 + δa) (max 0 0 + δa) + δa) + δm = 2 * δa + δm
  omega

/-! ### Concrete numbers — nominal sky130 (`sky130_fd_sc_hd`)

Illustrative single scalars at a nominal corner (proposal §5; same discipline
and caveats as `PLLTiming.lean`).  Values in picoseconds:

* `dAND   = 90`   — `sky130_fd_sc_hd__and2_1`  (reused from `PLLTiming`)
* `dCARRY = 120`  — full-adder carry (`sky130_fd_sc_hd__maj3_1` / `a2bb2o`-class)
* `dMUX   = 100`  — `sky130_fd_sc_hd__mux2_1`  (skip multiplexer)
-/

/-- Full-adder carry-stage nominal delay (ps). -/
def dCARRY : ℕ := 120
/-- `sky130_fd_sc_hd__mux2_1` nominal delay (ps). -/
def dMUX : ℕ := 100

/-- **The topological longest path** to `cout` (structural,
sensitisation-blind): `cin → ripple(4 stages) → cripple → mux`, i.e.
`4·δ_carry + δ_mux`.  This is the classic false path (ripple **and** skip),
and it is what naive topological STA reports. -/
def dTopoAdder : ℕ := 4 * dCARRY + dMUX

/-- The topological longest carry path is `580 ps`. -/
example : dTopoAdder = 580 := by decide

/-- The ripple sub-path alone (`c₄` ready-time) is `480 ps`. -/
example : (rippleTm.eval (· + ·) 0 B (envRipple dCARRY 0 0 0 0 0)).1 = 480 := by decide

/-- The all-propagate skip carry-out is ready at `280 ps` (`= 2·δ_and + δ_mux`). -/
example : (coutSkip.eval (· + ·) 0 B (envSkip dAND dMUX 0 0 0 0 0)).1 = 280 := by decide

/-- **The false-path punchline at scale, kernel-checked.**  The data-dependent
carry-out extracted from the `P = 1` skip proof (`280 ps`) is **strictly below**
the topological longest path (`580 ps`): the ripple-and-skip path is
non-sensitisable, so it never enters a correct proof's constraint set.
Extraction beats topological STA by `300 ps` (over 2×) — for free. -/
theorem skip_beats_topological :
    (coutSkip.eval (· + ·) 0 B (envSkip dAND dMUX 0 0 0 0 0)).1 < dTopoAdder := by
  decide

/-- The saving is exactly `4·δ_carry - 2·δ_and = 300 ps`. -/
example : dTopoAdder - (coutSkip.eval (· + ·) 0 B (envSkip dAND dMUX 0 0 0 0 0)).1 = 300 := by
  decide

/-! ## Axiom audits -/

/-- info: 'PLLND.ripple_extract' does not depend on any axioms -/
#guard_msgs in
#print axioms ripple_extract

/-- info: 'PLLND.coutSkip_extract' does not depend on any axioms -/
#guard_msgs in
#print axioms coutSkip_extract

/-- info: 'PLLND.skip_beats_topological' does not depend on any axioms -/
#guard_msgs in
#print axioms skip_beats_topological

end PLLND
