import wip.towerkit
import LaxLogic.PLLSearch

/-!
# `roomhunt` — the descent hunted INSIDE its own room hypothesis

`cascade_low_pos_box` (`wip/absorb_base.lean:2273`) is

    hbox  : ¬ (S box-free ∧ S subformula-closed ∧ g ∈ S ∧ Γ ⊆ S)
    hd1   : 1 ≤ defect S Γ
    hroom : defect S Γ * (|jumpGoals S| + 2) ≤ c
    hamb  : Δ ⊢ itpE p S fuel (c+1) Γ
    hhead : Δ ⊢ itpA p S fh (c+1) Γ g          (fh ≤ fuel)
    ⟹      Δ ⊢ itpA p S fuel c Γ g

Every previous refutation of a *variant* (`not_roomFreeDescent`,
`not_ambGuardAscent`, `not_floorDescent`) violated `hroom`: those probe
families put a single head piece in `Γ`, so `defect` was 6–15 and the
product law demanded `c` in the 30–165 range while the certified failures
all sat at `c ≤ 1`.  The room hypothesis made them vacuous.

**The dimension July never used: saturate the context.**  `room` is
`defect · (J+2)`, and `defect = |S \ Γ|`.  Putting nearly all of `S` into
`Γ` drives `defect` to 1, so `room = J+2` — a *small* number that the
sweep can actually reach.  The tension is that a live gate needs its
consequent MISSING from `Γ`:

* `◯A ⊃ B ∈ Γ` gates iff `B ∉ Γ`, `B ∈ S`, `◯A ⊃ B ∈ S`;
* `(A ⊃ B) ⊃ D ∈ Γ` gates iff `D ∉ Γ`, `D ∈ S`, `B ⊃ D ∈ Γ`, `(A⊃B)⊃D ∈ S`.

So every live gate costs defect — *unless the gates share a consequent*.
That is what the **gate tower** below does: `k+1` gates all pointing at the
same `D`, with the `◯`-antecedents chosen so that they reuse each other's
jump goals:

    X := A ⊃ B ,  clauses  X ⊃ D ,  ◯X ⊃ D ,  ◯◯X ⊃ D , … , ◯ᵏX ⊃ D
    S := clauses ∪ {D} ,   Γ := clauses ∪ {B ⊃ D}

`jumpGoals S = {X, ◯X, …, ◯ᵏX}` (the `⊃⊃` clause contributes `X`; the
`i`-th `◯` clause contributes `◯ⁱ⁻¹X` and `◯ⁱX`, all already present), so
`J = k+1`, `defect = 1`, `room = k+3`, and **all `k+1` gates are live**.
This is the maximal gate density per unit of room that the definition
allows, and it is exactly the `⊃◯`-antecedent shape at which the July
boundary measured every low-budget failure.

Ladder instantiation: `X := rnSub 2 = ◯⊥ ⊃ ⊥`, `D := ⊥` gives the same
tower built entirely from Rieger–Nishimura material, and
`S := pieceClosure (gap k)` gives the genuine gap-formula spaces.

## What is measured

For every instance: `defect`, `J`, `room`, whether `hbox` holds, gate
liveness per context formula, goal-gate shape, and **budget activity** —
whether `itpA @ c` and `itpA @ (c+1)` are literally different formulas.
A budget-inactive cell makes the descent an identity and can refute
nothing; this is the syntactic strengthening of §81's `budgetBlind`
(which reads shapes only and misses the two *goal-driven* budget gates,
`C = ◯D` and `C = C₁ ⊃ C₂` with `C₁ ∈ Γ`).

Then the descent verdict, countermodel-first, at `c` from `0` up to
`room + 1`, with the cells `c < room` marked VACUOUS (they cannot refute
the lemma) and the cells `c ≥ room` marked LIVE.

Run: `lake build roomhunt && scripts/probe 600 roomhunt <stage>`
with `<stage>` one of `cover`, `sweep`, `fuel`, `ladder`, `oracle`.
-/

open PLLFormula PLLND PLLND.RNEmbed PLLND.Search

namespace RoomHunt

/-! ## 0.  Transcribed predicates (`wip/absorb_base.lean` is not a Lake
target, so its definitions cannot be imported into a probe) -/

/-- `jumpGoals`, verbatim from `wip/absorb_base.lean:37`. -/
def jumpGoals (S : Finset PLLFormula) : Finset PLLFormula :=
  S.biUnion (fun F => match F with
    | .ifThen (.ifThen A B) _ => {A.ifThen B}
    | .ifThen (.somehow A) _ => {A, A.somehow}
    | _ => ∅)

/-- The room the kernel assumes. -/
def roomProduct (S : Finset PLLFormula) (Γ : List PLLFormula) : Nat :=
  defect S Γ * ((jumpGoals S).card + 2)

/-- `boxFree` of `wip/absorb_base.lean:903`, as a `Bool`. -/
def bfree : PLLFormula → Bool
  | .prop _ => true
  | .falsePLL => true
  | .and A B => bfree A && bfree B
  | .or A B => bfree A && bfree B
  | .ifThen A B => bfree A && bfree B
  | .somehow _ => false

/-- The three closure conditions of `hbox`, on the space list. -/
def closedB (Sl : List PLLFormula) : Bool :=
  Sl.all (fun F => match F with
    | .and A B => Sl.contains A && Sl.contains B
    | .or A B => Sl.contains A && Sl.contains B
    | .ifThen A B => Sl.contains A && Sl.contains B
    | _ => true)

/-- `hbox` holds (so the holdout genuinely applies) iff the conjunction of
box-freeness, closure and coverage FAILS. -/
def hboxHolds (Sl : List PLLFormula) (Γ : List PLLFormula) (g : PLLFormula) : Bool :=
  ! (Sl.all bfree && closedB Sl && Sl.contains g && Γ.all (fun F => Sl.contains F))

/-! ## 1.  Coverage instruments -/

def shapeTag : PLLFormula → String
  | .falsePLL => "bot"
  | .prop _ => "atom"
  | .and _ _ => "conj"
  | .or _ _ => "disj"
  | .somehow _ => "box"
  | .ifThen .falsePLL _ => "imp-bot"
  | .ifThen (.prop _) _ => "imp-atom"
  | .ifThen (.and _ _) _ => "imp-conj"
  | .ifThen (.or _ _) _ => "imp-disj"
  | .ifThen (.ifThen _ _) _ => "imp-imp*"
  | .ifThen (.somehow _) _ => "imp-box*"

def coverTags (L : List PLLFormula) : List String := (L.map shapeTag).dedup

def budgetBlind (L : List PLLFormula) : Bool :=
  ¬ ((coverTags L).contains "imp-imp*" || (coverTags L).contains "imp-box*")

/-- Context-gate liveness, per context formula (`wip/budgetfit.lean` §3,
re-read off `LaxLogic/PLLG4UITrunc.lean` lines 252-290). -/
def gateLive (Sl : List PLLFormula) (Γ : List PLLFormula) :
    List (String × Bool) :=
  Γ.filterMap (fun F => match F with
    | .ifThen (.somehow A) B =>
        some (s!"◯{A.toString}⊃{B.toString}",
          (!Γ.contains B) && Sl.contains B && Sl.contains F)
    | .ifThen (.ifThen A B) D =>
        some (s!"({A.toString}⊃{B.toString})⊃{D.toString}",
          (!Γ.contains D) && Sl.contains D && Γ.contains (B.ifThen D)
            && Sl.contains F)
    | _ => none)

def liveGateCount (Sl : List PLLFormula) (Γ : List PLLFormula) : Nat :=
  ((gateLive Sl Γ).filter (fun x => x.2)).length

/-- **The goal-driven budget gates** — missed by §81's shape instrument,
which reads the space only.  `itpA`'s `goal` list reads `b` at two places
(`LaxLogic/PLLG4UITrunc.lean`: the `⊃`-goal with the antecedent already in
`Γ`, and the `◯`-goal, plus the `◯`-goal's truncation disjunct). -/
def goalGate (Γ : List PLLFormula) (g : PLLFormula) : String :=
  match g with
  | .somehow _ => "BOX-GOAL (b-gated: goal disjunct + truncation)"
  | .ifThen C₁ _ =>
      if Γ.contains C₁ then "IMP-GOAL, antecedent present (b-gated)"
      else "imp-goal, fresh antecedent (not itself gated)"
  | _ => "goal not b-gated"

/-! ## 2.  The descent instance -/

def descHyps (p : String) (S : Finset PLLFormula) (fuel fh c : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) : List PLLFormula :=
  [itpA p S fh (c + 1) Γ g, itpE p S fuel (c + 1) Γ]

def descGoal (p : String) (S : Finset PLLFormula) (fuel c : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) : PLLFormula :=
  itpA p S fuel c Γ g

/-- **Budget activity**: the descent is a syntactic identity — hence
unrefutable — unless the two tables actually differ. -/
def budgetActive (p : String) (S : Finset PLLFormula) (fuel c : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) : Bool :=
  descGoal p S fuel (c + 1) Γ g != descGoal p S fuel c Γ g

inductive V4 | prov | refCert | clean deriving BEq

def V4.tag : V4 → String
  | .prov => "P" | .refCert => "R!" | .clean => "~"

/-- Frames the default battery does not carry, aimed at the `◯⊥`-ladder:
longer chains with a *rigid* `Rₘ` (the `¬◯⊥` regions), infallible variants
of the chains, and a rigid fork.  `Config.frames` is untrusted — a wider
battery can only find more countermodels, never certify a wrong one. -/
def ladderFrames : List Frame :=
  [ -- 3-chain, rigid modal, infallible: the plain ladder segment
    ⟨3, [(0,1),(1,2),(0,2)], [], []⟩
    -- 3-chain, rigid modal, fallible top
  , ⟨3, [(0,1),(1,2),(0,2)], [], [2]⟩
    -- 4-chain, fully constrained, infallible
  , ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)],
       [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], []⟩
    -- 4-chain, rigid modal, infallible
  , ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [], []⟩
    -- 4-chain, one modal edge at the bottom
  , ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(0,1)], []⟩
    -- 5-chain, rigid modal, fallible top (the abyss-lifted ladder shape)
  , ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],
       [], [4]⟩
    -- 5-chain, modal only on the last step
  , ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)],
       [(3,4)], []⟩
    -- rigid fork
  , ⟨3, [(0,1),(0,2)], [], []⟩
    -- fork with both arms constrained, infallible
  , ⟨3, [(0,1),(0,2)], [(0,1),(0,2)], []⟩ ]

def cfgFull : Config := { findBudget := some 20000, emitClosureCap := 0 }
def cfgCheap : Config := { findBudget := some 1500, emitClosureCap := 0 }

/-- The hunt configuration: countermodel-first with the widened battery and
a token positive stage. -/
def cfgHunt : Config :=
  { frames := ladderFrames ++ defaultFrames
  , findBudget := some 900
  , emitClosureCap := 0 }

def descVerdictC (cf : Config) (p : String) (S : Finset PLLFormula)
    (fuel fh c : Nat) (Γ : List PLLFormula) (g : PLLFormula) : V4 :=
  match settleWhy cf (descHyps p S fuel fh c Γ g) (descGoal p S fuel c Γ g) with
  | .proved _ => .prov
  | .refuted _ _ _ => .refCert
  | .unknown _ => .clean

/-! ## 3.  The instances -/

structure Inst where
  name : String
  Sl : List PLLFormula
  ctx : List PLLFormula
  g : PLLFormula

def Inst.S (i : Inst) : Finset PLLFormula := i.Sl.toFinset

def pv' : String := "p"
def pA : PLLFormula := prop "p"
def rA : PLLFormula := prop "r"
def zA : PLLFormula := prop "z"
def yA : PLLFormula := prop "y"

def boxN : Nat → PLLFormula → PLLFormula
  | 0, F => F
  | n + 1, F => (boxN n F).somehow

/-- **The gate tower.**  `k+1` live gates sharing the consequent `D`, with
`jumpGoals = {X, ◯X, …, ◯ᵏX}`; `defect = 1`, `room = k+3`. -/
def gateTower (nm : String) (A B D g : PLLFormula) (k : Nat) : Inst :=
  let X := A.ifThen B
  let cls := (X.ifThen D) :: ((List.range k).map (fun i => (boxN (i + 1) X).ifThen D))
  { name := nm
  , Sl := (cls ++ [D]).dedup
  , ctx := (cls ++ [B.ifThen D]).dedup
  , g := g }

/-- The `◯`-only tower (no `⊃⊃` clause): `jumpGoals = {X, ◯X, …, ◯ᵏX}`
still, one gate fewer. -/
def boxTowerI (nm : String) (X D g : PLLFormula) (k : Nat) : Inst :=
  let cls := (List.range k).map (fun i => (boxN (i + 1) X).ifThen D)
  { name := nm, Sl := (cls ++ [D]).dedup, ctx := cls.dedup, g := g }

/-- The single `⊃⊃` gate: `J = 1`, `defect = 1`, `room = 3` — the cheapest
budget-active instance the room hypothesis admits. -/
def impGate (nm : String) (A B D g : PLLFormula) : Inst :=
  { name := nm
  , Sl := [(A.ifThen B).ifThen D, D]
  , ctx := [(A.ifThen B).ifThen D, B.ifThen D]
  , g := g }

/-- The single `◯` gate: `J = 2`, `defect = 1`, `room = 4`. -/
def boxGate (nm : String) (A D g : PLLFormula) : Inst :=
  { name := nm
  , Sl := [(A.somehow).ifThen D, D]
  , ctx := [(A.somehow).ifThen D]
  , g := g }

/-- `rnSub 2 = ◯⊥ ⊃ ⊥`, the ladder's first implication rung. -/
def rn2 : PLLFormula := rnSub 2

def rn3 : PLLFormula := rnSub 3

/-- `chainF k = ◯(rnSub (2k+1))`, verbatim from `wip/chainStrict.lean:64`
(that module's import closure reaches `wip/rnc_probe.lean`, which declares
a root-level `main`, so an executable root cannot import it). -/
def chainF (k : Nat) : PLLFormula := (rnSub (2 * k + 1)).somehow

/-- `gap k = chainF k ⊃ rnSub (2k+1)`, verbatim from `wip/gapWidth.lean:51`. -/
def gapK (k : Nat) : PLLFormula := (chainF k).ifThen (rnSub (2 * k + 1))

/-- A list-level `pieceClosure` mirroring `TowerKit.pieceClosure`
(`Finset.toList` is noncomputable, so a probe cannot read the original's
list).  `pieceClosure_agrees` below pins the two together. -/
def pclL : PLLFormula → List PLLFormula
  | .prop a => [PLLFormula.prop a]
  | .falsePLL => [falsePLL]
  | .and A B => ((A.and B) :: (pclL A ++ pclL B)).dedup
  | .or A B => ((A.or B) :: (pclL A ++ pclL B)).dedup
  | .ifThen (.prop a) D =>
      (((PLLFormula.prop a).ifThen D) :: (pclL (PLLFormula.prop a) ++ pclL D)).dedup
  | .ifThen .falsePLL D => ((falsePLL.ifThen D) :: (pclL falsePLL ++ pclL D)).dedup
  | .ifThen (.and A B) D =>
      (((A.and B).ifThen D) :: (pclL (A.and B) ++ pclL D
        ++ pclL (A.ifThen (B.ifThen D)))).dedup
  | .ifThen (.or A B) D =>
      (((A.or B).ifThen D) :: (pclL (A.or B) ++ pclL D
        ++ pclL (A.ifThen D) ++ pclL (B.ifThen D))).dedup
  | .ifThen (.ifThen A B) D =>
      (((A.ifThen B).ifThen D) :: (pclL (A.ifThen B) ++ pclL D
        ++ pclL (B.ifThen D))).dedup
  | .ifThen (.somehow X) D =>
      (((somehow X).ifThen D) :: (pclL (somehow X) ++ pclL D)).dedup
  | .somehow χ => (χ.somehow :: pclL χ).dedup
termination_by φ => φ.weight
decreasing_by all_goals (simp only [PLLFormula.weight]; omega)

/-- The gap-`k` space with the context saturated except for the gate's own
consequent — the minimum-room ladder instance. -/
def gapInst (k : Nat) (g : PLLFormula) : Inst :=
  let Sl := pclL (gapK k)
  let miss := rnSub (2 * k + 1)
  { name := s!"gap{k}", Sl := Sl, ctx := Sl.filter (fun F => F != miss), g := g }

def instRow (i : Inst) : String :=
  let S := i.S
  let d := defect S i.ctx
  let J := (jumpGoals S).card
  s!"|S|={i.Sl.length} defect={d} J={J} room={d * (J + 2)} \
hbox={hboxHolds i.Sl i.ctx i.g} liveGates={liveGateCount i.Sl i.ctx} \
blind={budgetBlind i.Sl}"

/-! ## 4.  The families -/

def goalMenu (D : PLLFormula) (X : PLLFormula) : List (String × PLLFormula) :=
  [ ("D", D)
  , ("fresh-atom", yA)
  , ("box-D", D.somehow)
  , ("box-fresh", yA.somehow)
  , ("impD-fresh", X.ifThen yA)
  , ("gateimp", ((X.somehow).ifThen D).ifThen yA) ]

def towerFams (kmax : Nat) : List Inst :=
  (List.range kmax).flatMap (fun k =>
    (goalMenu zA (pA.ifThen rA)).map (fun (gn, g) =>
      gateTower s!"tower{k}/{gn}" pA rA zA g k))

/-- The ladder instantiation: `X = rnSub 2 = ◯⊥ ⊃ ⊥`, `D = ⊥`, so every
clause is Rieger–Nishimura material and the tower is `¬◯ⁱ(¬◯⊥)`. -/
def ladderFams (kmax : Nat) : List Inst :=
  (List.range kmax).flatMap (fun k =>
    (goalMenu falsePLL rn2).map (fun (gn, g) =>
      gateTower s!"ldtower{k}/{gn}" oBot falsePLL falsePLL g k))

/-- The same, but with the eliminated variable `p` inside the ladder
material — `X = ◯p ⊃ ⊥`, `D = ⊥`: `p`-elimination is then non-trivial at
every gate. -/
def ladderPFams (kmax : Nat) : List Inst :=
  (List.range kmax).flatMap (fun k =>
    (goalMenu falsePLL (pA.somehow.ifThen falsePLL)).map (fun (gn, g) =>
      gateTower s!"ldp{k}/{gn}" pA.somehow falsePLL falsePLL g k))

/-- `◯`-only towers: no `⊃⊃` clause, so one gate fewer at the same `J`. -/
def boxTowerFams (kmax : Nat) : List Inst :=
  (List.range kmax).flatMap (fun k =>
    (goalMenu zA (pA.ifThen rA)).map (fun (gn, g) =>
      boxTowerI s!"btower{k}/{gn}" (pA.ifThen rA) zA g (k + 1)))

def cheapFams : List Inst :=
  (goalMenu zA (pA.ifThen rA)).map (fun (gn, g) => impGate s!"impgate/{gn}" pA rA zA g)
  ++ (goalMenu zA (pA.ifThen rA)).map (fun (gn, g) => boxGate s!"boxgate/{gn}" pA zA g)

/-! ### Defect scaling at fixed `J`

`m` gates sharing one antecedent but with `m` DIFFERENT consequents:
`jumpGoals = {A ⊃ B}` (or `{A, ◯A}`), so `J` stays at 1 (resp. 2) while
`defect = m` and all `m` gates are live.  `room = 3m` (resp. `4m`).  If the
true requirement grew faster than linearly in the defect — the one shape
of miscalibration the product law could not absorb — this is the family
that would show it. -/
def defectFamI (m : Nat) (g : PLLFormula) : Inst :=
  let X := pA.ifThen rA
  let Ds := (List.range m).map (fun i => prop s!"d{i}")
  { name := s!"defI{m}"
  , Sl := (Ds.map (fun D => X.ifThen D) ++ Ds).dedup
  , ctx := (Ds.map (fun D => X.ifThen D) ++ Ds.map (fun D => rA.ifThen D)).dedup
  , g := g }

def defectFamO (m : Nat) (g : PLLFormula) : Inst :=
  let Ds := (List.range m).map (fun i => prop s!"d{i}")
  { name := s!"defO{m}"
  , Sl := (Ds.map (fun D => (pA.somehow).ifThen D) ++ Ds).dedup
  , ctx := (Ds.map (fun D => (pA.somehow).ifThen D)).dedup
  , g := g }

def defectFams (mmax : Nat) : List Inst :=
  (List.range mmax).flatMap (fun i =>
    [defectFamI (i + 1) zA, defectFamI (i + 1) yA, defectFamI (i + 1) (yA.somehow),
     defectFamO (i + 1) zA, defectFamO (i + 1) yA, defectFamO (i + 1) (yA.somehow)])

/-! ### UNPAID GROWTH — the fourth seal, at the room floor

`cascade_low_pos_box`'s own failure analysis names four sealed positions;
the fourth is *"the fresh-antecedent goal implication with the new piece
outside `S` (the impR seals; the defect does not pay)"*.  That site is
reachable at room 3, and it is the one place where the context can grow
without the room hypothesis noticing:

`itpA`'s goal clause for `C = C₁ ⊃ C₂` with `C₁ ∉ Γ` recurses at
`Γ' = C₁ :: Γ` — and if `C₁ ∉ S` then `defect S Γ' = defect S Γ`, so the
growth is free of charge in the ledger.  Meanwhile `room` is computed at
`Γ`, not at `Γ'`.

The construction makes that free growth *do work*: the `⊃⊃` gate
`(A⊃B)⊃D ∈ Γ` is DEAD at `Γ` (its guard `B ⊃ D` is missing) and becomes
LIVE at `Γ'` when the goal's fresh antecedent is exactly `B ⊃ D`.  So

* the ambient `itpE p S fuel (c+1) Γ` is budget-BLIND (no gate fires at
  `Γ` at all — the clause emits nothing, since `B⊃D ∉ Γ` and `B⊃D ∉ S`),
  hence finances nothing;
* the whole budget-active content sits at `Γ'`, where the only available
  financing would be `E@(c+1)(Γ')` — the `AmbGuardAscent` step that
  `wip/ascRefute.lean` REFUTED (for `X ∈ S`, at `c = 1`).

This is the July refutation's mechanism relocated to a configuration whose
room is 3 instead of 56. -/

/-- Unpaid growth, box-free non-closed `S` (`hbox` via non-closure). -/
def freshImp (g : PLLFormula) : Inst :=
  { name := "fresh-impgate"
  , Sl := [(pA.ifThen rA).ifThen zA, zA]
  , ctx := [(pA.ifThen rA).ifThen zA]
  , g := g }

/-- Unpaid growth, `S` subformula-CLOSED and `Γ ⊆ S` (`hbox` via `g ∉ S`
only).  Box-free. -/
def freshClosed (g : PLLFormula) : Inst :=
  { name := "fresh-closed"
  , Sl := [(pA.ifThen rA).ifThen zA, pA.ifThen rA, pA, rA, zA]
  , ctx := [(pA.ifThen rA).ifThen zA, pA.ifThen rA, pA, rA]
  , g := g }

/-- Unpaid growth, `S` subformula-closed, `Γ ⊆ S`, and **`◯`-involving**:
the gate's consequent is `◯w`.  `hbox` via `g ∉ S` only. -/
def freshBoxed (g : PLLFormula) : Inst :=
  { name := "fresh-boxed"
  , Sl := [(pA.ifThen rA).ifThen ((prop "w").somehow), pA.ifThen rA, pA, rA,
           (prop "w").somehow, prop "w"]
  , ctx := [(pA.ifThen rA).ifThen ((prop "w").somehow), pA.ifThen rA, pA, rA,
            prop "w"]
  , g := g }

/-- Two unpaid growths in series: the goal opens two fresh antecedents,
each activating one of two dead gates, and `defect` never moves. -/
def freshDouble (g : PLLFormula) : Inst :=
  { name := "fresh-double"
  , Sl := [(pA.ifThen rA).ifThen zA, ((pA.somehow).ifThen rA).ifThen zA, zA]
  , ctx := [(pA.ifThen rA).ifThen zA, ((pA.somehow).ifThen rA).ifThen zA]
  , g := g }

/-- The fresh antecedents that activate each dead gate. -/
def actImp : PLLFormula := rA.ifThen zA
def actBox : PLLFormula := rA.ifThen ((prop "w").somehow)

def freshFams : List Inst :=
  [ freshImp (actImp.ifThen yA)
  , freshImp (actImp.ifThen zA)
  , freshImp (actImp.ifThen (yA.somehow))
  , freshImp (actImp.ifThen (actImp.ifThen yA))
  , freshClosed (actImp.ifThen yA)
  , freshClosed (actImp.ifThen zA)
  , freshClosed (actImp.ifThen (yA.somehow))
  , freshBoxed (actBox.ifThen yA)
  , freshBoxed (actBox.ifThen ((prop "w").somehow))
  , freshBoxed (actBox.ifThen (yA.somehow))
  , freshDouble (actImp.ifThen yA)
  , freshDouble (actImp.ifThen (actImp.ifThen yA)) ]

/-! ### Calibration: §79's refuting configuration

`wip/ascRefute.lean` §2 (`Sk`, `Gk`, `gk`), transcribed.  Its descent is
`checkB`-certified FALSE at `c = 1`, `fuel = 4` (`not_derivable_k`).  Its
room is `defect · (J+2) = 8 · 6 = 48`, so the cell is vacuous for
`cascade_low_pos_box` — but it is the instrument's live-fire test: a sweep
that cannot reproduce `R!` here is reporting nothing when it prints `~`. -/
def SkL : List PLLFormula :=
  [(pA.somehow).ifThen rA, pA.somehow, pA, rA,
   (((rA.somehow).ifThen (prop "s"))).ifThen (prop "t"),
   (rA.somehow).ifThen (prop "s"), rA.somehow, prop "s", prop "t"]

def calibInst : Inst :=
  { name := "CALIB(ascRefute §2)"
  , Sl := SkL
  , ctx := [(pA.somehow).ifThen rA]
  , g := ((rA.somehow).ifThen (prop "s")).ifThen (prop "t") }

/-! ## 5.  Stages -/

def pf (F : PLLFormula) : String := F.toString

def coverStage (out : IO.FS.Stream) (fams : List Inst) : IO Unit := do
  for i in fams do
    out.putStrLn s!"{i.name}: {instRow i}"
    out.putStrLn s!"   S  = {i.Sl.map pf}"
    out.putStrLn s!"   Γ  = {i.ctx.map pf}"
    out.putStrLn s!"   g  = {pf i.g}   [{goalGate i.ctx i.g}]"
    out.putStrLn s!"   gates = {gateLive i.Sl i.ctx}"
    out.flush

/-- Size + budget-activity scan.  Prints before each computation so a
blow-up is localised rather than silent. -/
def sizeStage (out : IO.FS.Stream) (fams : List Inst) (fuels : List Nat)
    (cmax : Nat) : IO Unit := do
  for i in fams do
    let S := i.S
    let room := roomProduct S i.ctx
    out.putStrLn s!"{i.name}: {instRow i}"
    out.flush
    for fuel in fuels do
      for c in List.range (cmax + 1) do
        out.putStrLn s!"   fuel={fuel} c={c} (room={room}) computing…"
        out.flush
        let t0 ← IO.monoMsNow
        let n ← IO.lazyPure (fun _ => TowerKit.sz (descGoal pv' S fuel c i.ctx i.g))
        let n2 ← IO.lazyPure (fun _ => TowerKit.sz (itpE pv' S fuel (c + 1) i.ctx))
        let act ← IO.lazyPure (fun _ => budgetActive pv' S fuel c i.ctx i.g)
        let _ ← IO.lazyPure (fun _ => n + n2 + (if act then 1 else 0))
        let t1 ← IO.monoMsNow
        out.putStrLn s!"   fuel={fuel} c={c} (room={room}) |A@c|={n} \
|E@(c+1)|={n2} active={act} {if c ≥ room then "LIVE" else "vacuous"} \
({t1 - t0} ms)"
        out.flush

/-- The **room-window sweep**: budgets from `room - 1` (the last vacuous
cell, kept as calibration) to `room + span`.  Cells below the room are
marked `vacuous`: a failure there refutes nothing about
`cascade_low_pos_box`, only about a room-free reformulation. -/
def windowStage (out : IO.FS.Stream) (cf : Config) (fams : List Inst)
    (fuels : List Nat) (span : Nat) (cap : Nat) : IO Unit := do
  for i in fams do
    let S := i.S
    let room := roomProduct S i.ctx
    out.putStrLn s!"{i.name}: {instRow i}  goalgate=[{goalGate i.ctx i.g}]"
    out.flush
    for fuel in fuels do
      for j in List.range (span + 2) do
        let c := room - 1 + j
        let t0 ← IO.monoMsNow
        let n ← IO.lazyPure (fun _ => TowerKit.sz (descGoal pv' S fuel c i.ctx i.g))
        let _ ← IO.lazyPure (fun _ => n)
        if n > cap then
          out.putStrLn s!"   fuel={fuel} c={c}: SKIP (|A@c|={n} > {cap})"
          out.flush
        else
          let act ← IO.lazyPure (fun _ => budgetActive pv' S fuel c i.ctx i.g)
          let v ← IO.lazyPure (fun _ => descVerdictC cf pv' S fuel fuel c i.ctx i.g)
          let _ ← IO.lazyPure (fun _ => v.tag.length + (if act then 1 else 0))
          let t1 ← IO.monoMsNow
          let flag := if c ≥ room then (if v == V4.refCert then "*** REFUTES ***" else "LIVE")
                      else "vacuous"
          out.putStrLn s!"   fuel={fuel} c={c}: {v.tag} active={act} \
|A@c|={n} room={room} {flag} ({t1 - t0} ms)"
          out.flush

def sweepStage (out : IO.FS.Stream) (cf : Config) (fams : List Inst)
    (fuels : List Nat) (cmax : Nat) (cap : Nat) : IO Unit := do
  for i in fams do
    let S := i.S
    let room := roomProduct S i.ctx
    out.putStrLn s!"{i.name}: {instRow i}  goalgate=[{goalGate i.ctx i.g}]"
    out.flush
    for fuel in fuels do
      for c in List.range (cmax + 1) do
        let t0 ← IO.monoMsNow
        let n ← IO.lazyPure (fun _ => TowerKit.sz (descGoal pv' S fuel c i.ctx i.g))
        let _ ← IO.lazyPure (fun _ => n)
        if n > cap then
          out.putStrLn s!"   fuel={fuel} c={c}: SKIP (|A@c|={n} > {cap})"
          out.flush
        else
          let act ← IO.lazyPure (fun _ => budgetActive pv' S fuel c i.ctx i.g)
          let v ← IO.lazyPure (fun _ => descVerdictC cf pv' S fuel fuel c i.ctx i.g)
          let _ ← IO.lazyPure (fun _ => v.tag.length + (if act then 1 else 0))
          let t1 ← IO.monoMsNow
          let flag := if c ≥ room then (if v == V4.refCert then "*** REFUTES ***" else "LIVE")
                      else "vacuous"
          out.putStrLn s!"   fuel={fuel} c={c}: {v.tag} active={act} \
|A@c|={n} room={room} {flag} ({t1 - t0} ms)"
          out.flush

/-! ## 6.  Oracle scan — the battery's tower values across budgets

`v ⊢ T b` is free at every budget and `T b ⊢ v` at one budget propagates
upward (`itp_budget_mono_le`), so a *regression* is impossible; what the
scan measures is the LEAST budget at which each row's tower value settles
onto the pinned semantic value.  That number is the empirical demand the
tables make, against the prescribed budget `kcap (pieceClosure φ) + 1`. -/

def oracleStage (out : IO.FS.Stream) (bmax : Nat) (cap : Nat) : IO Unit := do
  for r in TowerKit.battery do
    match r.val with
    | none => out.putStrLn s!"{r.name} ({r.side}): value OPEN — skipped"
    | some v =>
      let pb := if r.side = "E" then TowerKit.eBudget r.subj
                else TowerKit.aBudget r.subj
      out.putStrLn s!"{r.name} ({r.side}): pinned = {pf v}  [prescribed budget = {pb}]"
      out.flush
      for b in List.range (bmax + 1) do
        let t ← IO.lazyPure (fun _ => TowerKit.rowTower r b)
        let n ← IO.lazyPure (fun _ => TowerKit.sz t)
        let _ ← IO.lazyPure (fun _ => n)
        if n > cap then
          out.putStrLn s!"   b={b}: SKIP (|T b|={n} > {cap})"
          out.flush
        else
          -- the one direction that is not free
          let dir := if r.side = "E" then ([t], v) else ([v], t)
          let vv ← IO.lazyPure (fun _ =>
            match settleWhy cfgFull dir.1 dir.2 with
            | .proved _ => "SETTLED"
            | .refuted _ _ _ => "NOT-YET (certified strict)"
            | .unknown _ => "undecided-at-budget")
          let _ ← IO.lazyPure (fun _ => vv.length)
          out.putStrLn s!"   b={b}: |T b|={n}  {vv}"
          out.flush

def runMain (args : List String) : IO Unit := do
  let out ← IO.getStdout
  let stage := args.headD "cover"
  out.putStrLn s!"== roomhunt, stage {stage} =="
  out.flush
  match stage with
  | "cover" => do
      out.putStrLn "-- cheap families --"; coverStage out cheapFams
      out.putStrLn "-- gate towers --"; coverStage out (towerFams 3)
      out.putStrLn "-- ladder towers --"; coverStage out (ladderFams 3)
      out.putStrLn "-- p-ladder towers --"; coverStage out (ladderPFams 3)
      out.putStrLn "-- box-only towers --"; coverStage out (boxTowerFams 3)
      out.putStrLn "-- gap closures --"
      coverStage out ((List.range 3).map (fun k => gapInst (k + 1) falsePLL))
  | "size" => do
      sizeStage out (cheapFams ++ towerFams 3) [4, 6, 8] 6
  | "sweep" => do
      sweepStage out cfgHunt cheapFams [3, 4, 6, 8, 10] 6 200000
  | "sweept" => do
      windowStage out cfgHunt (towerFams 4) [4, 6, 8, 10] 2 200000
  | "sweepl" => do
      windowStage out cfgHunt (ladderFams 4) [4, 6, 8, 10] 2 200000
  | "sweeplp" => do
      windowStage out cfgHunt (ladderPFams 4) [4, 6, 8, 10] 2 200000
  | "sweepb" => do
      windowStage out cfgHunt (boxTowerFams 4) [4, 6, 8, 10] 2 200000
  | "gap" => do
      let fams := (List.range 3).flatMap (fun k =>
        [gapInst (k + 1) falsePLL, gapInst (k + 1) yA,
         gapInst (k + 1) (yA.somehow),
         gapInst (k + 1) ((rnSub (2 * (k + 1) + 1)).somehow)])
      coverStage out fams
      windowStage out cfgHunt fams [6, 8] 1 400000
  | "adapt" => do
      -- fuel chosen ADAPTIVELY (`c + 3`, `c + 5`): the b-recursion at the
      -- same context has depth `b`, so fuel below `c + 2` truncates it
      -- away and fuel far above it only inflates the tables.
      let fams := towerFams 4 ++ ladderFams 4 ++ ladderPFams 3
                  ++ boxTowerFams 3 ++ defectFams 3
      for i in fams do
        let S := i.S
        let room := roomProduct S i.ctx
        out.putStrLn s!"{i.name}: {instRow i}  goalgate=[{goalGate i.ctx i.g}]"
        out.flush
        for j in [0, 1] do
          let c := room + j
          for d in [3, 5] do
            let fuel := c + d
            let t0 ← IO.monoMsNow
            let n ← IO.lazyPure (fun _ =>
              TowerKit.sz (descGoal pv' S fuel c i.ctx i.g))
            let _ ← IO.lazyPure (fun _ => n)
            if n > 250000 then
              out.putStrLn s!"   fuel={fuel} c={c}: SKIP (|A@c|={n})"
              out.flush
            else
              let act ← IO.lazyPure (fun _ => budgetActive pv' S fuel c i.ctx i.g)
              let v ← IO.lazyPure (fun _ =>
                descVerdictC cfgHunt pv' S fuel fuel c i.ctx i.g)
              let _ ← IO.lazyPure (fun _ => v.tag.length + (if act then 1 else 0))
              let t1 ← IO.monoMsNow
              let flag := if v == V4.refCert then "*** REFUTES ***" else "LIVE"
              out.putStrLn s!"   fuel={fuel} c={c}: {v.tag} active={act} \
|A@c|={n} room={room} {flag} ({t1 - t0} ms)"
              out.flush
  | "sharp" => do
      -- the single sharpest cell of the whole space: `c = room` exactly,
      -- with a real positive budget so the answer is two-sided
      let cf : Config := { frames := ladderFrames ++ defaultFrames
                         , findBudget := some 400000, emitClosureCap := 0 }
      let fams := cheapFams ++ towerFams 2 ++ ladderFams 2
      for i in fams do
        let S := i.S
        let room := roomProduct S i.ctx
        for fuel in [3, 4, 5, 6] do
          let t0 ← IO.monoMsNow
          let n ← IO.lazyPure (fun _ => TowerKit.sz (descGoal pv' S fuel room i.ctx i.g))
          let act ← IO.lazyPure (fun _ => budgetActive pv' S fuel room i.ctx i.g)
          let v ← IO.lazyPure (fun _ => descVerdictC cf pv' S fuel fuel room i.ctx i.g)
          let _ ← IO.lazyPure (fun _ => n + v.tag.length + (if act then 1 else 0))
          let t1 ← IO.monoMsNow
          out.putStrLn s!"{i.name} fuel={fuel} c=room={room}: {v.tag} \
active={act} |A@c|={n} ({t1 - t0} ms)"
          out.flush
  | "fresh" => do
      coverStage out freshFams
      out.putStrLn "-- room window, adaptive fuel --"
      for i in freshFams do
        let S := i.S
        let room := roomProduct S i.ctx
        out.putStrLn s!"{i.name}: {instRow i}  g={pf i.g}"
        out.flush
        for j in [0, 1, 2] do
          let c := room + j
          for d in [2, 3, 5, 7] do
            let fuel := c + d
            let t0 ← IO.monoMsNow
            let n ← IO.lazyPure (fun _ =>
              TowerKit.sz (descGoal pv' S fuel c i.ctx i.g))
            let _ ← IO.lazyPure (fun _ => n)
            if n > 250000 then
              out.putStrLn s!"   fuel={fuel} c={c}: SKIP (|A@c|={n})"
              out.flush
            else
              let act ← IO.lazyPure (fun _ => budgetActive pv' S fuel c i.ctx i.g)
              let v ← IO.lazyPure (fun _ =>
                descVerdictC cfgHunt pv' S fuel fuel c i.ctx i.g)
              let _ ← IO.lazyPure (fun _ => v.tag.length + (if act then 1 else 0))
              let t1 ← IO.monoMsNow
              let flag := if v == V4.refCert then "*** REFUTES ***" else "LIVE"
              out.putStrLn s!"   fuel={fuel} c={c}: {v.tag} active={act} \
|A@c|={n} room={room} {flag} ({t1 - t0} ms)"
              out.flush
  | "freshlow" => do
      -- the same instances BELOW the room, to locate their failure
      -- boundary (vacuous cells, but they calibrate the family)
      for i in freshFams do
        let S := i.S
        let room := roomProduct S i.ctx
        out.putStrLn s!"{i.name}: {instRow i}  g={pf i.g}"
        out.flush
        for c in List.range room do
          for d in [3, 5] do
            let fuel := c + d
            let act ← IO.lazyPure (fun _ => budgetActive pv' S fuel c i.ctx i.g)
            let v ← IO.lazyPure (fun _ =>
              descVerdictC cfgHunt pv' S fuel fuel c i.ctx i.g)
            let _ ← IO.lazyPure (fun _ => v.tag.length + (if act then 1 else 0))
            out.putStrLn s!"   fuel={fuel} c={c}: {v.tag} active={act} \
room={room} vacuous"
            out.flush
  | "calib" => do
      coverStage out [calibInst]
      out.putStrLn "-- default battery --"
      sweepStage out { findBudget := some 900, emitClosureCap := 0 } [calibInst]
        [4] 3 400000
      out.putStrLn "-- widened battery (cfgHunt) --"
      sweepStage out cfgHunt [calibInst] [4] 3 400000
  | "defect" => do
      coverStage out (defectFams 3)
      windowStage out cfgHunt (defectFams 3) [4, 6, 8] 1 300000
  | "oracle" => do
      oracleStage out 3 400000
  | _ => out.putStrLn "stages: cover size sweep sweept sweepl sweeplp sweepb \
gap defect calib oracle"
  out.putStrLn "== done =="

end RoomHunt

def main (args : List String) : IO Unit := RoomHunt.runMain args
