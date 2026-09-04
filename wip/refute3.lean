import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLG4Dec

/-!
# refute3 — systematic semantic DISPROOF campaign against `cascade_low_pos`

Probe file, not a proof.  Target (wip/absorb_base.lean:930):

    cascade_low_pos : 1 ≤ defect S Γ → defect S Γ * (J+2) ≤ c →
      G4c Δ (itpE p S fuel (c+1) Γ) → G4c Δ (itpA p S fh (c+1) Γ g) →
      fh ≤ fuel → G4c Δ (itpA p S fuel c Γ g)         (J = |jumpGoals S|)

Refutation shape: take Δ := [X1, X2] with X1 = itpE p S fuel (c+1) Γ and
X2 = itpA p S fh (c+1) Γ g; hamb/hhead hold by identity+weakening, so the
lemma forces G4c [X1,X2] Y with Y = itpA p S fuel c Γ g.  Finite Heyting
algebras with a nucleus interpret G4c soundly (◯ = nucleus), so ANY point
v with v(X1) ⊓ v(X2) ≰ v(Y) is a countermodel refuting the statement.

Instruments:
* algebra zoo — ALL nuclei on 6 base Heyting algebras, enumerated and
  filter-verified (inflationary, idempotent, meet-preserving), the base
  lattices adjunction-checked;
* instance sweep — curated batteries at the exact room floor
  `c = defect·(J+2)` (and floor+1), plus a mechanical sublist sweep of
  spaces over piece closures;
* every configuration is size-gated (fsize before any zoo pass);
* decider spot-checks (`search`, kernel-grade via `search_sound`).
-/

open PLLFormula

namespace PLLND
namespace Refute3

/-! ### Formula utilities -/

/-- Node count — the size gate. -/
def fsize : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and A B => fsize A + fsize B + 1
  | .or A B => fsize A + fsize B + 1
  | .ifThen A B => fsize A + fsize B + 1
  | .somehow A => fsize A + 1

/-- Atoms as a deduped list. -/
def fatoms (F : PLLFormula) : List String :=
  (go F).eraseDups
where go : PLLFormula → List String
  | .prop s => [s]
  | .falsePLL => []
  | .and A B => go A ++ go B
  | .or A B => go A ++ go B
  | .ifThen A B => go A ++ go B
  | .somehow A => go A

/-- Compact printer for witnesses. -/
def pf : PLLFormula → String
  | .prop s => s
  | .falsePLL => "F"
  | .and A B => "(" ++ pf A ++ "&" ++ pf B ++ ")"
  | .or A B => "(" ++ pf A ++ "|" ++ pf B ++ ")"
  | .ifThen A B => "(" ++ pf A ++ ">" ++ pf B ++ ")"
  | .somehow A => "O" ++ pf A

/-- Local copy of `wip/absorb_base.lean`'s `jumpGoals` (that file is not
an importable module). -/
def jumpGoals' (S : Finset PLLFormula) : Finset PLLFormula :=
  S.biUnion (fun F => match F with
    | .ifThen (.ifThen A B) _ => {A.ifThen B}
    | .ifThen (.somehow A) _ => {A, A.somehow}
    | _ => ∅)

/-! ### Algebra zoo: base Heyting algebras from their order tables -/

structure Alg where
  name : String
  n : Nat                      -- elements are 0..n-1
  meet : Array (Array Nat)
  join : Array (Array Nat)
  imp : Array (Array Nat)
  bot : Nat
  top : Nat
  ok : Bool                    -- lattice + Heyting adjunction verified
deriving Inhabited

@[inline] def l2 (t : Array (Array Nat)) (i j : Nat) : Nat := (t[i]!)[j]!

/-- Build a (claimed) Heyting algebra from its order relation; `ok`
records the full adjunction check `z ≤ (x→y) ↔ z⊓x ≤ y` plus totality,
so a bogus `le` table cannot silently poison the zoo. -/
def mkAlg (name : String) (n : Nat) (le : Nat → Nat → Bool) : Alg :=
  let es := List.range n
  let theMax (l : List Nat) : Nat :=
    (l.find? (fun z => l.all (fun w => le w z))).getD 999
  let theMin (l : List Nat) : Nat :=
    (l.find? (fun z => l.all (fun w => le z w))).getD 999
  let mtf (x y : Nat) := theMax (es.filter (fun z => le z x && le z y))
  let jnf (x y : Nat) := theMin (es.filter (fun z => le x z && le y z))
  let imf (x y : Nat) := theMax (es.filter (fun z => le (mtf z x) y))
  let mt := (Array.range n).map fun x => (Array.range n).map fun y => mtf x y
  let jn := (Array.range n).map fun x => (Array.range n).map fun y => jnf x y
  let im := (Array.range n).map fun x => (Array.range n).map fun y => imf x y
  let bot := theMin es
  let top := theMax es
  let total := es.all fun x => es.all fun y =>
    l2 mt x y != 999 && l2 jn x y != 999 && l2 im x y != 999
  let adj := es.all fun z => es.all fun x => es.all fun y =>
    (le z (l2 im x y) == le (l2 mt z x) y)
  ⟨name, n, mt, jn, im, bot, top,
    total && adj && bot != 999 && top != 999⟩

def leChain (x y : Nat) : Bool := x ≤ y
def leDiam4 (x y : Nat) : Bool := x &&& y == x          -- Boolean 2×2
def leDiamT5 (x y : Nat) : Bool :=                       -- 0 < 1,2 < 3 < 4
  x == y || x == 0 || y == 4 || (x == 1 && y == 3) || (x == 2 && y == 3)
def leC32 (x y : Nat) : Bool :=                          -- chain3 × chain2
  (x / 2 ≤ y / 2) && (x % 2 ≤ y % 2)

def bases : List Alg :=
  [mkAlg "chain2" 2 leChain, mkAlg "chain3" 3 leChain,
   mkAlg "chain4" 4 leChain, mkAlg "diam4" 4 leDiam4,
   mkAlg "diamT5" 5 leDiamT5, mkAlg "c3xc2" 6 leC32]

/-! ### Nuclei: exhaustive enumeration -/

/-- Little-endian base-`n` digits of `k`, length `len`. -/
def digits (n len k : Nat) : Array Nat :=
  (Array.range len).map (fun i => k / n ^ i % n)

/-- Nucleus test: inflationary, idempotent, meet-preserving. -/
def isNucleus (A : Alg) (j : Array Nat) : Bool :=
  (List.range A.n).all (fun a =>
    l2 A.meet a (j[a]!) == a && j[(j[a]!)]! == j[a]!)
  && (List.range A.n).all (fun a => (List.range A.n).all (fun b =>
    j[(l2 A.meet a b)]! == l2 A.meet (j[a]!) (j[b]!)))

def nucleiOf (A : Alg) : List (Array Nat) :=
  ((List.range (A.n ^ A.n)).map (digits A.n A.n)).filter (isNucleus A)

def zooOf (as : List Alg) : List (Alg × Array Nat) :=
  as.flatMap fun A => (nucleiOf A).map (A, ·)

/-! ### Evaluation and the countermodel test -/

def aeval (A : Alg) (j : Array Nat) (v : String → Nat) : PLLFormula → Nat
  | .prop s => v s
  | .falsePLL => A.bot
  | .and X Y => l2 A.meet (aeval A j v X) (aeval A j v Y)
  | .or X Y => l2 A.join (aeval A j v X) (aeval A j v Y)
  | .ifThen X Y => l2 A.imp (aeval A j v X) (aeval A j v Y)
  | .somehow X => j[(aeval A j v X)]!

def vals (n : Nat) : List String → List (String → Nat)
  | [] => [fun _ => 0]
  | a :: as => (vals n as).flatMap fun v =>
      (List.range n).map fun x => fun s => if s = a then x else v s

/-- Over one (algebra, nucleus): (failures, tight points) for
`X1 ⊓ X2 ≤ Y`.  A failure is a countermodel point; a tight point has
`v(X1)⊓v(X2) = v(Y)` exactly (zero slack — the "closest" signal). -/
def checkPair (A : Alg) (j : Array Nat) (ats : List String)
    (X1 X2 Y : PLLFormula) : Nat × Nat :=
  (vals A.n ats).foldl (init := (0, 0)) fun (f, t) v =>
    let a := l2 A.meet (aeval A j v X1) (aeval A j v X2)
    let y := aeval A j v Y
    if l2 A.meet a y == a then (f, if a == y then t + 1 else t)
    else (f + 1, t)

/-- First failing point, with everything needed to reproduce it. -/
def firstWitness (zoo : List (Alg × Array Nat)) (ats : List String)
    (X1 X2 Y : PLLFormula) : Option String :=
  zoo.findSome? fun (A, j) =>
    (vals A.n ats).findSome? fun v =>
      let a := l2 A.meet (aeval A j v X1) (aeval A j v X2)
      let y := aeval A j v Y
      if l2 A.meet a y == a then none
      else some s!"alg={A.name} j={j.toList} v={ats.map (fun s => (s, v s))} lhs={a} rhs={y}"

/-! ### Instance driver -/

structure Cfg where
  name : String
  ctx : List PLLFormula
  spc : List PLLFormula
  g : PLLFormula
  bump : Nat := 0              -- c := defect·(J+2) + bump
  fhAbs : Option Nat := none   -- fh override (default fh = fuel)

/-- Size-gated run of one configuration against a zoo.  Sizes are
computed BEFORE any semantic pass; over-cap configurations are skipped
with their sizes reported. -/
def runCfg (zoo : List (Alg × Array Nat)) (cap : Nat) (cfg : Cfg) : String :=
  let S := cfg.spc.toFinset
  let d := defect S cfg.ctx
  let J := (jumpGoals' S).card
  if d == 0 then s!"{cfg.name}: BADCFG defect=0" else
  let c := d * (J + 2) + cfg.bump
  let W0 := ((cfg.ctx ++ cfg.spc ++ [cfg.g]).map weight).foldl max 0
  let fuel := (d + c + 2) * (W0 + 1) + W0 + 3
  let fh := cfg.fhAbs.getD fuel
  let X1 := itpE "p" S fuel (c + 1) cfg.ctx
  let X2 := itpA "p" S fh (c + 1) cfg.ctx cfg.g
  let Y := itpA "p" S fuel c cfg.ctx cfg.g
  let sz := fsize X1 + fsize X2 + fsize Y
  let hdr := s!"{cfg.name}: d={d} J={J} c={c} fuel={fuel} fh={fh} sz={sz}"
  -- degenerate: conclusion syntactically = the head hypothesis; the
  -- instance is trivially true, no countermodel possible — skip the zoo
  if X2 == Y then s!"DEGEN| {hdr}" else
  if sz > cap then s!"{hdr} SKIP-size" else
  let ats := (fatoms X1 ++ fatoms X2 ++ fatoms Y).eraseDups
  let pLeak := if ats.contains "p" then " P-LEAK!" else ""
  let res := zoo.map fun (A, j) => checkPair A j ats X1 X2 Y
  let fails := (res.map (·.1)).foldl (· + ·) 0
  let tights := (res.map (·.2)).foldl (· + ·) 0
  let pts := zoo.foldl (fun acc (A, _) => acc + A.n ^ ats.length) 0
  if fails == 0 then
    s!"{hdr} ats={ats} pts={pts} fails=0 tight={tights}{pLeak}"
  else
    s!"!!!COUNTERMODEL!!! {hdr} ats={ats} pts={pts} FAILS={fails} " ++
      s!"wit: {(firstWitness zoo ats X1 X2 Y).getD "?"} " ++
      s!"S={cfg.spc.map pf} G={cfg.ctx.map pf} g={pf cfg.g}{pLeak}"

/-- Sizes-only probe (the gate itself, for calibration). -/
def sizeCfg (cfg : Cfg) : String :=
  let S := cfg.spc.toFinset
  let d := defect S cfg.ctx
  let J := (jumpGoals' S).card
  let c := d * (J + 2) + cfg.bump
  let W0 := ((cfg.ctx ++ cfg.spc ++ [cfg.g]).map weight).foldl max 0
  let fuel := (d + c + 2) * (W0 + 1) + W0 + 3
  let fh := cfg.fhAbs.getD fuel
  let s1 := fsize (itpE "p" S fuel (c + 1) cfg.ctx)
  let s2 := fsize (itpA "p" S fh (c + 1) cfg.ctx cfg.g)
  let s3 := fsize (itpA "p" S fuel c cfg.ctx cfg.g)
  s!"{cfg.name}: d={d} J={J} c={c} fuel={fuel} sizes=({s1},{s2},{s3})"

def runBatch (tag : String) (zoo : List (Alg × Array Nat)) (cap : Nat)
    (cfgs : List Cfg) (quietDegen : Bool := false) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.println s!"=== {tag}: {cfgs.length} cfgs, zoo pairs={zoo.length} ==="
  let mut degens := 0
  for cfg in cfgs do
    let ti ← IO.monoMsNow
    let r := runCfg zoo cap cfg
    let tj ← IO.monoMsNow
    if quietDegen && r.startsWith "DEGEN|" then
      degens := degens + 1
    else
      IO.println s!"[{tj - ti}ms] {r}"
  let t1 ← IO.monoMsNow
  IO.println s!"=== {tag} done in {t1 - t0}ms, silent degens={degens} ==="

/-! ### Piece pool -/

private def pP := prop "p"
private def rP := prop "r"
private def sP := prop "s"
private def jpr := (pP.somehow).ifThen rP      -- ◯p⊃r
private def jrs := (rP.somehow).ifThen sP      -- ◯r⊃s
private def jrp := (rP.somehow).ifThen pP      -- ◯r⊃p (cycle through p)
private def iprs := (pP.ifThen rP).ifThen sP   -- (p⊃r)⊃s
private def iprr := (pP.ifThen rP).ifThen rP   -- (p⊃r)⊃r
private def g3f := (jpr.ifThen pP.somehow).somehow  -- ◯((◯p⊃r)⊃◯p)

end Refute3
end PLLND

/-! ## Phase 1 — sanity (RUN 2026-07-12, results):

* base algebras all `ok = true` (adjunction audit passed):
  chain2/2, chain3/3, chain4/4, diam4/4, diamT5/5, c3xc2/6.
* nuclei counts: chain2 2, chain3 4, chain4 8, diam4 4, diamT5 8,
  c3xc2 8 — TOTAL ZOO = 34 (algebra, nucleus) pairs.
* fuel-stabilization: itpE/itpA syntactically equal at (fuel, fuel+50)
  on both the J0-c2 and the canonical J2-c4 instances with
  fuel = (d+c+2)(W0+1)+W0+3 — (true,true,true)/(true,true,true).
* size ladder (fuel per the formula above):
  z-J0-c2 (3,3,3) · z-J0-c2-Og (3,22,22) · z-J1-c3 (3,3,3, clause dead)
  z-J2-c4 (66992,66988,10351) · z-J2-c4-Og (66992,299110,46273)
  z-gam-d2c4 (57,43,43) · z-J2-c5 bump1 (433103,433099,66988)
  z-g3-J2c4 (= canonical: the g3 member is dead with that S).
-/

open PLLND PLLND.Refute3 PLLFormula

/-! ## Phase 2 — curated battery at the exact floor, full 34-pair zoo.

Design notes: the countermodel surface needs budget-CONSULTING clauses
(the only places `c+1` vs `c` can differ): the ◯-imp jump pair
(`A.somehow⊃B ∈ S`, B ∈ S), the impImp jump (`(A⊃B)⊃D ∈ S`, `B⊃D ∈ Γ`),
the goal-imp with `C₁ ∈ Γ` (E at b'), ◯-goals (E at b' in γ/wrap), and
the γ-scan (◯x ∈ Γ, x ∈ S).  Configurations that fire none of these are
degenerate (X2 = Y) and get flagged. -/

section
-- canonical ◯-imp jump space: Γ=[◯p⊃r], S={◯p⊃r, r}, d=1 J=2 c=4
private def cA : List Cfg := [
  { name := "A-r",    ctx := [jpr], spc := [jpr, rP], g := rP },
  { name := "A-s",    ctx := [jpr], spc := [jpr, rP], g := sP },
  { name := "A-Op",   ctx := [jpr], spc := [jpr, rP], g := pP.somehow },
  { name := "A-Or",   ctx := [jpr], spc := [jpr, rP], g := rP.somehow },
  { name := "A-jpr>r", ctx := [jpr], spc := [jpr, rP], g := jpr.ifThen rP },
  { name := "A-s>r",  ctx := [jpr], spc := [jpr, rP], g := sP.ifThen rP },
  { name := "A-r>s",  ctx := [jpr], spc := [jpr, rP], g := rP.ifThen sP },
  { name := "A-OpAr", ctx := [jpr], spc := [jpr, rP], g := (pP.and rP).somehow },
  { name := "A-Or>p", ctx := [jpr], spc := [jpr, rP], g := rP.somehow.ifThen pP }
]

-- p-consequent twist: Γ=[◯p⊃r, ◯r⊃p], S={◯r⊃p, p}, d=1 J=2 c=4
private def cE : List Cfg := [
  { name := "E-r",    ctx := [jpr, jrp], spc := [jrp, pP], g := rP },
  { name := "E-p",    ctx := [jpr, jrp], spc := [jrp, pP], g := pP },
  { name := "E-Or",   ctx := [jpr, jrp], spc := [jrp, pP], g := rP.somehow },
  { name := "E-jrp>p", ctx := [jpr, jrp], spc := [jrp, pP], g := jrp.ifThen pP },
  { name := "E-s>r",  ctx := [jpr, jrp], spc := [jrp, pP], g := sP.ifThen rP },
  { name := "E1-r",   ctx := [jrp], spc := [jrp, pP], g := rP },
  { name := "E1-Or",  ctx := [jrp], spc := [jrp, pP], g := rP.somehow }
]

-- impImp jump LIVE: Γ=[(p⊃r)⊃s, r⊃s], S={(p⊃r)⊃s, s}, d=1 J=1 c=3
private def cC : List Cfg := [
  { name := "C-s",    ctx := [iprs, rP.ifThen sP], spc := [iprs, sP], g := sP },
  { name := "C-Os",   ctx := [iprs, rP.ifThen sP], spc := [iprs, sP], g := sP.somehow },
  { name := "C-p>r",  ctx := [iprs, rP.ifThen sP], spc := [iprs, sP], g := pP.ifThen rP },
  { name := "C-iprs>s", ctx := [iprs, rP.ifThen sP], spc := [iprs, sP],
    g := iprs.ifThen sP },
  { name := "C-r>s",  ctx := [iprs, rP.ifThen sP], spc := [iprs, sP], g := rP.ifThen sP },
  { name := "C-Op",   ctx := [iprs, rP.ifThen sP], spc := [iprs, sP], g := pP.somehow },
  -- (p⊃r)⊃r self-consequent variant
  { name := "C2-r",   ctx := [iprr, rP.ifThen rP], spc := [iprr, rP], g := rP },
  { name := "C2-Or",  ctx := [iprr, rP.ifThen rP], spc := [iprr, rP], g := rP.somehow }
]

-- γ-live small: Γ=[◯p⊃r, ◯p], S={◯p, ...} variants; d=1 J=2 c=4
private def cD : List Cfg := [
  { name := "D-p",    ctx := [jpr, pP.somehow], spc := [jpr, pP], g := rP },
  { name := "D-Or",   ctx := [jpr, pP.somehow], spc := [jpr, pP], g := rP.somehow },
  { name := "D2-r",   ctx := [jpr, pP.somehow], spc := [rP, pP], g := rP },
  { name := "D2-Or",  ctx := [jpr, pP.somehow], spc := [rP, pP], g := rP.somehow },
  { name := "D2-s>r", ctx := [jpr, pP.somehow], spc := [rP, pP], g := sP.ifThen rP }
]

-- fh-variants on the canonical (fh < mu: truncated head hypothesis)
private def cF : List Cfg := [
  { name := "F-fh6",  ctx := [jpr], spc := [jpr, rP], g := rP, fhAbs := some 6 },
  { name := "F-fh12", ctx := [jpr], spc := [jpr, rP], g := rP.somehow,
    fhAbs := some 12 },
  { name := "F-fh1",  ctx := [jpr], spc := [jpr, rP], g := rP, fhAbs := some 1 }
]

/- P2 RUN (2026-07-12, full 34-pair zoo, cap 500k) — ALL fails=0:
  A: r/s/Op/Or/s>r/r>s ran (sz 144k–412k, pts 152–724, tight 98–570);
     jpr>r (2.13M), OpAr (721k), Or>p (803k) SKIP-size → Phase 3.
  E (p-consequent, Γ=[◯p⊃r,◯r⊃p], S={◯r⊃p,p}): all fails=0, ALL
     tight=pts (lemma holds with zero slack everywhere!); jrp>p 2.27M skip.
  C (impImp live jump): all fails=0 (sz 5.9k–47k).
  D (γ-only): every config DEGEN(X2=Y) — at floor ≤ 4 the γ-scan fires
     but nothing consults b; γ+jump combined needs S ⊇ {◯p⊃r,r,p},
     d=2 J=2 → floor 8 (Phase 3 probes its size).
  F (fh < mu: 1/6/12 on canonical): fails=0.
  Total wall ≈ 172 s. -/
set_option linter.unusedVariables false in
/-- keep the P2 batteries elaborated (rerun by pasting into an #eval):
`runBatch "P2" (zooOf bases) 500000 (cA ++ cE ++ cC ++ cD ++ cF)` -/
private def p2all : List Cfg := cA ++ cE ++ cC ++ cD ++ cF
end

/-! ## Phase 3 — harness positive control; the size-skipped configs at a
reduced zoo; the γ+jump floor-8 configuration. -/

section
-- 3a. positive control: ◯r ⊬ r — the harness MUST find failures here
#eval ((zooOf bases).map fun (A, j) =>
    (checkPair A j ["r"] truePLL (rP.somehow) rP).1).foldl (· + ·) 0

-- 3b. the four size-skipped configs, chains+diam4 zoo (10 pairs), cap 2.5M
private def zooMid : List (Alg × Array Nat) :=
  zooOf [mkAlg "chain2" 2 leChain, mkAlg "chain3" 3 leChain,
         mkAlg "chain4" 4 leChain, mkAlg "diam4" 4 leDiam4]

private def zooC23 : List (Alg × Array Nat) :=
  zooOf [mkAlg "chain2" 2 leChain, mkAlg "chain3" 3 leChain]

-- the size-skipped ◯-band configs (◯-imp in S, b-consulting imp goals)
-- plus the never-zoo'd budget-ladder step c = floor+1
private def cBig : List Cfg := [
  { name := "B-jpr>r", ctx := [jpr], spc := [jpr, rP], g := jpr.ifThen rP },
  { name := "B-jrp>p", ctx := [jpr, jrp], spc := [jrp, pP], g := jrp.ifThen pP },
  { name := "B-r-c5",  ctx := [jpr], spc := [jpr, rP], g := rP, bump := 1 },
  { name := "B-Op-c5", ctx := [jpr], spc := [jpr, rP], g := pP.somehow, bump := 1 }
]

/- 3c RESULT (2026-07-12): γ+jump combined — S={◯p⊃r,r,p}, Γ=[◯p⊃r,◯p],
d=2 J=2 floor=8, b=9, the seal-crossing shape.  The graduated
partial-fuel fsize probe (fuel 8 of the ~64 needed) ran >20 min without
returning and was killed: the value passes the ~30M-node horizon at an
eighth of the required fuel.  Every γ+jump-combined instance (the floor
forces c ≥ 8 there) is beyond the evaluable-size horizon — SKIP-horizon,
matching the docstring's expectation that seal-crossing chains are the
expensive band. -/
end

/-! ## Phase 4 — mechanical breadth sweep: spaces = sublists of the
piece closure, defect ∈ {1,2}, floor ≤ 4, ≤ 3 members; goals from the
antecedent/consequent pool; chains+diam4 zoo.  Degenerates short-circuit. -/

namespace PLLND.Refute3

def subsOf : PLLFormula → List PLLFormula
  | .prop s => [.prop s]
  | .falsePLL => [.falsePLL]
  | .and A B => .and A B :: (subsOf A ++ subsOf B)
  | .or A B => .or A B :: (subsOf A ++ subsOf B)
  | .ifThen A B => .ifThen A B :: (subsOf A ++ subsOf B)
  | .somehow A => .somehow A :: subsOf A

/-- Subformulas plus the G4-style `B⊃D` pieces of impImp members. -/
def closureOf (Γ : List PLLFormula) : List PLLFormula :=
  let s := (Γ.flatMap subsOf).eraseDups
  (s ++ s.filterMap (fun F => match F with
    | .ifThen (.ifThen _ B) D => some (B.ifThen D)
    | _ => none)).eraseDups

def subls : List α → List (List α)
  | [] => [[]]
  | a :: as => (subls as).flatMap (fun s => [s, a :: s])

/-- All configurations for one context: spaces from the closure with
`1 ≤ defect ≤ 2`, room floor ≤ `floorCap`, at most `maxCard` members. -/
def sweepCfgs (nm : String) (Γ : List PLLFormula) (goals : List PLLFormula)
    (maxCard floorCap : Nat) : List Cfg :=
  ((subls (closureOf Γ)).filter fun sl =>
    sl.length ≤ maxCard &&
    (let S := sl.toFinset
     let d := defect S Γ
     1 ≤ d && d ≤ 2 && d * ((jumpGoals' S).card + 2) ≤ floorCap))
  |>.flatMap fun sl =>
    goals.map fun g =>
      { name := s!"{nm}|S={sl.map pf}|g={pf g}", ctx := Γ, spc := sl, g := g }

def sweepGoals : List PLLFormula :=
  [rP, rP.somehow, pP.somehow, sP.ifThen rP]

/-- ◯-band-weighted sweep families (`cascade_low_pos_box` emphasis:
◯-implications in Γ, ◯-members, ◯-shaped goals; s6 is the in-band
non-⊃-closed impImp control). -/
def sweepAll : List Cfg :=
  sweepCfgs "s1" [jpr] sweepGoals 3 4
  ++ sweepCfgs "s2" [jrp] sweepGoals 3 4
  ++ sweepCfgs "s5" [jpr, pP.somehow] sweepGoals 3 4
  ++ sweepCfgs "s6" [iprs, rP.ifThen sP] sweepGoals 3 4
  ++ sweepCfgs "s7" [jpr, jrp] sweepGoals 3 4
  ++ sweepCfgs "s8" [g3f, jpr] sweepGoals 3 4

/-- Kernel-grade spot check: `search` (G4c-complete via `G4c_iff_search`
at sufficient fuel; sound at ANY fuel via `search_sound`) pointed at the
instance sequent [X1, X2] ⊢ Y.  `true` confirms the instance; `false`
at pragmatic fuel decides nothing. -/
def deciderCheck (cfg : Cfg) (sfuel : Nat) : IO Unit := do
  let S := cfg.spc.toFinset
  let d := defect S cfg.ctx
  let J := (jumpGoals' S).card
  let c := d * (J + 2) + cfg.bump
  let W0 := ((cfg.ctx ++ cfg.spc ++ [cfg.g]).map weight).foldl max 0
  let fuel := (d + c + 2) * (W0 + 1) + W0 + 3
  let fh := cfg.fhAbs.getD fuel
  let X1 := itpE "p" S fuel (c + 1) cfg.ctx
  let X2 := itpA "p" S fh (c + 1) cfg.ctx cfg.g
  let Y := itpA "p" S fuel c cfg.ctx cfg.g
  let W := ([X1, X2, Y].map weight).foldl max 0
  let ats := ((fatoms X1 ++ fatoms X2 ++ fatoms Y).eraseDups).toFinset
  let t0 ← IO.monoMsNow
  let r := search W ats sfuel ∅ [X1, X2] Y
  let t1 ← IO.monoMsNow
  IO.println s!"{cfg.name}: W={W} search-fuel={sfuel} → {r} [{t1 - t0}ms]"

end PLLND.Refute3

/- RUN-A RESULTS (2026-07-12, chains zoo = 6 pairs):
  * positive control (◯r ⊬ r over the FULL 34-pair zoo): 66 failure
    points — the harness finds countermodels when they exist.
  * sweepAll.length = 416.
  * P3-big: B-jpr>r sz 2.13M fails=0 tight 12/16 · B-jrp>p sz 2.27M
    fails=0 tight 16/16 · B-r-c5 (c=floor+1) sz 933k fails=0 16/16 ·
    B-Op-c5 sz 2.67M fails=0 12/16.  19.4 s.
  * P4-sweep: 416 cfgs = 376 DEGEN (b never consulted; short-circuit
    proves instance trivially true) + 24 SKIP-size at cap 200k (all but
    one identical to P2-zoo'd values; the one new point runs in RUN-B)
    + 16 zoo'd — ALL fails=0 (s6 impImp family tight 30-32/44; the
    J2 families tight 16/16).  5.5 s. -/

-- RUN-B: the one sweep point size-skipped and not P2-covered
-- (Γ=[◯r⊃p], S={◯r⊃p, p}, g=◯p) — own #eval so its result flushes
#eval show IO Unit from do
  runBatch "P5-gap (chains)" zooC23 600000
    [{ name := "G-jrp-Op", ctx := [jrp], spc := [jrp, pP], g := pP.somehow },
     { name := "G-jrp2-Op", ctx := [jpr, jrp], spc := [jrp, pP], g := pP.somehow }]

/- decider note: fuel 10 on the 5.9k-node C-s instance ran >12 min
(search re-scans `InSpace` over every context member per node;
branching^fuel explodes) and was killed — consistent with HANDOFF.md's
"kernel decider infeasible" warning.  One shrunk attempt at fuel 6: -/
#eval show IO Unit from do
  IO.println "--- decider spot-check (search; true = kernel confirmation) ---"
  -- dc1 (C-s) @8 → TRUE (kernel-grade); @6 false; @10 hung >12 min.
  -- dc2 (C-s>r) @8 ran >3.5 min pre-restart without returning: infeasible.
  let dc3 : Cfg :=
    { name := "C2-r", ctx := [iprr, rP.ifThen rP], spc := [iprr, rP], g := rP }
  deciderCheck dc3 8

-- ◯-band decider attempt: ◯-shaped goal on the in-band impImp family
#eval show IO Unit from do
  let dcO : Cfg :=
    { name := "C2-Or", ctx := [iprr, rP.ifThen rP], spc := [iprr, rP],
      g := rP.somehow }
  deciderCheck dcO 7
