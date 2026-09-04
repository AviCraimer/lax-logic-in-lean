import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLG4Dec

/-!
# refute4 — zoo adjudication of the GUARDED/CONSUMED reshaping laws
# for the `cascade_low_pos_box` seals (2026-07-12, task #14)

Probe file, not a proof.  Context: the g4ill_ui task-#13 result showed
consumed-form glue (`guardMP`) admissible exactly where retained forms
fail, and Pitts' guarded `L4→` clause provable where Iemhoff's
unguarded one needs cut.  Transfer hypothesis: restate the four seal
crossings of the cascade in guarded/consumed style.  Before any proof
attempt, each candidate law is adjudicated here on the 34-pair
exhaustive-nuclei zoo (harness copied verbatim from `wip/refute3.lean`).

Laws under adjudication (indices follow the v3 tables: the ◯-goal
disjunct of `A@(f+1,b,Γ,◯D)` is `◯(E@(f,b−1) ⇢ A@(f,b,Γ,D))`; the
γ-head of the ◯-imp clause is `◯(E@(f,b−1) ⇢ A@(f,b−1,Γ,◯A))`):

* Z1(c) — the BARE below-floor descent `E@(c+1) ⊓ A@(c+1) ≤ A@c` at
  absolute `c = 0,1,2,…` ignoring the floor `defect·(J+2) ≤ c`.  The
  exact semantic threshold decides whether any ledger-free (fuel-only)
  induction could exist: the value-form chains are forced through
  `c−1, c−2, …`, so a FALSE point at some `c₀` blocks every proof
  whose chain can reach `c₀`.
* Z2a/Z2b — re-guarding a sealed box one budget down,
  `◯(E@c ⇢ Z) ≤ ◯(E@(c−1) ⇢ Z)`, without (Z2a) and with (Z2b) the
  ambient `E@(c+1)` outside the box.  Predicted: Z2a fails (the guard
  ascent inside the box is the hard direction), Z2b holds and is
  provable outright (laxL keeps the context, so the ambient re-imports
  and fires the old guard) — the (A)-family survivor.
* Z3/Z7 — the ◯-goal and γ-head seal crossings stated as one-formula
  laws (source disjunct + ambient ≤ target disjunct).  These are the
  sealed obligations themselves; expected true (the holdout is
  zoo-true) and tight — run to confirm the reduction is faithful.
* Z5 — the fresh-antecedent guarded ascent
  `E@(c+1)(Γ) ⊓ E@c(C₁::Γ) ≤ E@(c+1)(C₁::Γ)`, `C₁ ∉ S ∪ Γ`: the
  grown-context ambient the fresh seal would need, with the grown
  guard assisting.  If false, the rebuild trick at that seal was
  forced; if true, a guarded-interface variant could kill the fresh
  seal (the one with no decreasing measure).
* Z6 — Z1 with the target-level guard `E@(c−1)(Γ)` added on the left.
  Budget-mono makes the guard redundant under the same-`Γ` ambient
  (`E@(c+1) ⊢ E@(c−1)` pointwise), so Z6 must agree with Z1 point for
  point; run as a harness sanity check and to machine-verify the
  redundancy claim on the failing band.
-/

open PLLFormula

namespace PLLND
namespace Refute4

/-! ### Harness (verbatim from refute3) -/

def fsize : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and A B => fsize A + fsize B + 1
  | .or A B => fsize A + fsize B + 1
  | .ifThen A B => fsize A + fsize B + 1
  | .somehow A => fsize A + 1

def fatoms (F : PLLFormula) : List String :=
  (go F).eraseDups
where go : PLLFormula → List String
  | .prop s => [s]
  | .falsePLL => []
  | .and A B => go A ++ go B
  | .or A B => go A ++ go B
  | .ifThen A B => go A ++ go B
  | .somehow A => go A

def pf : PLLFormula → String
  | .prop s => s
  | .falsePLL => "F"
  | .and A B => "(" ++ pf A ++ "&" ++ pf B ++ ")"
  | .or A B => "(" ++ pf A ++ "|" ++ pf B ++ ")"
  | .ifThen A B => "(" ++ pf A ++ ">" ++ pf B ++ ")"
  | .somehow A => "O" ++ pf A

def jumpGoals' (S : Finset PLLFormula) : Finset PLLFormula :=
  S.biUnion (fun F => match F with
    | .ifThen (.ifThen A B) _ => {A.ifThen B}
    | .ifThen (.somehow A) _ => {A, A.somehow}
    | _ => ∅)

structure Alg where
  name : String
  n : Nat
  meet : Array (Array Nat)
  join : Array (Array Nat)
  imp : Array (Array Nat)
  bot : Nat
  top : Nat
  ok : Bool
deriving Inhabited

@[inline] def l2 (t : Array (Array Nat)) (i j : Nat) : Nat := (t[i]!)[j]!

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
def leDiam4 (x y : Nat) : Bool := x &&& y == x
def leDiamT5 (x y : Nat) : Bool :=
  x == y || x == 0 || y == 4 || (x == 1 && y == 3) || (x == 2 && y == 3)
def leC32 (x y : Nat) : Bool :=
  (x / 2 ≤ y / 2) && (x % 2 ≤ y % 2)

def bases : List Alg :=
  [mkAlg "chain2" 2 leChain, mkAlg "chain3" 3 leChain,
   mkAlg "chain4" 4 leChain, mkAlg "diam4" 4 leDiam4,
   mkAlg "diamT5" 5 leDiamT5, mkAlg "c3xc2" 6 leC32]

def digits (n len k : Nat) : Array Nat :=
  (Array.range len).map (fun i => k / n ^ i % n)

def isNucleus (A : Alg) (j : Array Nat) : Bool :=
  (List.range A.n).all (fun a =>
    l2 A.meet a (j[a]!) == a && j[(j[a]!)]! == j[a]!)
  && (List.range A.n).all (fun a => (List.range A.n).all (fun b =>
    j[(l2 A.meet a b)]! == l2 A.meet (j[a]!) (j[b]!)))

def nucleiOf (A : Alg) : List (Array Nat) :=
  ((List.range (A.n ^ A.n)).map (digits A.n A.n)).filter (isNucleus A)

def zooOf (as : List Alg) : List (Alg × Array Nat) :=
  as.flatMap fun A => (nucleiOf A).map (A, ·)

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

def checkPair (A : Alg) (j : Array Nat) (ats : List String)
    (X1 X2 Y : PLLFormula) : Nat × Nat :=
  (vals A.n ats).foldl (init := (0, 0)) fun (f, t) v =>
    let a := l2 A.meet (aeval A j v X1) (aeval A j v X2)
    let y := aeval A j v Y
    if l2 A.meet a y == a then (f, if a == y then t + 1 else t)
    else (f + 1, t)

def firstWitness (zoo : List (Alg × Array Nat)) (ats : List String)
    (X1 X2 Y : PLLFormula) : Option String :=
  zoo.findSome? fun (A, j) =>
    (vals A.n ats).findSome? fun v =>
      let a := l2 A.meet (aeval A j v X1) (aeval A j v X2)
      let y := aeval A j v Y
      if l2 A.meet a y == a then none
      else some s!"alg={A.name} j={j.toList} v={ats.map (fun s => (s, v s))} lhs={a} rhs={y}"

/-! ### Generic law driver: named (X1, X2, Y) triples, size-gated -/

structure Law where
  name : String
  X1 : PLLFormula
  X2 : PLLFormula
  Y  : PLLFormula

def runLaw (zoo : List (Alg × Array Nat)) (cap : Nat) (L : Law) : String :=
  let sz := fsize L.X1 + fsize L.X2 + fsize L.Y
  let hdr := s!"{L.name}: sz={sz}"
  if L.X2 == L.Y then s!"DEGEN| {hdr}" else
  if sz > cap then s!"{hdr} SKIP-size" else
  let ats := (fatoms L.X1 ++ fatoms L.X2 ++ fatoms L.Y).eraseDups
  let pLeak := if ats.contains "p" then " P-LEAK!" else ""
  let res := zoo.map fun (A, j) => checkPair A j ats L.X1 L.X2 L.Y
  let fails := (res.map (·.1)).foldl (· + ·) 0
  let tights := (res.map (·.2)).foldl (· + ·) 0
  let pts := zoo.foldl (fun acc (A, _) => acc + A.n ^ ats.length) 0
  if fails == 0 then
    s!"{hdr} ats={ats} pts={pts} fails=0 tight={tights}{pLeak}"
  else
    s!"FAILS {hdr} ats={ats} pts={pts} FAILS={fails} " ++
      s!"wit: {(firstWitness zoo ats L.X1 L.X2 L.Y).getD "?"}{pLeak}"

def runLaws (tag : String) (zoo : List (Alg × Array Nat)) (cap : Nat)
    (ls : List Law) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.println s!"=== {tag}: {ls.length} laws, zoo pairs={zoo.length} ==="
  for L in ls do
    let ti ← IO.monoMsNow
    let r := runLaw zoo cap L
    let tj ← IO.monoMsNow
    IO.println s!"[{tj - ti}ms] {r}"
  let t1 ← IO.monoMsNow
  IO.println s!"=== {tag} done in {t1 - t0}ms ==="

/-! ### Configurations (the refute3 adversarial band) -/

private def pP := prop "p"
private def rP := prop "r"
private def sP := prop "s"
private def uP := prop "u"
private def jpr := (pP.somehow).ifThen rP      -- ◯p⊃r
private def jrp := (rP.somehow).ifThen pP      -- ◯r⊃p
private def iprs := (pP.ifThen rP).ifThen sP   -- (p⊃r)⊃s

/-- Canonical ◯-imp jump space: `Γ=[◯p⊃r]`, `S={◯p⊃r,r}`, d=1 J=2
floor=4.  Spaces are kept as lists (Finset.toList is noncomputable);
constructors take the list and finsetize internally. -/
private def SA : List PLLFormula := [jpr, rP]
private def GA : List PLLFormula := [jpr]

/-- p-consequent twist: `Γ=[◯p⊃r,◯r⊃p]`, `S={◯r⊃p,p}`, d=1 J=2 floor=4. -/
private def SE : List PLLFormula := [jrp, pP]
private def GE : List PLLFormula := [jpr, jrp]

/-- impImp jump live: `Γ=[(p⊃r)⊃s, r⊃s]`, `S={(p⊃r)⊃s,s}`, d=1 J=1
floor=3. -/
private def SC : List PLLFormula := [iprs, sP]
private def GC : List PLLFormula := [iprs, rP.ifThen sP]

/-- Uniform big fuel for a config (their stabilized formula at the
largest budget probed, `cmax`); the space is passed as a list so the
weight fold stays computable. -/
private def fuelFor (Sl : List PLLFormula) (Γ : List PLLFormula)
    (g : PLLFormula) (cmax : Nat) : Nat :=
  let W0 := ((Γ ++ [g]).map weight ++ (Sl.map weight)).foldl max 0
  (defect Sl.toFinset Γ + cmax + 2) * (W0 + 1) + W0 + 3

/-! #### Z1 — bare descent at absolute budgets (below and at floor) -/

private def z1 (nm : String) (Sl : List PLLFormula) (Γ : List PLLFormula)
    (g : PLLFormula) (cmax : Nat) (c : Nat) : Law :=
  let S := Sl.toFinset
  let fuel := fuelFor Sl Γ g cmax
  { name := s!"Z1-{nm}-c{c}"
    X1 := itpE "p" S fuel (c + 1) Γ
    X2 := itpA "p" S fuel (c + 1) Γ g
    Y  := itpA "p" S fuel c Γ g }

/-! #### Z6 — Z1 plus the (redundant) target-level guard -/

private def z6 (nm : String) (Sl : List PLLFormula) (Γ : List PLLFormula)
    (g : PLLFormula) (cmax : Nat) (c : Nat) : Law :=
  let S := Sl.toFinset
  let fuel := fuelFor Sl Γ g cmax
  { name := s!"Z6-{nm}-c{c}"
    X1 := (itpE "p" S fuel (c + 1) Γ).and (itpE "p" S fuel (c - 1) Γ)
    X2 := itpA "p" S fuel (c + 1) Γ g
    Y  := itpA "p" S fuel c Γ g }

/-! #### Z2a/Z2b — re-guarding a sealed box one budget down -/

private def z2 (nm : String) (amb : Bool) (Sl : List PLLFormula)
    (Γ : List PLLFormula) (D : PLLFormula) (cmax : Nat) (c : Nat) : Law :=
  let S := Sl.toFinset
  let fuel := fuelFor Sl Γ D.somehow cmax
  let inner := itpA "p" S (fuel - 1) (c + 1) Γ D
  { name := s!"Z2{if amb then "b" else "a"}-{nm}-c{c}"
    X1 := if amb then itpE "p" S fuel (c + 1) Γ else truePLL
    X2 := ((itpE "p" S (fuel - 1) c Γ).ifThen inner).somehow
    Y  := ((itpE "p" S (fuel - 1) (c - 1) Γ).ifThen inner).somehow }

/-! #### Z3 — the ◯-goal seal crossing as a law (source disjunct of
`A@(F+1,c+1,Γ,◯D)` + ambient ≤ target disjunct of `A@(fl+1,c,Γ,◯D)`) -/

private def z3 (nm : String) (Sl : List PLLFormula) (Γ : List PLLFormula)
    (D : PLLFormula) (cmax : Nat) (c : Nat) : Law :=
  let S := Sl.toFinset
  let fuel := fuelFor Sl Γ D.somehow cmax
  { name := s!"Z3-{nm}-c{c}"
    X1 := itpE "p" S fuel (c + 1) Γ
    X2 := ((itpE "p" S (fuel - 1) c Γ).ifThen
            (itpA "p" S (fuel - 1) (c + 1) Γ D)).somehow
    Y  := ((itpE "p" S (fuel - 1) (c - 1) Γ).ifThen
            (itpA "p" S (fuel - 1) c Γ D)).somehow }

/-! #### Z7 — the γ-head seal crossing as a law (both components one
budget down: `◯(E@c ⇢ A@c(Γ,◯A))` + ambient ≤ `◯(E@(c−1) ⇢ A@(c−1)(Γ,◯A))`) -/

private def z7 (nm : String) (Sl : List PLLFormula) (Γ : List PLLFormula)
    (A : PLLFormula) (cmax : Nat) (c : Nat) : Law :=
  let S := Sl.toFinset
  let fuel := fuelFor Sl Γ A.somehow cmax
  { name := s!"Z7-{nm}-c{c}"
    X1 := itpE "p" S fuel (c + 1) Γ
    X2 := ((itpE "p" S (fuel - 1) c Γ).ifThen
            (itpA "p" S (fuel - 1) c Γ A.somehow)).somehow
    Y  := ((itpE "p" S (fuel - 1) (c - 1) Γ).ifThen
            (itpA "p" S (fuel - 1) (c - 1) Γ A.somehow)).somehow }

/-! #### Z5 — fresh-antecedent guarded E-ascent at the grown context -/

private def z5 (nm : String) (Sl : List PLLFormula) (Γ : List PLLFormula)
    (C₁ : PLLFormula) (cmax : Nat) (c : Nat) : Law :=
  let S := Sl.toFinset
  let fuel := fuelFor Sl Γ C₁ cmax
  { name := s!"Z5-{nm}-c{c}"
    X1 := itpE "p" S fuel (c + 1) Γ
    X2 := itpE "p" S (fuel - 1) c (C₁ :: Γ)
    Y  := itpE "p" S (fuel - 1) (c + 1) (C₁ :: Γ) }

end Refute4
end PLLND

open PLLND PLLND.Refute4 PLLFormula

/-! ## Phase 0 — size calibration (no zoo): every law instance, sizes only. -/

section
private def rP' := prop "r"
private def pP' := prop "p"
private def sP' := prop "s"
private def uP' := prop "u"
private def jpr' := (pP'.somehow).ifThen rP'
private def jrp' := (rP'.somehow).ifThen pP'
private def iprs' := (pP'.ifThen rP').ifThen sP'
private def SA' : List PLLFormula := [jpr', rP']
private def GA' : List PLLFormula := [jpr']
private def SE' : List PLLFormula := [jrp', pP']
private def GE' : List PLLFormula := [jpr', jrp']
private def SC' : List PLLFormula := [iprs', sP']
private def GC' : List PLLFormula := [iprs', rP'.ifThen sP']

private def z1A : List Law :=
  (List.range 6).map (fun c => z1 "A-r" SA' GA' rP' 5 c)
private def z1AOp : List Law :=
  (List.range 6).map (fun c => z1 "A-Op" SA' GA' (pP'.somehow) 5 c)
private def z1E : List Law :=
  (List.range 6).map (fun c => z1 "E-r" SE' GE' rP' 5 c)
private def z1C : List Law :=
  (List.range 5).map (fun c => z1 "C-s" SC' GC' sP' 4 c)

#eval show IO Unit from do
  for L in z1A ++ z1AOp ++ z1E ++ z1C do
    IO.println s!"{L.name}: sz={fsize L.X1 + fsize L.X2 + fsize L.Y}"

/- Phase-0 RESULT (2026-07-12): sizes tiny below the floor, largest
c5 instance 2.67M (A-Op) — everything within the 30M gate; the
below-floor band (c ≤ 3) is ≤ 64k per law. -/

/-! ## Phase 1 — harness sanity: bases audited, positive control. -/

#eval (bases.map fun A => (A.name, A.ok), (zooOf bases).length)

-- ◯r ⊬ r: the harness MUST report failures
#eval ((zooOf bases).map fun (A, j) =>
    (checkPair A j ["r"] truePLL ((prop "r").somehow) (prop "r")).1).foldl
  (· + ·) 0

/-! ## Phase 2a — Z1: the bare descent at absolute budgets c = 0..4
(floor is 4 for A/E, 3 for C).  The BELOW-floor points are the new
content: a failure at c₀ blocks every value-form chain that reaches
c₀; the exact threshold profile decides whether a ledger-free
fuel-only induction could exist. -/

set_option linter.unusedVariables false in
/-- P2a battery (rerun: `runLaws "P2a-Z1" (zooOf bases) 600000 p2aAll`). -/
private def p2aAll : List Law :=
  (List.range 5).map (fun c => z1 "A-r" SA' GA' rP' 5 c)
   ++ (List.range 5).map (fun c => z1 "A-Op" SA' GA' (pP'.somehow) 5 c)
   ++ (List.range 5).map (fun c => z1 "E-r" SE' GE' rP' 5 c)
   ++ (List.range 4).map (fun c => z1 "C-s" SC' GC' sP' 4 c)

/- P2a RESULT (2026-07-12, 17.9s): FAILS at exactly ONE point —
Z1-A-Op-c0 (68 countermodel points; wit chain2, const-⊤ nucleus,
v(r)=1): at target budget 0 the ◯-goal table is empty (goal clause and
truncation both b-gated), so A@0(Γ,◯p) = ⊥ while E@1 ⊓ A@1 > ⊥.
EVERYTHING ELSE fails=0 — including the whole below-floor band
c = 1..3 (floor 4/3), with tight=pts (exact equality) at the r/s
goals and slack only at the ◯-goal (tight 98/152).  The bare
semantic threshold on defect-1 configs is c ≥ 1, NOT the ledger
floor — the ledger is a proof artifact, but chains through jump
goals do reach the genuinely-false (◯-goal, c=0) point. -/

/-! ## Phase 2b — Z1 at defect 2 with the jump clause live: does the
truth band scale with the defect (floor 8 here) or stay at c ≥ 1?
Also the eliminated-atom jump-goal instances (g = p: chains visit
them; values stay p-free). -/

section
private def S2A : List PLLFormula := [jpr', rP', sP']   -- d=2 J=2 floor=8
private def G2A : List PLLFormula := [jpr']

set_option linter.unusedVariables false in
/-- P2b battery (rerun: `runLaws "P2b-Z1-d2" (zooOf bases) 3000000 p2bAll`). -/
private def p2bAll : List Law :=
  (List.range 6).map (fun c => z1 "d2-r" S2A G2A rP' 6 c)
   ++ (List.range 6).map (fun c => z1 "d2-Op" S2A G2A (pP'.somehow) 6 c)
   ++ (List.range 5).map (fun c => z1 "A-p" SA' GA' pP' 5 c)
end

/- P2b RESULT (2026-07-12, 92s): the unreachable-piece d2 config has
IDENTICAL tables to d1 (sizes equal — `s ∈ S` unreachable from Γ
changes only the ledger, floor 8), and Z1 passes from c = 1 up: the
defect-scaled floor is pure proof artifact there.  The only failure
is again (◯-goal, c=0).  The eliminated-atom jump goal (g = p) is
degenerate: p-goals vanish at gated tables (X2 semantically ⊥),
fails=0 tight=pts at every c including 0. -/

/-! ## Phase 2c — Z1 at REACHABLE defect 2 (chained jumps
`S={◯p⊃r,r,◯r⊃s,s}`, `Γ=[◯p⊃r,◯r⊃s]`, J=4 floor=12) and at the
shared-consequent worst case (`S={◯p⊃r,◯p₂⊃r,r}`, J=4 floor=6, the
shape whose live-jump count exceeds every defect bound).  All probed
budgets are BELOW the respective floors. -/

section
private def jrs' := (rP'.somehow).ifThen sP'
private def p2P := prop "p2"
private def jp2r := (p2P.somehow).ifThen rP'
private def S2C : List PLLFormula := [jpr', rP', jrs', sP']  -- d=2 J=4 floor=12
private def G2C : List PLLFormula := [jpr', jrs']
private def SSH : List PLLFormula := [jpr', jp2r, rP']       -- d=1 J=4 floor=6
private def GSH : List PLLFormula := [jpr', jp2r]

set_option linter.unusedVariables false in
/-- P2c batteries (rerun: `runLaws "P2c" (zooOf bases) 3000000 p2cAll`;
the d2c c=3 instances cost ~13 min wall). -/
private def p2cAll : List Law :=
  (List.range 4).map (fun c => z1 "d2c-s" S2C G2C sP' 4 c)
   ++ (List.range 4).map (fun c => z1 "d2c-r" S2C G2C rP' 4 c)
   ++ (List.range 4).map (fun c => z1 "d2c-Op" S2C G2C (pP'.somehow) 4 c)
   ++ (List.range 4).map (fun c => z1 "sh-r" SSH GSH rP' 4 c)
   ++ (List.range 4).map (fun c => z1 "sh-Op" SSH GSH (pP'.somehow) 4 c)

/- P2c RESULT (2026-07-12, 809s + 129s, full 34-pair zoo):
* d2chain (S={◯p⊃r,r,◯r⊃s,s}, Γ=[◯p⊃r,◯r⊃s], d=2 J=4 floor=12):
  s-goals c=1..3 fails=0 tight=570/724; r-goals c=0..3 fails=0
  tight=402; ◯p-goal: FAILS at c=0 only (216 pts, wit chain2
  const-⊤ nucleus v(r)=v(s)=1), c=1..2 fails=0 tight=242 (c3 8.3M
  SKIP-size).
* shared-consequent (S={◯p⊃r,◯p₂⊃r,r}, d=1 J=4 floor=6): r-goals
  c=0..3 fails=0 tight=ALL 724 (zero slack everywhere); ◯p-goal
  FAILS at c=0 only (334 pts), c=1..3 fails=0 tight=337.
THE PATTERN ACROSS EVERY CONFIG (d ∈ {1,2}, J ∈ {1,2,4}, chained and
shared jumps): the bare descent law holds at EVERY probed c ≥ 1 —
the defect-scaled floor is invisible to the semantics — and fails at
exactly the structural point (◯-shaped goal, c = 0), where the
target table is empty (goal clause and truncation both b-gated:
A@0(Γ,◯D) = ⊥).  The floor hypothesis is a pure artifact of the
pigeonhole ledger; the semantic threshold is the constant 1. -/
end

/-! ## Phase 3 — Z6: the target-level guard is redundant under the
same-Γ ambient (budget-mono `E@(c+1) ⊢ E@(c−1)` pointwise);
machine-check the redundancy AT the unique failing point (◯-goal,
c=0) — Z6 must fail there too, or the domination argument is wrong. -/

#eval runLaws "P3-Z6" (zooOf bases) 600000
  [z6 "A-Op" SA' GA' (pP'.somehow) 5 0,
   z6 "A-Op" SA' GA' (pP'.somehow) 5 1,
   z6 "A-r" SA' GA' rP' 5 0]

/- P3 RESULT (2026-07-12): Z6-A-Op-c0 FAILS with the SAME 68 points
and witness as Z1-A-Op-c0 (chain2, const-⊤ nucleus, v(r)=1); c1 and
the r-goal pass exactly as Z1.  The target-level guard is
ambient-DOMINATED — machine-confirmed at the failing point. -/

/-! ## Phase 4 — Z2a/Z2b: re-guarding a sealed box one budget down,
without/with the outer ambient.  The body `Z := A@(c+1)(Γ,p)` is held
FIXED — this isolates the guard plumbing from the value map. -/

set_option linter.unusedVariables false in
/-- P4 battery (rerun: `runLaws "P4-Z2" (zooOf bases) 1500000 p4All`). -/
private def p4All : List Law :=
  [z2 "A" false SA' GA' pP' 5 2, z2 "A" false SA' GA' pP' 5 4,
   z2 "A" true  SA' GA' pP' 5 2, z2 "A" true  SA' GA' pP' 5 4,
   z2 "E" false SE' GE' rP' 5 4, z2 "E" true  SE' GE' rP' 5 4]

/- P4 RESULT (2026-07-12, 16s): ALL fails=0 — including Z2a (no
ambient), with tight=pts everywhere: on configs A/E the E-value is
budget-CONSTANT from 1 up (Z8 below: E@c = E@(c+1) semantically), so
the A/E-config Z2a pass is a stabilization artifact, not evidence for
the in-box ascent.  The moving-E control is Phase 7. -/

/-! ## Phase 5 — the ◯-goal (Z3) and γ-head (Z7) seal crossings as
one-formula laws: source disjunct + ambient ≤ target disjunct — the
sealed obligations themselves, across the burned band c = 1..4. -/

set_option linter.unusedVariables false in
/-- P5 battery (rerun: `runLaws "P5-Z3Z7" (zooOf bases) 1500000 p5All`). -/
private def p5All : List Law :=
  (List.range 4).map (fun i => z3 "A" SA' GA' pP' 5 (i + 1))
   ++ (List.range 4).map (fun i => z7 "A" SA' GA' pP' 5 (i + 1))

/- P5 RESULT (2026-07-12, 7s): all fails=0, tight=98/152 — the ◯-goal
and γ-head seal crossings hold with slack across the burned band
c = 1..4, confirming the seal reduction is faithful to the holdout. -/

/-! ## Phase 6 — Z5 (fresh-antecedent guarded E-ascent at the grown
context, `C₁ ∉ S ∪ Γ`: the law that would kill the fourth seal
without the whole-head rebuild) and Z8 (the FLOORLESS E-ascent
`E@c ⊢ E@(c+1)`, same and grown context: the E-half mate of the
floorless A-band found in P2a–c). -/

section
private def uP'' := prop "u"
private def z8 (nm : String) (Sl : List PLLFormula) (Γ : List PLLFormula)
    (cmax : Nat) (c : Nat) : Law :=
  let S := Sl.toFinset
  let fuel := fuelFor Sl Γ truePLL cmax
  { name := s!"Z8-{nm}-c{c}"
    X1 := truePLL
    X2 := itpE "p" S fuel c Γ
    Y  := itpE "p" S fuel (c + 1) Γ }

set_option linter.unusedVariables false in
/-- P6 battery (rerun: `runLaws "P6-Z5Z8" (zooOf bases) 1500000 p6All`). -/
private def p6All : List Law :=
  [z5 "A-u" SA' GA' uP'' 5 1, z5 "A-u" SA' GA' uP'' 5 2,
   z5 "A-u" SA' GA' uP'' 5 4,
   z5 "A-u>r" SA' GA' (uP''.ifThen rP') 5 2,
   z5 "A-u>r" SA' GA' (uP''.ifThen rP') 5 4,
   z5 "A-Ou" SA' GA' (uP''.somehow) 5 2,
   z8 "A" SA' GA' 5 1, z8 "A" SA' GA' 5 2, z8 "A" SA' GA' 5 3,
   z8 "A" SA' GA' 5 4,
   z8 "Agrown" SA' (rP' :: GA') 5 1, z8 "Agrown" SA' (rP' :: GA') 5 2,
   z8 "d2c" S2C G2C 4 1, z8 "d2c" S2C G2C 4 2]

/- P6 RESULT (2026-07-12, 57s):
* Z5 (fresh-antecedent guarded ascent, C₁ ∈ {u, u⊃r, ◯u}, c ∈
  {1,2,4}): ALL fails=0 with tight=pts — EQUALITY
  `E@(c+1)(Γ) ⊓ E@c(C₁::Γ) = E@(c+1)(C₁::Γ)` on the whole zoo.
* Z8 (floorless E-ascent E@c ⊢ E@(c+1)): config A passes c=1..4
  tight=pts (E budget-constant); saturated grown context DEGEN
  (tables literally budget-free); d2chain FAILS at c=1 (18 pts,
  chain3, nucleus [0,2,2], v(r)=v(s)=1, lhs=2 rhs=1) and passes at
  c=2 tight — the E-side has a GENUINE low-band failure: the
  floorless mutual pair is refuted on the E-half at c=1. -/
end

/-! ## Phase 7 — the moving-E control: at (d2chain, c=1) the E-ascent
genuinely moves (Z8 failed there), so re-probe the guard laws and the
fresh ascent THERE, separating "law" from "E-stabilization artifact"
(config A's E is budget-constant from 1 up, so its Z2a pass is
uninformative). -/

section
private def uP3 := prop "u"
set_option linter.unusedVariables false in
/-- P7 battery (rerun: `runLaws "P7-movingE" (zooOf bases) 1500000
p7All`; ~256 s wall). -/
private def p7All : List Law :=
  [z2 "d2c" false S2C G2C pP' 4 1, z2 "d2c" false S2C G2C pP' 4 2,
   z2 "d2c" true  S2C G2C pP' 4 1, z2 "d2c" true  S2C G2C pP' 4 2,
   z5 "d2c-u" S2C G2C uP3 4 1, z5 "d2c-u" S2C G2C uP3 4 2,
   z3 "d2c" S2C G2C pP' 4 1, z3 "d2c" S2C G2C pP' 4 2,
   z7 "d2c" S2C G2C pP' 4 1, z7 "d2c" S2C G2C pP' 4 2]
end

/- P7 RESULT (2026-07-12, 256s) — the moving-E separation:
* Z2a-d2c-c1 FAILS (212 pts; chain2, identity nucleus, v(r)=1,
  v(s)=0): the ambient-free re-guard is REFUTED exactly where the
  E-value moves — the P4 pass was the stabilization artifact.
* Z2b-d2c passes c=1,2 (slack): the proved engine `box_reguard`'s
  law is robust where E moves.
* Z5-d2c passes c=1,2 with tight=pts — the fresh-ascent EQUALITY
  survives the moving-E config.
* Z3/Z7-d2c pass c=1,2: the seal laws are robust where E moves.

## VERDICT (the transfer hypothesis, adjudicated)

1. Guarded engines: `box_reguard` (Z2b) is the sole (A)-family
   survivor and is PROVED (`wip/absorb_base.lean`); its ambient-free
   mirror Z2a is zoo-refuted (P7).  `box_remap` (proved) delimits
   what any seal crossing can carry: everything formula-shaped;
   never the conclusion-anchored continuations.
2. Guard strengthening cannot help at same-context seals: every
   reachable guard is budget-mono-dominated by the ambient (P3:
   Z6 ≡ Z1 at the unique failing point).
3. The A-side descent is semantically FLOORLESS above 0: true at
   every probed c ≥ 1 across defect 1–2, J 1–4, chained and shared
   jump structures; false exactly at (◯-goal, c=0) (empty b-gated
   table).  The defect-scaled floor is a pigeonhole-ledger artifact.
4. The E-side ascent is NOT floorless: refuted at (d2chain, c=1),
   true at c ≥ 2 — the mutual-pair decomposition is closed below
   c = 2 by countermodel, independently of the seals.
5. The fresh-antecedent seal's missing law (Z5) is a zoo-EQUALITY
   everywhere probed, including moving-E configs — a genuine open
   target whose proof would kill the fourth seal without the
   whole-head rebuild.
6. The Pitts/guardMP analogy breaks structurally: her guards are
   antecedent-side (weakening-portable); the seal deficit is
   succedent-side-under-◯ (continuations conclude the outer R,
   strictly weaker than the ◯-disjunct a seal must produce), and
   ledger-raising leaves the J+1 allotment deficit invariant.

Full narrative: the holdout docstring in `wip/absorb_base.lean` and
docs/ui-endgame.md §"The guarded/consumed reshaping of the seals". -/
