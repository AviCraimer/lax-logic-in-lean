import wip.rnEmbed

/-!
# After `coverConj_false`: what is `∃p.φ★`?

`wip/coverfail.lean` refutes the substitution-cover method with

    φ★ = ((◯⊥ ⊃ p) ⊃ (◯⊥ ∧ p)) ∧ ¬¬p ,      φ★ ⊢ ¬¬◯⊥,  φ★ ⊬ ◯⊥ .

The obvious candidate for the uniform post-interpolant is `¬¬◯⊥`.  It IS
the interpolant iff every variable-free `χ` with `φ★ ⊢ χ` already follows
from `¬¬◯⊥`; by the finite model property that is:

  (†) for every finite rooted model whose root forces `¬¬◯⊥` and refutes
      `χ`, there is SOME finite model with a `φ★`-world refuting `χ`.

This probe measures (†) on the small-model battery in two ways.

* `same-model` test: for how many rooted models with `root ⊩ ¬¬◯⊥` is
  there a valuation `U` of `p` making `φ★` true at the root?  (If this
  were always so, (†) would follow at once, since variable-free formulas
  do not see `V(p)`.)
* `type` test: the finer question.  A variable-free `χ` can only
  distinguish worlds through their *variable-free type* — here measured
  by a fixed dictionary (`⊥, ⊤, ◯⊥, ¬◯⊥, ¬¬◯⊥, ◯¬◯⊥`, and the
  Rieger–Nishimura rungs `rnSub 1 … rnSub 10` over `◯⊥`).  If every type
  realised at a `¬¬◯⊥`-root is ALSO realised at some `φ★`-root, then no
  `χ` in the dictionary separates the two, and `¬¬◯⊥` survives as the
  candidate interpolant.

Run: `scripts/probe <sec> interpprobe <maxN>`
-/

namespace InterpProbe

open PLLFormula PLLND.RNEmbed

abbrev Mask := Nat

structure FM where
  n : Nat
  ri : Array Mask
  rm : Array Mask
  f : Mask
  deriving Inhabited

def bit (i : Nat) : Mask := 1 <<< i
def hasBit (m : Mask) (i : Nat) : Bool := (m >>> i) % 2 == 1
def FM.full (M : FM) : Mask := (1 <<< M.n) - 1

def maskStr (n : Nat) (m : Mask) : String := Id.run do
  let mut s := "{"
  let mut first := true
  for i in [0:n] do
    if hasBit m i then
      s := s ++ (if first then "" else ",") ++ toString i
      first := false
  return s ++ "}"

def mImp (M : FM) (a b : Mask) : Mask := Id.run do
  let mut r := 0
  for v in [0:M.n] do
    if (M.ri[v]! &&& a &&& (M.full ^^^ b)) == 0 then r := r ||| bit v
  return r

def mBox (M : FM) (a : Mask) : Mask := Id.run do
  let mut r := 0
  for v in [0:M.n] do
    let mut ok := true
    for u in [0:M.n] do
      if hasBit M.ri[v]! u && (M.rm[u]! &&& a) == 0 then ok := false
    if ok then r := r ||| bit v
  return r

/-- Truth set of a formula, with the single variable `p` valued at `U`. -/
def eval (M : FM) (U : Mask) : PLLFormula → Mask
  | .prop _ => U
  | .falsePLL => M.f
  | .and a b => eval M U a &&& eval M U b
  | .or a b => eval M U a ||| eval M U b
  | .ifThen a b => mImp M (eval M U a) (eval M U b)
  | .somehow a => mBox M (eval M U a)

def isUp (M : FM) (m : Mask) : Bool := Id.run do
  for v in [0:M.n] do
    if hasBit m v && (M.ri[v]! &&& (M.full ^^^ m)) != 0 then return false
  return true

def upsets (M : FM) : Array Mask := Id.run do
  let mut acc : Array Mask := #[]
  for m in [0:(1 <<< M.n)] do
    if isUp M m then acc := acc.push m
  return acc

def posets (n : Nat) : Array (Array Mask) := Id.run do
  let mut acc : Array (Array Mask) := #[]
  let mut opts : Array (Array Mask) := #[]
  for v in [0:n] do
    if v == 0 then
      opts := opts.push #[((1 <<< n) - 1)]
    else
      let hi := n - v - 1
      let mut o : Array Mask := #[]
      for s in [0:(1 <<< hi)] do
        o := o.push (bit v ||| (s <<< (v + 1)))
      opts := opts.push o
  let mut idx : Array Nat := Array.replicate n 0
  let mut go := true
  while go do
    let mut ri : Array Mask := #[]
    for v in [0:n] do
      ri := ri.push ((opts[v]!)[idx[v]!]!)
    let mut ok := true
    for v in [0:n] do
      for u in [0:n] do
        if hasBit ri[v]! u && (ri[u]! &&& (((1 <<< n) - 1) ^^^ ri[v]!)) != 0 then
          ok := false
    if ok then acc := acc.push ri
    let mut i := 0
    let mut carry := true
    while carry && i < n do
      if idx[i]! + 1 < opts[i]!.size then
        idx := idx.set! i (idx[i]! + 1)
        carry := false
      else
        idx := idx.set! i 0
        i := i + 1
    if carry then go := false
  return acc

def modals (n : Nat) (ri : Array Mask) : Array (Array Mask) := Id.run do
  let full := (1 <<< n) - 1
  let mut opts : Array (Array Mask) := #[]
  for v in [0:n] do
    let mut o : Array Mask := #[]
    for m in [0:(1 <<< n)] do
      if hasBit m v && (m &&& (full ^^^ ri[v]!)) == 0 then o := o.push m
    opts := opts.push o
  let mut acc : Array (Array Mask) := #[]
  let mut idx : Array Nat := Array.replicate n 0
  let mut go := true
  while go do
    let mut rm : Array Mask := #[]
    for v in [0:n] do
      rm := rm.push ((opts[v]!)[idx[v]!]!)
    let mut ok := true
    for v in [0:n] do
      for u in [0:n] do
        if hasBit rm[v]! u && (rm[u]! &&& (full ^^^ rm[v]!)) != 0 then ok := false
    if ok then acc := acc.push rm
    let mut i := 0
    let mut carry := true
    while carry && i < n do
      if idx[i]! + 1 < opts[i]!.size then
        idx := idx.set! i (idx[i]! + 1)
        carry := false
      else
        idx := idx.set! i 0
        i := i + 1
    if carry then go := false
  return acc

def enumerate (n : Nat) : Array FM := Id.run do
  let mut acc : Array FM := #[]
  for ri in posets n do
    let M0 : FM := { n := n, ri := ri, rm := ri, f := 0 }
    for rm in modals n ri do
      let M1 : FM := { M0 with rm := rm }
      for f in upsets M1 do
        if !hasBit f 0 then
          acc := acc.push { M1 with f := f }
  return acc

def describe (M : FM) : String := Id.run do
  let mut s := s!"n={M.n} F={maskStr M.n M.f}"
  s := s ++ " Ri:"
  for v in [0:M.n] do
    s := s ++ s!" {v}↑{maskStr M.n M.ri[v]!}"
  s := s ++ " Rm:"
  for v in [0:M.n] do
    s := s ++ s!" {v}⇝{maskStr M.n M.rm[v]!}"
  return s

/-! ## The objects -/

def P : PLLFormula := .prop pv
def Top : PLLFormula := PLLFormula.falsePLL.ifThen PLLFormula.falsePLL
def neg (A : PLLFormula) : PLLFormula := A.ifThen PLLFormula.falsePLL
def bx : PLLFormula := PLLFormula.falsePLL.somehow

/-- `φ★ = ((◯⊥ ⊃ p) ⊃ (◯⊥ ∧ p)) ∧ ¬¬p`. -/
def phiStar : PLLFormula :=
  ((bx.ifThen P).ifThen (bx.and P)).and (neg (neg P))

/-- The variable-free dictionary: enough to separate the small models. -/
def dict : List (String × PLLFormula) :=
  [("⊥", PLLFormula.falsePLL), ("⊤", Top), ("◯⊥", bx), ("¬◯⊥", neg bx),
   ("¬¬◯⊥", neg (neg bx)), ("◯¬◯⊥", (neg bx).somehow),
   ("◯¬¬◯⊥", (neg (neg bx)).somehow), ("◯⊥∨¬◯⊥", bx.or (neg bx))]
  ++ (List.range 10).map (fun k => (s!"t{k+1}", rnSub (k + 1)))

/-- The variable-free type of the root: which dictionary entries hold
there.  (In a rooted model an up-set contains the root iff it is
everything.) -/
def rootType (M : FM) : Nat := Id.run do
  let mut t := 0
  let mut i := 0
  for (_, A) in dict do
    if hasBit (eval M 0 A) 0 then t := t ||| bit i
    i := i + 1
  return t

def typeStr (t : Nat) : String := Id.run do
  let mut s := ""
  let mut i := 0
  for (nm, _) in dict do
    if hasBit t i then s := s ++ (if s == "" then "" else ",") ++ nm
    i := i + 1
  return "[" ++ s ++ "]"

def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  let pl (x : String) : IO Unit := do out.putStrLn x; out.flush
  let maxN := (args[0]?.getD "5").toNat!
  pl s!"== ∃p.φ★ probe: maxN={maxN} =="
  pl s!"   φ★ = ((◯⊥ ⊃ p) ⊃ (◯⊥ ∧ p)) ∧ ¬¬p"
  pl s!"   dictionary ({dict.length}): {dict.map (·.1)}"
  let mut nnTypes : Array Nat := #[]        -- types realised at ¬¬◯⊥-roots
  let mut phiTypes : Array Nat := #[]       -- types realised at φ★-roots
  for n in [2:maxN+1] do
    let ms := enumerate n
    let mut nnRoots := 0
    let mut nnWithVal := 0
    let mut deficient : Array (FM × Nat) := #[]
    for M in ms do
      let nn := eval M 0 (neg (neg bx))
      let isNN := hasBit nn 0
      let ups := upsets M
      let cands := ups.filter (fun u => (M.f &&& (M.full ^^^ u)) == 0)
      let mut good : Option Mask := none
      for u in cands do
        if hasBit (eval M u phiStar) 0 then
          if good.isNone then good := some u
      let ty := rootType M
      if isNN then
        nnRoots := nnRoots + 1
        if !nnTypes.contains ty then nnTypes := nnTypes.push ty
        match good with
        | some _ => nnWithVal := nnWithVal + 1
        | none => if deficient.size < 3 then deficient := deficient.push (M, ty)
      if good.isSome then
        if !phiTypes.contains ty then phiTypes := phiTypes.push ty
        if !isNN then
          pl s!"  !! UNSOUND: φ★ satisfiable at a root NOT forcing ¬¬◯⊥: {describe M}"
    pl s!"-- n={n}: {ms.size} models; roots forcing ¬¬◯⊥: {nnRoots}, of which \
{nnWithVal} admit a valuation of p making φ★ true at the root \
({nnRoots - nnWithVal} deficient)"
    for (M, ty) in deficient do
      pl s!"     deficient: {describe M}"
      pl s!"                root type {typeStr ty}"
  pl ""
  pl s!"== variable-free root types realised at ¬¬◯⊥-roots: {nnTypes.size} =="
  for t in nnTypes do pl s!"   {typeStr t}"
  pl s!"== variable-free root types realised at φ★-roots: {phiTypes.size} =="
  for t in phiTypes do pl s!"   {typeStr t}"
  let missing := nnTypes.filter (fun t => !phiTypes.contains t)
  if missing.isEmpty then
    pl "== EVERY ¬¬◯⊥-root type is realised at some φ★-root: no dictionary \
formula separates φ★ from ¬¬◯⊥ =="
  else
    pl s!"== {missing.size} ¬¬◯⊥-root types NOT realised at any φ★-root =="
    for t in missing do pl s!"   {typeStr t}"
  pl "done"

end InterpProbe

def main (args : List String) : IO Unit := InterpProbe.main args
