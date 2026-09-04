import LaxLogic.PLLFormula

/-!
# MixedCoverConj probe: does the JOIN of the stretch bound and the
substitution instances exhaust every one-variable formula?

`wip/coverprobe.lean` refuted `CoverConj` by an exhaustive
product-subalgebra search: for each rooted model `C` and each UNDEFINABLE
up-set `U` as `‖p‖` it generated every one-variable formula up to semantic
equivalence, as a tuple of truth sets (coordinate `0` = the model with
`p ↦ U`, one further coordinate per variable-free truth set `d ∈ D(C)`),
and looked for a tuple whose `U`-coordinate is the whole model while every
`d`-coordinate is proper.  `φ★` is such a hit.

`wip/phistar.lean` adds a SECOND, non-substitutional lower bound on the
consequence filter `F(φ)`: the GUARDED STRETCH.  `stretch C` doubles `C`
over the region `‖◯⊥‖`, and forcing at the two copies of a world is
computed by a pair of variable-free translations `Lo`, `Up`:

    Lo p     = ⊥                     Up p     = ⊤
    Lo ⊥     = ⊥                     Up ⊥     = ⊥
    Lo (A∧B) = Lo A ∧ Lo B           Up (A∧B) = Up A ∧ Up B
    Lo (A∨B) = Lo A ∨ Lo B           Up (A∨B) = Up A ∨ Up B
    Lo (A⊃B) = (Lo A ⊃ Lo B)         Up (A⊃B) = Up A ⊃ Up B
               ∧ (◯⊥ ⊃ (Up A ⊃ Up B))
    Lo ◯A    = ◯(Lo A) ∧ (◯⊥ ⊃ ◯(Up A))     Up ◯A = ◯(Up A)

This probe searches for a counterexample to the JOIN of the two methods,

    MixedCoverConj : ∀ φ one-variable, φ ⊢ Lo φ ∨ ⋁_{θ ∈ S} φ[p := θ] .

Semantically (`hasMixedCover_iff_semMixed`), a counterexample is a rooted
`C`, a valuation `U` of `p` and a one-variable `φ` with

    root ⊩_U φ ,   root ⊮ Lo φ ,   root ⊮ φ[p := d]  for every d ∈ D(C).

Since `Lo`/`Up` are structurally compositional, the extended tuple
`(‖φ‖_U, ‖φ‖_{d₁}, …, ‖φ‖_{d_k}, ‖Lo φ‖, ‖Up φ‖)` closes under the
connectives, so the same exhaustive subalgebra generation applies —
now in a product with two extra coordinates.

## Generalised guards

The guard `◯⊥` in the stretch may be replaced by ANY variable-free `χ`:
the upper layer is attached over `‖χ‖`, which is `Rᵢ`-upward closed
because it is a truth set.  Writing `LoG χ`, `UpG χ` for the resulting
translations (the clauses above with `◯⊥` replaced by `χ`), every `χ`
gives its own lower bound `LoG χ φ ⊢ ψ` for variable-free `ψ` with
`φ ⊢ ψ`.  Mode `guarded` carries one `(lo, up)` pair per `χ ∈ D(C)` and
demands that ALL of them fail at the root — a counterexample to the
strengthened `GuardedMixedConj`.

Run: `scripts/probe <sec> mixedprobe <maxN> <cap> <mode>`
  mode = "mixed" (default; guard `◯⊥` only) | "guarded" (every guard in
  `D(C)`) | "models" | "detail".
-/

namespace MixedProbe

open PLLFormula

abbrev Mask := Nat

/-- A finite rooted constraint model: worlds `0 … n-1`, world `0` the
root, `ri[v]`/`rm[v]` the `Rᵢ`/`Rₘ`-successor masks, `f` the fallible
mask. -/
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

/-! ## The four operations on truth sets -/

def mAnd (a b : Mask) : Mask := a &&& b
def mOr (a b : Mask) : Mask := a ||| b

/-- `‖A ⊃ B‖ = {v : ∀ u ≥ᵢ v, u ∈ A → u ∈ B}`. -/
def mImp (M : FM) (a b : Mask) : Mask := Id.run do
  let mut r := 0
  for v in [0:M.n] do
    if (M.ri[v]! &&& a &&& (M.full ^^^ b)) == 0 then r := r ||| bit v
  return r

/-- `‖◯A‖ = {v : ∀ u ≥ᵢ v, ∃ y, u Rₘ y ∧ y ∈ A}`. -/
def mBox (M : FM) (a : Mask) : Mask := Id.run do
  let mut r := 0
  for v in [0:M.n] do
    let mut ok := true
    for u in [0:M.n] do
      if hasBit M.ri[v]! u && (M.rm[u]! &&& a) == 0 then ok := false
    if ok then r := r ||| bit v
  return r

/-- Direct evaluation of a formula, `p` valued at `vp`.  Used only to
CHECK hits (against the compositional `Lo`/`Up` coordinates and against
an explicitly built stretch frame). -/
def eval (M : FM) (vp : Mask) : PLLFormula → Mask
  | .prop _ => vp
  | .falsePLL => M.f
  | .and a b => mAnd (eval M vp a) (eval M vp b)
  | .or a b => mOr (eval M vp a) (eval M vp b)
  | .ifThen a b => mImp M (eval M vp a) (eval M vp b)
  | .somehow a => mBox M (eval M vp a)

/-! ## The variable-free truth sets -/

/-- `D(C)`: closure of `{‖⊥‖}` under `∧, ∨, ⊃, ◯`. -/
def defClosure (M : FM) : Array Mask := Id.run do
  let mut S : Array Mask := #[M.f]
  let mut changed := true
  while changed do
    changed := false
    let cur := S
    for a in cur do
      for b in cur do
        for c in [mAnd a b, mOr a b, mImp M a b] do
          if !S.contains c then
            S := S.push c
            changed := true
      let c := mBox M a
      if !S.contains c then
        S := S.push c
        changed := true
  return S

/-! ## Up-sets, and the model enumeration -/

def isUp (M : FM) (m : Mask) : Bool := Id.run do
  for v in [0:M.n] do
    if hasBit m v && (M.ri[v]! &&& (M.full ^^^ m)) != 0 then return false
  return true

def upsets (M : FM) : Array Mask := Id.run do
  let mut acc : Array Mask := #[]
  for m in [0:(1 <<< M.n)] do
    if isUp M m then acc := acc.push m
  return acc

/-- All rooted partial orders on `0 … n-1` whose numbering is a linear
extension.  Complete up to isomorphism. -/
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

/-- All reflexive transitive `Rₘ ⊆ Rᵢ`. -/
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

/-! ## The guarded stretch as an explicit frame (hit verification only)

`stretchFM M c` has worlds `0 … n-1` (the ground copies) and
`n … 2n-1` (the upper copies), with `inl x ⊑ inr y` iff `x ⊑ y` and
`y ∈ c`.  Its canonical valuation of `p` is the whole upper layer
together with the fallible ground worlds. -/

def stretchFM (M : FM) (c : Mask) : FM := Id.run do
  let n := M.n
  let mut ri : Array Mask := #[]
  for x in [0:n] do
    ri := ri.push (M.ri[x]! ||| ((M.ri[x]! &&& c) <<< n))
  for x in [0:n] do
    ri := ri.push (M.ri[x]! <<< n)
  let mut rm : Array Mask := #[]
  for x in [0:n] do
    rm := rm.push M.rm[x]!
  for x in [0:n] do
    rm := rm.push (M.rm[x]! <<< n)
  return { n := 2 * n, ri := ri, rm := rm, f := M.f ||| (M.f <<< n) }

def stretchVp (M : FM) : Mask := M.f ||| (M.full <<< M.n)

/-! ## The product-subalgebra search with `Lo`/`Up` coordinates -/

/-- One element of the generated algebra: its truth set under each
valuation (`t`), and, for each guard `χ`, the truth sets of `LoG χ` and
`UpG χ` of its term. -/
structure Elt where
  t : Array Mask
  lo : Array Mask
  up : Array Mask
  e : PLLFormula

def encode (n : Nat) (x : Elt) : Nat := Id.run do
  let mut acc := 0
  for m in x.t do acc := acc * (1 <<< n) + m
  for m in x.lo do acc := acc * (1 <<< n) + m
  for m in x.up do acc := acc * (1 <<< n) + m
  return acc

def zipMask (f : Mask → Mask → Mask) (a b : Array Mask) : Array Mask := Id.run do
  let mut r : Array Mask := #[]
  for i in [0:a.size] do r := r.push (f a[i]! b[i]!)
  return r

def eAnd (a b : Elt) : Elt :=
  { t := zipMask mAnd a.t b.t, lo := zipMask mAnd a.lo b.lo,
    up := zipMask mAnd a.up b.up, e := a.e.and b.e }

def eOr (a b : Elt) : Elt :=
  { t := zipMask mOr a.t b.t, lo := zipMask mOr a.lo b.lo,
    up := zipMask mOr a.up b.up, e := a.e.or b.e }

/-- `LoG χ (A ⊃ B) = (LoG A ⊃ LoG B) ∧ (χ ⊃ (UpG A ⊃ UpG B))`,
`UpG χ (A ⊃ B) = UpG A ⊃ UpG B`. -/
def eImp (M : FM) (gs : Array Mask) (a b : Elt) : Elt := Id.run do
  let mut lo : Array Mask := #[]
  let mut up : Array Mask := #[]
  for i in [0:gs.size] do
    let u := mImp M a.up[i]! b.up[i]!
    lo := lo.push (mAnd (mImp M a.lo[i]! b.lo[i]!) (mImp M gs[i]! u))
    up := up.push u
  return { t := zipMask (mImp M) a.t b.t, lo := lo, up := up, e := a.e.ifThen b.e }

/-- `LoG χ ◯A = ◯(LoG A) ∧ (χ ⊃ ◯(UpG A))`, `UpG χ ◯A = ◯(UpG A)`. -/
def eBox (M : FM) (gs : Array Mask) (a : Elt) : Elt := Id.run do
  let mut lo : Array Mask := #[]
  let mut up : Array Mask := #[]
  for i in [0:gs.size] do
    let u := mBox M a.up[i]!
    lo := lo.push (mAnd (mBox M a.lo[i]!) (mImp M gs[i]! u))
    up := up.push u
  return { t := a.t.map (mBox M), lo := lo, up := up, e := a.e.somehow }

/-- A COVER separator: true at the root under `U`, false at the root
under every variable-free valuation (this is `coverprobe`'s `isSep`). -/
def isCoverSep (M : FM) (x : Elt) : Bool := Id.run do
  if x.t[0]! != M.full then return false
  for i in [1:x.t.size] do
    if x.t[i]! == M.full then return false
  return true

/-- A MIXED separator: a cover separator whose `LoG χ`-coordinate also
fails at the root, for every guard `χ` carried. -/
def isMixedSep (M : FM) (x : Elt) : Bool := Id.run do
  if !isCoverSep M x then return false
  for i in [0:x.lo.size] do
    if x.lo[i]! == M.full then return false
  return true

structure SearchOut where
  hit : Option Elt := none
  coverSeen : Bool := false
  size : Nat := 0
  capped : Bool := false

def fsize : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and a b => 1 + fsize a + fsize b
  | .or a b => 1 + fsize a + fsize b
  | .ifThen a b => 1 + fsize a + fsize b
  | .somehow a => 1 + fsize a

/-- Generate the subalgebra of `∏ A_{vals i} × ∏_χ A_{stretch χ}`
generated by `p` and `⊥`, in order of increasing term size, looking for a
MIXED separator.  `coverSeen` records whether a plain cover separator
turned up on the way (so the run also reproduces `coverprobe`). -/
def search (M : FM) (vals : Array Mask) (gs : Array Mask) (cap : Nat) :
    SearchOut := Id.run do
  let botE : Elt :=
    { t := vals.map (fun _ => M.f), lo := gs.map (fun _ => M.f),
      up := gs.map (fun _ => M.f), e := PLLFormula.falsePLL }
  let genE : Elt :=
    { t := vals, lo := gs.map (fun _ => M.f), up := gs.map (fun _ => M.full),
      e := PLLFormula.prop "p" }
  let mut seen : Std.HashMap Nat Unit := {}
  let mut all : Array Elt := #[]
  let mut frontier : Array Elt := #[]
  let mut coverSeen := false
  for x in [botE, genE] do
    let k := encode M.n x
    if !seen.contains k then
      seen := seen.insert k ()
      all := all.push x
      frontier := frontier.push x
      if isCoverSep M x then coverSeen := true
      if isMixedSep M x then
        return { hit := some x, coverSeen := true, size := all.size }
  while frontier.size > 0 do
    if all.size > cap then
      return { coverSeen := coverSeen, size := all.size, capped := true }
    let mut next : Array Elt := #[]
    let cur := all
    let mut best : Option Elt := none
    for a in frontier do
      let mut cands : Array Elt := #[eBox M gs a]
      for b in cur do
        cands := cands.push (eAnd a b)
        cands := cands.push (eOr a b)
        cands := cands.push (eImp M gs a b)
        cands := cands.push (eImp M gs b a)
      for x in cands do
        let k := encode M.n x
        if !seen.contains k then
          seen := seen.insert k ()
          all := all.push x
          next := next.push x
          if isCoverSep M x then coverSeen := true
          if isMixedSep M x then
            match best with
            | none => best := some x
            | some x' => if fsize x.e < fsize x'.e then best := some x
    match best with
    | some h => return { hit := some h, coverSeen := true, size := all.size }
    | none => pure ()
    frontier := next
  return { coverSeen := coverSeen, size := all.size }

/-! ## Driver -/

structure Stats where
  models : Nat := 0
  pairs : Nat := 0
  capped : Nat := 0
  coverHits : Nat := 0
  mixedHits : Nat := 0
  maxClosure : Nat := 0
  deriving Repr

def describe (M : FM) : String := Id.run do
  let mut s := s!"n={M.n} F={maskStr M.n M.f}"
  s := s ++ " Ri:"
  for v in [0:M.n] do
    s := s ++ s!" {v}↑{maskStr M.n M.ri[v]!}"
  s := s ++ " Rm:"
  for v in [0:M.n] do
    s := s ++ s!" {v}⇝{maskStr M.n M.rm[v]!}"
  return s

/-- Independent check of a hit: the `Lo`/`Up` coordinates recomputed
inside the explicitly built stretch frame, and the valuation coordinates
recomputed by direct evaluation. -/
def checkHit (M : FM) (vals : Array Mask) (gs : Array Mask) (x : Elt) : String :=
  Id.run do
  let mut msgs : Array String := #[]
  for i in [0:vals.size] do
    if eval M vals[i]! x.e != x.t[i]! then
      msgs := msgs.push s!"COORD {i} MISMATCH"
  for j in [0:gs.size] do
    let S := stretchFM M gs[j]!
    let v := eval S (stretchVp M) x.e
    let loS := v &&& M.full
    let upS := (v >>> M.n) &&& M.full
    if loS != x.lo[j]! then msgs := msgs.push s!"LO {j} MISMATCH {loS} vs {x.lo[j]!}"
    if upS != x.up[j]! then msgs := msgs.push s!"UP {j} MISMATCH {upS} vs {x.up[j]!}"
  if msgs.isEmpty then return "stretch-frame check OK"
  return String.intercalate "; " msgs.toList

def runModel (pl : String → IO Unit) (M : FM) (cap : Nat) (allGuards : Bool)
    (verbose : Bool) (st : Stats) : IO Stats := do
  let mut st := st
  let D := defClosure M
  let ups := upsets M
  let gs : Array Mask := if allGuards then D else #[mBox M M.f]
  let cands := ups.filter (fun u => (M.f &&& (M.full ^^^ u)) == 0 && !D.contains u)
  if verbose && cands.size > 0 then
    pl s!"  model {describe M}"
    pl s!"    definable truth sets ({D.size}): {D.toList.map (maskStr M.n)}"
    pl s!"    guards ({gs.size}): {gs.toList.map (maskStr M.n)}"
    pl s!"    undefinable valuations ({cands.size}): {cands.toList.map (maskStr M.n)}"
  for u in cands do
    st := { st with pairs := st.pairs + 1 }
    let vals : Array Mask := #[u] ++ D
    let out := search M vals gs cap
    st := { st with maxClosure := max st.maxClosure out.size }
    if out.coverSeen then st := { st with coverHits := st.coverHits + 1 }
    if out.capped then
      st := { st with capped := st.capped + 1 }
      pl s!"  CAPPED at {out.size}: {describe M} U={maskStr M.n u}"
    match out.hit with
    | some x =>
        st := { st with mixedHits := st.mixedHits + 1 }
        pl "  *** MIXED SEPARATING FORMULA FOUND ***"
        pl s!"      model  : {describe M}"
        pl s!"      V(p)   : {maskStr M.n u}"
        pl s!"      D      : {D.toList.map (maskStr M.n)}"
        pl s!"      guards : {gs.toList.map (maskStr M.n)}"
        pl s!"      φ      : {x.e.toString}"
        pl s!"      tuple  : {x.t.toList.map (maskStr M.n)}"
        pl s!"      Lo     : {x.lo.toList.map (maskStr M.n)}"
        pl s!"      Up     : {x.up.toList.map (maskStr M.n)}"
        pl s!"      check  : {checkHit M vals gs x}"
    | none => pure ()
  return st

def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  let pl (x : String) : IO Unit := do out.putStrLn x; out.flush
  let maxN := (args[0]?.getD "4").toNat!
  let cap := (args[1]?.getD "4000").toNat!
  let mode := args[2]?.getD "mixed"
  let allGuards := mode == "guarded"
  pl s!"== MixedCoverConj probe: maxN={maxN} closureCap={cap} mode={mode} =="
  for n in [2:maxN+1] do
    let ms := enumerate n
    pl s!"-- n={n}: {ms.size} rooted models (poset × Rₘ × F) --"
    if mode == "models" then continue
    let t0 ← IO.monoMsNow
    let mut st : Stats := {}
    for M in ms do
      st := { st with models := st.models + 1 }
      st ← runModel pl M cap allGuards (mode == "detail") st
    let t1 ← IO.monoMsNow
    pl s!"   models {st.models}, (model,U) pairs with U undefinable {st.pairs}, \
capped {st.capped}, cover-hit pairs {st.coverHits}, MIXED HITS {st.mixedHits}, \
max closure {st.maxClosure} [{t1 - t0} ms]"
  pl "done"

end MixedProbe

def main (args : List String) : IO Unit := MixedProbe.main args
