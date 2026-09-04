import LaxLogic.PLLFormula

/-!
# `ParamForkMixedConj` probe: does the JOIN of the guarded stretch
bounds, the PARAMETERISED fork bounds and the substitution instances
exhaust every one-variable formula?

`wip/branchprobe.lean` searched the join with the `(χ,⊥)`-fork
coordinate only, and found `φ♣` at `n = 5` — now pinned in
`wip/paramfork.lean` (`branchMixedConj_false`).  The corrected family
frees the two copy valuations:

    fork C χ δ₁ δ₂ :  Rᵢ (inl x) (inl y) ⟺ x Rᵢ y
                      Rᵢ (inr x) (inr y) ⟺ x Rᵢ y
                      Rᵢ (inl x) (inr y) ⟺ x Rᵢ y ∧ x ⊮ χ
                      Rᵢ (inr x) (inl y) ⟺ x Rᵢ y ∧ x ⊮ χ
                      V(p) = ‖δ₁‖ on inl, ‖δ₂‖ on inr,
                      for variable-free δ₁, δ₂ with δᵢ ⊢ χ

`bstretch C χ = fork C χ χ ⊥`, so the branch coordinate is the member
at `(χ, χ, ⊥)` and is subsumed.

## Design: two phases

Carrying one `(FLo, FUp)` pair per TRIPLE inside the generated
subalgebra would multiply the per-element state by `|D|³`; carrying
even one `(LoG, UpG)` pair per GUARD already made the `n = 5` sweep
intractable (`branchprobe`'s `guarded` mode never finished).  So the
subalgebra carries the VALUATION coordinates only, and both
non-substitutional families are tested afterwards:

* **phase A** — `coverprobe`'s subalgebra search: one coordinate per
  valuation (`‖p‖ = U`, then each `d ∈ D(C)`).  A COVER SEPARATOR is an
  element true at the root under `U` and false at the root under every
  `d`;
* **phase B** — each cover separator (a concrete formula) is tested
  against EVERY guard `χ ∈ D(C)` in the explicitly built guarded
  STRETCH frame, and against EVERY parameterised triple
  `(χ, δ₁, δ₂) ∈ D(C)³` with `δᵢ ⊆ χ` in the explicitly built FORK
  frame.  A separator that nothing rescues is a defeater of the FULL
  join.

Phase B is exact (no compositional arithmetic to trust), and the split
is sound in the conservative direction: phase A over-generates
candidates (it does not pre-filter by the stretch), so no defeater can
be lost.  `bcap` bounds the number of separators tested per
`(model, U)` pair; the rest are reported as `skipped-at-budget`, which
is the only thing standing between a "no hits" line and a complete
verdict.

Mode `verify` checks that `pforkFM`/`pforkVp` really is a constraint
model for every `(χ, δ₁, δ₂)` with `δᵢ ⊆ χ` — reflexivity and
transitivity of `Rᵢ`, `Rₘ ⊆ Rᵢ` reflexive and transitive, `F` and
`‖p‖` upward closed, `F ⊆ ‖p‖` — and that the `δᵢ ⊆ χ` condition is
what makes `‖p‖` upward closed (the same check with the condition
dropped reports the violations).

Run: `scripts/probe <sec> pforkprobe <maxN> <cap> <mode> <bcap>`
  mode = "run" (default) | "models" | "verify" | "detail"
-/

namespace PForkProbe

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

/-- Direct evaluation of a formula, `p` valued at `vp`. -/
def eval (M : FM) (vp : Mask) : PLLFormula → Mask
  | .prop _ => vp
  | .falsePLL => M.f
  | .and a b => mAnd (eval M vp a) (eval M vp b)
  | .or a b => mOr (eval M vp a) (eval M vp b)
  | .ifThen a b => mImp M (eval M vp a) (eval M vp b)
  | .somehow a => mBox M (eval M vp a)

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

/-! ## The guarded stretch and the PARAMETERISED fork as explicit frames -/

/-- `stretchFM M c`: ground copies `0 … n-1`, upper copies `n … 2n-1`,
`inl x ⊑ inr y` iff `x ⊑ y` and `y ∈ c`. -/
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

/-- `pforkFM M c`: the fork FRAME, which depends only on the guard `c`;
the cross edges out of `x` exist exactly when `x ∉ c`. -/
def pforkFM (M : FM) (c : Mask) : FM := Id.run do
  let n := M.n
  let mut ri : Array Mask := #[]
  for x in [0:n] do
    let cross := if hasBit c x then 0 else (M.ri[x]! <<< n)
    ri := ri.push (M.ri[x]! ||| cross)
  for x in [0:n] do
    let cross := if hasBit c x then 0 else M.ri[x]!
    ri := ri.push ((M.ri[x]! <<< n) ||| cross)
  let mut rm : Array Mask := #[]
  for x in [0:n] do
    rm := rm.push M.rm[x]!
  for x in [0:n] do
    rm := rm.push (M.rm[x]! <<< n)
  return { n := 2 * n, ri := ri, rm := rm, f := M.f ||| (M.f <<< n) }

/-- The fork VALUATION: `δ₁` on the `inl` copy, `δ₂` on the `inr` copy. -/
def pforkVp (M : FM) (d1 d2 : Mask) : Mask := d1 ||| (d2 <<< M.n)

/-- The admissible parameterised coordinates of `C`: `(χ, δ₁, δ₂)` with
all three in `D(C)` and `δᵢ ⊆ χ`.  (`‖⊥‖ ⊆ δᵢ` is automatic: every
truth set contains the fallible worlds.) -/
def triples (M : FM) (D : Array Mask) : Array (Mask × Mask × Mask) := Id.run do
  let mut acc : Array (Mask × Mask × Mask) := #[]
  for c in D do
    for d1 in D do
      if (d1 &&& (M.full ^^^ c)) == 0 then
        for d2 in D do
          if (d2 &&& (M.full ^^^ c)) == 0 then
            acc := acc.push (c, d1, d2)
  return acc

/-- Admissible coordinates with the fork FRAME precomputed (the frame
depends only on the guard, so it is built once per guard, not once per
triple). -/
def forkTable (M : FM) (D : Array Mask) : Array (FM × Mask × Mask × Mask) := Id.run do
  let mut acc : Array (FM × Mask × Mask × Mask) := #[]
  for c in D do
    let K := pforkFM M c
    for d1 in D do
      if (d1 &&& (M.full ^^^ c)) == 0 then
        for d2 in D do
          if (d2 &&& (M.full ^^^ c)) == 0 then
            acc := acc.push (K, c, d1, d2)
  return acc

/-- The guarded-stretch frames, one per guard. -/
def stretchTable (M : FM) (D : Array Mask) : Array (FM × Mask) := Id.run do
  let mut acc : Array (FM × Mask) := #[]
  for c in D do
    acc := acc.push (stretchFM M c, c)
  return acc

/-- **Phase B, stretch half.**  Does SOME guarded stretch rescue `e`? -/
def stretchRescues (M : FM) (S : Array (FM × Mask)) (e : PLLFormula) :
    Option Mask := Id.run do
  for t in S do
    let v := eval t.1 (stretchVp M) e
    if hasBit v 0 then return some t.2
  return none

/-- **Phase B, fork half.**  Does SOME parameterised fork rescue `e` — i.e. is `e`
forced at the ground copy of the root of `fork C χ δ₁ δ₂` for some
admissible triple?  Returns the first such triple. -/
def paramForkRescues (M : FM) (T : Array (FM × Mask × Mask × Mask)) (e : PLLFormula) :
    Option (Mask × Mask × Mask) := Id.run do
  for t in T do
    let v := eval t.1 (pforkVp M t.2.2.1 t.2.2.2) e
    if hasBit v 0 then return some (t.2.1, t.2.2.1, t.2.2.2)
  return none

/-! ## Phase A: the product-subalgebra search with `LoG`/`UpG`
coordinates -/

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
under every variable-free valuation. -/
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
  mixedSeen : Nat := 0
  killed : Nat := 0
  skipped : Nat := 0
  size : Nat := 0
  capped : Bool := false

def fsize : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and a b => 1 + fsize a + fsize b
  | .or a b => 1 + fsize a + fsize b
  | .ifThen a b => 1 + fsize a + fsize b
  | .somehow a => 1 + fsize a

/-- Generate the subalgebra of `∏ A_{vals i} × ∏_χ A_{gstretch χ}`
generated by `p` and `⊥`, in order of increasing term size.  Every
MIXED separator met on the way is immediately submitted to phase B; a
separator no parameterised fork rescues is a defeater of the full join
and is returned. -/
def search (M : FM) (vals : Array Mask) (gs : Array Mask)
    (SG : Array (FM × Mask)) (T : Array (FM × Mask × Mask × Mask))
    (cap : Nat) (bcap : Nat) : SearchOut := Id.run do
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
  let mut mixedSeen := 0
  let mut killed := 0
  let mut skipped := 0
  for x in [botE, genE] do
    let k := encode M.n x
    if !seen.contains k then
      seen := seen.insert k ()
      all := all.push x
      frontier := frontier.push x
      if isCoverSep M x then coverSeen := true
      if isCoverSep M x then
        mixedSeen := mixedSeen + 1
        if killed + skipped >= bcap then skipped := skipped + 1
        else
          match stretchRescues M SG x.e with
          | some _ => killed := killed + 1
          | none =>
          match paramForkRescues M T x.e with
          | some _ => killed := killed + 1
          | none =>
              return { hit := some x, coverSeen := true, mixedSeen := mixedSeen,
                       killed := killed, skipped := skipped, size := all.size }
  while frontier.size > 0 do
    if all.size > cap then
      return { coverSeen := coverSeen, mixedSeen := mixedSeen, killed := killed,
               skipped := skipped, size := all.size, capped := true }
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
          if isCoverSep M x then
            mixedSeen := mixedSeen + 1
            if killed + skipped >= bcap then skipped := skipped + 1
            else
              match stretchRescues M SG x.e with
              | some _ => killed := killed + 1
              | none =>
              match paramForkRescues M T x.e with
              | some _ => killed := killed + 1
              | none =>
                  match best with
                  | none => best := some x
                  | some x' => if fsize x.e < fsize x'.e then best := some x
    match best with
    | some h =>
        return { hit := some h, coverSeen := true, mixedSeen := mixedSeen,
                 killed := killed, skipped := skipped, size := all.size }
    | none => pure ()
    frontier := next
  return { coverSeen := coverSeen, mixedSeen := mixedSeen, killed := killed,
           skipped := skipped, size := all.size }

/-! ## Driver -/

structure Stats where
  models : Nat := 0
  pairs : Nat := 0
  capped : Nat := 0
  coverHits : Nat := 0
  mixedSeps : Nat := 0
  killed : Nat := 0
  skipped : Nat := 0
  joinHits : Nat := 0
  maxClosure : Nat := 0
  maxTriples : Nat := 0
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

def runModel (pl : String → IO Unit) (M : FM) (cap : Nat) (bcap : Nat) (verbose : Bool)
    (st : Stats) : IO Stats := do
  let mut st := st
  let D := defClosure M
  let ups := upsets M
  let T := forkTable M D
  let SG := stretchTable M D
  let cands := ups.filter (fun u => (M.f &&& (M.full ^^^ u)) == 0 && !D.contains u)
  st := { st with maxTriples := max st.maxTriples T.size }
  if verbose && cands.size > 0 then
    pl s!"  model {describe M}"
    pl s!"    D ({D.size}): {D.toList.map (maskStr M.n)}   triples: {T.size}"
    pl s!"    undefinable valuations ({cands.size}): {cands.toList.map (maskStr M.n)}"
  for u in cands do
    st := { st with pairs := st.pairs + 1 }
    let vals : Array Mask := #[u] ++ D
    let out := search M vals #[] SG T cap bcap
    st := { st with maxClosure := max st.maxClosure out.size,
                    mixedSeps := st.mixedSeps + out.mixedSeen,
                    killed := st.killed + out.killed,
                    skipped := st.skipped + out.skipped }
    if out.coverSeen then st := { st with coverHits := st.coverHits + 1 }
    if out.capped then
      st := { st with capped := st.capped + 1 }
      pl s!"  CAPPED at {out.size}: {describe M} U={maskStr M.n u}"
    match out.hit with
    | some x =>
        st := { st with joinHits := st.joinHits + 1 }
        pl "  *** FULL-JOIN SEPARATING FORMULA FOUND (φ♠ candidate) ***"
        pl s!"      model  : {describe M}"
        pl s!"      V(p)   : {maskStr M.n u}"
        pl s!"      D      : {D.toList.map (maskStr M.n)}"
        pl s!"      φ      : {x.e.toString}"
        pl s!"      tuple  : {x.t.toList.map (maskStr M.n)}"
        pl s!"      LoG    : {x.lo.toList.map (maskStr M.n)}"
        pl s!"      UpG    : {x.up.toList.map (maskStr M.n)}"
        pl s!"      triples tested: {T.size}"
    | none => pure ()
  return st

/-! ## Verification: `pforkFM`/`pforkVp` really is a constraint model -/

/-- Check the constraint-model laws for `fork C χ δ₁ δ₂`.  Returns the
list of violated laws (empty = OK). -/
def checkFork (M : FM) (c d1 d2 : Mask) : List String := Id.run do
  let K := pforkFM M c
  let vp := pforkVp M d1 d2
  let full := K.full
  let mut bad : List String := []
  for v in [0:K.n] do
    if !hasBit K.ri[v]! v then bad := "refl_i" :: bad
    if !hasBit K.rm[v]! v then bad := "refl_m" :: bad
    if (K.rm[v]! &&& (full ^^^ K.ri[v]!)) != 0 then bad := "sub_mi" :: bad
    for u in [0:K.n] do
      if hasBit K.ri[v]! u && (K.ri[u]! &&& (full ^^^ K.ri[v]!)) != 0 then
        bad := "trans_i" :: bad
      if hasBit K.rm[v]! u && (K.rm[u]! &&& (full ^^^ K.rm[v]!)) != 0 then
        bad := "trans_m" :: bad
    if hasBit K.f v && (K.ri[v]! &&& (full ^^^ K.f)) != 0 then bad := "hered_F" :: bad
    if hasBit vp v && (K.ri[v]! &&& (full ^^^ vp)) != 0 then bad := "hered_V" :: bad
    if hasBit K.f v && !hasBit vp v then bad := "full_F" :: bad
  let mut acc : List String := []
  for s in bad do
    if !acc.contains s then acc := s :: acc
  return acc

/-- The validation battery: `p`, `⊥`, `◯⊥`, `◯⊥ ⊃ p`, `¬p`, `¬¬p`,
`φ★`, `φ♦` and `φ♣`. -/
def battery : Array PLLFormula := Id.run do
  let p : PLLFormula := PLLFormula.prop "p"
  let bot : PLLFormula := PLLFormula.falsePLL
  let ob : PLLFormula := bot.somehow
  let np : PLLFormula := p.ifThen bot
  let phiStar : PLLFormula := ((ob.ifThen p).ifThen (ob.and p)).and (np.ifThen bot)
  let phiDia : PLLFormula :=
    ((ob.ifThen p).or (ob.or np)).ifThen ((ob.and p).or (ob.and np))
  let phiClub : PLLFormula :=
    ((p.ifThen ob).or (np.ifThen ob)).ifThen ((ob.ifThen bot).or (ob.and p))
  return #[p, bot, ob, ob.ifThen p, np, np.ifThen bot, phiStar, phiDia, phiClub,
           phiClub.somehow]

/-- `verify`: (a) every admissible triple gives a constraint model;
(b) DROPPING the `δᵢ ⊆ χ` condition breaks `hered_V` (so the condition
is not decorative); (c) the degenerate triple `(χ, χ, ⊥)` reproduces the
`(χ,⊥)`-fork of `wip/branchdia.lean` on the whole battery. -/
def verifyModel (pl : String → IO Unit) (M : FM)
    (ok : Nat) (bad : Nat) (viol : Nat) (deg : Nat) : IO (Nat × Nat × Nat × Nat) := do
  let mut ok := ok
  let mut bad := bad
  let mut viol := viol
  let mut deg := deg
  let D := defClosure M
  for c in D do
    for d1 in D do
      for d2 in D do
        let adm := (d1 &&& (M.full ^^^ c)) == 0 && (d2 &&& (M.full ^^^ c)) == 0
        let errs := checkFork M c d1 d2
        if adm then
          if errs.isEmpty then ok := ok + 1
          else
            bad := bad + 1
            pl s!"  FORK-LAW FAILURE {describe M} ({maskStr M.n c},{maskStr M.n d1},\
{maskStr M.n d2}): {errs}"
        else
          if !errs.isEmpty then viol := viol + 1
    -- the degenerate member: (χ, χ, ⊥) must be the (χ,⊥)-fork
    let K := pforkFM M c
    for e in battery do
      let v1 := eval K (pforkVp M c M.f) e
      let v2 := eval K (c ||| (M.f <<< M.n)) e
      if v1 != v2 then
        deg := deg + 1
        pl s!"  DEGENERATE MISMATCH {describe M} guard={maskStr M.n c} φ={e.toString}"
  return (ok, bad, viol, deg)

def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  let pl (x : String) : IO Unit := do out.putStrLn x; out.flush
  let maxN := (args[0]?.getD "4").toNat!
  let cap := (args[1]?.getD "4000").toNat!
  let mode := args[2]?.getD "run"
  let bcap := (args[3]?.getD "64").toNat!
  pl s!"== ParamForkMixedConj probe: maxN={maxN} closureCap={cap} mode={mode} \
phaseBcap={bcap} =="
  for n in [2:maxN+1] do
    let ms := enumerate n
    pl s!"-- n={n}: {ms.size} rooted models (poset × Rₘ × F) --"
    if mode == "models" then continue
    let t0 ← IO.monoMsNow
    if mode == "verify" then
      let mut ok := 0
      let mut bad := 0
      let mut viol := 0
      let mut deg := 0
      for M in ms do
        let (a, b, c, d) ← verifyModel pl M ok bad viol deg
        ok := a; bad := b; viol := c; deg := d
      let t1 ← IO.monoMsNow
      pl s!"   verify: admissible triples {ok} (law failures {bad}); \
inadmissible triples breaking a law {viol}; degenerate mismatches {deg} [{t1 - t0} ms]"
      continue
    let mut st : Stats := {}
    let mut tick := 0
    for M in ms do
      st := { st with models := st.models + 1 }
      st ← runModel pl M cap bcap (mode == "detail") st
      tick := tick + 1
      -- checkpoint, so a run stopped at the wall-clock cap still reports
      if tick % 100 == 0 then
        let tc ← IO.monoMsNow
        pl s!"   [checkpoint {st.models}/{ms.size}] pairs {st.pairs}, capped {st.capped}, \
cover-hit pairs {st.coverHits}, COVER separators {st.mixedSeps} (killed by stretch-or-fork {st.killed}, \
skipped-at-budget {st.skipped}), FULL-JOIN HITS {st.joinHits}, max closure {st.maxClosure}, \
max triples {st.maxTriples} [{tc - t0} ms]"
    let t1 ← IO.monoMsNow
    pl s!"   models {st.models}, (model,U) pairs with U undefinable {st.pairs}, \
capped {st.capped}, cover-hit pairs {st.coverHits}, COVER separators {st.mixedSeps} \
(killed by a guarded stretch or a parameterised fork {st.killed}, \
skipped-at-budget {st.skipped}), \
FULL-JOIN HITS {st.joinHits}, max closure {st.maxClosure}, max triples {st.maxTriples} \
[{t1 - t0} ms]"
  pl "done"

end PForkProbe

def main (args : List String) : IO Unit := PForkProbe.main args
