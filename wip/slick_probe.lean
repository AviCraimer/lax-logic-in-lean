import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLG4Dec

/-!
# Canon-as-you-go interpolants + the deep X9 probe

The raw `itpA`/`itpE` construction explodes ~7×/budget step (X9 at b ≥ 6 is
unbuildable), so budgets past X9's threshold 16 are unreachable for the
library functions.  This file transcribes the two interpolant recursions
VERBATIM (same clauses, same guards, same assembly order) but applies a
canonicalising simplifier to every recursive return value.

SOUNDNESS OF THE TRANSCRIPTION: the clause guards test membership of
*context* formulas (`A ∈ Γ`, `A ∈ S`) only — never interpolant values —
and interpolants are only assembled by ∧ ∨ ⊃ ◯, for which PLL-equivalence
is a congruence.  Hence `itpE' ≡ itpE` and `itpA' ≡ itpA` (same equivalence
class), which is the object `descent_forcing` speaks about.  Cross-checked
below against the library functions by oracle at small budgets.

The canonicaliser: `nf` (equivalence-preserving rewrites) followed by
oracle-backed identification against a growing dictionary of
representatives; a syntactic memo avoids repeated oracle calls.
`search … = true` is kernel-grade (search_sound), so identifications are
sound; a missed identification (fuel) only makes the dictionary redundant,
never wrong.
-/

open PLLFormula
namespace PLLND
namespace Slick

/-! ## oracle -/

def provF (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C
def entails (X Y : PLLFormula) : Bool := provF 4000 [X] Y
def equivO (X Y : PLLFormula) : Bool := entails X Y && entails Y X
/-- cheap equivalence for canonicalisation: a missed identification only
adds a redundant representative — sound either way. -/
def equivC (X Y : PLLFormula) : Bool :=
  X = Y || (provF 1200 [X] Y && provF 1200 [Y] X)

/-! ## syntactic rewriter (each rewrite a PLL-equivalence) -/

def isTop (X : PLLFormula) : Bool := decide (X = truePLL)
def isBot (X : PLLFormula) : Bool := decide (X = falsePLL)

def simp1 : PLLFormula → PLLFormula
  | .and a b =>
      let a := simp1 a; let b := simp1 b
      if isBot a || isBot b then falsePLL
      else if isTop a then b else if isTop b then a
      else if a = b then a else .and a b
  | .or a b =>
      let a := simp1 a; let b := simp1 b
      if isTop a || isTop b then truePLL
      else if isBot a then b else if isBot b then a
      else if a = b then a else .or a b
  | .ifThen a b =>
      let a := simp1 a; let b := simp1 b
      if a = b then truePLL
      else if isTop a then b
      else if isTop b then truePLL
      else if isBot a then truePLL
      else .ifThen a b
  | .somehow a =>
      let a := simp1 a
      if isTop a then truePLL
      else match a with
        | .somehow c => .somehow c            -- ◯◯c ≡ ◯c
        | _ => .somehow a
  | X => X

/-- n-ary flatten + syntactic dedup + absorption for ∨ (all lattice laws,
equivalence-preserving).  `a ∨ (a ∧ c) ≡ a` and duplicate removal. -/
def orLeaves : PLLFormula → List PLLFormula
  | .or a b => orLeaves a ++ orLeaves b
  | x => [x]

def andLeaves : PLLFormula → List PLLFormula
  | .and a b => andLeaves a ++ andLeaves b
  | x => [x]

def rebuildOr : List PLLFormula → PLLFormula
  | [] => falsePLL
  | [x] => x
  | x :: xs => x.or (rebuildOr xs)

def rebuildAnd : List PLLFormula → PLLFormula
  | [] => truePLL
  | [x] => x
  | x :: xs => x.and (rebuildAnd xs)

def flatten1 : PLLFormula → PLLFormula
  | .or a b =>
      let ls := (orLeaves (.or (flatten1 a) (flatten1 b))).eraseDups
      -- absorption: drop an ∧-leaf if one of its conjuncts is another ∨-leaf
      let ls := ls.filter (fun x => match x with
        | .and _ _ => ¬ (andLeaves x).any (fun c => c ≠ x ∧ c ∈ ls)
        | _ => true)
      rebuildOr ls
  | .and a b =>
      let ls := (andLeaves (.and (flatten1 a) (flatten1 b))).eraseDups
      let ls := ls.filter (fun x => match x with
        | .or _ _ => ¬ (orLeaves x).any (fun c => c ≠ x ∧ c ∈ ls)
        | _ => true)
      rebuildAnd ls
  | .ifThen a b => .ifThen (flatten1 a) (flatten1 b)
  | .somehow a => .somehow (flatten1 a)
  | x => x

def nf (X : PLLFormula) : PLLFormula := Id.run do
  let mut x := X
  for _ in List.range 12 do
    let y := flatten1 (simp1 x)
    if y = x then return x
    x := y
  return x

/-! ## canonicalisation state -/

def fhash : PLLFormula → UInt64
  | .prop s => mixHash 1 (hash s)
  | .falsePLL => 2
  | .and a b => mixHash 3 (mixHash (fhash a) (fhash b))
  | .or a b => mixHash 5 (mixHash (fhash a) (fhash b))
  | .ifThen a b => mixHash 7 (mixHash (fhash a) (fhash b))
  | .somehow a => mixHash 11 (fhash a)

instance : Hashable PLLFormula := ⟨fhash⟩

structure St where
  dict : Array PLLFormula := #[]                 -- canonical representatives
  memo : Std.HashMap PLLFormula PLLFormula := {} -- nf-form ↦ representative
  oracleCalls : Nat := 0
  identify : Bool := true   -- false ⇒ nf+memo only (diagnosis mode, no oracle)

abbrev M := StateM St

/-- weight cap beyond which we skip dictionary identification (safety valve;
a skipped identification is only a lost collapse, never unsoundness). -/
def canonCap : Nat := 150

def canonM (X : PLLFormula) : M PLLFormula := do
  let n := nf X
  let st ← get
  match st.memo[n]? with
  | some r => return r
  | none =>
      if n.weight > canonCap ∨ !st.identify then
        return n                                  -- unregistered / diagnosis
      else
        let mut hit : Option PLLFormula := none
        let mut calls := 0
        for ψ in st.dict do
          calls := calls + 1
          if equivC n ψ then hit := some ψ; break
        match hit with
        | some ψ =>
            modify fun s => { s with memo := s.memo.insert n ψ,
                                     oracleCalls := s.oracleCalls + calls }
            return ψ
        | none =>
            modify fun s => { s with dict := s.dict.push n,
                                     memo := s.memo.insert n n,
                                     oracleCalls := s.oracleCalls + calls }
            return n

def flatMapM (f : α → M (List β)) : List α → M (List β)
  | [] => pure []
  | x :: xs => do
      let ys ← f x
      let zs ← flatMapM f xs
      pure (ys ++ zs)

/-! ## the transcribed interpolants (library clauses + canon at returns) -/

mutual

partial def itpE' (p : String) (S : Finset PLLFormula) :
    Nat → Nat → List PLLFormula → M PLLFormula
  | 0, _, _ => pure truePLL
  | fuel + 1, b, Γ => do
      let base :=
        (if falsePLL ∈ Γ then [falsePLL] else [])
        ++ Γ.filterMap (fun F => match F with
            | .prop q => if q = p then none else some (prop q)
            | _ => none)
      let rest ← flatMapM (fun F => match F with
          | .and A B =>
              if A ∈ Γ ∧ B ∈ Γ then pure []
              else if (A ∈ Γ ∨ A ∈ S) ∧ (B ∈ Γ ∨ B ∈ S) then do
                pure [← itpE' p S fuel b (A :: B :: Γ)]
              else pure []
          | .or A B =>
              if A ∈ Γ ∨ B ∈ Γ then pure []
              else if A ∈ S ∧ B ∈ S then do
                let x ← itpE' p S fuel b (A :: Γ)
                let y ← itpE' p S fuel b (B :: Γ)
                pure [x.or y]
              else pure []
          | .ifThen (.prop q) B =>
              if B ∈ Γ then pure []
              else if B ∈ S then
                if PLLFormula.prop q ∈ Γ then do
                  pure [← itpE' p S fuel b (B :: Γ)]
                else if q = p then pure []
                else do
                  pure [(prop q).ifThen (← itpE' p S fuel b (B :: Γ))]
              else pure []
          | .ifThen (.and A B) D =>
              if A.ifThen (B.ifThen D) ∈ Γ then pure []
              else if A.ifThen (B.ifThen D) ∈ S then do
                pure [← itpE' p S fuel b (A.ifThen (B.ifThen D) :: Γ)]
              else pure []
          | .ifThen (.or A B) D =>
              if A.ifThen D ∈ Γ ∧ B.ifThen D ∈ Γ then pure []
              else if (A.ifThen D ∈ Γ ∨ A.ifThen D ∈ S) ∧
                  (B.ifThen D ∈ Γ ∨ B.ifThen D ∈ S) then do
                pure [← itpE' p S fuel b (A.ifThen D :: B.ifThen D :: Γ)]
              else pure []
          | .ifThen (.ifThen A B) D =>
              if D ∈ Γ then pure []
              else if D ∈ S then
                if B.ifThen D ∈ Γ then
                  if (A.ifThen B).ifThen D ∈ S then
                    match b with
                    | 0 => pure []
                    | b' + 1 => do
                        let e ← itpE' p S fuel b' Γ
                        let a ← itpA' p S fuel b' Γ (A.ifThen B)
                        let e2 ← itpE' p S fuel b (D :: Γ)
                        pure [(e.ifThen a).ifThen e2]
                  else pure []
                else if B.ifThen D ∈ S then do
                  let e ← itpE' p S fuel b (B.ifThen D :: Γ)
                  let a ← itpA' p S fuel b (B.ifThen D :: Γ) (A.ifThen B)
                  let e2 ← itpE' p S fuel b (D :: Γ)
                  pure [(e.ifThen a).ifThen e2]
                else pure []
              else pure []
          | .ifThen (.somehow A) B =>
              if B ∈ Γ then pure []
              else if B ∈ S then do
                let part1 ←
                  (if A.somehow.ifThen B ∈ S then
                    (match b with
                     | 0 => pure []
                     | b' + 1 => do
                        let a ← itpA' p S fuel b' Γ A
                        let eB ← itpE' p S fuel b (B :: Γ)
                        let e ← itpE' p S fuel b' Γ
                        let am ← itpA' p S fuel b' Γ A.somehow
                        pure [a.ifThen eB, ((e.ifThen am).somehow).ifThen eB])
                  else pure [])
                let part2 ← flatMapM (fun X => match X with
                    | .somehow x =>
                        if x ∈ Γ ∨ x ∉ S then pure []
                        else do
                          let e ← itpE' p S fuel b (x :: Γ)
                          let am ← itpA' p S fuel b (x :: Γ) A.somehow
                          let eB ← itpE' p S fuel b (B :: Γ)
                          pure [((e.ifThen am).somehow).ifThen eB]
                    | _ => pure []) Γ
                pure (part1 ++ part2)
              else pure []
          | .somehow χ =>
              if χ ∈ Γ ∨ χ ∉ S then pure []
              else do
                pure [(← itpE' p S fuel b (χ :: Γ)).somehow]
          | _ => pure []) Γ
      canonM (andAll (base ++ rest))

partial def itpA' (p : String) (S : Finset PLLFormula) :
    Nat → Nat → List PLLFormula → PLLFormula → M PLLFormula
  | 0, _, _, _ => pure falsePLL
  | fuel + 1, b, Γ, C => do
      let env ← flatMapM (fun F => match F with
          | .prop q =>
              if q = p ∧ C = PLLFormula.prop p then pure [truePLL] else pure []
          | .and A B =>
              if A ∈ Γ ∧ B ∈ Γ then pure []
              else if (A ∈ Γ ∨ A ∈ S) ∧ (B ∈ Γ ∨ B ∈ S) then do
                pure [← itpA' p S fuel b (A :: B :: Γ) C]
              else pure []
          | .or A B =>
              if A ∈ Γ ∨ B ∈ Γ then pure []
              else if A ∈ S ∧ B ∈ S then do
                let eA ← itpE' p S fuel b (A :: Γ)
                let aA ← itpA' p S fuel b (A :: Γ) C
                let eB ← itpE' p S fuel b (B :: Γ)
                let aB ← itpA' p S fuel b (B :: Γ) C
                pure [(eA.ifThen aA).and (eB.ifThen aB)]
              else pure []
          | .ifThen (.prop q) B =>
              if B ∈ Γ then pure []
              else if B ∈ S then
                if PLLFormula.prop q ∈ Γ then do
                  pure [← itpA' p S fuel b (B :: Γ) C]
                else if q = p then pure []
                else do
                  pure [(prop q).and (← itpA' p S fuel b (B :: Γ) C)]
              else pure []
          | .ifThen (.and A B) D =>
              if A.ifThen (B.ifThen D) ∈ Γ then pure []
              else if A.ifThen (B.ifThen D) ∈ S then do
                pure [← itpA' p S fuel b (A.ifThen (B.ifThen D) :: Γ) C]
              else pure []
          | .ifThen (.or A B) D =>
              if A.ifThen D ∈ Γ ∧ B.ifThen D ∈ Γ then pure []
              else if (A.ifThen D ∈ Γ ∨ A.ifThen D ∈ S) ∧
                  (B.ifThen D ∈ Γ ∨ B.ifThen D ∈ S) then do
                pure [← itpA' p S fuel b (A.ifThen D :: B.ifThen D :: Γ) C]
              else pure []
          | .ifThen (.ifThen A B) D =>
              if D ∈ Γ then pure []
              else if D ∈ S then
                if B.ifThen D ∈ Γ then
                  if (A.ifThen B).ifThen D ∈ S then
                    match b with
                    | 0 => pure []
                    | b' + 1 => do
                        let e ← itpE' p S fuel b' Γ
                        let a ← itpA' p S fuel b' Γ (A.ifThen B)
                        let aD ← itpA' p S fuel b (D :: Γ) C
                        pure [(e.ifThen a).and aD]
                  else pure []
                else if B.ifThen D ∈ S then do
                  let e ← itpE' p S fuel b (B.ifThen D :: Γ)
                  let a ← itpA' p S fuel b (B.ifThen D :: Γ) (A.ifThen B)
                  let aD ← itpA' p S fuel b (D :: Γ) C
                  pure [(e.ifThen a).and aD]
                else pure []
              else pure []
          | .ifThen (.somehow A) B =>
              if B ∈ Γ then pure []
              else if B ∈ S then do
                let part1 ←
                  (if A.somehow.ifThen B ∈ S then
                    (match b with
                     | 0 => pure []
                     | b' + 1 => do
                        let a ← itpA' p S fuel b' Γ A
                        let aB ← itpA' p S fuel b (B :: Γ) C
                        let e ← itpE' p S fuel b' Γ
                        let am ← itpA' p S fuel b' Γ A.somehow
                        pure [a.and aB, ((e.ifThen am).somehow).and aB])
                  else pure [])
                let part2 ← flatMapM (fun X => match X with
                    | .somehow x =>
                        if x ∈ Γ ∨ x ∉ S then pure []
                        else do
                          let e ← itpE' p S fuel b (x :: Γ)
                          let am ← itpA' p S fuel b (x :: Γ) A.somehow
                          let aB ← itpA' p S fuel b (B :: Γ) C
                          pure [((e.ifThen am).somehow).and aB]
                    | _ => pure []) Γ
                pure (part1 ++ part2)
              else pure []
          | .somehow χ => (match C with
                | .somehow _ =>
                    if χ ∈ Γ ∨ χ ∉ S then pure []
                    else do
                      let e ← itpE' p S fuel b (χ :: Γ)
                      let a ← itpA' p S fuel b (χ :: Γ) C
                      pure [(e.ifThen a).somehow]
                | _ => pure [])
          | _ => pure []) Γ
      let goal ← (match C with
          | .prop q => if q = p then pure [] else pure [prop q]
          | .falsePLL => pure []
          | .and C₁ C₂ => do
              let x ← itpA' p S fuel b Γ C₁
              let y ← itpA' p S fuel b Γ C₂
              pure [x.and y]
          | .or C₁ C₂ => do
              let x ← itpA' p S fuel b Γ C₁
              let y ← itpA' p S fuel b Γ C₂
              pure [x, y]
          | .ifThen C₁ C₂ =>
              if C₁ ∈ Γ then
                match b with
                | 0 => pure []
                | b' + 1 => do
                    let e ← itpE' p S fuel b' (C₁ :: Γ)
                    let a ← itpA' p S fuel b (C₁ :: Γ) C₂
                    pure [e.ifThen a]
              else do
                let e ← itpE' p S fuel b (C₁ :: Γ)
                let a ← itpA' p S fuel b (C₁ :: Γ) C₂
                pure [e.ifThen a]
          | .somehow D =>
              match b with
              | 0 => pure []
              | b' + 1 => do
                  let e ← itpE' p S fuel b' Γ
                  let a ← itpA' p S fuel b Γ D
                  pure [(e.ifThen a).somehow])
      let others := goal ++ env
      match C with
      | .somehow _ =>
          if others.isEmpty then canonM (orAll others)
          else
            (match b with
             | 0 => canonM (orAll others)
             | b' + 1 => do
                 let e ← itpE' p S fuel b' Γ
                 -- TRUNCATION ABSORPTION (sound, oracle-free):
                 --   orAll (others ++ [◯(e ⊃ orAll others)]) ≡ ◯(e ⊃ orAll others)
                 -- since each o ∈ others ⊢ orAll others ⊢ e ⊃ orAll others
                 -- ⊢ ◯(e ⊃ orAll others) by the ◯-unit.  This is the rewrite
                 -- that kills the ~7×/step raw growth.
                 canonM ((e.ifThen (orAll others)).somehow))
      | _ => canonM (orAll others)

end

/-! ## drivers -/

def op : PLLFormula := prop "p"
def bx (X : PLLFormula) : PLLFormula := X.somehow
def bb : PLLFormula := bx falsePLL              -- ◯⊥
def nbb : PLLFormula := bb.ifThen falsePLL      -- ¬◯⊥
def pp : String := "p"

/-- run itpA' from a given state, returning value + new state. -/
def runA (st : St) (S : Finset PLLFormula) (fuel b : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) : PLLFormula × St :=
  (itpA' pp S fuel b Γ g).run st
def runE (st : St) (S : Finset PLLFormula) (fuel b : Nat)
    (Γ : List PLLFormula) : PLLFormula × St :=
  (itpE' pp S fuel b Γ).run st

/-- DIAGNOSIS MODE: canon without oracle identification (nf+memo only) —
zero oracle calls, so the pure-nf value SHAPES print fast.  Used to design
targeted rewrites; flip back for the identifying run. -/
def diagMain : IO Unit := do
  let out ← IO.getStdout
  IO.println "diagnosis: pure-nf value shapes (no oracle)"; out.flush
  let X9S : Finset PLLFormula := {falsePLL, bb, nbb, op, bx op}
  let X9Γ : List PLLFormula := [nbb]
  let X9g : PLLFormula := bx op
  let mut st : St := { identify := false }
  for b in List.range 7 do
    let (vA, st') := (itpA' pp X9S 24 b X9Γ X9g).run st
    let (vE, st'') := (itpE' pp X9S 24 b X9Γ).run st'
    st := st''
    IO.println s!"-- b={b}: A w={vA.weight}  E w={vE.weight}"
    if vA.weight ≤ 260 then IO.println s!"   A = {vA.toString}"
    if vE.weight ≤ 260 then IO.println s!"   E = {vE.toString}"
    out.flush

def main : IO Unit := do
  let out ← IO.getStdout
  IO.println "main started"; out.flush
  -- ===== cross-check vs library at small budgets (soundness of transcription)
  let fuelI := 24
  let X9S : Finset PLLFormula := {falsePLL, bb, nbb, op, bx op}
  let X9Γ : List PLLFormula := [nbb]
  let X9g : PLLFormula := bx op
  let C1S : Finset PLLFormula := {(bx op).ifThen op, op, bx op}
  let C1Γ : List PLLFormula := [(bx op).ifThen op]
  IO.println "== cross-check (itpA' ≡ library itpA, oracle) =="
  let mut st : St := {}
  for (nm, S, Γ, g) in [("C1", C1S, C1Γ, op), ("X9", X9S, X9Γ, X9g)] do
    for b in [0, 1, 2] do
      let (v, st') := runA st S fuelI b Γ g
      st := st'
      -- compare against nf of the library value (nf is equivalence-preserving,
      -- and feeding the RAW library formula to the oracle is hopeless: its
      -- weight sets the search-space cap)
      let libn := nf (itpA pp S fuelI b Γ g)
      let verdict := if libn.weight ≤ 80 then s!"{equivO v libn}"
                     else s!"skipped (nf-lib w={libn.weight})"
      IO.println s!"  {nm} b={b}: itpA'≡itpA? {verdict}   (canonW={v.weight}, nfLibW={libn.weight})"
      out.flush
  -- ===== the deep X9 run: b = 0..18 vs threshold 16
  IO.println ""
  IO.println "== deep X9:  S = ⊥ ◯⊥ ¬◯⊥ p ◯p, Γ = [¬◯⊥], g = ◯p, threshold 16 =="
  let mut prevA : Option PLLFormula := none
  let mut prevE : Option PLLFormula := none
  for b in List.range 5 do
    let t0 ← IO.monoMsNow
    let (vA, st') := runA st X9S fuelI b X9Γ X9g
    let (vE, st'') := runE st' X9S fuelI b X9Γ
    st := st''
    let t1 ← IO.monoMsNow
    let chk := fun (q v : PLLFormula) =>
      if q = v then "same"
      else if q.weight ≤ 100 ∧ v.weight ≤ 100 then
        s!"CHANGED (desc {entails v q}, asc {entails q v})"
      else s!"CHANGED (oracle skipped, w={q.weight}→{v.weight})"
    let chA := match prevA with | none => "-" | some q => chk q vA
    let chE := match prevE with | none => "-" | some q => chk q vE
    prevA := some vA; prevE := some vE
    IO.println s!"  b={b}: A-class w={vA.weight} [{chA}]  E-class w={vE.weight} [{chE}]  dict={st.dict.size} ({t1-t0} ms)"
    out.flush
  IO.println ""
  IO.println s!"final: dict size {st.dict.size}, oracle calls {st.oracleCalls}"
  IO.println "dictionary (weights): "
  IO.println s!"  {st.dict.toList.map (fun ψ => ψ.weight)}"
  -- print the stabilised A/E values if small
  match prevA, prevE with
  | some a, some e =>
      IO.println s!"final A-class ({a.weight}): {if a.weight ≤ 120 then a.toString else "big"}"
      IO.println s!"final E-class ({e.weight}): {if e.weight ≤ 120 then e.toString else "big"}"
  | _, _ => pure ()

-- run with:  lake env lean --run wip/slick_probe.lean
-- (NOT #eval: #eval buffers all IO output until completion, so long runs
-- look silent; --run streams to real stdout.)

end Slick
end PLLND

def main : IO Unit := PLLND.Slick.main   -- (diagMain = shape diagnosis mode)
