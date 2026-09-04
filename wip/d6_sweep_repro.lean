import LaxLogic.PLLSearch

/-! Reproduce the exact v2quant scan call on the stalled cell:
`Search.decide cfgScan [D₆] ◯(◯p⊃p)` — sweep stage only, then the
full decide. -/

open PLLFormula
namespace PLLND
namespace D6Repro

def bb : PLLFormula := falsePLL.somehow
def nbb : PLLFormula := bb.ifThen falsePLL
def D6 : PLLFormula := (nbb.somehow).ifThen (bb.or nbb)
def op : PLLFormula := .prop "p"
def phi : PLLFormula := (op.somehow.ifThen op).somehow

-- the v2quant battery, rebuilt verbatim
def closeF (f : Search.Frame) : Search.Frame := Id.run do
  let mut ri := f.ri
  let mut rm := f.rm
  let mut changed := true
  while changed do
    changed := false
    for e in ri do
      for e' in ri do
        if e.2 == e'.1 && !(decide ((e.1, e'.2) ∈ ri)) && e.1 != e'.2 then
          ri := ri ++ [(e.1, e'.2)]
          changed := true
    for e in rm do
      for e' in rm do
        if e.2 == e'.1 && !(decide ((e.1, e'.2) ∈ rm)) && e.1 != e'.2 then
          rm := rm ++ [(e.1, e'.2)]
          changed := true
  return ⟨f.n, ri, rm, f.fall⟩

def chain3F : Search.Frame := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], []⟩

def residFrames : List Search.Frame :=
  [⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)], [], [4]⟩,
   ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)], [(3,4)], [4]⟩,
   ⟨5, [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)], [], []⟩,
   ⟨3, [(0,1),(0,2)], [], []⟩,
   ⟨3, [(0,1),(0,2)], [], [2]⟩,
   ⟨3, [(0,1),(0,2)], [(0,2)], [2]⟩,
   ⟨4, [(0,1),(0,2),(1,3),(2,3)], [], [3]⟩,
   ⟨4, [(0,1),(0,2),(1,3),(2,3)], [(1,3),(2,3)], [3]⟩,
   ⟨4, [(0,1),(0,2),(1,3),(2,3)], [], []⟩,
   ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [], [3]⟩,
   ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [], []⟩,
   ⟨4, [(0,1),(0,2),(0,3),(1,3),(2,3)], [(0,1)], [3]⟩]

def scanFrames : List Search.Frame :=
  (Search.defaultFrames ++ [chain3F] ++ residFrames).map closeF

def cfgScan : Search.Config :=
  { frames := scanFrames, findBudget := some 2000, emitClosureCap := 0 }

-- sweep stage alone (the untrusted proposer + checkB gate)
def sweepRes : Option (FinCM × Nat) :=
  match Search.sweepCert cfgScan [Search.nf D6] (Search.nf phi) [D6] phi with
  | some ⟨M, w, _⟩ => some (M, w)
  | none => none

#eval sweepRes
#eval match Search.decide cfgScan [D6] phi with
      | .proved _ => "proved"
      | .refuted M w _ => s!"REFUTED at w={w} in {repr M}"
      | .unknown => "unknown"

end D6Repro
end PLLND
