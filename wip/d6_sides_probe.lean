import LaxLogic.PLLSearch

/-! Secondary diagnostics for the gap-row forced-skip cell:
(a) was the ∀-side sweep-refutable on `defaultFrames` alone (i.e. was
    there ever a battery gap for THIS cell)?
(b) sweep-only verdicts on the three ∃-side skipped cells of the gap
    row: ◯(◯p⊃p) ⊢ D for D ∈ { (◯¬◯⊥)∨¬¬◯⊥, ◯D₆-class, D₆ }. -/

open PLLFormula
namespace PLLND
namespace D6Sides

def bb : PLLFormula := falsePLL.somehow
def nbb : PLLFormula := bb.ifThen falsePLL
def nnbb : PLLFormula := nbb.ifThen falsePLL
def D6 : PLLFormula := (nbb.somehow).ifThen (bb.or nbb)
def op : PLLFormula := .prop "p"
def phi : PLLFormula := (op.somehow.ifThen op).somehow

def dOr : PLLFormula := (nbb.somehow).or nnbb        -- (◯¬◯⊥) ∨ ¬¬◯⊥, crank≤5
def dBox : PLLFormula := D6.somehow                  -- ◯D₆, crank≤8

def cfgDefault : Search.Config := { findBudget := some 0, emitClosureCap := 0 }

def sweepOnly (cfg : Search.Config) (Γ : List PLLFormula) (C : PLLFormula) :
    Option (FinCM × Nat) :=
  match Search.sweepCert cfg (Γ.map Search.nf) (Search.nf C) Γ C with
  | some ⟨M, w, _⟩ => some (M, w)
  | none => none

-- (a) ∀-side on defaultFrames only
#eval sweepOnly cfgDefault [D6] phi

-- (b) ∃-side sweeps on the widened battery shapes (defaultFrames is
-- a sublist of the v2quant battery; try both batteries)
#eval sweepOnly cfgDefault [phi] D6
#eval sweepOnly cfgDefault [phi] dOr
#eval sweepOnly cfgDefault [phi] dBox

end D6Sides
end PLLND
