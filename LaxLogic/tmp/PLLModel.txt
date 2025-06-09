import LaxLogic.PLLFormula
import Mathlib.Tactic

structure PLLModelComponents.{w} (World: Type w) where
  accessibility: (Preorder  World)
  modality: (Preorder World)
  fallible: Set World
  evaluate (p: PLLFormula) : Set World

abbrev PLLModelComponents.Rᵢ.{w} {World: Type w} (M: PLLModelComponents World):= M.accessibility
abbrev PLLModelComponents.Rₘ.{w} {World: Type w} (M: PLLModelComponents World):= M.modality
abbrev PLLModelComponents.F.{w} {World: Type w} (M: PLLModelComponents World):= M.fallible
abbrev PLLModelComponents.V.{w} {World: Type w} (M: PLLModelComponents World):= M.evaluate


structure PLLModelAxioms.{w}{World: Type w} (M : PLLModelComponents.{w} World) : Type where
  nonempty_worlds: Nonempty World
  modality_subrelation_accessibility: M.Rₘ.lt ≤ M.Rᵢ.lt
  fallible_hereditary  {w w': World} (h1: M.Rᵢ.lt w w') : w ∈  M.F → w' ∈ M.F
  evaluation_hereditary  {w w': World} {p: PLLFormula} (h1: M.Rᵢ.lt w w')  : w ∈ M.V p  →  w' ∈ M.V p
  fallible_evaluation (p: PLLFormula) :   M.F ⊆ M.V p

-- A model is a triple of the world type, the components and proofs of the axioms.
def PLLModel.{w} := Σ (World: Type w), Σ (MC : PLLModelComponents World), PLLModelAxioms MC

-- Define accessors
def PLLModel.WorldType (M: PLLModel) := M.1
abbrev PLLModel.W (M: PLLModel) := M.WorldType
def PLLModel.components (M: PLLModel) := M.2.1

abbrev PLLModel.Rᵢ (M: PLLModel):= M.components.accessibility
abbrev PLLModel.Rₘ (M: PLLModel):= M.components.modality
abbrev PLLModel.F (M: PLLModel ):= M.components.fallible
abbrev PLLModel.V (M: PLLModel):= M.components.evaluate

def PLLModel.axioms (M: PLLModel) := M.2.2
