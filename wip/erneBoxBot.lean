import LaxLogic.PLLSearchCmd
import rnEmbed

/-!
# What is `𝔟◯⊥`?

`𝔟a = {x → a | x ∈ A}` is the range of the boolean nucleus `βₐ x = (x→a)→a`
(Erné §5).  For `a = ⊥` that is the booleanization, proved four-element in
`wip/negFour.lean` + `wip/negFourDistinct.lean`.  For `a = ◯⊥` it is the least
l-ideal containing `◯⊥` (Erné Thm 5.2), boolean, with least element `◯⊥` and
greatest `⊤`.

`𝔟◯⊥` is the image of `· → ◯⊥`, so the same computation answers it: apply
`· → ◯⊥` to a spread of closed formulas and count the distinct classes.

Three members are known already: `◯⊥`, `⊤`, and `¬¬◯⊥ ⊃ ◯⊥` (which is
`β_◯⊥(¬◯⊥)`, computed in `wip/erneNuclei.lean`, and is Figure 6's fifth
element).  A boolean lattice cannot have exactly three elements, so there is
at least a fourth.

Needs `rnEmbed.olean` on `LEAN_PATH`; see `wip/erneBool2.lean` for the recipe.
PROBE, not a theorem.
-/

open PLLFormula PLLND PLLND.Search

namespace ErneBoxBot

def oBot : PLLFormula := falsePLL.somehow
def imp (x a : PLLFormula) : PLLFormula := x.ifThen a
def neg (x : PLLFormula) : PLLFormula := imp x falsePLL

/-- `x → ◯⊥`, the map whose image is `𝔟◯⊥`. -/
def toBox (x : PLLFormula) : PLLFormula := imp x oBot

def t (n : Nat) : PLLFormula := PLLND.RNEmbed.rnSub n

def derives (P Q : PLLFormula) : Bool :=
  match settle budgetedConfig [P] Q with
  | .proved _ => true
  | _         => false

def interdB (A B : PLLFormula) : Bool := derives A B && derives B A

/-- The spread of `x` we apply `· → ◯⊥` to: the Figure 6 elements, the ladder
rungs, the boxed rungs, and the boxed odd chain. -/
def sample : List (String × PLLFormula) :=
  let ng := neg oBot
  let nng := neg ng
  [ ("⊥", falsePLL), ("◯⊥", oBot), ("¬◯⊥", ng), ("¬¬◯⊥", nng)
  , ("◯¬◯⊥", ng.somehow), ("¬¬◯⊥⊃◯⊥", imp nng oBot)
  , ("(¬¬◯⊥⊃◯⊥)⊃◯¬◯⊥", imp (imp nng oBot) ng.somehow), ("⊤", truePLL)
  , ("◯⊥∨¬◯⊥", oBot.or ng), ("¬◯⊥∨¬¬◯⊥", ng.or nng) ]
  ++ (List.range 7).map (fun (n : Nat) => ("t " ++ ToString.toString n, t n))
  ++ (List.range 5).map (fun (n : Nat) => ("◯t " ++ ToString.toString n, (t n).somehow))
  ++ (List.range 4).map (fun (k : Nat) => ("chainF " ++ ToString.toString k, (t (2*k+1)).somehow))

/-- Collect the distinct interderivability classes of `{x → ◯⊥ : x ∈ sample}`,
keeping the first name that produced each. -/
def classes : List (String × PLLFormula) :=
  sample.foldl
    (fun acc (nm, x) =>
      let v := toBox x
      if acc.any (fun (_, w) => interdB v w) then acc else acc ++ [(nm, v)])
    []

def report : String :=
  "distinct classes in the image of (· → ◯⊥), over "
    ++ ToString.toString sample.length ++ " sampled arguments:\n"
  ++ String.intercalate "\n"
       (classes.map (fun (nm, _) => "  from " ++ nm))
  ++ "\n\ncount: " ++ ToString.toString classes.length

/-- Where each class sits relative to the known three. -/
def locate : String :=
  let known : List (String × PLLFormula) :=
    [ ("◯⊥", oBot)
    , ("¬¬◯⊥⊃◯⊥", imp (neg (neg oBot)) oBot)
    , ("⊤", truePLL) ]
  String.intercalate "\n"
    (classes.map (fun (nm, v) =>
      let hits := known.filterMap (fun (kn, k) => if interdB v k then some kn else none)
      "  (" ++ nm ++ " → ◯⊥)  ⊣⊢  "
        ++ (if hits.isEmpty then "*** NEW, none of the three ***"
            else String.intercalate "/" hits)))

/-! ## Honest, three-valued comparison

`derives` above folds `.unknown` into `false`, so a budget-exhausted search
reads as "not derivable" and inflates the class count.  A finite boolean
lattice cannot have five elements, so the count of 5 above is an artefact.
Here is the full pairwise matrix on the candidate values, with `?` kept
distinct from `.`. -/

def cell3 (A B : PLLFormula) : String :=
  match settle budgetedConfig [A] B with
  | .proved _      => "Y"
  | .refuted _ _ _ => "."
  | .unknown       => "?"

def cands : List (String × PLLFormula) :=
  let ng := neg oBot
  let nng := neg ng
  [ ("◯⊥",              oBot)
  , ("¬◯⊥→◯⊥",          toBox ng)
  , ("¬¬◯⊥→◯⊥",         toBox nng)
  , ("((..)⊃◯¬◯⊥)→◯⊥",  toBox (imp (imp nng oBot) ng.somehow))
  , ("chainF 3→◯⊥",     toBox ((t 7).somehow))
  , ("⊤",               truePLL) ]

def matrix3 : String :=
  String.intercalate "\n"
    (cands.map (fun (n1, a) =>
      let pad := String.ofList (List.replicate (max 1 (20 - n1.length)) ' ')
      n1 ++ pad ++ String.intercalate " " (cands.map (fun (_, b) => cell3 a b))))

end ErneBoxBot

#eval IO.println ("columns, in order: " ++
  String.intercalate ", " (ErneBoxBot.cands.map Prod.fst))
#eval IO.println ErneBoxBot.matrix3

/-! ## Where `¬◯⊥→◯⊥` sits in Figure 6

It is closed and `∨`-free, so by Bezhanishvili et al. Thm 9.3 it is one of the
eight. -/

namespace ErneBoxBot
def fig6 : List (String × PLLFormula) :=
  let ng := neg oBot
  let nng := neg ng
  [ ("⊥", falsePLL), ("◯⊥", oBot), ("¬◯⊥", ng), ("¬¬◯⊥", nng)
  , ("◯¬◯⊥", ng.somehow), ("¬¬◯⊥⊃◯⊥", imp nng oBot)
  , ("(¬¬◯⊥⊃◯⊥)⊃◯¬◯⊥", imp (imp nng oBot) ng.somehow), ("⊤", truePLL) ]

def placeIt : String :=
  let v := toBox (neg oBot)
  String.intercalate "\n"
    (fig6.map (fun (nm, e) => "  ¬◯⊥→◯⊥ vs " ++ nm ++ " : " ++ cell3 v e ++ cell3 e v))
end ErneBoxBot

#eval IO.println ErneBoxBot.placeIt
