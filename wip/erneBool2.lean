import LaxLogic.PLLSearchCmd
import rnEmbed

/-!
# 𝔟⊥ against the parts of RN(◯,{}) that are actually infinite

`wip/erneBool.lean` negated twenty small closed formulas and every result
landed in `{⊥, ¬◯⊥, ¬¬◯⊥, ⊤}`.  That sample proves nothing about the question,
because it never touched the parts of RN(◯,{}) that make it infinite:

* the Rieger–Nishimura ladder `rnSub n` embedded by `p ↦ ◯⊥`
  (`closed_lax_infinite`);
* the boxed odd rungs `chainF k = ◯ rnSub (2k+1)`, strictly increasing in `k`
  (`chain_step_strict`);
* the gap antichain `gap k` and the meets `Gmeet n`, which have no greatest
  lower bound (`gap_no_glb`) — the floorless descending chain.

If `¬` takes infinitely many values on any of these families then 𝔟⊥ is
infinite.  If they all collapse into the same four, that is real evidence the
booleanization is the four-element free boolean algebra on one generator —
i.e. our classical rung `varfree_exactly_four`.

Needs `rnEmbed.olean` on `LEAN_PATH` (it is imported under its root-level
name, so `lake build` does not cover it):

    D=$(mktemp -d)
    lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$D\" lean wip/rnEmbed.lean -o $D/rnEmbed.olean"
    lake env sh -c "LEAN_PATH=\"\$LEAN_PATH:$D\" lean wip/erneBool2.lean"

PROBE, not a theorem.
-/

open PLLFormula PLLND PLLND.Search

namespace ErneBool2

def g : PLLFormula := falsePLL.somehow
def neg (x : PLLFormula) : PLLFormula := x.ifThen falsePLL

def reps : List (String × PLLFormula) :=
  [ ("⊥", falsePLL), ("¬◯⊥", neg g), ("¬¬◯⊥", neg (neg g)), ("⊤", truePLL) ]

def derives (P Q : PLLFormula) : Bool :=
  match settle budgetedConfig [P] Q with
  | .proved _ => true
  | _         => false

def interdB (A B : PLLFormula) : Bool := derives A B && derives B A

def classify (x : PLLFormula) : String :=
  match reps.find? (fun (_, r) => interdB (neg x) r) with
  | some (nm, _) => nm
  | none         => "*** NONE OF THE FOUR ***"

/-- The ladder rung `tₙ`, embedded by `p ↦ ◯⊥`. -/
def t (n : Nat) : PLLFormula := PLLND.RNEmbed.rnSub n

/-- The ladder rungs `tₙ`, the boxed rungs `◯tₙ`, the boxed odd rungs
`chainF k = ◯t_{2k+1}` (strictly increasing in `k`), and `tₙ ⊃ ◯⊥`. -/
def families : List (String × (Nat → PLLFormula)) :=
  [ ("t n      ", fun n => t n)
  , ("◯t n     ", fun n => (t n).somehow)
  , ("chainF k ", fun k => (t (2 * k + 1)).somehow)
  , ("t n ⊃ ◯⊥ ", fun n => (t n).ifThen g) ]

def rowFor (nm : String) (f : Nat → PLLFormula) (ns : List Nat) : String :=
  nm ++ ":  " ++ String.intercalate "  "
    (ns.map (fun (n : Nat) => toString n ++ "↦" ++ classify (f n)))

def report : String :=
  String.intercalate "\n"
    (families.map (fun (nm, f) => rowFor nm f [0,1,2,3,4,5,6,7,8]))

end ErneBool2

#eval IO.println ErneBool2.report
