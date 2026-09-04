import LaxLogic.PLLSearchCmd

/-!
# The eight elements of Figure 6, in our notation

Bezhanishvili–Bezhanishvili–Carai–Gabelaia–Ghilardi–Jibladze, *Diego's
Theorem for nuclear implicative semilattices* (arXiv:2001.11060), Theorem 9.3
with Figure 6: the free 0-generated **bounded** nuclear implicative
semilattice — equivalently (their §1) the `∨`-free closed fragment of
Fairtlough–Mendler lax logic — is the eight-element algebra

                              1
              (¬¬j(0)→j(0))→j(¬j(0))     ¬¬j(0)→j(0)
                     ¬¬j(0)              j(¬j(0))
                      j(0)               ¬j(0)
                              0

Reading `j = ◯` and `0 = ⊥`, this probe computes the full order among those
eight formulas *in our formalisation*, by certificate-carrying search.  Its
purpose is to check that their Figure 6 transcribes into our syntax as
claimed, and in particular that the two middle layers really are antichains.

This is a PROBE, not a theorem: `#eval` output is not kernel-checked.  What
it produces is a matrix to be read, and the cells worth pinning afterwards.

DELIBERATELY NOT REGISTERED in `lakefile.toml`: the escalation at the foot of
the file runs a 5-million-node search, too slow for every `lake build`.  Run
it on demand with

    lake env lean wip/nisFig6.lean

The 8×8 matrix itself is cheap and is pinned with `#guard_msgs`, so that much
is checked whenever the file is run.
-/

open PLLFormula PLLND PLLND.Search

namespace NISFig6

/-- `⊥`. -/
def e0 : PLLFormula := falsePLL
/-- `◯⊥` = `j(0)`. -/
def e1 : PLLFormula := falsePLL.somehow
/-- `¬◯⊥` = `¬j(0)`. -/
def e2 : PLLFormula := e1.ifThen falsePLL
/-- `¬¬◯⊥` = `¬¬j(0)`. -/
def e3 : PLLFormula := e2.ifThen falsePLL
/-- `◯¬◯⊥` = `j(¬j(0))`. -/
def e4 : PLLFormula := e2.somehow
/-- `¬¬◯⊥ ⊃ ◯⊥` = `¬¬j(0) → j(0)`. -/
def e5 : PLLFormula := e3.ifThen e1
/-- `(¬¬◯⊥ ⊃ ◯⊥) ⊃ ◯¬◯⊥` = `(¬¬j(0)→j(0)) → j(¬j(0))`. -/
def e6 : PLLFormula := e5.ifThen e4
/-- `⊤`. -/
def e7 : PLLFormula := truePLL

def elts : List PLLFormula := [e0, e1, e2, e3, e4, e5, e6, e7]

def names : List String :=
  ["⊥", "◯⊥", "¬◯⊥", "¬¬◯⊥", "◯¬◯⊥", "¬¬◯⊥⊃◯⊥", "(¬¬◯⊥⊃◯⊥)⊃◯¬◯⊥", "⊤"]

/-- `Y` = `A ⊢ B` proved, `.` = refuted by a checked countermodel,
`?` = neither within the budget. -/
def cell (A B : PLLFormula) : String :=
  match settle budgetedConfig [A] B with
  | .proved _      => "Y"
  | .refuted _ _ _ => "."
  | .unknown       => "?"

/-- Row `i` of the entailment matrix: which `e j` follow from `e i`. -/
def row (i : Nat) : String :=
  let A := elts.getD i truePLL
  String.intercalate " " (List.range 8 |>.map (fun j => cell A (elts.getD j truePLL)))

/-- The full 8×8 entailment matrix, rows = antecedent, columns = succedent. -/
def matrix : String :=
  String.intercalate "\n"
    (List.range 8 |>.map (fun i =>
      let nm := names.getD i "?"
      nm ++ String.ofList (List.replicate (max 1 (16 - nm.length)) ' ') ++ row i))

/-! ## Local density

Their Definition 9.4: a nucleus is **dense** if `j(0) = 0` and **locally
dense** if `j(¬j(0)) = 1`.  Reading `j = ◯`, `0 = ⊥`:

* dense      = `¬◯⊥`      — our infallible rung (`varfree_dichotomy`);
* locally dense = `◯¬◯⊥`  — a `∨`-FREE axiom.

Their Theorem 9.7: the free 0-generated locally dense NIS is the FOUR-element
algebra `{0, j(0), ¬j(0), 1}` — the same four representatives as our
`varfree_exactly_four`, which we obtain from excluded middle.  Since
`box_nobot_em` derives `◯¬◯⊥ ⊣⊢ ⊤` from excluded middle, local density is
implied by it.  The question their theorem raises is whether the four-element
collapse survives the addition of `∨` under the WEAKER, `∨`-free hypothesis.
The decisive extra element is `◯⊥ ∨ ¬◯⊥`, which excluded middle sends to `⊤`.
-/

/-- `◯⊥ ∨ ¬◯⊥` — the element that separates the six-rung from the four-rung. -/
def split : PLLFormula := e1.or e2

def localDensityProbe : String :=
  String.intercalate "\n"
    [ "[◯¬◯⊥] ⊢ ¬¬◯⊥ ⊃ ◯⊥      " ++ cell e4 e5
    , "[◯¬◯⊥] ⊢ ◯⊥ ∨ ¬◯⊥       " ++ cell e4 split
    , "[◯¬◯⊥] ⊢ ¬◯⊥            " ++ cell e4 e2
    , "[◯⊥ ∨ ¬◯⊥] ⊢ ◯¬◯⊥       " ++ cell split e4
    , "[] ⊢ ◯⊥ ∨ ¬◯⊥           " ++ cell truePLL split ]

end NISFig6

-- The order.  Read: row A, column B, `Y` iff A ⊢ B.
/--
info: ⊥               Y Y Y Y Y Y Y Y
◯⊥              . Y . Y Y Y Y Y
¬◯⊥             . . Y . Y Y Y Y
¬¬◯⊥            . . . Y . . Y Y
◯¬◯⊥            . . . . Y Y Y Y
¬¬◯⊥⊃◯⊥         . . . . . Y . Y
(¬¬◯⊥⊃◯⊥)⊃◯¬◯⊥  . . . . . . Y Y
⊤               . . . . . . . Y
-/
#guard_msgs in
#eval IO.println NISFig6.matrix

-- Does the four-element collapse survive `∨` under local density alone?
#eval IO.println NISFig6.localDensityProbe

/-! ### Escalation on the open cell

`[◯¬◯⊥] ⊢ ◯⊥ ∨ ¬◯⊥` came back `.unknown` at the default budget.  Raise the
positive budget by 25×, lift the closure cap so the complete-over-the-closure
emitter runs, and report the reason if it still misses. -/

def bigCfg : Config :=
  { findBudget := some 5000000, emitClosureCap := 40, comboCap := 2000000 }

def openCell : String :=
  match verdictWhy [NISFig6.e4] NISFig6.split bigCfg with
  | .proved _      => "PROVED: local density forces the split"
  | .refuted _ _ _ => "REFUTED: local density does NOT force the split"
  | .unknown r     => "still unknown — " ++ r.describe

#eval IO.println openCell
