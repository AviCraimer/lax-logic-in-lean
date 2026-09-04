import LaxLogic.PLLSearchCmd
import rnEmbed

/-!
# How big is `𝔟a`, as `a` varies?

`𝔟a = {x → a | x ∈ A}` is the range of Erné's boolean nucleus
`βₐ x = (x→a)→a`; by his Theorem 5.2 it is the least l-ideal containing `a`,
it is a **boolean lattice** with least element `a` and greatest `⊤`, and the
complement of `y` in it is `y → a`.

Two data points are known:

    𝔟⊥   = {⊥,  ¬◯⊥,  ¬¬◯⊥,     ⊤}     (a THEOREM: wip/negFour*.lean)
    𝔟◯⊥  = {◯⊥, ¬¬◯⊥, ¬¬◯⊥⊃◯⊥,  ⊤}     (probe: wip/erneBoxBot.lean)

Matthew's conjecture from those two: `𝔟φ = {φ, ¬¬φ, ¬¬φ ⊃ φ, ⊤}`.

It is already refuted at `φ = ⊥`, since `¬¬⊥ = ⊥` and `¬¬⊥ ⊃ ⊥ = ⊤`, so it
predicts two elements where there are four.  What survives is the *shape*
forced by Thm 5.2: a four-element `𝔟a` must be `{a, y, y→a, ⊤}`.  For `a = ◯⊥`
that `y` is `¬¬a`; for `a = ⊥` it is `¬◯⊥`, which is not `¬¬a`.

This file measures `|𝔟a|` for a spread of `a`, to see which sizes occur.
Since a finite boolean lattice has size `2ⁿ`, any count that is not a power of
two is a bug — that is exactly how the first version of `wip/erneBoxBot.lean`
caught its own `.unknown`-folded-into-`false` error, so the comparison here is
three-valued and unknowns are counted and reported separately.

Needs `rnEmbed.olean` on `LEAN_PATH`; recipe in `wip/erneBool2.lean`.
PROBE, not a theorem — and NOT YET RUN TO COMPLETION.  Started 2026-08-07
and stopped after 10 minutes: it is thousands of searches (10 values of `a` x
22 arguments x pairwise comparisons), so it wants running deliberately rather
than interactively.  The code is here; the numbers are not.

What is already known without it: `|𝔟⊥| = 4` (a theorem), `|𝔟◯⊥| = 4` (probe),
and `|𝔟⊤| = 1` trivially, since `x → ⊤ = ⊤` for every `x`.  So the sizes are
not constant, and the question is which values occur and whether they are
bounded.
-/

open PLLFormula PLLND PLLND.Search

set_option maxHeartbeats 1000000

namespace ErneBsize

def oBot : PLLFormula := falsePLL.somehow
def imp (x a : PLLFormula) : PLLFormula := x.ifThen a
def neg (x : PLLFormula) : PLLFormula := imp x falsePLL
def t (n : Nat) : PLLFormula := PLLND.RNEmbed.rnSub n

inductive Cmp | eq | ne | dunno
  deriving DecidableEq, BEq

/-- Three-valued interderivability: `.dunno` is kept distinct from `.ne`. -/
def cmp (A B : PLLFormula) : Cmp :=
  let one := fun (P Q : PLLFormula) =>
    match settle budgetedConfig [P] Q with
    | .proved _      => some true
    | .refuted _ _ _ => some false
    | .unknown       => none
  match one A B, one B A with
  | some false, _ => .ne
  | _, some false => .ne
  | some true, some true => .eq
  | _, _ => .dunno

/-- The arguments `x` we push through `· → a`. -/
def args : List PLLFormula :=
  let ng := neg oBot
  let nng := neg ng
  [ falsePLL, oBot, ng, nng, ng.somehow, imp nng oBot
  , imp (imp nng oBot) ng.somehow, truePLL, oBot.or ng, ng.or nng ]
  ++ (List.range 7).map t
  ++ (List.range 5).map (fun (n : Nat) => (t n).somehow)

/-- The distinct classes of `{x → a}` found in `args`. -/
def repsOf (a : PLLFormula) : List PLLFormula :=
  args.foldl
    (fun acc x =>
      let v := imp x a
      if acc.any (fun w => cmp v w == Cmp.eq) then acc else acc ++ [v])
    []

/-- Undecided comparisons among the representatives kept — if this is nonzero
the count below is not trustworthy. -/
def dunnoOf (a : PLLFormula) : Nat :=
  let R := repsOf a
  ((R.flatMap (fun x => R.map (fun y => cmp x y))).filter (fun c => c == Cmp.dunno)).length

def probes : List (String × PLLFormula) :=
  let ng := neg oBot
  let nng := neg ng
  [ ("⊥",              falsePLL)
  , ("◯⊥",             oBot)
  , ("¬◯⊥",            ng)
  , ("¬¬◯⊥",           nng)
  , ("◯¬◯⊥",           ng.somehow)
  , ("¬¬◯⊥⊃◯⊥",        imp nng oBot)
  , ("⊤",              truePLL)
  , ("t 3",            t 3)
  , ("t 4",            t 4)
  , ("◯⊥ ∨ ¬◯⊥",       oBot.or ng) ]

def report : String :=
  "|𝔟a| over " ++ ToString.toString args.length ++ " sampled arguments\n"
  ++ "(a size that is not a power of two indicates undecided comparisons)\n"
  ++ String.intercalate "\n"
      (probes.map (fun (nm, a) =>
        let n := (repsOf a).length
        let unk := dunnoOf a
        let pad := String.ofList (List.replicate (max 1 (14 - nm.length)) ' ')
        "  a = " ++ nm ++ pad ++ "|𝔟a| = " ++ ToString.toString n
          ++ (if unk = 0 then "" else "   (" ++ ToString.toString unk ++ " UNDECIDED)")))

end ErneBsize

#eval IO.println ErneBsize.report
