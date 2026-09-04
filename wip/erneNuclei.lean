import LaxLogic.PLLSearchCmd

/-!
# Erné's ABC applied to RN(◯,{})

Marcel Erné, *Nuclear ranges in implicative semilattices*, Algebra Universalis
83 (2022), art. 18.  For an implicative semilattice `A` and `a ∈ A` he studies
three families of l-ideals (§5), writing `xᵃ` for `x → a`:

    𝔞a = {a → x | x ∈ A}    basic open      (nucleus αₐ = a → ·)
    𝔟a = {x → a | x ∈ A}    boolean         (nucleus βₐ x = (x→a)→a)
    𝔠a = ↑a                 basic closed    (nucleus γₐ = a ∨ ·)

`A = RN(◯,{})`, the closed fragment of PLL, is a bounded Heyting LATTICE
(it has `∨`), but it is **not complete** and **not boolean** — the latter
because `⊬ ◯⊥ ∨ ¬◯⊥`, pinned in `wip/nisFig6.lean`.

## What this file probes

Erné's **Theorem 5.9**: for a Heyting semilattice `A` the following are
equivalent — `A` is a boolean lattice; `𝔟_A` is isotone; `𝔟_A : A → 𝒩A` is an
isomorphism; and several more.  His closing remark: *"It is quite surprising
that isotonicity of the map `𝔟_A` resp. `β_A` is already sufficient (and
necessary) for `A` to be a boolean lattice."*

Contrapositive, for us: since RN(◯,{}) is **not** boolean, `a ↦ 𝔟a` is **not
isotone** on it.

MIND THE ORDER.  `𝒩A` carries **dual** inclusion (Proposition 3.2), a point
Erné flags with an exclamation mark inside the proof of 5.9: isotone means

    a ≤ b   implies   𝔟b ⊆ 𝔟a.

So a witness to the failure is `a ≤ b` together with an element of
`𝔟b ∖ 𝔟a` — NOT of `𝔟a ∖ 𝔟b`.  (An earlier version of this file had the
inclusion the wrong way round and so checked the wrong thing.)

Theorem 5.9 guarantees a witness but does not name one.  Here is one, at the
smallest place the failure of booleanness lives:

    a = ⊥ ≤ b = ◯⊥,   and the element ◯⊥ itself.

`𝔟⊥` is the set of regular elements `{y | y = ¬¬y}` — the booleanization, by
the Glivenko–Frink theorem Erné cites.  `◯⊥` is the *least* element of `𝔟◯⊥`
(Theorem 5.2), and directly `(◯⊥→◯⊥)→◯⊥ = ⊤→◯⊥ = ◯⊥`.  So the one thing to
check is that `◯⊥` is **not** regular, i.e. `¬¬◯⊥ ⊬ ◯⊥` — which is already a
pinned cell of the Figure 6 matrix in `wip/nisFig6.lean`.

The `¬◯⊥` computation is kept below because it is worth having on record: it
shows `β_◯⊥(¬◯⊥) ⊣⊢ ¬¬◯⊥⊃◯⊥`, Figure 6's fifth element, so `𝔟⊥ ⊄ 𝔟◯⊥` as
well.  Both inclusions fail; only the second direction bears on 5.9.

PROBE, not a theorem: `#eval` output is not kernel-checked.  Not registered in
`lakefile.toml`; run with `lake env lean wip/erneNuclei.lean`.
-/

open PLLFormula PLLND PLLND.Search

namespace ErneNuclei

/-- `◯⊥`. -/
def oBot : PLLFormula := falsePLL.somehow
/-- `x → a`, Erné's `xᵃ`. -/
def imp (x a : PLLFormula) : PLLFormula := x.ifThen a
/-- `¬x = x → ⊥`. -/
def neg (x : PLLFormula) : PLLFormula := imp x falsePLL
/-- `βₐ x = (x → a) → a`. -/
def beta (a x : PLLFormula) : PLLFormula := imp (imp x a) a

/-- `y = ¬◯⊥`, the candidate witness. -/
def y : PLLFormula := neg oBot

/-- Interderivability, both directions, by certificate-carrying search. -/
def interd (A B : PLLFormula) : String :=
  let f := fun (P Q : PLLFormula) =>
    match settle budgetedConfig [P] Q with
    | .proved _      => "Y"
    | .refuted _ _ _ => "."
    | .unknown       => "?"
  f A B ++ f B A

/-- THE witness for Theorem 5.9, in the direction that matters:
`⊥ ≤ ◯⊥` but `𝔟◯⊥ ⊄ 𝔟⊥`, because `◯⊥ ∈ 𝔟◯⊥ ∖ 𝔟⊥`. -/
def isotonicityWitness : String :=
  String.intercalate "\n"
    [ "  ◯⊥ ∈ 𝔟◯⊥ :  ◯⊥ ⊣⊢ β_◯⊥(◯⊥) = (◯⊥→◯⊥)→◯⊥      " ++ interd oBot (beta oBot oBot)
    , "  ◯⊥ ∈ 𝔟⊥  :  ◯⊥ ⊣⊢ β_⊥(◯⊥)  = ¬¬◯⊥            " ++ interd oBot (beta falsePLL oBot)
    , "    of which the failing half:  ¬¬◯⊥ ⊢ ◯⊥       " ++
        (match settle budgetedConfig [beta falsePLL oBot] oBot with
         | .proved _ => "Y" | .refuted _ _ _ => "REFUTED" | .unknown => "?") ]

def report : String :=
  String.intercalate "\n"
    [ "A is not boolean:      ⊢ ◯⊥ ∨ ¬◯⊥                " ++
        (match settle budgetedConfig [] (oBot.or y) with
         | .proved _ => "derivable" | .refuted _ _ _ => "REFUTED" | .unknown => "?")
    , "y regular (y ∈ 𝔟⊥):    ¬◯⊥ ⊣⊢ β_⊥(¬◯⊥) = ¬¬¬◯⊥   " ++ interd y (beta falsePLL y)
    , "y ∈ 𝔟◯⊥ ?             ¬◯⊥ ⊣⊢ β_◯⊥(¬◯⊥)          " ++ interd y (beta oBot y)
    , "  (the two halves separately, ⊢ then ⊣)"
    , "    ¬◯⊥ ⊢ (¬◯⊥→◯⊥)→◯⊥                            " ++
        (match settle budgetedConfig [y] (beta oBot y) with
         | .proved _ => "Y" | .refuted _ _ _ => "." | .unknown => "?")
    , "    (¬◯⊥→◯⊥)→◯⊥ ⊢ ¬◯⊥                            " ++
        (match settle budgetedConfig [beta oBot y] y with
         | .proved _ => "Y" | .refuted _ _ _ => "." | .unknown => "?")
    , "β_◯⊥(¬◯⊥) vs ⊤:        (¬◯⊥→◯⊥)→◯⊥ ⊣⊢ ⊤          " ++ interd (beta oBot y) truePLL ]

/-! ### Where the witness lives

`β_◯⊥(¬◯⊥) = (¬◯⊥→◯⊥)→◯⊥` is closed and `∨`-free, so by Bezhanishvili et al.
Theorem 9.3 (`wip/nisFig6.lean`) it must be interderivable with one of the
eight elements of their Figure 6.  Which one? -/

def fig6 : List (String × PLLFormula) :=
  [ ("⊥",              falsePLL)
  , ("◯⊥",             oBot)
  , ("¬◯⊥",            y)
  , ("¬¬◯⊥",           neg y)
  , ("◯¬◯⊥",           y.somehow)
  , ("¬¬◯⊥⊃◯⊥",        imp (neg y) oBot)
  , ("(¬¬◯⊥⊃◯⊥)⊃◯¬◯⊥", imp (imp (neg y) oBot) y.somehow)
  , ("⊤",              truePLL) ]

def locate : String :=
  let w := beta oBot y
  String.intercalate "\n"
    (fig6.map (fun (nm, e) => "  β_◯⊥(¬◯⊥) ⊣⊢ " ++ nm ++ "  " ++ interd w e))

end ErneNuclei

#eval IO.println ErneNuclei.isotonicityWitness
#eval IO.println ErneNuclei.report
#eval IO.println ErneNuclei.locate
