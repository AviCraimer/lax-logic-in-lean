import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin

/-!
# The other residual branch: the fresh-antecedent goal clause at budget 1

PROGRESS §93 addendum records two open branches at target budget `1`.  §§86-93
narrowed the first (the boxed floor branch).  This probe examines the second,
which has been open since July and never looked at disjunct by disjunct.

The branch: the descent's goal-side clause for `C = C₁ ⊃ C₂` with `C₁ ∉ Γ`.  It
is *not* budget-gated, so both components sit at the incoming budget:

    source   E@2(C₁::Γ)  ⇢  A@2(C₁::Γ, C₂)
    target   E@1(C₁::Γ)  ⇢  A@1(C₁::Γ, C₂)

Introduce the target's guard and the source can only be fired with
`E@2(C₁::Γ)` — the ∃-ascent at budget `1` at the grown context, which is exactly
what `not_ambGuardAscent` refutes.  So *this* route is dead, and the question is
whether the branch can reach a **different** disjunct of the target table.

The probe asks, for each disjunct `χ` of `itpAoth p S fl 1 Γ (C₁⊃C₂)`:

    E@2(Γ) ,  E@2(C₁::Γ) ⇢ A@2(C₁::Γ,C₂)   ⊢   χ

and also the whole target, at two configurations.

Run: `lake build sealprobe10 && .lake/build/bin/sealprobe10`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe10

def gam (a b : String) : PLLFormula := ((prop a).somehow).ifThen (prop b)

def S1 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s", prop "z" }
def G1 : List PLLFormula := [gam "r" "s"]

def S2 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s",
    gam "u" "v", (prop "u").somehow, prop "u", prop "v", prop "z" }
def G2 : List PLLFormula := [gam "r" "s", gam "u" "v"]

def cfg (bud : Nat) : Config := { findBudget := some bud, emitClosureCap := 0 }

def tag (cf : Config) (hyps : List PLLFormula) (goal : PLLFormula) : String :=
  match settleWhy cf hyps goal with
  | .proved t => s!"PROVED({t.size})"
  | .refuted _ _ _ => "REFUTED"
  | .unknown _ => "~"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== the fresh-antecedent goal branch at target budget 1 =="
  pl ""
  for (snm, S, Γ) in [("S1", S1, G1), ("S2", S2, G2)] do
    -- C₁ = r (fresh, in S), C₂ = z (so the goal is r ⊃ z, C₁ ∉ Γ)
    for (cnm, C₁, C₂) in [("r ⊃ z", prop "r", prop "z"),
                          ("r ⊃ s", prop "r", prop "s")] do
      let F := 3
      let fl := 3
      let C := C₁.ifThen C₂
      let amb := itpE "p" S (fl + 1) 2 Γ
      let src := (itpE "p" S F 2 (C₁ :: Γ)).ifThen
        (itpA "p" S F 2 (C₁ :: Γ) C₂)
      let tgts := itpAoth "p" S fl 1 Γ C
      pl s!"{snm}, C = {cnm}: {tgts.length} target disjunct(s), weights \
{tgts.map PLLFormula.weight}"
      let whole ← IO.lazyPure (fun _ => tag (cfg 20000) [amb, src] (orAll tgts))
      let _ ← IO.lazyPure (fun _ => whole.length)
      pl s!"   whole target: {whole}"
      let mut j := 0
      for χ in tgts do
        let t ← IO.lazyPure (fun _ => tag (cfg 20000) [amb, src] χ)
        let _ ← IO.lazyPure (fun _ => t.length)
        pl s!"   disjunct {j} (weight {χ.weight}): {t}"
        j := j + 1
      -- and the ascent instance the natural route needs, for contrast
      let asc ← IO.lazyPure (fun _ =>
        tag (cfg 20000) [amb, itpE "p" S F 1 (C₁ :: Γ)]
          (itpE "p" S F 2 (C₁ :: Γ)))
      let _ ← IO.lazyPure (fun _ => asc.length)
      pl s!"   [the ascent E@2(C₁::Γ) from E@1(C₁::Γ) + ambient]: {asc}"
  pl ""
  pl "== done =="

end SealProbe10

def main : IO Unit := SealProbe10.main
