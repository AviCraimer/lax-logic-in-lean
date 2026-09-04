import wip.secondgen
import LaxLogic.PLLLaxInfinite

/-!
# The free two-generated Heyting algebra does not embed over `◯⊥`

**The statement.**  Write `H` for the Lindenbaum algebra of the
variable-free fragment RN(◯,{}): elements are interderivability classes
of variable-free PLL formulas, with the Heyting operations induced by
`∧, ∨, ⊃, ⊥` (`◯` is extra structure `H` carries, but it is not part of
the Heyting signature and a Heyting homomorphism need not respect it).

A variable-free formula `B` determines the map

    τ_B [X]  =  [ X[p := ◯⊥, q := B] ]

from the free two-generated Heyting algebra `F(p, q)` to `H`.  This map
is automatically a Heyting homomorphism — substitution commutes with
the connectives — and every homomorphism `F(p, q) → H` with `p ↦ [◯⊥]`
is of this form: homomorphisms out of a free algebra correspond exactly
to the images of the generators.  The elements of `F(p, q)` are the
IPC-equivalence classes of two-variable pure Heyting formulas.

`B` *embeds* `F(p, q)` when `τ_B` is injective: two-variable ◯-free
formulas that are IPC-distinct must remain non-interderivable in PLL
after the substitution.

The Lean rendering `EmbedsOver` below asks for slightly less: the
conclusion is PLL-interderivability of the sources, not their
IPC-equivalence.  Since IPC derivability is contained in PLL
derivability on ◯-free formulas, `EmbedsOver B` is a consequence of
genuine injectivity — so refuting `EmbedsOver B` refutes injectivity
a fortiori.  On the witness side the collapsed pairs below are
separated by one-world *classical* models, so they are Boolean-distinct,
hence IPC-distinct: the failure is as strong as it can be.

**The theorem** (`no_embedding_over_oBot`): NO variable-free `B` embeds
`F(p, q)`.  This is in sharp contrast with one generator: `p ↦ ◯⊥`
embeds the free ONE-generated Heyting algebra — that is the
Rieger–Nishimura ladder result `rn_pairwise_pll`.

**The engine** (`dichotomy`) is a fact of independent interest:

    every variable-free B satisfies   ◯⊥ ⊢ B   or   B ⊢ ¬◯⊥

and never both (`dichotomy_exclusive`).  The proof is a structural
induction in which every case is elementary; the only modal ingredient
is `◯⊥ ⊢ ◯X` (`secondgen.boxBot_below_box`).  The dichotomy then kills
every candidate second generator at once:

* `◯⊥ ⊢ B`  →  `τ_B` identifies `[p ⊃ q]` with `[⊤]`;
* `B ⊢ ¬◯⊥` →  `τ_B` identifies `[q ⊃ ¬p]` with `[⊤]`.

This subsumes `twogenStmt.tauW_derivable` (the case `B = ◯¬◯⊥`, which
is high) and completes `secondgen`: the two obstructions there ruled
out the known classes one at a time; the dichotomy rules out every `B`
at once.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-- `¬◯⊥`. -/
def notOBot : PLLFormula := oBot.ifThen falsePLL

/-- Weakening at the head of the context. -/
theorem wkHead {Γ : List PLLFormula} {C : PLLFormula} (X : PLLFormula)
    (h : Deriv Γ C) : Deriv (X :: Γ) C :=
  h.rename fun _ hy => .tail _ hy

/-- **The dichotomy.**  Every variable-free formula lies above `◯⊥` or
below `¬◯⊥`.  Structural induction; the `⊃` case is the one with
content: if `X` is high and `Y` is low then `X ⊃ Y` is low, because
`◯⊥` supplies `X`, modus ponens gives `Y`, and `Y` refutes `◯⊥`. -/
theorem dichotomy : ∀ B : PLLFormula, atomFree B = true →
    Deriv [oBot] B ∨ Deriv [B] notOBot
  | .prop _, h => by simp [atomFree] at h
  | .falsePLL, _ => Or.inr (Deriv.falsoElim _ (Deriv.iden (.head _)))
  | .and X Y, h => by
      have hXY : atomFree X = true ∧ atomFree Y = true := by
        simpa [atomFree] using h
      rcases dichotomy X hXY.1 with dX | dX
      · rcases dichotomy Y hXY.2 with dY | dY
        · exact Or.inl (Deriv.andIntro dX dY)
        · exact Or.inr
            (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) dY)
      · exact Or.inr
          (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) dX)
  | .or X Y, h => by
      have hXY : atomFree X = true ∧ atomFree Y = true := by
        simpa [atomFree] using h
      rcases dichotomy X hXY.1 with dX | dX
      · exact Or.inl (Deriv.orIntro1 dX)
      · rcases dichotomy Y hXY.2 with dY | dY
        · exact Or.inl (Deriv.orIntro2 dY)
        · exact Or.inr (Deriv.orElim (Deriv.iden (.head _))
            (wk1 _ dX) (wk1 _ dY))
  | .ifThen X Y, h => by
      have hXY : atomFree X = true ∧ atomFree Y = true := by
        simpa [atomFree] using h
      rcases dichotomy Y hXY.2 with dY | dY
      · -- Y high: ◯⊥ ⊢ X ⊃ Y outright
        exact Or.inl (Deriv.impIntro (wkHead X dY))
      · rcases dichotomy X hXY.1 with dX | dX
        · -- X high, Y low: X ⊃ Y is low
          refine Or.inr (Deriv.impIntro ?_)
          have dY' : Deriv [oBot, X.ifThen Y] Y :=
            Deriv.impElim (Deriv.iden (.tail _ (.head _))) (wk1 _ dX)
          exact Deriv.impElim (Deriv.cutHead dY' dY) (Deriv.iden (.head _))
        · -- X low: from ◯⊥ and X, contradiction, so Y by ex falso
          refine Or.inl (Deriv.impIntro ?_)
          exact Deriv.falsoElim _
            (Deriv.impElim (Deriv.toHead dX) (Deriv.iden (.tail _ (.head _))))
  | .somehow X, _ => Or.inl (boxBot_below_box X)

/-- `◯⊥ ⊬ ⊥`: the two-world model `0 ⊑ 1`, `0 ⇝ₘ 1`, with `1` fallible
and `0` not. -/
theorem oBot_not_bot : ¬ Deriv [oBot] falsePLL :=
  FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩)
    (w := 0) (by decide)

/-- The dichotomy is exclusive: no variable-free `B` is both high and
low, else `◯⊥ ⊢ ⊥`. -/
theorem dichotomy_exclusive (B : PLLFormula) :
    ¬ (Deriv [oBot] B ∧ Deriv [B] notOBot) := fun ⟨h1, h2⟩ =>
  oBot_not_bot (Deriv.impElim (Deriv.cutHead h1 h2) (Deriv.iden (.head _)))

/-! ## The embedding property, and its refutation -/

/-- Atoms confined to `p` and `q`: the formula presents an element of
the free TWO-generated algebra, not a larger one. -/
def varsPQ : PLLFormula → Bool
  | .prop a => a == "p" || a == "q"
  | .falsePLL => true
  | .and X Y => varsPQ X && varsPQ Y
  | .or X Y => varsPQ X && varsPQ Y
  | .ifThen X Y => varsPQ X && varsPQ Y
  | .somehow X => varsPQ X

/-- The substitution `p ↦ ◯⊥`, `q ↦ B` (order immaterial: `B` is
variable-free). -/
def tauSub (B X : PLLFormula) : PLLFormula :=
  substP "p" oBot (substP "q" B X)

/-- **What "embed" means, in Lean.**  `B` embeds the free two-generated
Heyting algebra over `◯⊥` when the substitution `p ↦ ◯⊥, q ↦ B` is
injective on pure Heyting two-variable formulas: interderivable images
force interderivable sources.  (True injectivity of `τ_B` on `F(p, q)`
concludes IPC-equivalence of the sources, which implies this; so
refuting THIS refutes injectivity.) -/
def EmbedsOver (B : PLLFormula) : Prop :=
  ∀ X Y : PLLFormula, boxFree X = true → boxFree Y = true →
    varsPQ X = true → varsPQ Y = true →
    Interd (tauSub B X) (tauSub B Y) → Interd X Y

/-- Substitution does not touch a variable-free formula. -/
theorem substP_atomFree (a : String) (C : PLLFormula) :
    ∀ B : PLLFormula, atomFree B = true → substP a C B = B
  | .prop _, h => by simp [atomFree] at h
  | .falsePLL, _ => rfl
  | .and X Y, h => by
      have hXY : atomFree X = true ∧ atomFree Y = true := by
        simpa [atomFree] using h
      simp [substP, substP_atomFree a C X hXY.1, substP_atomFree a C Y hXY.2]
  | .or X Y, h => by
      have hXY : atomFree X = true ∧ atomFree Y = true := by
        simpa [atomFree] using h
      simp [substP, substP_atomFree a C X hXY.1, substP_atomFree a C Y hXY.2]
  | .ifThen X Y, h => by
      have hXY : atomFree X = true ∧ atomFree Y = true := by
        simpa [atomFree] using h
      simp [substP, substP_atomFree a C X hXY.1, substP_atomFree a C Y hXY.2]
  | .somehow X, h => by
      have hX : atomFree X = true := by simpa [atomFree] using h
      simp [substP, substP_atomFree a C X hX]

/-! ### The witnesses -/

/-- `p ⊃ q`. -/
def pImpQ : PLLFormula := (prop "p").ifThen (prop "q")

/-- `q ⊃ ¬p`. -/
def qImpNotP : PLLFormula := (prop "q").ifThen ((prop "p").ifThen falsePLL)

/-- `⊤`. -/
def topF : PLLFormula := falsePLL.ifThen falsePLL

theorem tauSub_pImpQ {B : PLLFormula} (hB : atomFree B = true) :
    tauSub B pImpQ = oBot.ifThen B := by
  show PLLFormula.ifThen oBot (substP "p" oBot B) = oBot.ifThen B
  rw [substP_atomFree "p" oBot B hB]

theorem tauSub_qImpNotP {B : PLLFormula} (hB : atomFree B = true) :
    tauSub B qImpNotP = B.ifThen notOBot := by
  show PLLFormula.ifThen (substP "p" oBot B) (oBot.ifThen falsePLL)
      = B.ifThen notOBot
  rw [substP_atomFree "p" oBot B hB]
  rfl

theorem tauSub_topF {B : PLLFormula} : tauSub B topF = topF := rfl

/-- Everything proves `⊤`. -/
theorem derivTopAny {Γ : List PLLFormula} : Deriv Γ topF :=
  Deriv.impIntro (Deriv.iden (.head _))

/-- High case collapse: if `◯⊥ ⊢ B` then `τ_B (p ⊃ q) ⊣⊢ ⊤`. -/
theorem collapse_high {B : PLLFormula} (hB : atomFree B = true)
    (h : Deriv [oBot] B) :
    Interd (tauSub B pImpQ) (tauSub B topF) := by
  rw [tauSub_pImpQ hB, tauSub_topF]
  exact ⟨derivTopAny, Deriv.impIntro (wk1 _ h)⟩

/-- Low case collapse: if `B ⊢ ¬◯⊥` then `τ_B (q ⊃ ¬p) ⊣⊢ ⊤`. -/
theorem collapse_low {B : PLLFormula} (hB : atomFree B = true)
    (h : Deriv [B] notOBot) :
    Interd (tauSub B qImpNotP) (tauSub B topF) := by
  rw [tauSub_qImpNotP hB, tauSub_topF]
  exact ⟨derivTopAny, Deriv.impIntro (wk1 _ h)⟩

/-- `⊤ ⊬ p ⊃ q`: one world, `p` true, `q` false — a classical
countermodel, so the pair is even Boolean-distinct. -/
theorem top_not_pImpQ : ¬ Deriv [topF] pImpQ :=
  FinCM.not_provable_of_check (M := ⟨1, [], [], [], [(0, "p")]⟩) (w := 0)
    (by decide)

/-- `⊤ ⊬ q ⊃ ¬p`: one world, `p` and `q` both true. -/
theorem top_not_qImpNotP : ¬ Deriv [topF] qImpNotP :=
  FinCM.not_provable_of_check
    (M := ⟨1, [], [], [], [(0, "p"), (0, "q")]⟩) (w := 0) (by decide)

/-- **No second generator.**  For every variable-free `B`, the
substitution `p ↦ ◯⊥`, `q ↦ B` fails to embed the free two-generated
Heyting algebra: a concrete pure-Heyting pair collapses that was not
interderivable — `(p ⊃ q, ⊤)` if `B` is high, `(q ⊃ ¬p, ⊤)` if low. -/
theorem no_embedding_over_oBot (B : PLLFormula) (hB : atomFree B = true) :
    ¬ EmbedsOver B := by
  intro hEmb
  rcases dichotomy B hB with h | h
  · exact top_not_pImpQ
      (hEmb pImpQ topF (by decide) (by decide) (by decide) (by decide)
        (collapse_high hB h)).2
  · exact top_not_qImpNotP
      (hEmb qImpNotP topF (by decide) (by decide) (by decide) (by decide)
        (collapse_low hB h)).2

/-! ## Axiom audits — sorry-free throughout -/

/-- info: 'PLLND.RNEmbed.dichotomy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms dichotomy

/-- info: 'PLLND.RNEmbed.dichotomy_exclusive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dichotomy_exclusive

/-- info: 'PLLND.RNEmbed.no_embedding_over_oBot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms no_embedding_over_oBot

end RNEmbed
end PLLND
