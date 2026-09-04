# Iemhoff's interpolant assignment — extracted verbatim (for wip/g4ill_ui.lean)

Sources: arXiv:2209.08976v1 (Proof Theory for Lax Logic), §6.3–6.8;
arXiv "Uniform interpolation and the existence of sequent calculi" (APAL 2019), §4.3, §5.
(Book chapter numbering: paper §6.6 = book §8.6.6; paper Thm 6 = book Thm 8.6.)

## Framework (paper §6.3–6.5)
- ∃pS / ∀pS defined per SEQUENT S=(Γ⇒Δ), |Δ|≤1, by rewrite ⟼ normal forms:
  ∃pS ⟼ ∃⁺pS ∧ ∃⁻pS ∧ ∃ᵃᵗpS ;  ∀pS ⟼ ∀⁺pS ∨ ∀⁻pS ∨ ∀ᵃᵗpS
  ∃⁺ = ⋀{ι∃ᴿpS : R instance with conclusion S}; ∃⁻ = ⋀{ι∃^R̄pS : S nonprincipal for some instance of R}
  Termination: her ≪ (DM on weight over Sᵃ∪Sˢ) — Fact 2 "G4iLL is reductive".
- ∃pS ≈ ∃p(⋀Sᵃ) (succedent semantically ignored); ∀pS ≈ ∀p I(S).
- Interpolant properties: (∀l) ⊢ Sᵃ,∀pS ⇒ Sˢ; (∃r) ⊢ Sᵃ ⇒ ∃pS;
  (∀∃) S derivable → ∀ p-partitions (Sʳ,Sⁱ): ⊢ Sʳ·(∃pSⁱ ⇒ ∀pSⁱ | ∅).
- ⊢ = ⊢_L (THE LOGIC), soundness def p.13: "where '⊢' equals '⊢_L'".
- Engine: Thm 5 (= 2019b Thm 31/Cor 32) needs a BALANCED calculus (cut+weakening admissible).
  Fact 3 (G4iLL balanced) justified "using Fact 2 and Corollary 1" — Cor 1 = G3iLL≡G4iLL,
  refuted by PLLG4Gap.lean; cut_not_admissible is a repo theorem. Fact 3 is FALSE.

## Atomic clauses (paper p.10)
∀ᵃᵗpS = ⋁{q ∈ Sˢ : q atom ≠ p, or q=⊤} ∨ ⋁{q ∧ ∀p(φ, Sᵃ∖{q→φ} ⇒ Sˢ) : (q→φ)∈Sᵃ, q≠p}
∃ᵃᵗpS = ⋀{q ∈ Sᵃ : q atom ≠ p, or q=⊥} ∧ ⋀{q → ∃p(φ, Sᵃ∖{q→φ} ⇒ Sˢ) : (q→φ)∈Sᵃ, q≠p}

## 2019b standard assignment
Axioms (At, L⊥), instance S: ι∀ᴿpS=⊤; ι∃ᴿpS=⋀{φ∈Sᵃ : p∉φ}.
Centered non-axiom (R∧,R∨,L∧,L∨,L∧→,L∨→), instance (S₁…Sₙ/S):
  ι∃ᴿpS = ⋁ᵢ∃pSᵢ ; ι∀ᴿpS = ⋀ᵢ(∃pSᵢ→∀pSᵢ). Nonprincipal: ⊤/⊥.
R→, instance (Γ,φ⇒ψ)/(Γ⇒φ→ψ):
  p∉φ: ι∃ᴿ=φ→∃pS₁, ι∀ᴿ=φ→∀pS₁ ;  p∈φ: ι∃ᴿ=⊤, ι∀ᴿ=∃pS₁→∀pS₁. ι∃^R̄=⊤, ι∀^R̄=⊥.
L1→ (q atom; q present, both q,q→ψ principal), instance (Γ,q,ψ⇒Δ)/(Γ,q,q→ψ⇒Δ):
  q≠p: ι∀ᴿ=q→∀pS₁, ι∃ᴿ=q∧∃pS₁ ;  q=p: ι∀ᴿ=∀pS₁, ι∃ᴿ=∃pS₁. ι∃^R̄=⋀{q∈Sᵃ:q≠p}, ι∀^R̄=⊥.
L4→, instance (Γ,ψ→γ⇒φ→ψ ; Γ,γ⇒Δ)/(Γ,(φ→ψ)→γ⇒Δ):
  ι∀ᴿ = ⋀ᵢ₌₁²(∃pSᵢ→∀pSᵢ) ; ι∃ᴿ = ∃pS₁ ∧ (∀pS₁→∃pS₂)
  ι∃^R̄ = ⊤ if Sˢ=∅ ; ⋀{∃p(Π⇒) : Π ⊆ Sᵃ} if Sˢ≠∅ (subset conjunction!). ι∀^R̄=⊥.
NOTE her G4ip Fig has NO rule for ⊥→ψ (⊥ not an atom). Repo G4 has impLBot — extension flagged.

## Lax assignments (paper §6.6)
R◯ instance (Γ⇒φ)/(Γ⇒◯φ) and L◯ instance (Γ,ψ⇒◯φ)/(Γ,◯ψ⇒◯φ):
  ι∃ᴿpS=◯∃pS₁, ι∀ᴿpS=◯∀pS₁; nonprincipal ⊤/⊥.
R◯→ instance (Γ⇒φ ; Γ,ψ⇒Δ)/(Γ,◯φ→ψ⇒Δ):
  ι∃ᴿ = ∃pS₁ ∧ (∀pS₁→∃pS₂) ; ι∀ᴿ = ∀pS₁ ∧ ∀pS₂  (∀-side UNguarded!)
  ι∃^R̄ = ⊤ if Sˢ=∅, ∃p(Sᵃ⇒) if Sˢ≠∅ ; ι∀^R̄ = ⊥.
L◯→ instance (Γ,χ⇒◯φ ; Γ,◯χ,ψ⇒Δ)/(Γ,◯χ,◯φ→ψ⇒Δ):
  ι∃ᴿ = ◯∃pS₁ ∧ (◯∀pS₁→∃pS₂) ; ι∀ᴿ = ◯∀pS₁ ∧ ∀pS₂.
  Nonprincipal, for γ = ◯α→β: S^γ0=(Sᵃ∖{γ}⇒◯α), S^γ1=(Sᵃ∖{γ},β⇒Sˢ):
  S^γ = ⋀_{◯α∈Sᵃ} ◯∃p(Sᵃ∖{◯α},α⇒) ∧ ⋀_{γ=◯α→β∈Sᵃ} [∃pS^γ0 ∧ (◯∀pS^γ0→∃pS^γ1)]
  ι∃^R̄ = S^γ if Sˢ=∅ ; ∃p(Sᵃ⇒) ∧ S^γ if Sˢ≠∅.
  ι∀^R̄ = ⋁_{γ=◯α→β∈Sᵃ} (◯∀pS^γ0 ∧ ∀pS^γ1).

## Her proofs' glue (for the local-correctness audit)
- Lemmas 3–6 (IPP/DPP per lax rule): rule applications + weakening + conjunct
  projection/absorption ("∃pSⁱ derives ∃pS₁ⁱ", "Since ∃pSⁱ⇒◯∃pS₁ⁱ is derivable"),
  i.e. identity-expansion + ⋀-handling; composition steps replace context formulas
  by entailing ones = cut-strength when read inside G4iLL.
- Lemma 7 (DPN, modal rules): "induction to the depth of the derivation of S for
  all rules at the same time"; cases use weakening, L◯, L◯→ applications; the
  L1→-DPN middle case APPLIES the rule to a partitioned premise (needs q reusable);
  final composition steps as above.
- Thm 6 (UI for PLL) = soundness of assignment + Thm 5 (needs balance = FALSE).
