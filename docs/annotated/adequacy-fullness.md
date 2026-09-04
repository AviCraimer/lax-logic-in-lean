# Adequacy and fullness for ⊩ᵖ: the decoration theorem

Source: `LaxLogic/PLLEvidence.lean` — `tokenEvidence`,
`realP_adequate_and_full`, `realP_refutes_sequent`, and the table algebra
`Tbl`/`tblPca` discharging every hypothesis. Audit:
`[propext, Quot.sound]` throughout — **no choice**, and the way the proof
achieves that is part of its content. Prerequisite: the obstruction
(`docs/annotated/fullness-obstruction.md`), which explains why the
⊃-clause of ⊩ᵖ carries the presented world.

## Setting

The theorem decorates *checked finite frames*: `FinCM`
(`LaxLogic/PLLCountermodelEmit.lean`) is a finite constraint model as
literal data, with an executable forcing function `forceB` and a
verified reflection lemma `force_iff` identifying the computation with
the genuine Kripke forcing of the induced model `M.toModel h`. Evidence
is as sparse as adequacy permits:

```lean
def tokenEvidence (P : Pca) (M : FinCM) (h : M.WellFormed)
    (tok : String → P.Carrier) : Evidence P (M.toModel h) where
  E s w := {x | M.fallB w.1 = true ∨ (M.valB w.1 s = true ∧ x = tok s)}
  ...
```

In words: one designated token per atom, present exactly at the worlds
where the atom holds (and everything everywhere at fallible worlds, as
the `Evidence` structure requires). Heredity of the assignment is
inherited from the frame's own heredity conditions, which is what the
`WellFormed` hypothesis is for.

## The statement

```lean
theorem realP_adequate_and_full (h : M.WellFormed) (tok : String → P.Carrier)
    (κ : Fin M.n → P.Carrier)
    (htab  : ∀ g : Fin M.n → P.Carrier, ∃ s, ∀ i, P.app s (κ i) = some (g i))
    (htabP : ∀ g : Fin M.n → P.Carrier,
      ∃ s, ∀ i b, P.app s (P.pair (κ i) b) = some (g i)) :
    ∀ φ : PLLFormula,
      (∀ (w : Fin M.n) (x : P.Carrier),
        (x ⊩ᵖ[tokenEvidence P M h tok, κ, w] φ) → (M.toModel h).force w φ) ∧
      (∃ wit : Fin M.n → P.Carrier, ∀ w : Fin M.n,
        (M.toModel h).force w φ →
          (wit w) ⊩ᵖ[tokenEvidence P M h tok, κ, w] φ)
```

In words: fix a checked frame, tokens, a world-coding, and two
table-forming capacities of the applicative structure — `htab` builds an
element realising any finite function of the presented world (used for
the ◯-witnesses), `htabP` an element answering on the first component of
a pair while ignoring the second (used for the ⊃-witnesses). Then for
every formula φ simultaneously:

* **adequacy** — any element ⊩ᵖ-realising φ at w certifies that φ is
  truth-forced at w; and
* **fullness** — there is a single *per-world witness function* `wit`
  such that at every world forcing φ, `wit w` realises φ there.

Note the shape of fullness: not "for each world there exists a witness"
but "there exists a function of worlds" — the induction needs the whole
function at once, because the ⊃- and ◯-witnesses are tables whose
entries are the subformula's witnesses *at other worlds*.

Both table hypotheses are discharged, with nothing assumed, by an
explicit algebra: `Tbl` has base codes, formal pairs and tags, and two
table constructors — `tbl` (answers on a world-code) and `ptbl` (answers
on the first component of a pair) — with application as decidable
lookup and the pairing/tagging laws holding by `rfl`. Hence the closed
capstones `realP_refutes_sequent_tbl` and `somehow_p_not_p_realP_tbl`.

## The proof, case by case

A single induction on φ proves the conjunction; each case may use both
halves of the inductive hypotheses. Throughout, `force_iff` converts
freely between the Prop-level `force` and the executable `forceB` — and
this is the engine of choice-freedom: **every branch decision in a
witness is a computation, not a case split on an undecided
proposition.**

**Atoms.** Adequacy: a realiser of `prop s` at a non-fallible w is the
token, present only where `valB` says the atom holds; at fallible worlds
the atom holds anyway. Fullness: `wit := fun _ => tok s` — the token
itself, wherever the atom is forced.

**⊥.** Both directions are the fallibility clause verbatim.

**∧.** Adequacy: componentwise, by both inductive adequacies. Fullness:
`wit w := pair (witφ w) (witψ w)`, with `fst_pair`/`snd_pair` unpacking.

**∨ — the first interesting case.** Adequacy: the tag decides which
disjunct the realiser carries; the matching inductive adequacy applies.
Fullness is where naive constructivity would stall — *which* disjunct is
forced at w? The witness computes it:

```lean
fun w => if M.forceB w.1 φ = true then P.tag false (witφ w)
         else P.tag true (witψ w)
```

In words: run the executable forcing of the left disjunct at w; tag
accordingly. If the test succeeds, `force_iff` converts the Boolean into
genuine forcing and the left inductive fullness supplies the payload; if
it fails and φ∨ψ is forced, the right disjunct must be forced (the
failed Boolean refutes the left via `force_iff`), and the right fullness
supplies it. No excluded middle: `forceB` is the oracle.

**⊃ — where the obstruction is answered.** Adequacy at φ⊃ψ: given a
realiser x and a future v forcing φ, feed x the pair ⟨κ v, witφ v⟩ — the
antecedent's *fullness* witness at v (this is the mutual dependency) —
and apply the *adequacy* of ψ to the answer. Fullness at φ⊃ψ: apply
`htabP` to ψ's witness function to get a single element s with

    app s ⟨κ v, b⟩ = some (witψ v)   for every v and every b.

Why is this correct? The clause only obliges s when b realises φ at v;
then φ is forced at v by the *adequacy* of φ (the mutual dependency in
the other direction), so ψ is forced at v because φ⊃ψ is forced at w ≤ v
— and then witψ v realises ψ at v by ψ's fullness. The table ignores b
entirely: the presented world alone determines the right answer, which
is precisely the lookup the obstruction proves impossible when the world
is not presented.

**◯.** Adequacy: the strategy's answer at a presented future names a
constraint-witness and carries evidence for the body there; the body's
adequacy converts, giving exactly the ∀∃ forcing clause. (At fallible
futures, reflexivity of Rₘ and fallible saturation close the case.)
Fullness: apply `htab` to the function

```lean
fun v => match (List.finRange M.n).find?
    (fun u => M.rmB v.1 u.1 && M.forceB u.1 φ) with
  | some u => P.pair (κ u) (witφ u)
  | none   => P.pair (κ v) (witφ v)    -- unreachable when obliged
```

In words: presented a future v, *search the finite frame* for a
constraint-successor of v forcing φ — a bounded, decidable search — and
answer with its name paired with φ's witness there. When ◯φ is forced at
w and v is a future of w, the ∀∃ clause guarantees the search succeeds
(`find?` cannot return `none` when a witness exists in the searched
list, and the found element's Boolean guard converts through `force_iff`
into the two facts needed: it is Rₘ-accessible and forces φ). The
default branch exists only to make the function total.

## The squeeze

```lean
theorem realP_refutes_sequent {w Γ C} (hcheck : FinCM.checkB M w Γ C = true)
    (tok) (κ) (htab) (htabP) :
    ∃ hwf hlt,
      (∀ ψ ∈ Γ, ∃ x, x ⊩ᵖ[tokenEvidence P M hwf tok, κ, ⟨w, hlt⟩] ψ) ∧
      ¬ ∃ x, x ⊩ᵖ[tokenEvidence P M hwf tok, κ, ⟨w, hlt⟩] C
```

In words: any countermodel validated by the verified checker is a
⊩ᵖ-refutation of its sequent — the hypotheses are realised at the
refuting world (they are forced there, so fullness realises them) and
the conclusion is unrealisable (it is unforced there, so adequacy
forbids a realiser). Combined with `emitter_completeness`
(`LaxLogic/PLLFinComp.lean`) this yields the completeness biconditional
`derivable_iff_no_realP_refutation` (`LaxLogic/PLLRealCompleteness.lean`).

## Two remarks for the paper

*Frame-aware versus frame-uniform.* The fullness witnesses are built by
surveying the finite frame (the ∨-branch test, the ◯-search, the
⊃-table). Contrast the soundness-side realisers extracted from proofs
(`extract_sound`, O3): one polynomial, valid in every model. Provable
formulas have evidence needing no knowledge of the situation; merely
true ones have evidence only relative to a survey of this situation's
futures. The idealisation of the completeness theorem is exactly this
survey — stated, and confined to where it belongs.

*Where the finiteness is used.* Only fullness needs it, and only in two
places: the ◯-witness's bounded search, and the very existence of the
witness *function* as a finite table. Adequacy holds over arbitrary
frames. This locates the finite-model property's role precisely: it is
what makes completeness-grade evidence *computable*.
