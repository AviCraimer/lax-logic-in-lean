# Applications programme — *Belief in Lax Logic*

*Draft, 2026-07-17. A programme of scientific studies (empirical / engineering
case studies) in which the evidential-belief semantics of PLL — the realisability
constraint model of `docs/route-b-model.md` — is the working instrument, not a
toy illustration. Written for Matthew (professional logician). Register: standard
proof-theoretic and modal-logic vocabulary only; formal claims as displayed
formulas; every citation tagged **VERIFIED** (primary/near-primary source
reached this session), **UNVERIFIED** (from memory / referenced but source not
opened — check before print), or **SPECULATIVE** (a proposed study whose payoff
is a conjecture, so labelled).*

*Matthew's verdict (2026-07-16): Studies 1–3 worth pursuing. Study 4 pending (a
CRDT explanation was requested). Study 5 belongs in the paper's theory section,
not as a study. Study 6 dropped.*

*Standing dependency (state it once, honestly): every study below is downstream
of the Route B mechanisation ladder. In particular each needs, at minimum, the
soundness-with-evidence-extraction theorem O3 (`route-b-model.md` §4) —
"a proof of `◯M` yields the evidence for `M`" — and the local-nucleus laws O2.
Both are currently **OPEN** (Lean obligations). No study can be reported as an
empirical result before its supporting mechanisation is `sorry`-free and
axiom-clean, per the machine-checked mandate. The studies are therefore staged:
each names the artefact it consumes, the Lean it adds, and the measurable outcome
that would count as success.*

---

## 0. Framing

The instrument these studies share is not "a belief logic" in the abstract but a
specific, machine-checked reading: `◯φ` = "φ is believed" = "φ holds once a
constraint is discharged", with a realiser at each world so that **a proof of
`◯φ` carries an executable witness for `φ`, valid after the discharge**. The
application history of lax and monadic modalities is exactly a history of *this*
reading under other names — "holds up to stabilisation" (hardware), "the
computation of type `T A`" (effects), "principal `K` says φ" (access control),
"safe subject to a checkable certificate" (proof-carrying code). The scientific
opportunity is that the belief semantics supplies three things those domains use
informally but have never had as a single certified object: (i) **evidence
extracted from the proof** as an auditable trail; (ii) a precise **rigid-vs-
strategy distinction** for disjunctive belief `◯(A∨B)` — commit to a disjunct now,
or keep a per-branch plan; (iii) **monotone belief growth over branching futures**
with *no* confluence forced, which is precisely the shape of concurrent /
constraint-indexed information growth. Each study below takes a real artefact from
one of these domains, formalises its belief content in the Route B model, and
measures whether the extracted evidence and the rigid/strategy classification say
something true and useful that the domain's existing tools do not already give.

A recurring, non-trivial cross-check runs through the whole programme. The
access-control literature independently rederived two of the belief paper's
signature facts and, remarkably, *stated them in the vocabulary of belief*:

> `A ⊃ ⟨K⟩A` — "if `A` has a proof, then every principal will believe it"
> `⟨K⟩⊥ ⊅ ⊥`  — "principals may make inconsistent statements without making the
>               logic inconsistent"

(both **VERIFIED**, Garg–Tschantz 2008, quoted in §Refs). The first is the paper's
truth-closure idealisation (§2E of the handover); the second is its quarantined
inconsistency (`◯⊥ ≠ ⊤`, credulous collapse without triviality). That a
security-engineering research line arrived at the same two structural commitments,
under the same doxastic gloss, is itself evidence the belief reading is not a
retrofit — and it makes access control the study where the paper's theses can be
checked against an *external* artefact.

---

## 1. Ranked studies

Ranked by realism and nearness-to-artefact: how close the study is to an existing
formal object we can consume, and how directly the belief semantics is the
instrument rather than a relabelling.

---

### Study 1 — Timing/stabilisation verification of digital circuits (the original application, nearest)

**(a) Phenomenon.** F&M's founding motivation: "correctness up to behavioural
constraints" in hardware, where a combinational or asynchronous circuit does not
compute its specified function *instantaneously* but *once signals have settled*
under timing/delay constraints. `◯φ` was born as "φ holds up to stabilisation".
[**VERIFIED**: F&M 1997; Mendler thesis 1993; F&M CSL 1994; and the dedicated
paper *Timing Analysis of Combinational Circuits in Intuitionistic Propositional
Logic*, Formal Methods in System Design.]

**(b) Mapping.**

| model component | in this domain |
|---|---|
| `W` (worlds) | observation stages: partial assignments of settled values to the circuit's nets (+ the timing assumptions in force) |
| `Rᵢ` (information growth) | more nets have reached a stable value / more input-timing assumptions adopted (a net never un-settles → heredity is literal) |
| `Rₘ` (constraint discharge) | passage to a stage where the stabilisation constraint holds — the circuit has been allowed enough time under the delay model |
| `F` (fallible worlds) | physically impossible configurations: glitch/hazard states, contradictory delay assumptions, short-circuit assignments (absorbed by saturation) |
| `E` (evidence) | a settling witness: a schedule / delay bound / waveform showing the net reaches value `v` — a realiser for "this signal stabilises to `v`" |
| `◯` (belief) | "holds up to stabilisation": `◯(out = spec)` = the circuit is *believed* to meet spec, the belief redeemed once settling completes |

**(c) The study.** Take a small family of real gate-level netlists with genuine
timing content — a ripple-carry adder, a two-input arbiter/mutex, a C-element
handshake — and their "stabilises-to" specifications. Formalise the netlist and
spec in the Route B realisability constraint model in Lean (the frame is exactly
F&M's, already mechanised as `ConstraintModel` in `PLLKripke.lean`; the new work
is the realiser layer `E`). Then **put these components together in a larger
netlist, under a specification that combines the component specifications
formally** (Matthew, 2026-07-19) — parallel composition under the strength `◯S`,
sequential discharge under `laxElim` — so that the composed proof is the
composition of the component proofs. Prove `◯(out = spec)` and **extract the
evidence term** via O3.

**(c′) STATUS (2026-07-19) — NOT completed; small-but-non-trivial is the gap.**
What the library has is the *delay-algebra half*: `PLLTiming.lean` (Mendler's
CIRC with the false-path punchline) and `PLLTimingAdder.lean` (ripple and
carry-skip adders, `skip_beats_topological`), all axiom-free — a genuine
precursor, exercised on toy-to-small circuits, but **not this study**: the
netlists and specs are not formalised in the Route B constraint model,
`◯(out = spec)` is not proved there, and **the realiser layer `E` is NOT
implemented**. O3 (`extract_sound`/`extractS_sound`, now in the library) removes
(e)'s precondition. Per Matthew, the unimplemented layer is best presented as a
**design brief with stages of implementation**:

1. **Waveform worlds.** Instantiate `ConstraintModel` (or finite `FinCM`
   instances) with observation stages per table (b): worlds = partial stable-net
   assignments + timing assumptions; `Rᵢ` = settling growth; `Rₘ` = stabilisation
   discharge under the delay model; `F` = glitch/contradiction states.
2. **The evidence layer `E`.** Realisers for atoms `net = v`: settling
   witnesses — a schedule/delay-bound/waveform object; heredity is "a net never
   un-settles", fullness on `F` is saturation. This is the new engineering.
3. **Component proofs.** `◯(out = spec)` for each of the three netlists,
   in the evidence semantics (`⊩ᵖ` for the completeness-grade reading;
   `⊩ᵘ`/`⊩ˢ` where rigid or reactive evidence suffices).
4. **Composition.** The larger netlist and the formally combined spec;
   the composed derivation should be built from the component derivations
   by `◯S` (parallel) and `laxElim` (sequential), and the extracted
   evidence should compose accordingly.
5. **Extraction and cross-check.** O3-extract the evidence terms; validate
   each witness against an independent event-driven timing simulation;
   any disagreement is a reportable defect in model or netlist (the
   study's measurable outcome, per (c)). *Question the study answers:* is the extracted realiser a correct — and,
for the small cases, minimal — stabilisation schedule? *Success (measurable):* for
each circuit the extracted witness is a valid settling order, validated against an
independent gate-delay simulation (e.g. a SPICE or event-driven timing run), for a
family of ≥ 3–4 circuits; disagreement between extracted witness and simulation
is a concrete, reportable defect in either the model or the netlist.

**(d) Value over existing tools / limits.** Static timing analysis and model
checking already decide such properties; the belief framework is *not* proposed as
a faster decision procedure. Its distinctive contribution is that the *proof
itself yields the timing witness as a first-class, machine-checked object*, in the
logic that was designed for exactly this reading — closing the loop F&M opened but
never mechanised end-to-end. Honest limit: the payoff is a certified evidence
artefact and a foundational demonstration, not a scalability result; industrial
STA will remain faster.

**(e) Effort.** Low–medium. ~4–6 weeks *after* O3 lands: the frame is already
mechanised, so the work is (i) the realiser layer over `ConstraintModel`, (ii)
encoding 3–4 netlists, (iii) the simulation cross-check harness. Highest-certainty
study; lowest new machinery.

---

### Study 2 — Decentralised access control / proof-carrying authorization (flagship: external artefacts + the paper's own theses)

**(a) Phenomenon.** In authorization logics the modality `⟨K⟩A` ("`K` says `A`")
is used to reason about who asserts what in a distributed system of mutually
distrusting principals. A large and explicit body of work chose `⟨K⟩A` to be a
**lax modality**, one per principal — *indexed lax logic*. [**VERIFIED**,
Garg–Tschantz 2008: "an increasingly large number of proposals … have chosen
`⟨K⟩A` to be a lax modality … the access control logic becomes an indexed lax
logic, with one lax modality for every principal", satisfying exactly
`A ⊃ ⟨K⟩A`, `⟨K⟩⟨K⟩A ⊃ ⟨K⟩A`, `⟨K⟩(A⊃B) ⊃ (⟨K⟩A ⊃ ⟨K⟩B)`. Also **VERIFIED**,
Garg–Abadi 2008: authorization logics interpreting `says` as a monad — "CDD and
ICL" — translate soundly and completely to S4, "and, as a special case, from lax
logic".] Proof-carrying authorization (PCA) systems ship the actual proof object
with the request; Garg–Pfenning's PCFS is a running file system built this way.

**(b) Mapping.** `⟨K⟩` is a *family* of believers indexed by principal `K` — the
multi-agent belief structure the paper's §9 flags as further work, here concrete.

| model component | in this domain |
|---|---|
| `W` (worlds) | states of the reference monitor's knowledge: the set of credentials / assertions presented so far |
| `Rᵢ` (information growth) | more certificates arrive; the monitor's admissible facts grow monotonically (heredity = credentials, once presented, stay) |
| `Rₘ` (constraint discharge, per `K`) | passage to a world where principal `K`'s asserted context is in force — `K`'s authority (or a delegation to `K`) is exercised |
| `F` (fallible worlds) | compromised/malicious principals asserting `⊥`; inconsistent credential sets — **quarantined**: `⟨K⟩⊥ ⊅ ⊥` |
| `E` (evidence) | the authorization proof term — literally the PCA certificate that `K says can_read(Bob, foo)` |
| `◯` = `⟨K⟩` (belief) | "`K` says / `K` believes `A`", the per-principal indexed lax modality |

**(c) The study.** Formalise a real published policy — the PCFS policy, or an
ABLP/Grey-style building- or file-access policy — in the *indexed* realisability
constraint model in Lean. From a proof that a given request is granted, **extract
the evidence term = the audit trail**: which principals said what, under which
discharged constraints, in what order. *Questions answered:* (i) is the extracted
belief-trail a faithful and minimal audit log of the authorization decision — does
it agree with the PCA certificate the running system actually produces? (ii) does
the **rigid-vs-strategy distinction** flag real policy smells? A permission granted
as `⟨K⟩(read ∨ write)` *without a decided disjunct* is ambient/over-broad
authority; the rigid-evidence variant, which validates
`◯(A∨B) ⊃ (◯A ∨ ◯B)`, forces the policy to name which right is actually conferred.
*Success (measurable):* the extracted evidence reconstructs the authorization
certificate for a suite of policy queries (agreement checked against PCFS-style
proof objects), and the rigid/strategy classifier separates least-privilege
policies (decided disjuncts) from ambient-authority ones on a labelled policy set.

This is the study that exercises the framework's **new features on an external,
running artefact**: evidence extraction → auditable belief trails; rigid-vs-
strategy → least-privilege analysis; and it re-verifies the paper's own
`A ⊃ ⟨K⟩A` (truth-closure) and `⟨K⟩⊥ ⊅ ⊥` (quarantined inconsistency of a
malicious principal) *in the security setting where they were independently found*.

**(d) Value over existing tools / limits.** PCA systems already check
certificates; what they do not have is a *semantics* in which the certificate is
recovered as the extracted evidence of a belief, nor a principled analysis of
disjunctive/ambient authority via `◯(A∨B)` vs `◯A∨◯B`. The belief model gives both
as machine-checked objects. Honest limits: existing PCA is a mature engineering
practice, so the value is analytic (audit-trail faithfulness, least-privilege
classification), not a new enforcement mechanism; and the indexed model multiplies
the mechanisation obligations O1–O3 per principal (see effort).

**(e) Effort.** Medium–high. ~2–3 months after O3: needs the *indexed* extension of
the Route B model (a family `{⟨K⟩}` of nuclei, with delegation = interaction
between indices — new lemmas beyond single-`◯` O2), the encoding of a real policy,
and the certificate cross-check. Highest scientific payoff in the programme;
strongly recommended as the flagship (see §2).

---

### Study 3 — Certified effectful computation & proof-carrying code (the monad heritage; a positioning + certification study)

**(a) Phenomenon.** Moggi's computational monad `T A` models "a computation of an
`A`, with effects"; under Curry–Howard the lax `◯` *is* this monad on the
propositional side. [**VERIFIED**, Moggi 1991; and the standard identification
lax ≅ monad, Benton–Bierman–de Paiva — **UNVERIFIED** exact reference, cited as
[BBdP98] in Garg–Tschantz.] Proof-carrying code ships a machine-checkable safety
proof with untrusted code so a host can *believe it safe subject to checking the
certificate*. [**VERIFIED**, Necula, POPL 1997.]

**(b) Mapping.**

| model component | in this domain |
|---|---|
| `W` (worlds) | program points / store-and-heap configurations; verification stages |
| `Rᵢ` (information growth) | the verifier's established invariants grow along the program |
| `Rₘ` (constraint discharge) | the effect executes / the certificate is checked — the monadic computation runs |
| `F` (fallible worlds) | unsafe states forbidden by the safety policy (out-of-bounds, type violation) |
| `E` (evidence) | the PCC safety proof / the effectful realiser (Moggi's `T A` value) |
| `◯` (belief) | "`φ` holds after running the computation / on passing the check" = believed-safe subject to the certificate |

**(c) The study.** Take a PCC-style safety proof for a small compiled routine (or a
monadic effectful program with a stated post-condition), map it to the Route B
model, extract the evidence via O3, and check the extracted object is exactly a
machine-checkable safety certificate — i.e. that "belief that the code is safe"
and "the certificate" are the *same* extracted realiser. *Question:* does the
evidential-belief reading recover PCC's certificate as `◯`-evidence, and does it
say precisely *which* effects fit? *Success:* for ≥ 1 real routine, the O3-
extracted evidence is a standalone checkable safety proof, and the write-up states
sharply the fragment of Moggi's monads that the belief reading covers.

**(d) Value / limits — and the honest boundary this study exists to draw.** The
key limit is a theorem, not a hedge: **PLL's `◯` is the lex-idempotent fragment of
Moggi's monads** (`◯◯ = ◯` and meet-preservation), whereas state and continuation
monads are *deliberately not* idempotent. [**VERIFIED**, nLab / effective-topos
analysis in `realisability-modal-lit.md`: LT-topologies ⟺ lex-idempotent monads;
`LT ⊂ monads`.] So the belief reading fits *verification/safety* effects
("safe", "well-typed", "checked" — idempotent: once believed-safe, believing-that
adds nothing) and does **not** claim to model general side effects. This study's
scientific output is exactly that boundary, drawn precisely and machine-checked on
one PCC example — valuable because it prevents the paper from over-claiming the
Moggi lineage.

**(e) Effort.** Low–medium. ~3–5 weeks after O3, mostly the single-example
encoding plus the idempotence-boundary lemma (which is small and worth having in
the paper's related-work section regardless).

---

### Study 4 — Eventual consistency / distributed belief convergence (exploits monotone growth over branching futures, no confluence)

**(a) Phenomenon.** In a replicated distributed system a fact is not globally true
at once but becomes agreed *once replicas synchronise* — "believed once the
synchronisation constraints discharge". CRDTs guarantee *strong eventual
consistency*: replicas that have seen the same operations converge, with no
coordination. This has a machine-checked metatheory. [**VERIFIED**, Gomes–
Kleppmann–Mulligan–Beresford, *Verifying Strong Eventual Consistency in
Distributed Systems*, OOPSLA 2017 (PACMPL 1), Isabelle/HOL.]

**(b) Mapping.** This is the study for which the Route B design choices —
**branching, monotone, no forward confluence** (`route-b-model.md` §3) — are not a
technicality but the domain's actual shape.

| model component | in this domain |
|---|---|
| `W` (worlds) | replica states: each replica's local view of the data |
| `Rᵢ` (information growth) | a replica applies more operations locally; its CRDT state climbs the join-semilattice (heredity = a replica never un-learns) |
| `Rₘ` (constraint discharge) | a synchronisation / merge (anti-entropy) step: a world reachable once messages are delivered and states merged |
| `F` (fallible worlds) | partition / failure / Byzantine-replica states |
| `E` (evidence) | the causal history / version vector / merge witness — a realiser that after merging, the value converges |
| `◯` (belief) | "`φ` is eventually consistent / believed-agreed" = `φ` holds once synchronisation completes |

Two structural coincidences make this more than a relabelling. First, concurrent
replicas are **incomparable `Rᵢ`-futures** — branching with *no* common refinement
forced — exactly the no-confluence regime the paper needs for soundness; forcing
confluence would (machine-checked, `PLLFrames.lean`) validate
`◯(A∨B) ⊃ ◯A ∨ ◯B`, unsound for PLL. Second, the **sequential-composition meet law**
(`route-b-model.md` §3: discharge one constraint, then the next *at the world the
first produced*) mirrors CRDT **merge associativity / commutativity** — the
convergence argument's engine.

**(c) The study.** Take one verified CRDT from the OOPSLA 2017 development (the
Observed-Remove Set or the Replicated Growable Array) and re-express its
convergence specification as a lax-belief statement `◯(all replicas agree)` in the
Route B model in Lean, proving strong eventual consistency *as a `◯`-theorem* with
the merge witness extracted via O3. *Question:* does the belief reading give a
*modular* convergence proof — belief = eventual agreement — that composes across
operations by the sequential-meet law, and does belief-growth track state-growth
(Lemma 1 heredity)? *Success:* reproduce the SEC theorem for one CRDT as a
machine-checked `◯`-statement with extracted evidence, and exhibit `Rᵢ`-heredity =
CRDT monotonicity as the *same* lemma.

**(d) Value / limits.** The OOPSLA 2017 proofs are complete and general; the belief
framework does not improve on their coverage. Its contribution is *conceptual
unification with an extracted artefact*: it identifies SEC as a belief-modal
statement, ties CRDT monotonicity to `◯`-heredity and merge to the lax meet, and
produces the convergence witness as `◯`-evidence — a bridge between the distributed-
systems and modal-logic accounts that neither side currently has. Honest limit: for
one CRDT this is a demonstration; a general "belief-modal SEC" metatheorem would be
a further, larger result (flag **SPECULATIVE** until proven).

**(e) Effort.** Medium. ~6–8 weeks after O3, plus a small model of one CRDT's
operations and merge. The branching/no-confluence structure is already the model's
default, which is why this fits cleanly.

---

### Study 5 — Evidence-graded diagnostic and safety-critical reasoning (exploits rigid-vs-strategy `◯(A∨B)`)

*Marked partly **SPECULATIVE**: the deliverable is a formalisation-and-classification
case study on real protocols, not a controlled clinical/field trial. Said plainly
so it is not oversold.*

**(a) Phenomenon.** In differential diagnosis (clinical), fault diagnosis
(engineering), and branching contingency planning, an agent holds a *disjunctive*
belief — "condition `A` or condition `B`" — and must decide whether to **commit**
to a disjunct now or **keep the differential open with a per-branch plan**. Forcing
commitment too early is a named diagnostic error ("premature closure"). This is
exactly the paper's rigid-vs-strategy distinction for `◯(A∨B)`.

**(b) Mapping.**

| model component | in this domain |
|---|---|
| `W` (worlds) | information states of the diagnostician: the test results / observations known so far |
| `Rᵢ` (information growth) | new results arrive (monotone: an observation does not un-happen) |
| `Rₘ` (constraint discharge) | the deciding test is performed — the constraint that resolves the disjunction (order the biopsy, run the diagnostic) |
| `F` (fallible worlds) | clinically/physically impossible states, contradictory findings |
| `E` (evidence) | the evidence chain: which findings support which diagnosis; a realiser deciding `A∨B` = a procedure naming the disjunct |
| `◯` (belief) | "`φ` is the believed diagnosis subject to confirmatory evidence" |

**(c) The study — the distinctive bite.** Formalise a *real, published* decision
protocol — a clinical diagnostic algorithm (e.g. a guideline decision tree), or an
aviation checklist / fault tree — in **both** Route B evidence clauses in Lean:

> `⊩ˢ` (strategy evidence): `◯(A∨B)` realisable by a *per-branch plan* — decide the
>       disjunct differently in each information-future. Keeps the differential open.
> `⊩ᵘ` (rigid evidence): `◯(A∨B)` demands *one committed disjunct across all futures*,
>       and validates `◯(A∨B) ⊃ (◯A ∨ ◯B)` — "decide now".

Classify each protocol step by which clause its safe execution requires. *Question:*
does the rigid/strategy separation correctly distinguish steps that *demand*
commitment (`◯A ∨ ◯B` — e.g. "administer the antidote for A or for B, but you must
choose") from steps that admit deferral (`◯(A∨B)` with a branch-specific plan —
"keep both on the differential, order the confirmatory test")? Does forcing `⊩ᵘ`
where the protocol intends `⊩ˢ` reproduce *premature closure* as a formal error?
*Success (measurable):* for ≥ 1 real protocol, the model's `⊩ˢ`/`⊩ᵘ` classification
matches an expert annotation of "safe to defer" vs "must commit", and the
separating formula `◯(A∨B) ⊃ ◯A∨◯B` is machine-checked to hold under `⊩ᵘ` and fail
under `⊩ˢ` on the protocol's own model (reusing the split-model triptych,
`route-b-model.md` §5–6).

**(d) Value / limits.** No existing diagnostic-support tool distinguishes
"disjunctive belief with a decision strategy" from "disjunctive belief forced to a
disjunct" as a *logical* property with an extracted witness; the rigid/strategy
pair does, and it lines up with a real, named class of reasoning errors. That
alignment is the scientific claim. Limit (stated up front): this is a
knowledge-representation / formalisation study; establishing that the classifier
*predicts* clinician behaviour or reduces error would be a separate empirical
programme (**SPECULATIVE**), outside a logic paper's reach. The defensible,
in-scope result is the machine-checked classification of a real protocol.

**(e) Effort.** Medium. ~6–10 weeks after O3 *and* the `⊩ˢ`/`⊩ᵘ` split (ladder items
4–6, currently OPEN): both clauses must be mechanised before any protocol is
encoded. Highest conceptual novelty; requires the most new model machinery.

---

### Study 6 (lighter) — Sensor fusion / provenance-tracked knowledge bases

*Listed briefly; **SPECULATIVE**, lower nearness.* `◯φ` = "φ believed given the
fused sensor evidence / the provenance-justified assertion"; `W` = fusion states,
`Rᵢ` = arrival of sensor reports / provenance records, `Rₘ` = the fusion/validation
step that discharges a reliability constraint, `E` = the provenance chain (which
sources, through which transforms), `F` = faulty-sensor / conflicting-source states.
Belief growth as sources report is monotone; provenance is the extracted evidence.
Attractive because provenance systems already record exactly `E`, but there is no
single external verified artefact as clean as PCFS or the OOPSLA CRDTs to consume,
so it ranks below Studies 1–5. Worth a paragraph in the paper as a natural fit; not
a first study.

---

## 2. What to build first

**Recommendation.** Do not start from a domain; start from the two mechanisations
every study needs, then run the two studies that de-risk the programme.

1. **Land the model core (prerequisite, already the ladder):** the
   `RealisabilityModel` structure, Lemma 1 (heredity = increasing belief), O2 (the
   five nucleus laws incl. the sequential-composition meet), and **O3 (soundness
   with evidence extraction)** — `route-b-model.md` §8 items 1–5. *No study is an
   empirical result before O3 is `sorry`-free and axiom-clean.*

2. **Flagship: Study 2 (access control), because it validates against external
   artefacts.** It is the only study whose extracted evidence can be checked against
   an *existing running system's* proof objects (PCFS-style PCA), it independently
   re-verifies the paper's own `A ⊃ ⟨K⟩A` and `⟨K⟩⊥ ⊅ ⊥` in a second field, and it
   exercises both new features (evidence trails; rigid-vs-strategy least-privilege).
   Highest scientific return.

3. **In parallel, Study 1 (hardware), because it is the lowest-risk correctness
   demonstrator** and reuses the already-mechanised F&M frame — the safest way to
   show the extracted evidence is *real* (validated against simulation) while the
   indexed machinery for Study 2 is being built.

4. **Then Study 4 (eventual consistency)** to showcase the branching/no-confluence
   design against a verified external CRDT, and **Study 5 (rigid-vs-strategy on a
   real protocol)** as the conceptual-novelty capstone, since it needs the most new
   model (`⊩ˢ`/`⊩ᵘ`). Study 3 (PCC/monad boundary) is a small, high-value
   related-work certification that can be slotted in whenever O3 is done.

Rationale in one line: **O3 first (the slogan-as-theorem), then the study whose
artefacts are external and already exist (access control), with the original
application (hardware) as the correctness anchor.**

---

## 3. References (tagged)

*Tag key: **VERIFIED** = primary/near-primary source reached this session;
**UNVERIFIED** = from memory or referenced-but-not-opened, check before print;
**SPECULATIVE** = a proposed study whose payoff is conjectural.*

**Lax logic — origin and hardware application**
- **[VERIFIED]** M. Fairtlough, M. Mendler, *Propositional Lax Logic*, Information
  and Computation **137**(1) (1997) 1–33. ScienceDirect S0890540197926274; durable
  PDF at uni-bamberg.de. The founding paper; `◯` as "correctness up to constraints".
- **[VERIFIED]** M. Mendler, *A Modal Logic for Handling Behavioural Constraints in
  Formal Hardware Verification*, PhD thesis, Univ. of Edinburgh, Dept. of Computer
  Science, ECS-LFCS-93-255, 1993. (era.ed.ac.uk handle 1842/15374.)
- **[VERIFIED]** M. Fairtlough, M. Mendler, *An Intuitionistic Modal Logic with
  Applications to the Formal Verification of Hardware*, CSL 1994, LNCS 933,
  doi 10.1007/BFb0022268.
- **[VERIFIED title/venue; author list UNVERIFIED]** *Timing Analysis of
  Combinational Circuits in Intuitionistic Propositional Logic*, Formal Methods in
  System Design (Springer), doi 10.1023/A:1008780817617. (Confirm exact authors
  before citing.)

**Computational monads (the effect heritage)**
- **[VERIFIED]** E. Moggi, *Notions of Computation and Monads*, Information and
  Computation **93**(1) (1991) 55–92, doi 10.1016/0890-5401(91)90052-4.
- **[UNVERIFIED]** N. Benton, G. Bierman, V. de Paiva, *Computational types from a
  logical perspective*, J. Functional Programming (1998) [cited as [BBdP98] in
  Garg–Tschantz for lax ≅ monad under Curry–Howard]. Confirm exact title/volume.

**Access control / authorization — `says` as a lax/indexed-lax/monadic modality**
- **[VERIFIED]** D. Garg, M. C. Tschantz, *From Indexed Lax Logic to Intuitionistic
  Logic*, Carnegie Mellon Univ. CMU-CS-07-167, Jan 2008. **The linchpin source.**
  Verbatim: "an increasingly large number of proposals … have chosen `⟨K⟩A` to be a
  lax modality … the access control logic becomes an indexed lax logic, with one lax
  modality for every principal"; "`A ⊃ ⟨K⟩A` forces every principal to state every
  true statement … if `A` has a proof, then every principal will believe it"; "It is
  not the case that `(⟨K⟩⊥) ⊃ ⊥`. Thus, individual principals may make inconsistent
  statements without making the logic inconsistent."
- **[VERIFIED]** D. Garg, M. Abadi, *A Modal Deconstruction of Access Control
  Logics*, FoSSaCS 2008, LNCS 4962. `says`-as-monad logics (CDD, ICL) translate
  soundly and completely to S4; "from lax logic to S4 … as a special case … appears
  to be new." (users.soe.ucsc.edu/~abadi/Papers/modal-decons.pdf.)
- **[VERIFIED]** M. Abadi, *Access Control in a Core Calculus of Dependency*,
  ICFP 2006 (also ENTCS), doi 10.1145/1159803.1159839. "A rather direct
  generalization of lax logic"; monad indexed by a lattice of security labels.
- **[VERIFIED]** D. Garg, F. Pfenning, *Non-Interference in Constructive
  Authorization Logic*, CSFW/CSF 2006 (people.mpi-sws.org/~dg/papers/csfw06.pdf).
  Constructive `says`; intuitionistic base motivated by "constructive evidence".
- **[VERIFIED existence; venue check advised]** D. Garg, F. Pfenning, *A
  Proof-Carrying File System* (PCFS), CMU-CS-09-123 (2009) / IEEE S&P 2010. Running
  PCA system — the external artefact for Study 2.
- **[UNVERIFIED]** M. Abadi, A. Banerjee, N. Heintze, J. G. Riecke, *A Core Calculus
  of Dependency* (DCC), POPL 1999, pp. 147–160. Named in the task; source not opened
  this session — confirm page range before citing.
- **[UNVERIFIED]** M. Abadi, M. Burrows, B. Lampson, G. Plotkin, *A Calculus for
  Access Control in Distributed Systems*, ACM TOPLAS 1993 [ABLP93] — origin of the
  `says` operator; referenced by Garg–Tschantz, not opened here.
- **[UNVERIFIED]** A. W. Appel, E. W. Felten, *Proof-Carrying Authentication*,
  ACM CCS 1999 [AF99] — PCA architecture; referenced, not opened here.

**Proof-carrying code**
- **[VERIFIED]** G. C. Necula, *Proof-Carrying Code*, POPL 1997,
  doi 10.1145/263699.263712. Code + machine-checkable safety certificate.

**Distributed systems — eventual consistency**
- **[VERIFIED]** V. B. F. Gomes, M. Kleppmann, D. P. Mulligan, A. R. Beresford,
  *Verifying Strong Eventual Consistency in Distributed Systems*, OOPSLA 2017 /
  Proc. ACM Program. Lang. **1** (2017), Isabelle/HOL. External artefact for Study 4.

**Epistemic / evidential background (from `docs/iel-justification-lit.md`,
`docs/realisability-modal-lit.md` — carried over, already tagged there)**
- **[VERIFIED]** S. Artemov, T. Protopopescu, *Intuitionistic Epistemic Logic*,
  Review of Symbolic Logic **9**(2) (2016) 266–298; arXiv:1406.1582. `IEL⁻` = the
  nearest published *belief* neighbour; differs from `◯` in idempotence.
- **[VERIFIED]** S. Artemov, M. Fitting, *Justification Logic*, SEP. Evidence-term
  models; standard `LP` forgetful projection is *factive* (reverse profile to `◯`) —
  an evidential `◯` needs a *non-factive* justification logic.
- **[VERIFIED]** M. Nakata (2026, arXiv:2602.23218); Yamada (2026, arXiv:2602.23086);
  N. Valliappan, *Lax Modal Lambda Calculi* (2026, arXiv:2512.10779, Agda-checked) —
  the realiser/nucleus-forcing model background for Route B.

**Internal (this repository, machine-checked or Lean-obligation)**
- Route B model + proof obligations O1–O3: `docs/route-b-model.md`.
- F&M constraint frame (mechanised): `LaxLogic/PLLKripke.lean` (`ConstraintModel`,
  `force_hered`, `soundness`); non-confluence facts: `LaxLogic/PLLFrames.lean`
  (`not_provable_somehow_or_dist`, `force_somehow_or_dist_of_confluent`).
- Context completeness (Curry Thm 6, "belief = provability under a constraint"),
  infinite closed fragment: `wip/context_completeness.lean`, `wip/lax_infinite.lean`.
- Normality/idempotence positioning vs IEL: `wip/belief_normality.lean`.
