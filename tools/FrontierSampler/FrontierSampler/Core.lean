/-!
# FrontierSampler — the generic core

A property-based-testing layer for formal developments whose interesting
instances are **sparse**: the statement under test carries side conditions
(closure, coverage, arithmetic "room" bounds) that a naive random instance
almost never satisfies, so an ungated generator spends its whole budget on
cells that prove nothing.

This file is **dependency-free** on purpose.  It supplies four things that a
QuickCheck-style library (in Lean: `Plausible`) does not:

1. **Seeded stratification.**  A campaign is a list of `Stratum`s, each a
   named region of instance space with its own generator, its own sample
   count and its own seed range.  Strata are the unit of reporting, so a
   campaign says *which structural region* was covered, not just how many
   tests passed.
2. **An admissibility gate.**  A `Gate` is a decidable side condition the
   generated instance must satisfy before the cell is counted at all.
   Gate failures are recorded, never counted as passes — an over-tight
   generator shows up in the ledger as a wall of `GATE` lines rather than
   as a silent clean run.
3. **A certificate-carrying, append-only corpus.**  Every cell appends one
   line to a ledger file as it finishes, so a killed run loses nothing, and
   a hit records enough (seed, stratum, columns, certificate) to be
   replayed and pinned without re-running the search.
4. **Replay.**  Because a cell is a pure function of `(stratum, seed, size)`
   the corpus can be re-driven against a *different* statement later: the
   same instances, a new verdict column, no regeneration guesswork.

Generation itself is delegated: `SeedGen` is a plain function type, so
`Plausible.Gen` plugs in with one line (see the README).  `Splitmix` below
is a fallback for dependency-free use, not a competitor.

## Contract on `SeedGen`

`gen seed size` must be a **pure function of its two arguments**.  Nothing in
this file reads a clock or a system entropy source, and `Plausible.Gen`'s own
default runner (`Gen.run`) does — it draws from the global `stdGenRef`.  Use
`Plausible.runRandWith`, which takes the seed explicitly.  A campaign whose
generator is not a pure function of `(seed, size)` cannot be replayed and its
corpus is worthless.
-/

namespace FrontierSampler

/-! ## 1  Seeded generation -/

/-- A **seeded generator**: a pure function of an explicit seed and a size
parameter, returning `none` when this seed names no instance in this
stratum (e.g. the grid position is past the end of the cell grid).

Instantiate from `Plausible.Gen` with

```
def ofGen (g : Plausible.Gen ι) : SeedGen ι := fun seed size =>
  ((Plausible.runRandWith seed g :
      ReaderT (ULift Nat) (Except Plausible.GenError) ι).run ⟨size⟩).toOption
```
-/
abbrev SeedGen (ι : Type) : Type := Nat → Nat → Option ι

/-! ### A fallback PRNG

Twenty-five lines of splitmix64, for users who do not want the `Plausible`
dependency.  It is deliberately not a monad: if you want combinators, use
`Plausible.Gen` and the one-line adapter above. -/

namespace Splitmix

/-- One splitmix64 step: returns `(output, next state)`. -/
def step (s : UInt64) : UInt64 × UInt64 :=
  let s' := s + 0x9e3779b97f4a7c15
  let z₀ := s'
  let z₁ := (z₀ ^^^ (z₀ >>> 30)) * 0xbf58476d1ce4e5b9
  let z₂ := (z₁ ^^^ (z₁ >>> 27)) * 0x94d049bb133111eb
  (z₂ ^^^ (z₂ >>> 31), s')

/-- `draw s n` returns a value in `[0, n)` (or `0` when `n = 0`) and the next
state. -/
def draw (s : UInt64) (n : Nat) : Nat × UInt64 :=
  let (z, s') := step s
  (if n == 0 then 0 else z.toNat % n, s')

/-- Seed the state. -/
def mk (seed : Nat) : UInt64 := UInt64.ofNat seed

end Splitmix

/-! ## 2  Strata -/

/-- A **stratum**: a named region of instance space, its generator, and the
seed range to sample from it.  Seeds actually used are
`seed0, …, seed0 + samples - 1`; recording `seed0` separately keeps two
campaigns over the same stratum from colliding in the corpus. -/
structure Stratum (ι : Type) where
  /-- Stratum name.  Appears in the corpus and is the key replay uses to
  find the generator again, so keep it stable across campaigns. -/
  name : String
  /-- The generator.  Must be a pure function of `(seed, size)`. -/
  gen : SeedGen ι
  /-- How many seeds to draw. -/
  samples : Nat := 12
  /-- The size parameter handed to the generator. -/
  size : Nat := 4
  /-- First seed. -/
  seed0 : Nat := 0
  /-- Free-text note recorded once per stratum in the corpus. -/
  note : String := ""

/-! ## 3  The admissibility gate -/

/-- An **admissibility gate**: one decidable clause of the statement's side
condition.  Gates are checked in order and the first failure is named, so
the corpus says *which* clause an inadmissible cell violated. -/
structure Gate (ι : Type) where
  /-- The clause's name, as it should appear in the corpus. -/
  name : String
  /-- The decision procedure.  Must be total and cheap. -/
  check : ι → Bool

/-- Run a gate stack; returns the name of the first failing clause. -/
def firstFailure {ι : Type} (gs : List (Gate ι)) (x : ι) : Option String :=
  (gs.find? (fun g => !(g.check x))).map (·.name)

/-! ## 4  Triage verdicts -/

/-- The verdict of one cell.

`hit` means a **certificate was found** — for a refutation hunt, a checked
countermodel.  `quiet` means the (bounded) hunt found nothing; it is NOT a
positive result and must never be reported as one.  `skip` means the cell was
too large for the cap and was not run at all. -/
inductive Triage where
  /-- A certificate was found and is recorded. -/
  | hit
  /-- The bounded hunt found nothing.  Not evidence of anything. -/
  | quiet
  /-- The cell exceeded the size cap and was not run. -/
  | skip
  deriving DecidableEq, Repr, Inhabited

def Triage.tag : Triage → String
  | .hit => "R!"
  | .quiet => "quiet"
  | .skip => "SKIP"

def Triage.ofTag? : String → Option Triage
  | "R!" => some .hit
  | "quiet" => some .quiet
  | "SKIP" => some .skip
  | _ => none

/-- What a triage function returns: the verdict, a certificate string
sufficient to replay/pin a hit, and any extra columns worth recording. -/
structure Outcome where
  triage : Triage
  /-- For a `hit`: enough to reconstruct the certificate (e.g. the model and
  refuting world).  Empty otherwise. -/
  cert : String := ""
  /-- Extra columns, recorded after the instance's own columns. -/
  cols : List (String × String) := []
  deriving Inhabited

/-! ## 5  The corpus ledger -/

/-- Field separator.  Values are sanitised against it. -/
def sep : String := "|"

private def sanitise (s : String) : String :=
  (s.replace "|" "/").replace "\n" " "

/-- One corpus line, parsed. -/
structure Rec where
  stratum : String
  seed : Nat
  size : Nat
  /-- Instance columns then outcome columns, in recording order. -/
  cols : List (String × String)
  /-- `none` = admissible; `some clause` = the gate clause that failed. -/
  gateFail : Option String
  triage : Triage
  ms : Nat
  cert : String
  deriving Inhabited

/-- The corpus format version.  Bump when the column contract changes; the
reader refuses lines it does not know. -/
def formatVersion : String := "fs1"

def Rec.render (r : Rec) : String :=
  let base :=
    [ formatVersion
    , "stratum=" ++ sanitise r.stratum
    , "seed=" ++ toString r.seed
    , "size=" ++ toString r.size ]
  let cols := r.cols.map (fun kv => sanitise kv.1 ++ "=" ++ sanitise kv.2)
  let tail :=
    [ "gate=" ++ (match r.gateFail with | none => "ok" | some c => "FAIL:" ++ sanitise c)
    , "verdict=" ++ r.triage.tag
    , "ms=" ++ toString r.ms
    , "cert=" ++ sanitise r.cert ]
  String.intercalate sep (base ++ cols ++ tail)

private def splitKV (s : String) : Option (String × String) :=
  match s.splitOn "=" with
  | [] => none
  | [_] => none
  | k :: rest => some (k, String.intercalate "=" rest)

/-- Parse one corpus line.  Returns `none` for comments, banners, blank lines
and lines of an unknown format version. -/
def Rec.parse? (line : String) : Option Rec := do
  let parts := line.splitOn sep
  match parts with
  | [] => none
  | v :: rest =>
    if v != formatVersion then none else
    let kvs := rest.filterMap splitKV
    let find? (k : String) : Option String := (kvs.find? (fun p => p.1 == k)).map (·.2)
    let stratum ← find? "stratum"
    let seed ← (find? "seed").bind (·.toNat?)
    let size ← (find? "size").bind (·.toNat?)
    let gate ← find? "gate"
    let verdict ← (find? "verdict").bind Triage.ofTag?
    let ms ← (find? "ms").bind (·.toNat?)
    let cert ← find? "cert"
    let reserved := ["stratum", "seed", "size", "gate", "verdict", "ms", "cert"]
    let cols := kvs.filter (fun p => !(reserved.contains p.1))
    some { stratum, seed, size, cols
         , gateFail := if gate == "ok" then none else some (gate.replace "FAIL:" "")
         , triage := verdict, ms, cert }

/-- Column lookup, for replay. -/
def Rec.col? (r : Rec) (k : String) : Option String :=
  (r.cols.find? (fun p => p.1 == k)).map (·.2)

/-- Column lookup as a `Nat`. -/
def Rec.natCol? (r : Rec) (k : String) : Option Nat := (r.col? k).bind (·.toNat?)

/-- An append-only corpus file.  Every write is flushed, so a killed run
keeps everything that reached the file. -/
structure Ledger where
  path : System.FilePath

def Ledger.line (l : Ledger) (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk l.path IO.FS.Mode.append
  IO.println s
  h.putStrLn s
  h.flush

/-- A non-record line (banner, note, timestamp).  `#` marks it as a comment
so `Rec.parse?` skips it. -/
def Ledger.comment (l : Ledger) (s : String) : IO Unit := l.line ("# " ++ s)

def Ledger.write (l : Ledger) (r : Rec) : IO Unit := l.line r.render

/-- Read and parse a corpus, discarding comments and unparsable lines. -/
def Ledger.read (l : Ledger) : IO (List Rec) := do
  let txt ← IO.FS.readFile l.path
  pure ((txt.splitOn "\n").filterMap Rec.parse?)

/-! ## 6  Tallies -/

structure Tally where
  hits : Nat := 0
  quiet : Nat := 0
  skips : Nat := 0
  gated : Nat := 0
  genFail : Nat := 0
  ms : Nat := 0
  deriving Inhabited

def Tally.add (a b : Tally) : Tally :=
  { hits := a.hits + b.hits, quiet := a.quiet + b.quiet, skips := a.skips + b.skips
  , gated := a.gated + b.gated, genFail := a.genFail + b.genFail, ms := a.ms + b.ms }

/-- Cells that were actually run (gate passed and size cap allowed). -/
def Tally.counted (t : Tally) : Nat := t.hits + t.quiet

def Tally.render (t : Tally) : String :=
  s!"hits={t.hits} quiet={t.quiet} skip={t.skips} gated-out={t.gated} \
gen-fail={t.genFail} counted={t.counted} ({t.ms} ms)"

/-! ## 7  The campaign runner -/

/-- Run one stratum: for each seed in the stratum's range, generate, gate,
triage, and append one corpus line.  Nothing is held in memory between
cells, and every line is flushed, so the run is safe to kill.

`cols` are the instance's own recorded columns; they must contain everything
a replay needs beyond `(stratum, seed, size)` — in practice nothing, since
the generator is a pure function of those three, but recording the shape
makes the corpus readable and lets a hit be checked by eye. -/
def runStratum {ι : Type} (led : Ledger) (st : Stratum ι)
    (gates : List (Gate ι)) (cols : ι → List (String × String))
    (triage : ι → IO Outcome) : IO Tally := do
  let mut t : Tally := {}
  for i in [0:st.samples] do
    let seed := st.seed0 + i
    match st.gen seed st.size with
    | none => t := { t with genFail := t.genFail + 1 }
    | some x =>
      let c := cols x
      match firstFailure gates x with
      | some clause =>
        led.write { stratum := st.name, seed, size := st.size, cols := c
                  , gateFail := some clause, triage := .skip, ms := 0, cert := "" }
        t := { t with gated := t.gated + 1 }
      | none =>
        let t0 ← IO.monoMsNow
        let o ← triage x
        let t1 ← IO.monoMsNow
        led.write { stratum := st.name, seed, size := st.size
                  , cols := c ++ o.cols, gateFail := none
                  , triage := o.triage, ms := t1 - t0, cert := o.cert }
        t := { t with ms := t.ms + (t1 - t0) }
        match o.triage with
        | .hit => t := { t with hits := t.hits + 1 }
        | .quiet => t := { t with quiet := t.quiet + 1 }
        | .skip => t := { t with skips := t.skips + 1 }
  led.comment s!"stratum {st.name}: {t.render}"
  pure t

/-- Run a list of strata against one gate stack and one triage function. -/
def runCampaign {ι : Type} (led : Ledger) (tag : String)
    (strata : List (Stratum ι))
    (gates : List (Gate ι)) (cols : ι → List (String × String))
    (triage : ι → IO Outcome) : IO Tally := do
  led.comment s!"=== campaign {tag} : {strata.length} strata ==="
  let mut t : Tally := {}
  for st in strata do
    led.comment s!"-- stratum {st.name} seeds {st.seed0}..{st.seed0 + st.samples - 1} \
size {st.size} {st.note}"
    let u ← runStratum led st gates cols triage
    t := t.add u
  led.comment s!"=== campaign {tag} TOTAL: {t.render} ==="
  pure t

/-! ## 8  Replay

A corpus is replayable because a cell is a pure function of
`(stratum, seed, size)`.  `replay` re-derives each recorded instance through
a caller-supplied `regen`, hands it to a caller-supplied `recheck` — which
may screen a **different** statement from the one the corpus recorded — and
reports every disagreement.

Two uses:

* **regression**: `recheck` is the original triage; any disagreement means
  the harness or the statement changed under the corpus.
* **re-aim**: `recheck` screens a new statement; the corpus supplies the
  instances for free, and a `hit` where the corpus has `quiet` is a
  refutation of the new statement at an instance already known admissible. -/

structure ReplayReport where
  total : Nat := 0
  regenFail : Nat := 0
  agreed : Nat := 0
  changed : Nat := 0
  newHits : Nat := 0
  notes : List String := []
  deriving Inhabited

def ReplayReport.render (r : ReplayReport) : String :=
  s!"replay: {r.total} records, {r.agreed} agree, {r.changed} changed \
({r.newHits} new hits), {r.regenFail} unregenerable"

/-- Replay a corpus.  `regen stratum seed size` must be the same function the
campaign used (look the stratum up by name); `recheck` returns the verdict of
the statement being screened now. -/
def replay {ι : Type} (led : Ledger)
    (regen : String → Nat → Nat → Option ι)
    (recheck : ι → Rec → IO Outcome) : IO ReplayReport := do
  let recs ← led.read
  let mut r : ReplayReport := {}
  for rc in recs do
    if rc.gateFail.isSome then continue
    r := { r with total := r.total + 1 }
    match regen rc.stratum rc.seed rc.size with
    | none =>
      -- NB: trailing commas, not leading.  A leading-comma field layout is
      -- legal in a plain structure literal but NOT in a `with`-update.
      r := { r with
             regenFail := r.regenFail + 1,
             notes := r.notes ++ [s!"{rc.stratum}/{rc.seed}: regen failed"] }
    | some x =>
      let o ← recheck x rc
      if o.triage == rc.triage then
        r := { r with agreed := r.agreed + 1 }
      else
        let isNew := o.triage == Triage.hit
        r := { r with
               changed := r.changed + 1,
               newHits := r.newHits + (if isNew then 1 else 0),
               notes := r.notes ++
                 [s!"{rc.stratum}/{rc.seed}: {rc.triage.tag} -> {o.triage.tag} {o.cert}"] }
  pure r

end FrontierSampler
