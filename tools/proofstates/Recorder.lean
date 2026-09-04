/-
# Proof-state recorder

Elaborates a Lean source file, walks the resulting info trees, and produces a
record of every tactic step: its source position and text, its depth in the
tactic tree, and the pretty-printed goals before and after it.

The record is the same data Lean's infoview shows when the cursor is placed on
a tactic; the difference is that we collect *all* of it, in source order, so it
can be replayed offline.

## Toolchain notes (Lean v4.31.0)

* `Lean.Elab.runFrontend` is **not** usable here: on this toolchain its
  signature is `... → IO (Option Environment)`, so it returns no command state
  and therefore no info trees.  We drive the frontend one command at a time
  with the pieces in `Lean.Elab.Frontend` instead.
* `Lean.Elab.Command.elabCommandTopLevel` resets `infoState` *per command*
  (`Lean/Elab/Command.lean`: `modify fun st => { st with messages := {},
  infoState := { enabled := st.infoState.enabled } }`).  So info trees and
  messages must be harvested after every command; the final command state only
  carries the last command's.
* `Lean.Elab.async` defaults to `false`, but `runFrontend` and the language
  server override it to `true`.  Asynchronous elaboration moves a declaration's
  tactic proof into a separate task whose info tree is reported lazily, and
  `PartialContextInfo.parentDeclCtx` is then not generated.  We set
  `Elab.async := false` explicitly so that every tree is complete and carries
  its parent declaration name.
-/
import Lean

open Lean Elab

namespace ProofStates

/-! ## Configuration -/

structure Config where
  /-- The `.lean` file to record. -/
  file       : System.FilePath
  /-- If present, keep only steps whose declaration name contains this string. -/
  declPat?   : Option String := none
  jsonOut?   : Option System.FilePath := none
  htmlOut?   : Option System.FilePath := none
  /-- Pretty-printing width for goals. -/
  width      : Nat := 100
  /-- Safety valve: stop recording after this many steps. -/
  maxSteps   : Nat := 200000
  /-- Keep every tactic node, including the nested duplicates that share a
  source span with their parent (`by` / `tacticSeq` chains, macro expansions). -/
  keepAll    : Bool := false
  quiet      : Bool := false
  deriving Inhabited

/-! ## The record -/

/-- One pretty-printed goal.  Goals are interned: `Step.before` and
`Step.after` hold indices into the goal pool, because consecutive steps share
most of their goals and the record would otherwise be enormous. -/
structure Goal where
  /-- The metavariable's name.  The viewer uses it to match goals across a
  step, so "this goal was closed" can be told apart from "this goal changed". -/
  id   : String
  text : String
  deriving Inhabited

structure Step where
  idx        : Nat
  /-- Index of the top-level command this step belongs to. -/
  cmdIdx     : Nat
  /-- Index into `Record.decls`. -/
  decl       : Nat
  /-- Depth in the tactic tree (0 = outermost recorded tactic of the proof). -/
  depth      : Nat
  /-- Index of the enclosing recorded step, or `-1`. -/
  parent     : Int
  children   : Array Nat := #[]
  line       : Nat
  col        : Nat
  endLine    : Nat
  endCol     : Nat
  /-- Syntax kind, e.g. `Lean.Parser.Tactic.induction`. -/
  kind       : String
  elaborator : String
  /-- The tactic's source text, verbatim. -/
  text       : String
  before     : Array Nat
  after      : Array Nat
  deriving Inhabited

structure Decl where
  name      : String
  /-- Syntax kind of the enclosing command. -/
  kind      : String
  /-- First line of the command's source text, trimmed: a usable label. -/
  header    : String
  line      : Nat
  col       : Nat
  endLine   : Nat
  nSteps    : Nat := 0
  firstStep : Int := -1
  lastStep  : Int := -1
  /-- The declaration's source range carries an error message. -/
  broken    : Bool := false
  /-- The declaration's source range carries a `sorry` warning. -/
  sorried   : Bool := false
  deriving Inhabited

structure Msg where
  line     : Nat
  col      : Nat
  endLine  : Nat
  endCol   : Nat
  severity : String
  text     : String
  /-- Index of the innermost recorded step whose span contains this message,
  or `-1`.  This is what makes a stuck proof legible: the message is anchored
  to the state the prover was in. -/
  step     : Int := -1
  deriving Inhabited

structure Record where
  file          : String
  declPat       : String
  leanVersion   : String
  elaborationOk : Bool
  /-- Wall-clock milliseconds spent elaborating, walking and printing. -/
  elapsedMs     : Nat
  elabMs        : Nat
  nCommands     : Nat
  /-- Tactic nodes seen by the walk before the declaration filter. -/
  nRawSteps     : Nat
  goals         : Array Goal
  decls         : Array Decl
  steps         : Array Step
  msgs          : Array Msg
  source        : Array String
  deriving Inhabited

/-! ## Driving the frontend -/

/-- A single command's harvest: its syntax, its info trees, its messages. -/
structure CmdResult where
  stx    : Syntax
  trees  : PersistentArray InfoTree
  msgs   : List Message

/--
Elaborate `input` command by command, harvesting info trees and messages after
each one.  Nothing is discarded on error: `Command.elabCommandTopLevel` turns
elaboration failures into messages and the parser recovers, so a file that does
not compile still yields a record of everything that did elaborate.
-/
def elaborateFile (input : String) (fileName : String) (mainModule : Name)
    (opts : Options) : IO (Array CmdResult × List Message) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  let (env, headerMessages) ←
    processHeader header opts headerMessages inputCtx (mainModule := mainModule)
  let cmdState0 := Command.mkState env headerMessages opts
  let cmdState0 := { cmdState0 with infoState := { enabled := true } }
  let mut frontendState : Frontend.State :=
    { commandState := cmdState0, parserState, cmdPos := parserState.pos }
  let frontendCtx : Frontend.Context := { inputCtx }
  let mut results : Array CmdResult := #[]
  repeat
    let (done, st) ← (Frontend.processCommand frontendCtx).run frontendState
    frontendState := st
    let cs := st.commandState
    let trees := cs.infoState.trees.map (·.substitute cs.infoState.assignment)
    let stx := st.commands.back?.getD .missing
    results := results.push { stx, trees, msgs := cs.messages.toList }
    if done then break
  return (results, headerMessages.toList)

/-! ## Walking the info trees -/

/-- A tactic node kept by the walk, before pretty-printing. -/
structure Raw where
  ctx    : ContextInfo
  info   : TacticInfo
  depth  : Nat
  parent : Int
  cmdIdx : Nat

/-- The byte span of a piece of syntax, if it is genuine source text (as
opposed to macro output). -/
def srcSpan? (stx : Syntax) : Option (Nat × Nat) :=
  match stx.getHeadInfo with
  | .original .. =>
    match stx.getPos?, stx.getTailPos? with
    | some p, some q => if p.byteIdx < q.byteIdx then some (p.byteIdx, q.byteIdx) else none
    | _, _ => none
  | _ => none

/--
Collect `TacticInfo` nodes in traversal order (which, for a tactic block, is
source order), preserving nesting as `depth` + `parent`.

Nodes whose syntax is not original source text are skipped, though their
children are still visited, so nothing produced by a macro is lost — only the
macro's own synthetic copy of the syntax.  Everything else is kept here; the
structural filtering happens afterwards in `isContainer`.
-/
partial def collectSteps (cmdIdx : Nat) :
    Option ContextInfo → Nat → Int → InfoTree → Array Raw → Array Raw
  | ctx?, depth, parent, .context i t, acc =>
    collectSteps cmdIdx (i.mergeIntoOuter? ctx?) depth parent t acc
  | _, _, _, .hole _, acc => acc
  | ctx?, depth, parent, .node i cs, acc =>
    let ctx?' := i.updateContext? ctx?
    let descend (d : Nat) (p : Int) (acc : Array Raw) : Array Raw :=
      cs.foldl (fun a c => collectSteps cmdIdx ctx?' d p c a) acc
    match ctx?, i with
    | some ctx, .ofTacticInfo ti =>
      match srcSpan? ti.stx with
      | some _ =>
        let idx := acc.size
        let acc := acc.push { ctx, info := ti, depth, parent, cmdIdx }
        descend (depth + 1) (Int.ofNat idx) acc
      | none => descend depth parent acc
    | _, _ => descend depth parent acc

/--
Syntax kinds that carry no proof step of their own: they only group other
tactics.  Every tactic block sits under a
`byTactic → by → tacticSeq → tacticSeq1Indented` chain whose four nodes share
one before/after pair, and every `·` focus dot contributes a `cdotTk` atom.
Dropping these keeps the recorded tree isomorphic to the tactic script as
written.
-/
def containerKinds : List String :=
  [ "Lean.Parser.Term.byTactic", "Lean.Parser.Term.byTactic'", "by",
    "Lean.Parser.Tactic.tacticSeq", "Lean.Parser.Tactic.tacticSeq1Indented",
    "Lean.Parser.Tactic.tacticSeqBracketed", "Lean.cdotTk" ]

/--
Is this node a pure container, to be dropped with its children reattached to
its nearest surviving ancestor?

* the kinds above, and bare punctuation atoms (whose syntax kind is the token
  itself, e.g. `«]»`), are always containers;
* a `null` node with children is a grouping wrapper — the `with` clause of
  `induction`/`cases`, for instance — *except* when its source text begins with
  `|`, which is an alternative header (`| succ n ih =>`) and is worth keeping
  as a case label;
* a childless `null` node is a genuine sub-step, for instance one rule of a
  `rw [r₁, r₂]`, each of which reports its own state.
-/
def isContainer (kind text : String) (hasChildren : Bool) : Bool :=
  if kind == "null" then hasChildren && !text.startsWith "|"
  else containerKinds.contains kind || kind.startsWith "«"

/-! ## Pretty-printing -/

/-- Pretty-print one goal in the metavariable context recorded at that point.
Returns `none` if the goal is no longer in the context, which happens for goals
discarded by backtracking. -/
def ppGoal? (ctx : ContextInfo) (mctx : MetavarContext) (width : Nat) (g : MVarId) :
    IO (Option String) := do
  let ctx := { ctx with mctx }
  try
    let fmt ← ctx.runMetaM {} (Meta.ppGoal g)
    return some (fmt.pretty (width := width))
  catch _ =>
    return none

/-- Interning table for goals. -/
structure Pool where
  goals : Array Goal := #[]
  index : Std.HashMap String Nat := {}

def Pool.intern (p : Pool) (id text : String) : Nat × Pool :=
  let key := id ++ " " ++ text
  match p.index[key]? with
  | some i => (i, p)
  | none =>
    let i := p.goals.size
    (i, { goals := p.goals.push { id, text }, index := p.index.insert key i })

/-! ## Positions -/

structure Span where
  line    : Nat
  col     : Nat
  endLine : Nat
  endCol  : Nat
  deriving Inhabited

def spanOf (fm : FileMap) (a b : Nat) : Span :=
  let p := fm.toPosition ⟨a⟩
  let q := fm.toPosition ⟨b⟩
  { line := p.line, col := p.column, endLine := q.line, endCol := q.column }

def sliceOf (input : String) (a b : Nat) : String :=
  (Substring.Raw.mk input ⟨a⟩ ⟨b⟩).toString

/-! ## Building the record -/

def severityName : MessageSeverity → String
  | .information => "information"
  | .warning     => "warning"
  | .error       => "error"

/-- `ContextInfo.parentDecl?` is populated for the final (synchronous) info tree
of a declaration; if it is missing we fall back to a placeholder. -/
def declNameOf (r : Raw) : String :=
  match r.ctx.parentDecl? with
  | some n => n.toString
  | none   => "«anonymous»"

def commandLabel (input : String) (stx : Syntax) : String :=
  match stx.getPos?, stx.getTailPos? with
  | some p, some q =>
    let s := sliceOf input p.byteIdx q.byteIdx
    ((s.splitOn "\n").headD s).trimAscii.toString
  | _, _ => ""

def commandSpan (fm : FileMap) (stx : Syntax) : Span :=
  match stx.getPos?, stx.getTailPos? with
  | some p, some q => spanOf fm p.byteIdx q.byteIdx
  | _, _ => { line := 0, col := 0, endLine := 0, endCol := 0 }

def containsStr (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

def matchesPat (pat? : Option String) (name : String) : Bool :=
  match pat? with
  | none => true
  | some pat => containsStr name pat

/-- Elaborate, walk, print, assemble. -/
def record (cfg : Config) : IO Record := do
  let t0 ← IO.monoMsNow
  let input ← IO.FS.readFile cfg.file
  let fileName := cfg.file.toString
  let mainModule :=
    match cfg.file.fileStem with
    | some s => Name.mkSimple s
    | none   => `Recorded
  let opts : Options := Lean.Elab.async.set {} false
  unless cfg.quiet do
    IO.eprintln s!"[pstates] elaborating {fileName} (Elab.async := false) ..."
  let (cmds, headerMsgs) ← elaborateFile input fileName mainModule opts
  let tElab ← IO.monoMsNow
  unless cfg.quiet do
    IO.eprintln s!"[pstates] elaborated {cmds.size} commands in {tElab - t0} ms"
  let fm := FileMap.ofString input

  -- Phase 1: walk the trees, command by command.
  let mut raws : Array Raw := #[]
  let mut cmdInfo : Std.HashMap Nat (Span × String × String) := {}
  let mut ci := 0
  for c in cmds do
    let mut locals : Array Raw := #[]
    for t in c.trees do
      locals := collectSteps ci none 0 (-1) t locals
    if !locals.isEmpty then
      cmdInfo := cmdInfo.insert ci
        (commandSpan fm c.stx, c.stx.getKind.toString, commandLabel input c.stx)
      let base := raws.size
      for r in locals do
        raws := raws.push { r with parent := if r.parent < 0 then -1 else r.parent + base }
    ci := ci + 1
  let nRawSteps := raws.size

  -- Phase 2: drop the pure containers and reattach their children to the
  -- nearest surviving ancestor.  Parents always precede children in `raws`,
  -- so one forward pass suffices.
  let mut hasKids : Array Bool := Array.replicate raws.size false
  for r in raws do
    if r.parent ≥ 0 then hasKids := hasKids.set! r.parent.toNat true
  let mut alive : Array Bool := #[]
  let mut newParent : Array Int := #[]
  let mut ri := 0
  for r in raws do
    let (a, b) := (srcSpan? r.info.stx).getD (0, 0)
    let live :=
      cfg.keepAll ||
        !isContainer r.info.stx.getKind.toString (sliceOf input a b) hasKids[ri]!
    -- nearest surviving ancestor
    let mut p := r.parent
    while p ≥ 0 && !alive[p.toNat]! do
      p := newParent[p.toNat]!
    alive := alive.push live
    newParent := newParent.push p
    ri := ri + 1
  unless cfg.quiet do
    let nAlive := (alive.filter id).size
    IO.eprintln s!"[pstates] {nRawSteps} tactic nodes, {nAlive} after dropping containers"

  -- Phase 3: group into declarations and pretty-print, in one pass.
  let mut decls : Array Decl := #[]
  let mut pool : Pool := {}
  let mut steps : Array Step := #[]
  let mut oldToNew : Std.HashMap Nat Nat := {}
  let mut curKey : Option (Nat × String) := none
  let mut i := 0
  for r in raws do
    let dn := declNameOf r
    let key := (r.cmdIdx, dn)
    if curKey != some key then
      let (sp, kind, header) :=
        cmdInfo[r.cmdIdx]?.getD ({ line := 0, col := 0, endLine := 0, endCol := 0 }, "", "")
      decls := decls.push
        { name := dn, kind, header, line := sp.line, col := sp.col, endLine := sp.endLine }
      curKey := some key
    let di := decls.size - 1
    if alive[i]! && matchesPat cfg.declPat? dn && steps.size < cfg.maxSteps then
      let ctx := r.ctx
      let mut before : Array Nat := #[]
      for g in r.info.goalsBefore do
        if let some txt ← ppGoal? ctx r.info.mctxBefore cfg.width g then
          let (gi, p) := pool.intern g.name.toString txt
          pool := p
          before := before.push gi
      let mut after : Array Nat := #[]
      for g in r.info.goalsAfter do
        if let some txt ← ppGoal? ctx r.info.mctxAfter cfg.width g then
          let (gi, p) := pool.intern g.name.toString txt
          pool := p
          after := after.push gi
      let (a, b) := (srcSpan? r.info.stx).getD (0, 0)
      let sp := spanOf fm a b
      let newIdx := steps.size
      oldToNew := oldToNew.insert i newIdx
      let parent : Int :=
        if newParent[i]! < 0 then -1
        else match oldToNew[newParent[i]!.toNat]? with
             | some p => Int.ofNat p
             | none   => -1
      steps := steps.push
        { idx := newIdx, cmdIdx := r.cmdIdx, decl := di, depth := r.depth, parent
          line := sp.line, col := sp.col, endLine := sp.endLine, endCol := sp.endCol
          kind := r.info.stx.getKind.toString, elaborator := r.info.elaborator.toString
          text := sliceOf input a b, before, after }
    i := i + 1

  -- Depth relative to the *kept* parents: a filtered-out ancestor must not
  -- leave a hole in the indentation.
  let mut fixed : Array Step := #[]
  for s in steps do
    let d := if s.parent < 0 then 0 else (fixed[s.parent.toNat]!).depth + 1
    fixed := fixed.push { s with depth := d }
  steps := fixed

  -- Children lists, so the viewer can draw the tactic tree.
  let mut kids : Array (Array Nat) := Array.replicate steps.size #[]
  for s in steps do
    if s.parent ≥ 0 then
      let p := s.parent.toNat
      kids := kids.set! p (kids[p]!.push s.idx)
  steps := steps.map fun s => { s with children := kids[s.idx]! }

  -- Declaration summaries.
  let mut declArr := decls
  for s in steps do
    let d := declArr[s.decl]!
    declArr := declArr.set! s.decl
      { d with nSteps := d.nSteps + 1
               firstStep := if d.firstStep < 0 then Int.ofNat s.idx else d.firstStep
               lastStep := Int.ofNat s.idx }

  -- Phase 3: messages, anchored to the innermost step that contains them.
  let mut msgs : Array Msg := #[]
  let allMsgs : List Message := headerMsgs ++ (cmds.toList.flatMap (·.msgs))
  for m in allMsgs do
    let txt ← m.data.toString
    let endPos := m.endPos.getD m.pos
    let mut best : Int := -1
    let mut bestSpan : Nat := 0
    for s in steps do
      let afterStart := s.line < m.pos.line || (s.line == m.pos.line && s.col ≤ m.pos.column)
      let beforeEnd := m.pos.line < s.endLine || (m.pos.line == s.endLine && m.pos.column ≤ s.endCol)
      if afterStart && beforeEnd then
        let len := s.endLine - s.line
        if best < 0 || len ≤ bestSpan then
          best := Int.ofNat s.idx
          bestSpan := len
    msgs := msgs.push
      { line := m.pos.line, col := m.pos.column
        endLine := endPos.line, endCol := endPos.column
        severity := severityName m.severity, text := txt, step := best }

  -- Mark broken / sorried declarations.
  for m in msgs do
    for di in [0:declArr.size] do
      let d := declArr[di]!
      if d.line ≤ m.line && m.line ≤ d.endLine then
        if m.severity == "error" then
          declArr := declArr.set! di { d with broken := true }
        else if m.severity == "warning" && containsStr m.text "sorry" then
          declArr := declArr.set! di { d with sorried := true }

  let t1 ← IO.monoMsNow
  return {
    file := fileName
    declPat := cfg.declPat?.getD ""
    leanVersion := Lean.versionString
    elaborationOk := !msgs.any (·.severity == "error")
    elapsedMs := t1 - t0
    elabMs := tElab - t0
    nCommands := cmds.size
    nRawSteps
    goals := pool.goals
    decls := declArr
    steps
    msgs
    source := (input.splitOn "\n").toArray
  }

/-! ## JSON -/

private def jnat (n : Nat) : Json := Json.num (JsonNumber.fromNat n)
private def jint (n : Int) : Json := Json.num (JsonNumber.fromInt n)
private def jnats (a : Array Nat) : Json := Json.arr (a.map jnat)

def Goal.toJson (g : Goal) : Json :=
  Json.mkObj [("id", Json.str g.id), ("t", Json.str g.text)]

def Step.toJson (s : Step) : Json :=
  Json.mkObj [
    ("i", jnat s.idx), ("c", jnat s.cmdIdx), ("d", jnat s.decl),
    ("dep", jnat s.depth), ("par", jint s.parent), ("kids", jnats s.children),
    ("l", jnat s.line), ("co", jnat s.col), ("el", jnat s.endLine), ("ec", jnat s.endCol),
    ("k", Json.str s.kind), ("e", Json.str s.elaborator), ("tx", Json.str s.text),
    ("b", jnats s.before), ("a", jnats s.after)
  ]

def Decl.toJson (d : Decl) : Json :=
  Json.mkObj [
    ("name", Json.str d.name), ("kind", Json.str d.kind), ("header", Json.str d.header),
    ("l", jnat d.line), ("co", jnat d.col), ("el", jnat d.endLine),
    ("n", jnat d.nSteps), ("first", jint d.firstStep), ("last", jint d.lastStep),
    ("broken", Json.bool d.broken), ("sorried", Json.bool d.sorried)
  ]

def Msg.toJson (m : Msg) : Json :=
  Json.mkObj [
    ("l", jnat m.line), ("co", jnat m.col), ("el", jnat m.endLine), ("ec", jnat m.endCol),
    ("sev", Json.str m.severity), ("tx", Json.str m.text), ("step", jint m.step)
  ]

def Record.toJson (r : Record) : Json :=
  Json.mkObj [
    ("file", Json.str r.file),
    ("declPat", Json.str r.declPat),
    ("leanVersion", Json.str r.leanVersion),
    ("elaborationOk", Json.bool r.elaborationOk),
    ("elapsedMs", jnat r.elapsedMs),
    ("elabMs", jnat r.elabMs),
    ("nCommands", jnat r.nCommands),
    ("nRawSteps", jnat r.nRawSteps),
    ("goals", Json.arr (r.goals.map Goal.toJson)),
    ("decls", Json.arr (r.decls.map Decl.toJson)),
    ("steps", Json.arr (r.steps.map Step.toJson)),
    ("msgs", Json.arr (r.msgs.map Msg.toJson)),
    ("source", Json.arr (r.source.map Json.str))
  ]

end ProofStates
