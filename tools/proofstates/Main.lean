/-
# `pstates` — the proof-state recorder command line

    lake exe pstates FILE.lean [options]

Records every tactic step in `FILE.lean` and writes a self-contained HTML
replay page (and, optionally, the raw JSON record).
-/
import tools.proofstates.Html

open Lean ProofStates

def usage : String :=
"pstates — record the proof states of a Lean file and emit a replay page

USAGE
  lake exe pstates FILE.lean [options]

OPTIONS
  --decl PAT        keep only steps in declarations whose name contains PAT
  --html PATH       write the self-contained HTML viewer here
                    (default: <file stem>[-<PAT>]-states.html in the cwd)
  --json PATH       also write the raw JSON record here
  --no-html         do not write HTML (use with --json)
  --template PATH   use this viewer template instead of the embedded copy
                    (tools/proofstates/viewer.html — edit it and re-run with
                    this flag, no Lean rebuild needed)
  --width N         pretty-printing width for goals (default 100)
  --max-steps N     stop after N recorded steps (default 200000)
  --keep-all        keep nested tactic nodes that share a source span with
                    their parent (by/tacticSeq chains, macro expansions)
  --quiet           no progress output on stderr
  -h, --help        this message

EXIT STATUS
  0 always, when a record was produced.  A file that fails to elaborate is not
  an error here: the partial record is exactly what is wanted in that case, and
  the page marks where elaboration broke.
"

structure Args where
  cfg       : Config
  noHtml    : Bool := false
  template? : Option System.FilePath := none

partial def parseArgs (as : List String) (acc : Args) : Except String Args :=
  match as with
  | [] => .ok acc
  | "--decl" :: v :: rest    => parseArgs rest { acc with cfg := { acc.cfg with declPat? := some v } }
  | "--html" :: v :: rest    => parseArgs rest { acc with cfg := { acc.cfg with htmlOut? := some v } }
  | "--json" :: v :: rest    => parseArgs rest { acc with cfg := { acc.cfg with jsonOut? := some v } }
  | "--width" :: v :: rest   =>
    match v.toNat? with
    | some n => parseArgs rest { acc with cfg := { acc.cfg with width := n } }
    | none   => .error s!"--width expects a number, got '{v}'"
  | "--max-steps" :: v :: rest =>
    match v.toNat? with
    | some n => parseArgs rest { acc with cfg := { acc.cfg with maxSteps := n } }
    | none   => .error s!"--max-steps expects a number, got '{v}'"
  | "--template" :: v :: rest => parseArgs rest { acc with template? := some v }
  | "--no-html" :: rest      => parseArgs rest { acc with noHtml := true }
  | "--keep-all" :: rest     => parseArgs rest { acc with cfg := { acc.cfg with keepAll := true } }
  | "--quiet" :: rest        => parseArgs rest { acc with cfg := { acc.cfg with quiet := true } }
  | a :: _ =>
    if a.startsWith "-" then .error s!"unknown option '{a}'"
    else .error s!"unexpected extra argument '{a}'"

def sanitise (s : String) : String :=
  String.ofList (s.toList.map fun c =>
    if c.isAlphanum || c == '-' || c == '_' then c else '_')

/-- `unsafe` because `Lean.enableInitializersExecution` is: importing modules
with `loadExts := true` runs their `initialize` blocks through the interpreter,
which is exactly what elaborating an arbitrary file needs (tactics, notations
and elaborators all arrive that way).  Without it `processHeader` fails with
"`enableInitializersExecution` must be run before calling `importModules
(loadExts := true)`". -/
unsafe def main (argv : List String) : IO UInt32 := do
  Lean.enableInitializersExecution
  match argv with
  | [] | ["-h"] | ["--help"] =>
    IO.println usage
    return 0
  | file :: rest =>
    if file.startsWith "-" then
      IO.eprintln usage
      return 1
    let cfg0 : Config := { file := file }
    match parseArgs rest { cfg := cfg0 } with
    | .error e =>
      IO.eprintln s!"pstates: {e}\n"
      IO.eprintln usage
      return 1
    | .ok args =>
      unless (← System.FilePath.pathExists args.cfg.file) do
        IO.eprintln s!"pstates: no such file: {args.cfg.file}"
        return 1
      Lean.initSearchPath (← Lean.findSysroot)
      let r ← ProofStates.record args.cfg
      let stem := (args.cfg.file.fileStem).getD "record"
      let suffix := match args.cfg.declPat? with
        | some p => "-" ++ sanitise p
        | none   => ""
      if let some p := args.cfg.jsonOut? then
        IO.FS.writeFile p (Json.pretty r.toJson)
        unless args.cfg.quiet do IO.eprintln s!"[pstates] wrote {p}"
      unless args.noHtml do
        let out := args.cfg.htmlOut?.getD (stem ++ suffix ++ "-states.html")
        let tpl ← match args.template? with
          | some p => IO.FS.readFile p
          | none   => pure viewerTemplate
        let html := renderHtmlWith tpl r
        IO.FS.writeFile out html
        unless args.cfg.quiet do
          IO.eprintln s!"[pstates] wrote {out} ({html.utf8ByteSize / 1024} KiB)"
      unless args.cfg.quiet do
        let errs := r.msgs.filter (·.severity == "error")
        IO.eprintln s!"[pstates] {r.steps.size} steps in {r.decls.size} declarations, \
          {r.goals.size} distinct goals, {errs.size} errors, {r.elapsedMs} ms total"
        unless r.elaborationOk do
          IO.eprintln "[pstates] the file did NOT elaborate cleanly; the record is partial \
            and the page marks the broken declarations"
      return 0
