import Lean

/-!
# `#guard_msgs_show` — check a command's output *and* leave it on screen

`#guard_msgs` compares a command's messages against the docstring above it and,
when they agree, **deletes them**: `elabGuardMsgs` puts only the *passed-through*
messages back on the log, and a checked message is not one of those.  That is
right for a test file, and wrong for a demonstration file, where the output is
the thing the reader came to see.  A file whose every command is wrapped in
`#guard_msgs` produces no info-view output at all: the editor shows the one
message the file does emit, which is whatever unguarded command comes last.

`#guard_msgs_show` is `#guard_msgs` with the deletion undone.  Written

```lean
/--
info: 3
-/
#guard_msgs_show in
#eval 1 + 2
```

it checks the output exactly as `#guard_msgs` does (the build fails if the
command stops printing `3`), and then re-emits the checked text as an
information message on the command, so that putting the cursor on the `#eval`
shows `3` in the info view.

What is re-emitted is the docstring, which `#guard_msgs` has just certified
against the real output (up to the newline-for-space normalisation that
`#guard_msgs` applies by default).  Nothing is displayed that has not been
checked: on a mismatch `#guard_msgs` reports the error and this command
re-emits nothing.

Used by `LaxLogic/PLLSearchDemo.lean`, whose whole purpose is to be stepped
through in the info view.
-/

namespace LaxLogic

open Lean Elab Command

/-- Drop the leading severity marker that `#guard_msgs` docstrings carry
(`info:`, `warning:`, `error:`, `trace:`), together with the single space
after it, leaving the message text itself. -/
private def stripSeverity (s : String) : String :=
  let t := s.trimAscii.copy
  let markers := ["info:", "warning:", "error:", "trace:"]
  match markers.find? (fun p => p.isPrefixOf t) with
  | some pre => (t.drop pre.length).trimAscii.copy
  | none     => t

/--
`#guard_msgs_show in cmd` — run `cmd`, check its messages against the
docstring exactly as `#guard_msgs` does, and then **show** the checked text in
the info view instead of swallowing it.

```lean
/--
info: 3
-/
#guard_msgs_show in
#eval 1 + 2
```

Use it in a file meant to be read and stepped through: the reader sees the
output on the command, and the build still fails if the output changes.  For a
pure test file, where nothing is meant to be displayed, use `#guard_msgs`.
-/
elab doc:docComment "#guard_msgs_show " "in " cmd:command : command => do
  elabCommandTopLevel (← `(command| $doc:docComment #guard_msgs in $cmd))
  unless (← get).messages.hasErrors do
    logInfoAt cmd (stripSeverity (← getDocStringText doc))

end LaxLogic

/-! ## Smoke tests -/

section
open LaxLogic

-- The wrapped command's output is checked …
/--
info: 3
-/
#guard_msgs_show in
#eval 1 + 2

-- … and then re-emitted, so `#guard_msgs` around the *whole* wrapper sees it
-- again.  This is the property the demo file relies on, stated as a test.
/--
info: 3
-/
#guard_msgs in
/--
info: 3
-/
#guard_msgs_show in
#eval 1 + 2

end
