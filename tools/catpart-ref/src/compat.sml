(* compat.sml : compatibility shim for catpart, a mid-1990s Standard ML
   program written against the pre-1997 SML/NJ "old I/O" library and a
   handful of old SML/NJ Library list functions that the Standard Basis
   Library (as shipped with SML/NJ 110.99.9) no longer provides at top
   level.

   This file is NOT part of the original 1990s catpart sources.  It is
   new code, added in 2026 purely to re-bind the old identifiers to their
   modern equivalents, so that the ORIGINAL catpart source files
   (catpart_parse_val.sml, catpart0.2_frame.sml, interface.sml, ...) can
   be loaded completely unmodified.

   It must be `use`d after pretty2.sml (which does `open TextIO`, and so
   would otherwise leave the 1-argument TextIO.input bound to the bare
   name `input`) and before catpart_parse_val.sml / catpart0.2_frame.sml
   (which call the old 2-argument `input`).  See BUILD.md. *)

(* --- old-style textual I/O (pre-Basis-Library SML/NJ) --- *)

val std_out : TextIO.outstream = TextIO.stdOut
val std_in  : TextIO.instream  = TextIO.stdIn

fun open_in  (name : string) : TextIO.instream  = TextIO.openIn name
fun open_out (name : string) : TextIO.outstream = TextIO.openOut name

fun close_in  (dev : TextIO.instream)  : unit = TextIO.closeIn dev
fun close_out (dev : TextIO.outstream) : unit = TextIO.closeOut dev

fun output (os : TextIO.outstream, s : string) : unit = TextIO.output (os, s)

(* old `input (stream, n)` returned a string of up to n characters,
   the empty string at end of file; TextIO.inputN has the same contract. *)
fun input (dev : TextIO.instream, n : int) : string = TextIO.inputN (dev, n)

(* old `input_line stream` returned "" at end of file rather than
   raising or returning NONE. *)
fun input_line (dev : TextIO.instream) : string =
    case TextIO.inputLine dev of NONE => "" | SOME s => s

(* old `makestring` was a polymorphic-via-overloading primitive; catpart
   only ever applies it to an int (interface.sml, error-position
   reporting), so a monomorphic replacement is all that's needed. *)
fun makestring (n : int) : string = Int.toString n

(* --- old SML/NJ Library list functions --- *)

(* old `nth (list, n)` : 0-based, same order/semantics as List.nth. *)
fun nth (l : 'a list, n : int) : 'a = List.nth (l, n)

(* old `fold f list start` = f(x1, f(x2, ..., f(xn, start))), i.e.
   exactly List.foldr with the function and the initial value swapped. *)
fun fold (f : 'a * 'b -> 'b) (l : 'a list) (e : 'b) : 'b = List.foldr f e l
