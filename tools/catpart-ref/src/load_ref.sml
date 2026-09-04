(* load_ref.sml : reference-implementation loader for catpart, version
   0.2, under SML/NJ 110.99.9 (MacPorts build, November 2025).

   This is NEW code (2026), not part of the original 1990s sources.  It
   replaces catpart0.2_load_most.sml, which cannot be used unmodified
   because it (a) references the two shared files one directory up by
   dead absolute paths ("/home/matt/ml/permlist.sml",
   "/home/matt/ml/interface.sml") instead of relative ones, and
   (b) predates ML-Yacc's runtime support library being something you
   have to load explicitly via CM (in the 1990s, `base.sml` was `use`d
   directly; the installed SML/NJ 110.99.9 distribution on this machine
   ships ml-yacc-lib only as a precompiled CM library, with no source
   files to `use`).

   Run from inside this directory:
       /opt/local/bin/sml load_ref.sml
*)

(* Pull in ML-Yacc's runtime support library (LrParser, Join, Stream,
   TOKEN, LEXER, PARSER_DATA, ... signatures and structures).  This is
   the modern replacement for `use "base.sml"`. *)
CM.make "$/ml-yacc-lib.cm";

use "permlist2.sml";
use "pretty2.sml";

(* compat.sml must load after pretty2.sml (which does `open TextIO`,
   binding the 1-argument TextIO.input to the bare name `input`) and
   before every file below that calls the old 2-argument `input`. *)
use "compat.sml";

use "catpart_absyn_val.sml";

use "catpart_val.grm.sig";
use "catpart_val.grm.sml";

use "interface.sml";
use "catpart0.2.lex.sml";

use "catpart_parse_val.sml";
use "catpart_link.sml";

use "catpart0.2_frame.sml";

print "\ncatpart 0.2 reference build loaded OK.\n";
