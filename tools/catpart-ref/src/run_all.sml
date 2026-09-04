(* run_all.sml : batch driver, NOT part of the original sources.
   Runs catpart's `process` over every .tsl spec in this directory,
   writing output to <name>.out.frm so the preserved 1990s <name>.frm
   files are never touched.  Prints PASS/FAIL/EXCEPTION per file.

   Self-contained: run with `/opt/local/bin/sml run_all.sml` from
   inside this directory. *)

use "load_ref.sml";

val specs =
    ["bad", "comment", "comment2", "fileinfo", "find",
     "find_route", "find_route_altered", "find_routes",
     "harrison", "mid_test", "test", "test2", "test3", "test5", "test6"];

fun run name =
    (process (name ^ ".out.frm", name ^ ".tsl");
     print ("OK    " ^ name ^ ".tsl -> " ^ name ^ ".out.frm\n"))
    handle e =>
           print ("FAIL  " ^ name ^ ".tsl : " ^ exnMessage e ^ "\n");

val _ = app run specs;
print "\nDone.\n";
