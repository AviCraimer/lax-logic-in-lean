(* experiments.sml : reproduces the answers to the four open questions
   from the archaeology (see ../../docs/catpart-reference-build.md, S5).
   NEW code (2026), not part of the original sources.  Run with:
       /opt/local/bin/sml experiments.sml
   from inside this directory (it loads load_ref.sml itself). *)

use "load_ref.sml";

print "\n=== Experiment 1: the fully-flagged-category crash =============\n";
print "flagcrash_min.tsl: category 1 has exactly one choice, and it is\n";
print "[single]-flagged, so its *unflagged* choice list is empty.\n";
print "generate_unflagged's `first`/`extract` machinery assumes index 0\n";
print "exists in every category, so nth([],0) is reached:\n\n";
(process ("flagcrash_min.frm", "flagcrash_min.tsl");
 print "  UNEXPECTED: process succeeded (no crash)\n")
handle e => print ("  process raised: " ^ exnMessage e ^ "\n");

print "\n=== Experiment 2: reproducing the zero-byte test6.frm.frm ======\n";
print "test6.frm.frm (0 bytes, no matching .tsl) is exactly what you\n";
print "get from `process(root^\".frm\", root^\".tsl\")` when root is\n";
print "\"test6.frm\" instead of \"test6\" (i.e. the tool was once invoked\n";
print "as `catpart test6.frm` instead of `catpart test6`): open_out\n";
print "creates/truncates the output file first, then open_in fails on\n";
print "the nonexistent \"test6.frm.tsl\":\n\n";
(process ("test6.frm.frm.repro", "test6.frm.tsl");
 print "  UNEXPECTED: process succeeded (no crash)\n")
handle e => print ("  process raised: " ^ exnMessage e ^ "\n");

print "\n=== Experiment 3: bad.tsl vs find.tsl ===========================\n";
print "bad.tsl = find.tsl with two deliberate typos (\"Categoies\" for\n";
print "\"Categories\", and a doubled \"**\" before the first choice).\n";
print "Claim: the error-correcting parser repairs both, and the parse\n";
print "tree -- hence the generated frame file -- comes out identical\n";
print "to find.tsl's:\n\n";
process ("bad.repro.frm", "bad.tsl");
process ("find.repro.frm", "find.tsl");
if TextIO.inputAll (TextIO.openIn "bad.repro.frm")
   = TextIO.inputAll (TextIO.openIn "find.repro.frm")
then print "  CONFIRMED: bad.repro.frm and find.repro.frm are byte-identical.\n"
else print "  NOT identical (unexpected).\n";

print "\n=== Experiment 4: are [error] and [single] distinguishable? ====\n";
print "flag_error.tsl / flag_single.tsl are identical except that the\n";
print "flagged choice carries [error] in one and [single] in the other:\n\n";
process ("flag_error.repro.frm", "flag_error.tsl");
process ("flag_single.repro.frm", "flag_single.tsl");
if TextIO.inputAll (TextIO.openIn "flag_error.repro.frm")
   = TextIO.inputAll (TextIO.openIn "flag_single.repro.frm")
then print "  CONFIRMED: identical output -- the generator only tests\n\
           \  `maybe_flag = Some _` (is a choice flagged at all?); it\n\
           \  never inspects *which* flag.  [error] and [single] are\n\
           \  indistinguishable to the frame generator.\n"
else print "  DIFFER (unexpected: this would mean error/single ARE\n\
           \  distinguished somewhere).\n";

print "\nDone.\n";
