(* cp_make.sml: load the code for catpart and make an executable binary *)

fun in_line f =
    let fun loop result =
	let val c = input(f,1)
	in if String.size c = 0 orelse c = "\n" then
	      String.implode (rev result)
	   else loop (c::result)
	end
    in loop []
    end;

print "Making catpart... \n\n";

System.Control.primaryPrompt := "catpart_make > ";

val version_no = (print "version number = "; in_line std_in);

val catpart_release = "catpart"^version_no;

(* load main code *)
use ("/home/matt/ml/catpart/"^catpart_release^"_load_most.sml");

(* set up the initial message consisting of a (lousy) banner and a welcome
   message *)

val catpart_banner =
    "\n C A T P A R T  T O O L   f o r  \n\n\
      \ C A T E G O R Y   P A R T I T I O N   T E S T I N G \n\n"

val shell = System.system;
val compilation_date =
if shell "date > today"=0 then 
    let val today = open_in "today"
	val date = in_line today 
    in  (close_in today; shell "rm -f today"; date)
    end
else (System.Print.say"Sorry, cannot write date\n"; "unknown");

val catpart_welcome_string =
    "\n\n This is version "^version_no^" of the \
     \test generation tool catpart \n\n\
     \ This version was compiled on: "^compilation_date^"\n\n";

val catpart_tail_string =
    "\n Enjoy and send suggestions for improvement etc. to matt@shef.ac.uk\n\n"

val catpart_start_string =
 catpart_banner^catpart_welcome_string;

    print ("Start string:\n"^catpart_start_string);

fun catpart(argv, env) =
    (print catpart_start_string;
     if length argv <> 2 then
     String.print" Syntax is \"catpart myfile\"\n\n"
     else
     (let val root = hd (tl argv)
      in
	 process(root^".frm", root^".tsl");
	 String.print(" File "^root^".tsl processed\n\n")
      end));

val proceed = (print "\nProceed to write binary? (y/n): "; in_line std_in);

if (proceed = "y" orelse proceed = "Y")
    then
      (String.print
       ("\nWriting version "^catpart_release^" of the catpart program\n");
       (* export the program and the initial message *)
       IO.exportFn(catpart_release,catpart);
        String.print catpart_start_string)
     else (System.Control.primaryPrompt := (catpart_release^"? > ");
           System.Control.secondaryPrompt := "more?  ";
	   String.print("\nOk, make halted.\n\n"));


