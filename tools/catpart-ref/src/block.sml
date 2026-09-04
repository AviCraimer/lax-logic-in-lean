(* pretty.sml : routines for printing *)

(* Larry Paulson's pretty printing routines augmented with newlines *)

signature PRETTY =
  sig
  type T
  val blo : int * T list -> T
  val str : string -> T
  val brk : int -> T
  val nl  : T
  val pr  : outstream * T * int -> unit
  end;

functor PrettyFun () : PRETTY =
  struct
  datatype T = Block of T list * int * int
	     | String of string
	     | Break of int
	     | Newline;

fun breakdist(Block(_,_,len)::es, after) = len + breakdist(es,after)
  | breakdist(String s::es, after) = size s + breakdist(es,after)
  | breakdist(Break _::es, after) = 0
  | breakdist(Newline::es, after) = breakdist(es, after)
  | breakdist([], after) = after;

fun pr (os, e, margin) =
  let val space = ref margin
      fun blanks 0 = ()
	| blanks n = (output(os," "); space := !space -1;
		      blanks(n-1))
      fun newline () = (output(os,"\n"); space := margin)

      fun printing ([],_,_) = ()
	| printing (e::es, blockspace, after) =
	  (case e of
		Block(bes,indent,len) =>
		  printing(bes, !space-indent, breakdist(es,after))
	      | String s => (output(os,s); space := !space - size s)
	      | Break len =>
		  if len + breakdist(es,after) <= !space
		  then blanks len
		  else (newline(); blanks(margin-blockspace))
              | Newline =>  (newline(); blanks(margin-blockspace));
	    printing (es, blockspace, after))
    in printing([e], margin, 0); newline() end;

fun length (Block(_,_,len)) = len
  | length (String s) = size s
  | length (Break len) = len
  | length Newline = 0;

val str = String and brk = Break and nl = Newline;

fun blo (indent, es) =
  let fun sum([], k) = k
	| sum(e::es, k) = sum(es, length e + k)
  in Block(es, indent, sum(es,0)) end;

end;


(* pervasives: I decided not to wrap these up in a structure, because
   there are enough structures around already *)

fun digit i = chr(i + ord"0");

fun string_of_int n =
  let fun digits 0 = []
        | digits n = (digits (n div 10)) @ [digit (n mod 10)]
  in if n = 0 then "0" else implode (digits n)
  end;

fun string_of_bool b = if b then "tt" else "ff";

