(* catpart0.1_frame.sml version 0.1 of
   the main processing functions for the catpart testing tool *)

open Parse
    
open Absyn

open PermList

nonfix |-;
nonfix |=;
nonfix /\;
nonfix \/;
fun /\ (b1, b2) = b1 andalso b2;
fun \/ (b1, b2) = b1 orelse b2;

exception Option

fun get_option (Some p) = p
  | get_option None = raise Option

fun partition p [] = ([], [])
  | partition p (h::t) =
    let val (ps, non_ps) = partition p t
    in if (p h)
	   then (h::ps, non_ps)
       else (ps, h::non_ps)
    end

fun group [] = ([], [])
  | group ((h1, h2)::t) =
    let val (t1, t2) = group t
    in
	(h1::t1, h2::t2)
    end

fun partition_spec
    (F {fun_letter=c, fun_name=f, categ_specs=cs})
    = let
	  fun partition_flags
	      (Cat{categ_no=cno, categ_name=cna, choices=chs})
	      =
	      let
		  fun is_flagged
		      (Ch{ch_name=_,
			  maybe_modifiers=(M{maybe_cond=_,
					     maybe_properties=_,
					     maybe_flag=Some _})})
		      = true
		  (* there is a flag on the choice *)
		    | is_flagged _ = false
		  (* there is no flag on the choice *)
		  val (flagged, unflagged) =
		      partition is_flagged chs
	      in
		  (Cat{categ_no=cno, categ_name=cna, choices=flagged},
		   Cat{categ_no=cno, categ_name=cna, choices=unflagged})
	      end
	  (* partition the choices of a category into flagged and unflagged *)
	
	  val (flagged_cs, unflagged_cs)
	      = group (map partition_flags cs)
	  (* partition each choice in each category
	     into flagged and unflagged choices, then group the flagged
             and unflagged choices together *) 
      in
	  (F{fun_letter=c, fun_name=f^"_flagged", categ_specs=flagged_cs},
	   F{fun_letter=c, fun_name=f^"_unflagged", categ_specs=unflagged_cs})
      end

fun make_lists
    (F {fun_letter=_, fun_name=_, categ_specs=cs})
    = let
	  fun ord 0 = []
	  | ord n = let val n_ = n - 1 in n_ :: (ord n_) end
	  fun make_ch_list (Cat{categ_no=_, categ_name=_, choices=chs})
	      = ord (length chs)
    in
	  map make_ch_list cs
    end
(* make a list of lists of numbers (representing choices) from a test 
   spec. *)  

fun make_bases
    (F {fun_letter=_, fun_name=_, categ_specs=cs})
    = let
	  fun make_ch_list (Cat{categ_no=_, categ_name=_, choices=chs})
	      = length chs
    in
	  map make_ch_list cs
    end
(* make a list of lengths (representing no.s of choices) from a test 
   spec. *)  

fun join l = fold (op @) l []
    
fun pS(l,m) = join (map (fn p => map (fn c => c::p) l) m)

fun product l = fold pS l [[]]

(* extract the test frame encoded by the list l from a test spec. *)
exception Combine
fun combine
    (F{fun_letter=_, fun_name=_, categ_specs=cs})
    l =
    let fun comb [] [] = []
	  | comb
	    ((Cat{categ_no=cno, categ_name=cna, choices=chs})::cats)
	    (n::t) =
	    {categ_no=cno, categ_name=cna, choice=nth(chs, n)} :: (comb cats t)
	  | comb _ _ = raise Combine 
    in
	comb cs l
    end

(* functions used in the calculation of validity of a combination of 
   choices *) 

fun properties 
    (Ch{ch_name=_,
	maybe_modifiers=(M{maybe_cond=_,
			   maybe_properties=None,
			   maybe_flag=_})}) = []
  | properties
    (Ch{ch_name=_,
	maybe_modifiers=(M{maybe_cond=_,
			   maybe_properties=Some props,
			   maybe_flag=_})}) = props;
    
fun cond
    (Ch{ch_name=_,
	maybe_modifiers=(M{maybe_cond=c,
			   maybe_properties=_,
			   maybe_flag=_})}) = c;
  
exception Setup;
fun setup_cond
    0
    ((Ch{ch_name=_,
	 maybe_modifiers=(M{maybe_cond=c,
			    maybe_properties=props,
			    maybe_flag=_})})::t)
    = (join(map properties t), c)
  | setup_cond
    n
    (ch::t)
    =
    if n > 0 then
	let val (props, c) = setup_cond (n-1) t
	in
	    ((properties ch) @ props, c)
	end
    else raise Setup
  | setup_cond _ _ = raise Setup;

infix /\;
infix \/;

fun |-  (V, Prop s) = member s V
  | |-  (V, Binary(Or,  c1, c2)) =
        let val b1 = (|- (V, c1))
	    val b2 = (|- (V, c2))
	in b1 \/ b2
	end
  | |-  (V, Binary(And, c1, c2)) =
        let val b1 = (|- (V, c1))
	    val b2 = (|- (V, c2))
	in b1 andalso b2  (* replacing andalso with /\ gives _strange_
			     syntax error! *)
	end
  | |-  (V, Not c) = not(|- (V, c));

fun |= (V, Some c) = |- (V, c)
  | |= (V, None)   = true;

fun valid comb = 
    let
	fun ord 0 = []
	  | ord n = let val n_ = n - 1 in n_ :: (ord n_) end
	val n = length comb
	val l = ord n
    in
	fold (op /\) (map (fn m => |= (setup_cond m comb)) l) true
    end

(* the following are more in keeping with conventional notation:   *)
infix |-;
infix |=;

fun mu (n,m) p =
    if n < m then
	if p n then n else mu (n+1,m) p
    else m

fun next bases _ []     = []
  | next bases m (n::t) =
    let val c = uth(bases, m)  (* or should it be nth ? *)
    in
	if n+1 < c then (n+1)::t
	else 0::(next bases (m-1) t)
    end;

exception Extract
fun extract
    (F{fun_letter=_, fun_name=_, categ_specs=cs})
    l =
    let fun comb [] [] = []
	  | comb
	    ((Cat{categ_no=cno, categ_name=cna, choices=chs})::cats)
	    (n::t) =
	    (nth(chs, n)) :: (comb cats t)
	  | comb _ _ = raise Extract 
    in
	comb cs l
    end
(* extract the choices encoded by the list l from a test spec. *)
(* we end up with a list of choices *)

fun ord 0 = []
  | ord n = let val n_ = n - 1 in n_ :: (ord n_) end

fun filter p [] = []
  | filter p (h::t) = if p h then h::(filter p t) else filter p t;

exception First;

(* first n is the lexicographically first word of length n *)
fun first 0 = []
  | first n = if n > 0 then 0::(first (n-1)) else raise First;

fun iterate cond f from =
    if cond from then from else iterate cond f (f from)
    handle Extract => from; 
 
fun print_comb os [] = (output(os,""))
  | print_comb os ({categ_no=_,
		   categ_name=cna,
		   choice=Ch{ch_name=ch,
			     maybe_modifiers=_}}::chs) =
    (output(os, (cna^" = "^ch^"\n"));
     print_comb os chs);
    
fun print_combs os [] _ = output(os,"")
  | print_combs os ([]::t) _ = output(os,"empty category!\n")
  | print_combs os (chs::t) n =
    (output(os, "\n"^(string_of_int n)^"\n");
     print_comb os chs; output(os,"\n");
     print_combs os t (n+1));

(* the main loop *)

exception None_valid;

(* generate the list of unflagged frames for a given tsl spec *)
fun generate_unflagged tsl =
    let val bases = make_bases tsl
	(* make bases for the tsl spec *)
	val m = length bases
	(* this means there are m categories in the spec *)
	val start = first m
	(* we start with the first combination *)
	val test = valid o (extract tsl)
	(* test for validity of the combination *)
	fun step l =
	    let
		val l' = next bases (m - 1) l
	    in
		if l' = start then []
		else if test l' then l' else step l'
	    end
	(* step chooses the next valid combination *)
	val res =
	    iterate
	    (fn (l, a) => null l)
	    (fn (l, a) => let val new = step l in (new, (new::a)) end)
	    (start, if test start then [start] else [])
	(* res contains a list of valid combinations *)
    in map (combine tsl) (tl (#2 res))
       (* extract the list from res and reconstitute the syntax *)
    end;

(* massage the flagged specification into a form suitable for output using
   print_combs *)
fun flagged_combs 
    (F {fun_letter=c, fun_name=f, categ_specs=cs}) =
    let fun isolate [] = []
	  | isolate
	    ((Cat{categ_no=cno, categ_name=cna, choices=chs})::cats) =
	    (map (fn c => [{categ_no=cno, categ_name=cna, choice=c}]) chs) @
	    (isolate cats)
    in isolate cs
    end;

(* generate the output for a parsed tsl *)
fun generate os tsl =
    let val (tsl_f, tsl_u) = partition_spec tsl
	val frames_f = flagged_combs tsl_f
	val frames_u = generate_unflagged tsl_u
    in print_combs os (frames_f @ frames_u) 1
    end;

fun process(out_file, in_file) =
    let val os = open_out out_file
	val maybe_tsl = file_parse in_file
    in (case maybe_tsl of Some tsl => generate os tsl
			| None => output(os, "Empty specification");
	close_out os)
    end;

(*

(* testing, testing, testing,... *)
val mb1 = make_bases tsl1;
    
val test_next = next mb1 0;

val tsl0 = get_option(file_parse "test.tsl");

val (tsl0_f, tsl0_u) = partition_spec tsl0;
val tsl0_u_l = make_lists tsl0_u;
val tsl0_u_combs = product tsl0_u_l;
	print_combs std_out (map (combine tsl0_u) tsl0_u_combs) 1;

val tsl1 = get_option(file_parse "mid_test.tsl");

val (tsl1_f, tsl1_u) = partition_spec tsl1;
val tsl1_u_l = make_lists tsl1_u;
val tsl1_u_combs = product tsl1_u_l;
	print_combs std_out (map (combine tsl1_u) tsl1_u_combs) 1;
val good_tsl1_u_combs
    = filter (fn comb => valid (extract tsl1 comb)) tsl1_u_combs;
	print_combs std_out (map (combine tsl1_u) good_tsl1_u_combs) 1;
val tsl1_f_combs = flagged_combs tsl1_f;

val tsl1_combs = product (make_lists tsl1);
filter (fn comb => valid (extract tsl1 comb)) tsl1_combs;

(* larger tests: uncomment to load ... *)
(*
val tsl2 = get_option(file_parse "find.tsl");

val (tsl2_f, tsl2_u) = partition_spec tsl2;
val tsl2_u_l = make_lists tsl2_u;
val tsl2_u_combs = product tsl2_u_l;
    map (combine tsl2_u) tsl2_u_combs;

val tsl3 = get_option(file_parse "fileinfo.tsl");

val (tsl3_f, tsl3_u) = partition_spec tsl3;
val tsl3_u_l = make_lists tsl3_u;
val tsl3_u_combs = product tsl3_u_l;
    map (combine tsl3_u) tsl3_u_combs;
*)




   
(* quarry:

fun odd n = (n = 2*(n div 2) + 1);   
    
    iterate
    (fn comb => valid (extract tsl1 comb))
    (step tsl1)
    (first 3);
    
val test_next' = next [1,2,3] 2;

(* this loops :
    iterate
    (fn (x,l) => x=[0,0,0])
    (fn (x,l) => let val nx = test_next' x in (nx, nx::l) end)
    ([1,1,1],[[]]); 
*)


fun and_tri True  v     = v
  | and_tri False _     = False
  | and_tri Maybe False = False
  | and_tri Maybe _     = Maybe

fun /\ (v1, v2) = and_tri v1 v2;
infix /\;

datatype Tri = True | False | Maybe;

fun |- (V, Prop s) = if member s V then True else Maybe
  | |- (V, Binary(Or, c1, c2)) =
     (case |- (V, c1) of
	  True  => True
	| False => |- (V, c2)
	| Maybe => (case |- (V, c2) of
			True => True
		      | _    => Maybe))
  | |- (V, Binary(And, c1, c2)) =
     (case |- (V, c1) of
	  True  => |- (V, c2)
	| False => False
	| Maybe => (case |- (V, c2) of
			False => False
		      | _     => Maybe))
  | |- (V, Not c) =
     (case |- (V, c) of
	  True  => False
	| False => True
	| Maybe => Maybe);
(* True means "this constraint is definitely satisfied with respect to 
   this list of properties or any extension of this list".
   False means "this constraint is definitely unsatisfiable with respect to
   this list of properties or any extension of this list".
   Maybe means "this constraint is not satisfied with respect to this list
   of properties, but could become satisfied if the list were extended". 
 *)

(*
fun extract
    (F{fun_letter=_, fun_name=_, param_specs=ps, env_specs=es})
    l =
    let val cats = rev(ps @ es)
	fun comb _ [] = []
	  | comb
	    ((Cat{categ_no=cno, categ_name=cna, choices=cs})::chs)
	    (n::t) =
	    (nth(cs, n)) :: (comb chs t)
	  | comb _ _ = raise Extract 
    in
	rev(comb cats (rev l))
    end
(* extract the partial choices encoded by the list l from a test spec. *)
*)

(*
fun check comb = (* intermediate test of validity *)
    let
	val n = length comb
	val l = ord n
    in
	fold
	(op /\)
	(map (fn m => (|= (setup_cond m comb) <> Firm false)) l)
	true
    end

fun valid comb = (* final test of validity *)
    let
	val n = length comb
	val l = ord n
    in
	fold
	(op /\)
	(map (fn m => eotr (|= (setup_cond m comb))) l)
	true
    end

*)

(* datatype Quad = Firm of bool | Weak of bool (* uncomment to recompile *) 

fun |- (V, Prop s) = if member s V then Firm true else Weak false
  | |- (V, Binary(Or, c1, c2)) =
     (case |- (V, c1) of
	  Firm true  => Firm true
	| Firm false => |- (V, c2)
	| Weak b1    => (case |- (V, c2) of
			     Firm true  => Firm true
			   | Firm false => Weak b1
			   | Weak b2    => Weak (b1 orelse b2)))
  | |- (V, Binary(And, c1, c2)) =
      (case |- (V, c1) of
	  Firm false  => Firm false
	| Firm true => |- (V, c2)
	| Weak b1    => (case |- (V, c2) of
			      Firm true  => Weak b1
			    | Firm false => Firm false
			    | Weak b2    => Weak (b1 andalso b2)))
  | |- (V, Not c) =
     (case |- (V, c) of
	  Firm b => Firm (not b)
	| Weak b => Weak (not b));
(* Firm b means that the constraint definitely has the value b and that
   this cannot be altered by adding extra properties.
   Weak b means that the constraint currently has the value b but that this
   could change if extra properties were added.  We need a function to
   apply when there are no more properties to add, which we call "eotr": *)

fun eotr (Firm b) = b
  | eotr (Weak b) = b;
(* eotr = "end of the road";
   if there are no more properties to be added then the weaks become firms
   and there is no need to distinguish them any more *)  

fun |= (V, Some c) = |- (V, c)
  | |= (V, None)   = Firm true;

fun next bases q m []     = (m, [])
  (* the integer returned is the place value of the list found *)
  (* the list is the next partial list satisfying q *)
  | next bases q m (n::t) =
    let val c = nth(bases, m) (* c is the current base *)
	val k = mu (n+1,c) (fn k => q (k::t))
    in (* k is the least value between n+1 and c such that q holds of k::t *)
	if k < c then (m, k::t)   (* next list satisfying q found *)
	else next bases q (m+1) t (* backtrack and try again *)
    end;

fun extend bases q m p [] = []
	(* has to terminate if next returns [] *)
  | extend bases q m p (n::t) =
    if m=0 then (* cannot extend *)
	if p (n::t) then n::t (* apply final test *)
	else let val (m', e) = next bases q m (n::t)
	     in extend bases q m' p e
	     end
        (* find, then extend next list satisfying intermediate test *)
    else (* can extend *)
	extend bases q (m-1) p (0::n::t);
	
fun ext l =
    let val p = fn x => true; val q = p;
	val bases = [1,2,3]
    in let val (m, e) = next bases q 0 l in
	extend bases q m p e
       end
    end;

fun ext l =
    let fun q x = true; fun p l = odd (hd (tl (tl l)));
	val bases = [1,2,3]
    in let val (m, e) = next bases q 0 l in
	extend bases q m p e
       end
    end;

iterate
    (fn comb => valid (extract tsl2 comb))
    (step tsl2)
    (first 7);
   


val tsl3 = get_option(file_parse"test.tsl");
val tsl3_l = make_lists tsl3;
val tsl3_combs = product tsl3_l;
    filter (fn comb => valid (extract tsl3 comb)) tsl3_combs;

    extract tsl3 [2,0,0,0,1];
    
    map (fn c => setup_cond c (extract tsl3 [2,0,0,0,1])) [0,1,2,3,4];

    map (op |=) it;

    map (eotr o (op |=)) it;
    
    
val tsl1 = get_option(file_parse "fileinfo.tsl");
val (tsl1_f, tsl1_u) = partition_spec tsl1;

val test1_u = testgen tsl1_u;
    
val combs1_u = map (combine tsl1_u) (tl(#2(test1_u)));
 
val (tsl2_f, tsl2_u) = partition_spec tsl2;

val test2_u = testgen tsl2_u;
    
val combs2_u = map (combine tsl2_u) (tl(#2(test2_u)));
    

    (* print_combs combs1_u 1; (* this is a long one! *) *)
    print_combs combs2_u 1;
   

*)
(*
fun testgen tsl =
    let val bases = make_bases tsl;
	val start = first (length bases);
	fun step l =
	    let
		val chk = check o (extract tsl)
		val final = valid o (extract tsl)
		val (m, e) = next bases chk 0 l
	    in
		extend bases chk m final e
	    end
    in
	iterate
	(fn (l, a) => null l)
	(fn (l, a) =>
	 let val nl = step l in (nl, (nl::a)) end)
	(start, [])
    end;
*)
(*
fun step tsl start
    =
    let
	val m = length(make_bases tsl)
    in
	next
	(make_bases tsl)
	(fn comb => valid (extract tsl comb) <> False)
	(m - 1)
	start
    end;
*)
(*
fun print_comb os [] = (String.print"")
  | print_comb ({categ_no=_,
		   categ_name=cna,
		   choice=Ch{ch_name=ch,
			     maybe_modifiers=_}}::chs) =
    (String.print (cna^" = "^ch^"\n");
     print_comb chs);
    
fun print_combs [] _ = (String.print "")
  | print_combs ([]::t) _ = (String.print "empty category!\n")
  | print_combs (chs::t) n =
    (String.print"\n"; print n; String.print"\n";
     print_comb chs; String.print"\n";
     print_combs t (n+1));
*)
(*
fun next bases q _ []     = []
  | next bases q m (n::t) =
    let val c = uth(bases, m)
	val k = mu (n+1,c+1) (fn k => q (k::t))
    in
	if k <= c then k::t
	else 0::(next bases q (m-1) t)
    end;
*)
*)

*)