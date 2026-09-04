open Parse
    
open Absyn

open PermList

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
    (F {fun_letter=c, fun_name=f, param_specs=ps, env_specs=es})
    = let
	  fun partition_flags
	      (Cat{categ_no=cno, categ_name=cna, choices=cs})
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
		      partition is_flagged cs
	      in
		  (Cat{categ_no=cno, categ_name=cna, choices=flagged},
		   Cat{categ_no=cno, categ_name=cna, choices=unflagged})
	      end
	  (* partition the choices of a category into flagged and unflagged *)
	
	  val (flagged_ps, unflagged_ps)
	      = group (map partition_flags ps)
	  (* partition each choice in each parameter category
	     into flagged and unflagged choices, then group the flagged
             and unflagged choices together *) 

	  val (flagged_es, unflagged_es)
	      = group (map partition_flags es)
	  (* do the same for the environmental categories *)
      in
	  (F{fun_letter=c, fun_name=f^"_flagged",
	     param_specs=flagged_ps, env_specs=flagged_es},
	   F{fun_letter=c, fun_name=f^"_unflagged",
	     param_specs=unflagged_ps, env_specs=unflagged_es})

      end

fun make_lists
    (F {fun_letter=_, fun_name=_, param_specs=ps, env_specs=es})
    = let
	  fun ord 0 = []
	  | ord n = let val n_ = n - 1 in n_ :: (ord n_) end
	  fun make_ch_list (Cat{categ_no=_, categ_name=_, choices=ps})
	      = ord (length ps)
    in
	  (map make_ch_list ps) @ (map make_ch_list es)
      end
(* make a list of lists of numbers (representing choices) from a test 
   spec. *)  

fun make_bases
    (F {fun_letter=_, fun_name=_, param_specs=ps, env_specs=es})
    = let
	  fun make_ch_list (Cat{categ_no=_, categ_name=_, choices=ps})
	      = length ps
    in
	  (map make_ch_list ps) @ (map make_ch_list es)
      end
(* make a list of lengths (representing no.s of choices) from a test 
   spec. *)  

fun join l = fold (op @) l []
    
fun pS(l,m) = join (map (fn p => map (fn c => c::p) l) m)

fun product l = fold pS l [[]]

exception Combine
fun combine
    (F{fun_letter=_, fun_name=_, param_specs=ps, env_specs=es})
    l =
    let val cats=ps@es
	fun comb [] [] = []
	  | comb
	    ((Cat{categ_no=cno, categ_name=cna, choices=cs})::chs)
	    (n::t) =
	    {categ_no=cno, categ_name=cna, choice=nth(cs, n)} :: (comb chs t)
	  | comb _ _ = raise Combine 
    in
	comb cats l
    end
(* extract the test frame encoded by the list l from a test spec. *)

(* tests:

val tsl2 = get_option(file_parse"find.tsl");
val tsl2_l = make_lists tsl2;
val tsl2_combs = product tsl2_l;
    map (combine tsl2) tsl2_combs;

val (tsl2_f, tsl2_u) = partition_spec tsl2;
val tsl2_u_l = make_lists tsl2_u;
val tsl2_u_combs = product tsl2_u_l;
    map (combine tsl2_u) tsl2_u_combs;
*)
   
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

fun |= (V, Some c) = |- (V, c)
  | |= (V, None)   = True;

(* the following is more in keeping with conventional notation:     
infix |-;
infix |=;
   but means it we cannot write the functions in the way we want
 *)

fun and_tri True  v     = v
  | and_tri False _     = False
  | and_tri Maybe False = False
  | and_tri Maybe _     = Maybe

fun /\ (v1, v2) = and_tri v1 v2;
infix /\;
    
fun valid comb = 
    let
	fun ord 0 = []
	  | ord n = let val n_ = n - 1 in n_ :: (ord n_) end
	val n = length comb
	val l = ord n
    in
	fold (op /\) (map (fn m => |= (setup_cond m comb)) l) True
    end

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
 
(* datatype Quad = Firm of bool | Weak of bool (* uncomment to recompile *) *)

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

fun /\ (b1, b2) = b1 andalso b2;
infix /\;

fun ord 0 = []
  | ord n = let val n_ = n - 1 in n_ :: (ord n_) end

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

exception Extract
fun extract
    (F{fun_letter=_, fun_name=_, param_specs=ps, env_specs=es})
    l =
    let val cats = ps @ es
	fun comb [] [] = []
	  | comb
	    ((Cat{categ_no=cno, categ_name=cna, choices=cs})::chs)
	    (n::t) =
	    (nth(cs, n)) :: (comb chs t)
	  | comb _ _ = raise Extract 
    in
	comb cats l
    end
(* extract the choices encoded by the list l from a test spec. *)

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

fun filter p [] = []
  | filter p (h::t) = if p h then h::(filter p t) else filter p t;
    
    filter (fn comb => valid (extract tsl2 comb) = True) tsl2_combs;

fun mu (n,m) p =
    if n < m then
	if p n then n else mu (n+1,m) p
    else m

fun next bases q _ []     = []
  | next bases q m (n::t) =
    let val c = uth(bases, m)
	val k = mu (n+1,c+1) (fn k => q (k::t))
    in
	if k <= c then k::t
	else 0::(next bases q (m-1) t)
    end;

exception First;

fun first 0 = []
  | first n = if n > 0 then 0::(first (n-1)) else raise First;

val mb2 = make_bases tsl2;
    
val test_next = next mb2 (fn x => true) 0;

fun iterate cond f from =
    if cond from then from else iterate cond f (f from)
    handle Nth => from;
    
fun odd n = (n = 2*(n div 2) + 1);   
    
    iterate
    (fn comb => valid (extract tsl2 comb))
    (step tsl2)
    (first 7);
    
val test_next' = next [1,2,3] (fn x => true) 2;

    iterate
    (fn (x,l) => x=[0,0,0])
    (fn (x,l) => let val nx = test_next' x in (nx, nx::l) end)
    ([1,1,1],[[]]); 

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
    
val tsl1 = get_option(file_parse "fileinfo.tsl");
val (tsl1_f, tsl1_u) = partition_spec tsl1;

val test1_u = testgen tsl1_u;
    
val combs1_u = map (combine tsl1_u) (tl(#2(test1_u)));
 
val (tsl2_f, tsl2_u) = partition_spec tsl2;

val test2_u = testgen tsl2_u;
    
val combs2_u = map (combine tsl2_u) (tl(#2(test2_u)));
    
fun print_comb [] = (String.print"")
  | print_comb ({categ_no=_,
		   categ_name=cna,
		   choice=Ch{ch_name=ch,
			     maybe_modifiers=_}}::chs) =
    (String.print (cna^" = "^ch^"\n");
     print_comb chs);
    
fun print_combs [] _ = (String.print "")
  | print_combs ([]::t) _ = (String.print "empty category!\n")
  | print_combs (chs::t) n =
    (print n; String.print"\n";
     print_comb chs; String.print"\n";
     print_combs t (n+1);
     String.print"\n");
  
    (* print_combs combs1_u 1; (* this is a long one! *) *)
    print_combs combs2_u 1;
   

















 

    
