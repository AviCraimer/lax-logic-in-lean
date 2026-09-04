(* catpart_absyn.sml : abstract syntax of catpart specifications.
 This file contains the ML definition of the abstract syntax,
 together with a function (print_result) that prints out the 
 result of a parse *)

signature ABSYN =
  sig

     datatype 'a Option = Some of 'a | None

     datatype Flag = Error | Single

     datatype Binop =
	 Or | And
     (* the type of binary logical operations *)

     datatype Cond = 
	      Prop of string 
	    | Binary of Binop * Cond * Cond
	    | Not of Cond
     (* the type of internal representations of conditions *)

     datatype Modifiers = M of
	 {maybe_cond: Cond Option,
	  maybe_properties: string list Option,
	  maybe_flag: Flag Option}

     datatype Choice = Ch of
	 {ch_name: string, maybe_modifiers: Modifiers}

     datatype Categ = Cat of
	 {categ_no: int, categ_name: string, choices: Choice list}

     datatype catpart = F of
	 {fun_letter: string,
	  fun_name: string, categ_specs: Categ list} 

     type result
     val print_result : result -> unit
  (* print out the result of a parse *)
  end


functor AbsynFun (structure Pretty: PRETTY) : ABSYN =
   struct

     datatype 'a Option = Some of 'a | None

     datatype Flag = Error | Single

     datatype Binop =
	 Or | And
     (* the type of binary logical operations *)

     datatype Cond = 
	      Prop of string 
	    | Binary of Binop * Cond * Cond
	    | Not of Cond
     (* the type of internal representations of conditions *)

    datatype Modifiers = M of
	 {maybe_cond: Cond Option,
	  maybe_properties: string list Option,
	  maybe_flag: Flag Option}

     datatype Choice = Ch of
	 {ch_name: string, maybe_modifiers: Modifiers}
 
     datatype Categ = Cat of
	 {categ_no: int, categ_name: string, choices: Choice list}

     datatype catpart = F of
	 {fun_letter: string,
	  fun_name: string, categ_specs: Categ list}  

     type result = catpart Option
     (* a value of type result can either be None , in which case an empty
      spec. was parsed, or Some P where P is of type catpart, i.e., is an
      internal representation of a test specification *)

     (* the following code is not satisfactory--printing is v. poor *)
     open Pretty;
     (* the structure Pretty is a parameter to this functor: opening it
      gives access to its components.  See pretty.sml for the signature 
      PRETTY. *)

     fun string_of_Binop Or     = "or"
       | string_of_Binop And    = "and";

     fun string_of_Flag Error   = "error"
       | string_of_Flag Single  = "single";

     fun mapnl f []	 = []
       | mapnl f [b]	 = [f b]
       | mapnl f (b::bl) = [f b, nl] @ (mapnl f bl)

     fun pretty_Cond (Prop s) = str s
       | pretty_Cond (Binary(f,e1,e2)) =
     	blo(2, [str"(", pretty_Cond e1, str(" "^(string_of_Binop f)), 
		brk 1, pretty_Cond e2, str")"])
       | pretty_Cond (Not e) = 
     	blo(2, [str("(not "), pretty_Cond e, str")"])

     and pretty_Modifiers
	 (M{maybe_cond=mc, maybe_properties=mpl, maybe_flag=mf}) =
	 let fun get_cond None = []
	       | get_cond (Some cond) =
		 [blo(2, [str"[", pretty_Cond cond, str"]", brk 1])] 
	     fun get_prop None = []
	       | get_prop (Some []) = []
	       | get_prop (Some [p]) = [str p]
	       | get_prop (Some (p::pl)) =
		 [str p, str",", brk 1] @ (get_prop (Some pl))
	     fun get_flag None = []
	       | get_flag (Some flag) =
		 [blo(2, [str"[", str(string_of_Flag flag), str"]"])]
	 in
	    blo(2, (get_cond mc)@[str"["]@(get_prop mpl)@[str"]"]
				@(get_flag mf))
	 end

     and pretty_Choice
	 (Ch{ch_name=n, maybe_modifiers=mods}) =
	 blo(2, [str"* ", str n, pretty_Modifiers mods])

     and pretty_Categ
	 (Cat{categ_no=cno, categ_name=n, choices=chl}) =
	 blo(2, [str(string_of_int cno), brk 2, str n,
	     blo(2, mapnl pretty_Choice chl)])
  
     and pretty_catpart
	 (F{fun_letter=c, fun_name=n, categ_specs=cgl}) =
	 blo(2, [str c, str" Function: ", str n, nl, 
		 str "Categories:"]@(mapnl pretty_Categ cgl)
				   @ [str"EndFunction;"]) 

     fun print_catpart f = pr(stdOut, pretty_catpart f, 72);
	 
     fun print_Cond f = pr(stdOut, pretty_Cond f, 72);

     fun print_result None = pr(stdOut, str "", 0)
       | print_result (Some f) = print_catpart f

   end
