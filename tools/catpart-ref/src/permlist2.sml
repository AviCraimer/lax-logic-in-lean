signature PERM_LIST = 
  sig
    val I : 'a -> 'a
    exception Zipf
    val zipf : ('a * 'b -> 'c) -> 'a list -> 'b list -> 'c list
    exception Foldr
    val foldr : ('a * 'a -> 'a) -> 'a list -> 'a
    val member : ''a -> ''a list -> bool
    val delete : ''a -> ''a list -> ''a list
    val perm : ''a list -> ''a list -> bool
    exception Idx
    val idx : (''a * ''a list) -> int
    val uth :  'a list * int -> 'a
  end;
  


structure PermList : PERM_LIST = 
    struct

      fun I x = x
      exception Zipf;
      fun zipf f   []     []   = []
	| zipf f (g::s) (h::t) = f(g, h)::(zipf f s t)
	| zipf f   _      _    = raise Zipf;
      (* zipf I is what is usually called zip *)	

      exception Foldr;
      fun foldr f [] = raise Foldr
	| foldr f [h] = h
	| foldr f (h::g::l) = f(h, foldr f (g::l));

      fun member a [] = false
	| member a (h::t) = if (a = h) then true else member a t

      fun delete a [] = []
	| delete a (h::t) = if (a = h) then t else h::(delete a t);
    
      fun perm [] [] = true
	| perm (h::t) l = (member h l) andalso (perm t (delete h l))
	| perm _ _ = false;

      exception Idx;
      fun idx (a,[])   = raise Idx
	| idx (a,h::t) = if a = h then length t else idx (a,t)
	  
      fun uth (l,a) = List.nth (rev l,a)
    (* replace with a more efficient implementation *)
    end;


