fun out_ppstream outstrm n =
    mk_ppstream{linewidth = n,
		flush = fn () => flush_out outstrm,
		consumer = outputc outstrm}


(* test *)

val my_ppstrm = out_ppstream std_out 72;

fun test () =
(begin_block my_ppstrm CONSISTENT 0;
 (begin_block my_ppstrm CONSISTENT 2;
   add_string my_ppstrm "beginning of block1";
   add_break  my_ppstrm (2,0);
   add_string my_ppstrm "first item";
    begin_block my_ppstrm CONSISTENT 3;
     add_newline my_ppstrm;
     add_string my_ppstrm "subitem a";
     add_newline my_ppstrm;
    end_block my_ppstrm;
   add_newline my_ppstrm;
   add_string my_ppstrm "second item";
   add_break  my_ppstrm (2,0); add_string my_ppstrm "and another";
   add_newline my_ppstrm;
  end_block my_ppstrm);
 add_string my_ppstrm "end of block1";
 add_newline my_ppstrm;
 end_block my_ppstrm; flush_ppstream my_ppstrm);


