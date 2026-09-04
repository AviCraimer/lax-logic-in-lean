fun prs b x = pr(std_out,b,x);

val t1 = blo(2, [str"hi", brk 1, str"there", nl, str"beautiful"]);

prs t1 20;

val t2 = blo(2, [str"hi", brk 1, str"there", nl, str"beautiful", brk 1,
		 str"person"]); 

prs t2 10;

val t3 = blo(2, [str"hi", brk 1, str"there", nl, str"beautiful", brk 1,
		 str"person", nl, str"indented"]); 

prs t3 10;

val t4 = blo(0, [brk 0, str"hi", brk 1, str"there", nl, str"pretty"]);

prs t4 10; 

prs t4 50;

val t5 = blo(0, [str"hi", brk 1, str"there", nl, str"pretty"]);

val test =  blo(0, [str"A Function:", brk 1, str"test", nl,
		    blo(2, [str"Categories:", nl, str"1", brk 1, str"foo",
			    nl, blo(2, [str"*", brk 1, str"bar"]), nl,
			    str"2", brk 1, str"bar",
			    nl, blo(2, [str"*", brk 1, str"foo", nl,
					str"*", brk 1, str"bar"])]), nl,
		    str"EndFunction;"]);

val test2 = blo(0, [str"A Function:", brk 1, str"test", 
		    blo(2, [nl, str"Categories:", nl, str"1", brk 1, str"foo",
			    blo(2, [nl, str"*", brk 1, str"bar"]), nl,
			    str"2", brk 1, str"bar",
			    blo(2, [nl, str"*", brk 1, str"foo", nl,
					str"*", brk 1, str"bar"])]), nl,
		    str"EndFunction;"]);
