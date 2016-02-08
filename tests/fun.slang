(* the reason we need closures on the heap ... *) 
let f y = 
	let g x = y + x in g end
in let add21 = f 21;
	   add17 = f 17
in add17 3 + add21 6 end end
