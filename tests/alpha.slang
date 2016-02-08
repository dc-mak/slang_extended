(* test alpha conversion *) 

let x = 1 in 
let x = 2 + x in
let x = 3 +x in
let g x = x + x;
	h x = x + g x
in g (h (g x)) end end end end
