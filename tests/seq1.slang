(* test store, sequence, assignment *) 

let x = ref 0; y = ref 0
in (
	x := 10; 
	y := 1; 
	x := 100; 
	!x + !y
) end 

