(* test store, sequence, assignment *) 
let x = ref (ref 777)  
in ( 
	x := (ref 101); 
    !!x 
) end 
