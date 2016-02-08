(* test store, sequence, assignment *) 

let x = ref (ref 777)  
in (
    (!x) := 101; 
    !!x 
) end 
