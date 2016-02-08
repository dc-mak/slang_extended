let x = ref (fun z -> z + 17);
	y = ref 0
in (
	y := !x 4; 
	x := fun w  -> w * 10; 
	((!x) 8) + !y
) end 
