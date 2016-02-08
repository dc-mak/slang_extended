let add p = 
	let g w = w;
		h z = z + g (snd p)
	in h (fst p) end
in  add(1, add(88,12)) end
