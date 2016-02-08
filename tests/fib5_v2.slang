let h p = 
	let fib m = 
		if (m = 0 || m = 1)
			then snd p
			else fib (m - 1) + fib (m -2) 

	in fib (fst p) end 

in h (5, 1) end 
