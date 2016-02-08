let gcd (m,n) = 
	if m = n then m else
	if m<n then gcd (m, n-m)
		   else gcd (m-n, n)

in let (x,y) = (10,2) in gcd (x,y) end end
