let gcd (m,n) = 
	if m = n then m else
	if m < n  then gcd (m,n-m)
			  else gcd (m-n,n)
in gcd (?, ?) end
