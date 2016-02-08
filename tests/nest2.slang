let x1 = 1;
	x2  = 2 + x1;
    x3  = 3 + x1 + x2;
	g y = y + x3;
    h z = z + g(z)
in g(h(g x3)) end
