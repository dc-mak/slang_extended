(* This is a file that demonstrates the changes I made *)
(* Nested (* comments *) are very useful *)

let abs x = if x < 0 then -x else x;

	// Line comment, and modulo operator
	even y = y % 2 = 0;

	odd z = 
	let absx   = abs z; (* short-circuit evaluation *)
		odd' w = w = 1 || if w = 0 then false else odd' (w-2)
	in  odd' (abs z) end;

	(* low precedence else *)
	mod_three x =
		if x%3 = 1 then 1 else if x%3 = 2 then 2 else 4*3;

	(* Pattern matching on products! *)
	fib m =
	let next (m, n) = (n, m+n);
		iter (m, r) = if m = 0 then fst r else 
		let (r1, r2) = r in iter (m-1, next (r1, r2)) end
	in  iter (m, (0,1)) end

(* Sequencing simplified to a simple_expr, and integer division *)
in  (fib ?; (if ? = 0 then even else odd) ?) end
(* Note it evaluates/asks for *argument* first *)
