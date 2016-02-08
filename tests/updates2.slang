let p = ref 42;

	(* brackets to prevent left associativity of + affecting intended type *)
	g x = case x of
		  inl empty -> 0
		| inr y  -> case y of
					inl (f,s) -> f p + (case s of
									inl y1 -> y1
								  | inr y2 -> 2*y2)
				  | inr b -> if b then 1 else 0
		(* pattern matching of products, loosely bound case statements *)

in	(
	(* sequence declaration with brackets and semi-colons *)
	g (inl ((int ref -> int) * (int + int) + bool) ());
	g (inr (unit) (inl (bool) (fun x -> !x + 69, inl (int) 0)));
	g (inr (unit) (inr ((int ref -> int) * (int + int)) true));
	(* product pattern matching in lambdas too *)
	(fun (x, y) -> x+y) (5,6)
) end
