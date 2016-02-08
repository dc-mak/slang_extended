let pair x =
	let pair2 y =
		let pair3 z =
			z x y
		in
			pair3
		end
	in
		pair2
	end
in
	let id y = y in
		let x1 y = pair y y in
			x1 id
			(* let x2 y = x1 (x1 y) in x2 id end *)
		end
	end
end
