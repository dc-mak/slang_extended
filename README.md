# Slang with extra features I wrote

I messed around with the compiler to implement the following features:
-	nested comments
-	line comments (thank you Emma Holliday for the help)
-	integer division `/`
-	integer modulo `%`
-	high precedence, left associative unambiguous function application
	- allows `if ... then ... else <fun> <args>` without `end`
-	removed `end` for `if-else` expressions
-	short-circuit evaluation for `&&` and `||`
-	removed `end` from lambda-expressions
-	removed `end` from case-expression
-	added declaration lists (as a derived form, allowing me to remove a bunch of `let`s and `end`s)
-	added pattern-matching for product types
-	added rudimentary type inference (thank you James Clarke for helping out)
-	hence removed type annotations (except for `inl` and `inr` where it is necessary)
-	removed need for parentheses around identifiers as patterns

The code is probably not the best/actual way a lot of these features would be
implemented but it was fun (and very distracting/addictive) to make these changes.

Type inference uses references and mutability all over the place. Algorithm W seems
like it would be worth a shot at some point.

## static.ml
This complete rewrite, at its essence, passes a reference to an expected type down
(a synthesised attribute) which is unified/constrained depending on the expression being typed.
