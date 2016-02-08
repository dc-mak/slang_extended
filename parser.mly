
/* Auxiliary code */

%{

let get_loc = Parsing.symbol_start_pos 

let make_seq (loc, expr) =
    match expr with
    | [e] -> e
    | es -> Past.Seq(get_loc(), es) 

(* Patterns *)
type pattern = Gnd of Past.var | Fst of pattern | Snd of pattern

let map_fst = List.map (fun x -> Fst x)
let map_snd = List.map (fun x -> Snd x)

let count  = ref 0
let incr x = (x := !x + 1; !x - 1)
let new_id () = "__auto__pat__gen" ^ string_of_int (incr count)

(* Pattern matching *)
let rec select (loc, matched) patt expr =
    match patt with 
        | Gnd id -> Past.Let (loc, id, matched, expr)
        | Fst p  -> select (loc, Past.Fst(loc, matched)) p expr
        | Snd p  -> select (loc, Past.Snd(loc, matched)) p expr

let match_patt (loc, id) = List.fold_right (select (loc, Past.Var(loc, id)))

(* Declaration and pattern nesting *)
let let_match (loc, patts, expr) rest =
    match patts with 
    | [Gnd id] -> Past.Let(loc, id, expr, rest)
    | patts    -> let id = new_id() in 
                  let matched = match_patt (loc, id) patts rest in
                  Past.Let(loc, id, expr, matched)

let fun_match (loc, id, patts, body) rest = 
    match patts with 
    | [Gnd args] -> Past.LetFun(loc, id, (args, body), rest)
    | patts      -> let args_id = new_id() in
                    let matched = match_patt (loc, args_id) patts body in
                    Past.LetFun(loc, id, (args_id, matched), rest)

(*
let rec_match (loc, id, patts, body) rest = 
    match patts with 
    | [Gnd args] -> Past.LetRecFun(loc, id, (args, body), rest)
    | patts      -> let args_id = new_id() in
                    let matched = match_patt (loc, args_id) patts body in
                    Past.LetRecFun(loc, id, (args_id, matched), rest)
*)

(* Pattern-only nesting *)
let lambda_match (loc, (patts, expr)) =
    match patts with 
    | [Gnd args] -> Past.Lambda(loc, (args, expr))
    | patts      -> let var_id = new_id() in
                    Past.Lambda(loc, (var_id, match_patt (loc, var_id) patts expr))

let case_match (loc, sum, (ps_l, ex_l), (ps_r, ex_r)) =
    let id_inl, ex_l' = match ps_l, ex_l with
    | [Gnd id], ex_l -> (id, ex_l)
    | ps_l, ex_l     -> let id = new_id() in
                        (id, match_patt (loc, id) ps_l ex_l) in
    let id_inr, ex_r' = match ps_r, ex_r with
    | [Gnd id], ex_r -> (id, ex_r)
    | ps_r, ex_r     -> let id = new_id() in
                        (id, match_patt (loc, id) ps_r ex_r) in
    Past.Case(loc, sum, (id_inl, ex_l'), (id_inr, ex_r'))

%}

/* Tokens and types */
%token<int> INT
%token<string> IDENT
%token EOF LPAREN RPAREN COMMA COLON SEMICOLON ADD SUB MUL DIV MOD NOT EQUAL
%token INT_EQ BOOL_EQ LT ANDOP OROP WHAT UNIT AND TRUE FALSE IF FI THEN ELSE
%token LET REC IN BEGIN END BOOL INTTYPE UNITTYPE ARROW BAR INL INR FST SND
%token FUN NUF CASE OF REF ASSIGN BANG WHILE DO OD APP

%nonassoc ELSE               /* bit of a hack?    */
%left ADD SUB                /* lowest precedence */
%left ANDOP OROP             /* medium precedence */
%left EQUAL INT_EQ BOOL_EQ %right ARROW %nonassoc LT
%left MUL DIV MOD 
%left ASSIGN              
%nonassoc UMINUS                  

/* Finally, the first tokens of simple_expr:       higer precedence */
%nonassoc UNIT INT WHAT IDENT TRUE FALSE LPAREN NOT BANG REF

/* May not be the "correct" way of enforcing left-associative,
 * highest precedence function application. */
%left APP
                   
%start start
%type <Past.type_expr> texpr
%type <Past.expr> simple_expr 
%type <Past.expr> expr 
%type <Past.expr list> exprlist
%type <Past.expr> start

%%

/* Grammar  */

start: 
| expr EOF { $1 }

/* problem 
   -e  (unary minus) 
    e e (application) 
    e1 - e2  (is the e1(-e2) or e1-e2???) 
*/

simple_expr:
| UNIT                              { Past.Unit (get_loc())}
| INT                               { Past.Integer (get_loc(), $1) }
| WHAT                              { Past.What (get_loc())} 
| IDENT                             { Past.Var (get_loc(), $1) }
| TRUE                              { Past.Boolean (get_loc(), true)}
| FALSE                             { Past.Boolean (get_loc(), false)}
| LPAREN exprlist RPAREN            { make_seq(get_loc(), $2) }
| LPAREN expr COMMA expr RPAREN     { Past.Pair(get_loc(), $2, $4) }
| NOT simple_expr                   { Past.UnaryOp(get_loc(), Past.NOT, $2) }
| BANG simple_expr                  { Past.Deref(get_loc(), $2) }
| REF simple_expr                   { Past.Ref(get_loc(), $2) }
| simple_expr simple_expr %prec APP { Past.App (get_loc(), $1, $2) } 

exprlist:
| expr                          { [$1] }
| expr SEMICOLON exprlist       { $1::$3  }

expr:
| simple_expr                 { $1 }
| SUB expr %prec UNIT         { Past.UnaryOp(get_loc(), Past.NEG, $2) }
| expr ADD expr               { Past.Op(get_loc(), $1, Past.ADD, $3) }
| expr SUB expr               { Past.Op(get_loc(), $1, Past.SUB, $3) }
| expr MUL expr               { Past.Op(get_loc(), $1, Past.MUL, $3) }
| expr DIV expr               { Past.Op(get_loc(), $1, Past.DIV, $3) }
| expr MOD expr               { Past.Op(get_loc(), $1, Past.MOD, $3) }
| expr LT expr                { Past.Op(get_loc(), $1, Past.LT, $3) }
| expr EQUAL expr             { Past.Op(get_loc(), $1, Past.EQ, $3) }
| expr INT_EQ expr            { Past.Op(get_loc(), $1, Past.EQI, $3) }
| expr BOOL_EQ expr           { Past.Op(get_loc(), $1, Past.EQB, $3) }
| expr ANDOP expr             { Past.Op(get_loc(), $1, Past.AND, $3) }
| expr OROP expr              { Past.Op(get_loc(), $1, Past.OR, $3) }
| expr ASSIGN expr            { Past.Assign(get_loc(), $1, $3) }
| WHILE expr DO simple_expr   { Past.While(get_loc(), $2, $4) }
| IF expr THEN expr ELSE expr { Past.If(get_loc(), $2, $4, $6) }
| FST expr %prec UMINUS       { Past.Fst(get_loc(), $2) }
| SND expr %prec UMINUS       { Past.Snd(get_loc(), $2) }
| INL texpr expr %prec UMINUS { Past.Inl(get_loc(), $2, $3) }
| INR texpr expr %prec UMINUS { Past.Inr(get_loc(), $2, $3) }

| FUN goesto                      { lambda_match (get_loc(), $2) }
| CASE expr OF INL goesto BAR INR goesto
                                  { case_match  (get_loc(), $2, $5, $8) }

| LET decllist IN expr END        { $2 $4 }
decllist:
| decl SEMICOLON decllist         { fun x -> $1 ($3 x) }
| decl                            { $1 }
decl:
| patts EQUAL expr                { let_match (get_loc(), $1, $3) }
| IDENT patts EQUAL expr          { fun_match (get_loc(), $1, $2, $4) }
/* 
| REC IDENT patts EQUAL expr      { rec_match (get_loc(), $2, $3, $5) }
*/
patts:
| IDENT                           { [Gnd $1] }
| LPAREN IDENT RPAREN             { [Gnd $2] }
| LPAREN patts COMMA patts RPAREN { map_fst $2 @ map_snd $4 }

goesto:
| patts ARROW expr %prec ELSE     { ($1, $3) }

texpr: 
| BOOL                               { Past.TEbool             }
| INTTYPE                            { Past.TEint              }
| UNITTYPE                           { Past.TEunit             }
| texpr ARROW texpr                  { Past.TEarrow ($1, $3)   }
| texpr MUL texpr                    { Past.TEproduct ($1, $3) }
| texpr ADD texpr                    { Past.TEunion ($1, $3)   }
| texpr REF                          { Past.TEref $1           }
| LPAREN texpr RPAREN                { $2                      }

