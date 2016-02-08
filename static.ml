open Past
let complain = Errors.complain

let internal_err msg = complain ("INTERNAL ERROR: " ^ msg)

(* Debugging... *)
let dbg       = ref false
let dbg_str s = if !dbg then s ^ "\n" else "\n"
let debug s   = if !dbg then print_string ("STATIC: " ^ s ^ "\n") else ()

(* Partial types *)
type type_infer =
    | INFnone
    | INFint
    | INFbool
    | INFequal
    | INFunit
    | INFref     of infer_set ref
    | INFarrow   of infer_set ref * infer_set ref
    | INFproduct of infer_set ref * infer_set ref
    | INFunion   of infer_set ref * infer_set ref

and  infer_set = Rep of type_infer ref * int *  infer_set ref
               | Mem of infer_set ref  | Nil

exception Nil_found of string

let nil_found s = raise (Nil_found (dbg_str s))

exception Not_cyclic of string
let not_cyclic s = raise (Not_cyclic (dbg_str s))

(* ...and reference tracking *)
let ref_count = ref 1
let ref_index = ref []

let new_ref a =
    let r = ref a in
    begin
        ref_index := (!ref_count, r) :: !ref_index;
        ref_count := !ref_count + 1;
        r
    end

let lookup x =
    try
        let n, _ = List.find (fun (n,y) -> x == y) !ref_index in
        n
   with Not_found -> 0

let lookup_str x = string_of_int (lookup x)

let to_alpha t = 
    let c = lookup t      in
    let a = Char.code 'a' in
    let rec string_type = function
        | 0 -> ""
        | n -> string_type (n/26)
                ^ String.make 1 (Char.chr (a + n mod 26)) in
    "'" ^ string_type c

(* back to type related functions *)
let rec to_infer = function
    | TEint              -> INFint
    | TEbool             -> INFbool
    | TEunit             -> INFunit
    | TEref t            -> INFref (to_set t)
    | TEarrow (f,t)      -> INFarrow (to_set f, to_set t)
    | TEproduct (t1, t2) -> INFproduct (to_set t1, to_set t2)
    | TEunion (t1, t2)   -> INFunion (to_set t1, to_set t2)

and to_set t =
    let t_ref = new_ref (to_infer t)      in
    let tmp   = ref Nil                   in
    let set   = ref (Rep (t_ref, 0, tmp)) in
    (set := Rep (t_ref, 0, set); set)

let rec mk_set t =
    let t_ref = new_ref t                 in
    let tmp   = ref Nil                   in
    let set   = ref (Rep (t_ref, 0, tmp)) in
    (set := Rep (t_ref, 0, set); set)

let rec find_set mem =
    match !mem with
    | Nil            -> nil_found "find_set"
    | Mem set        -> let root = find_set set in (set := !root; root)
    | Rep (_,_,root) -> if mem == root then root else not_cyclic "find_set"

let rec get_rep func mem =
    match !mem with
    | Nil         -> nil_found func
    | Mem set     -> let root = find_set set in get_rep func root
    | Rep (t,n,r) -> if mem == r then (t,n,r) else not_cyclic func

let rec get_tref func mem = let t, _, _ = get_rep func mem in t 

let mk_none()  = mk_set INFnone
let mk_int()   = mk_set INFint
let mk_bool()  = mk_set INFbool
let mk_unit()  = mk_set INFunit
let mk_equal() = mk_set INFequal

let mk_ref r     = mk_set (INFref r)
let mk_prod a b  = mk_set (INFproduct (a,b))
let mk_union a b = mk_set (INFunion (a,b))
let mk_arr a b   = mk_set (INFarrow(a,b))

let rec string_of_infer = function
    | INFnone             -> "INFnone"
    | INFint              -> "INFint"
    | INFbool             -> "INFbool"
    | INFequal            -> "INFequal"
    | INFunit             -> "INFunit"
    | INFref t            -> "INFref ("     ^ string_of_set !t   ^ ")"
    | INFarrow (frm, t)   -> "INFarrow ("   ^ string_of_set !frm ^ ", " ^ string_of_set !t  ^ ")"
    | INFproduct (t1, t2) -> "INFproduct (" ^ string_of_set !t1  ^ ", " ^ string_of_set !t2 ^ ")"
    | INFunion (t1, t2)   -> "INFunion ("   ^ string_of_set !t1  ^ ", " ^ string_of_set !t2 ^ ")"

and string_of_set = function
    | Nil         -> nil_found "string_of_set"
    | Mem set     -> string_of_set !(find_set set)
    | Rep (t,_,_) -> string_of_infer !t

let string_of_infer_norec = function
    | INFnone             -> "INFnone"
    | INFint              -> "INFint"
    | INFbool             -> "INFbool"
    | INFequal            -> "INFequal"
    | INFunit             -> "INFunit"
    | INFref _            -> "INFref"
    | INFarrow (_, _)     -> "INFarrow"
    | INFproduct (_, _)   -> "INFproduct"
    | INFunion (_, _)     -> "INFunion"

let rec unifiable_infer = function
    | INFnone, _         | _, INFnone
    | INFequal, INFequal
    | INFequal, INFint   | INFint, INFequal  | INFint, INFint
    | INFequal, INFbool  | INFbool, INFequal | INFbool, INFbool
    | INFunit, INFunit   -> true

    | INFref a, INFref b -> unifiable (a,b)

    | INFarrow (a1, b1),   INFarrow (a2, b2)
    | INFproduct (a1, b1), INFproduct (a2, b2)
    | INFunion (a1, b1),   INFunion (a2, b2)
        -> unifiable (a1,a2) && unifiable (b1,b2)

    | _ -> false

and unifiable (a,b) =
    let ta = !(get_tref "unifiable" a) in
    let tb = !(get_tref "unifiable" b) in
    unifiable_infer (ta, tb)

let rec pp_infer t = function
    | INFnone           -> "?"
    | INFint            -> "int"
    | INFbool           -> "bool"
    | INFequal          -> "eq"
    | INFunit           -> "unit"
    | INFref r          -> choose (r,t) ^ " ref"
    | INFarrow (f, r)   -> choose (f,t) ^ " -> " ^ choose (r,t)
    | INFproduct (a, b) -> choose (a,t) ^ " * "  ^ choose (b,t)
    | INFunion (a, b)   -> choose (a,t) ^ " + "  ^ choose (b,t)

and choose (set,tb) =
    let prec = function
        | INFnone         | INFint
        | INFbool         | INFunit
        | INFequal                       -> 4
        | INFref _   -> 3 | INFarrow _   -> 0
        | INFunion _ -> 1 | INFproduct _ -> 2 in

    let assoc = function
        | INFarrow   _, INFarrow (_,d) -> set == d
        | INFunion   _, INFunion   _   -> false
        | INFproduct _, INFproduct _   -> false
        | _                            -> true in

    let tr         = get_tref "choose" set  in
    let pp_paren t = "(" ^ pp_i_ref t ^ ")" in
    if prec !tr >= prec tb && assoc (!tr,tb) then pp_i_ref tr else pp_paren tr

and pp_i_ref t_ref =
    match !t_ref with
    | INFnone           -> to_alpha t_ref
    | INFint            -> "int"
    | INFbool           -> "bool"
    | INFequal          -> "eq"
    | INFunit           -> "unit"
    | INFref r          -> choose (r,!t_ref) ^ " ref"
    | INFarrow (f, r)   -> choose (f,!t_ref) ^ " -> " ^ choose (r,!t_ref)
    | INFproduct (a, b) -> choose (a,!t_ref) ^ " * "  ^ choose (b,!t_ref)
    | INFunion (a, b)   -> choose (a,!t_ref) ^ " + "  ^ choose (b,!t_ref)

and pp_set func set  = pp_i_ref (get_tref func set)

let rec reftree a =
    match !a with
    | INFnone             -> "#ref: " ^ lookup_str a ^ pp_i_ref a
    | INFint              -> "#ref: " ^ lookup_str a ^ " int"
    | INFbool             -> "#ref: " ^ lookup_str a ^ " bool"
    | INFequal            -> "#ref: " ^ lookup_str a ^ " eq"
    | INFunit             -> "#ref: " ^ lookup_str a ^ " unit"
    | INFref t            -> "#ref: " ^ lookup_str a ^ ", Ref: (" 
                                      ^ set_reftree "reftree" t   ^ ")"
    | INFarrow (frm, t)   -> "#ref: " ^ lookup_str a ^ ", Arr: (" 
                                      ^ set_reftree "reftree" frm ^ ", "
                                      ^ set_reftree "reftree" t  ^ ")"
    | INFproduct (t1, t2) -> "#ref: " ^ lookup_str a ^ ", Prod: ("
                                      ^ set_reftree "reftree" t1  ^ ", "
                                      ^ set_reftree "reftree" t2 ^ ")"
    | INFunion (t1, t2)   -> "#ref: " ^ lookup_str a ^ ", Sum: (" 
                                      ^ set_reftree "reftree" t1  ^ ", "
                                      ^ set_reftree "reftree" t2 ^ ")"

and set_reftree func set = reftree (get_tref func set)

let rec unify (s1, s2) =
    let t1, n1, r1 = get_rep "unify" s1 in
    let t2, n2, r2 = get_rep "unify" s2 in

    let _ = debug ("UNIFY: " ^ lookup_str t1 ^ " & " ^ lookup_str t2) in
    let _ = debug ("  ---> " ^ pp_i_ref t1 ^  " U " ^ pp_i_ref t2)    in
    match !t1, !t2 with
    | INFnone, a
    | a, INFnone
    | (INFequal as a), INFequal
    | INFequal, (INFbool as a)
    | INFequal, (INFint as a)
    | (INFbool as a), INFequal
    | (INFint as a), INFequal  ->
            if r1 == r2 then () (* already same set *) else
            if n1 > n2  then (t1 := a; r2 := Mem r1)   else
            if n1 = n2  then 
                (t2 := a; r2 := Rep (t2, n2+1, r2); r1 := Mem r2)
            else (* n1 < n2 *) (t2 := a; r1 := Mem r2)

    | INFint, INFint     -> ()
    | INFbool, INFbool   -> ()
    | INFunit, INFunit   -> ()
    | INFref a,            INFref b            -> unify (a,b)
    | INFarrow (a1, b1),   INFarrow (a2, b2)   -> ((unify (a1,a2); unify (b1,b2)))
    | INFproduct (a1, b1), INFproduct (a2, b2) -> ((unify (a1,a2); unify (b1,b2)))
    | INFunion (a1, b1),   INFunion (a2, b2)   -> ((unify (a1,a2); unify (b1,b2)))
    | _ -> internal_err "Inferred types not mergeable"

(* environments *)
let rec free_var v = function
    | Unit _ | What _ | Integer (_, _) | Boolean (_, _) -> false

    | Var (_, w) -> w=v | Lambda(loc, (x, e)) -> x != v && free_var v e

    | LetFun(loc, f, (x, e1), e2) ->
            (x != v && free_var v e1) || f != v && free_var v e2

    | LetRecFun(loc, f, (x, e1), e2) ->
            f != v && (x != v && free_var v e1 || free_var v e2)

    | Case(loc, e, (x1, e1), (x2, e2)) ->
            free_var v e || x1 != v && free_var v e1 || x2 != v && free_var v e2

    | UnaryOp(_, _, e) | Fst(_, e) | Snd(_, e)   | Inl(_, _, e)
    | Inr(_, _, e)     | Ref(_, e) | Deref(_, e) -> free_var v e

    | Op(_, e1, _, e2)  | Pair(_, e1, e2) | While (_, e1, e2)
    | Assign(_, e1, e2) | App(_, e1, e2)  | Let(_, _, e1, e2)
        -> free_var v e1 || free_var v e2

    | If(loc, e1, e2, e3) -> free_var v e1 || free_var v e2 || free_var v e3

    | Seq (loc, el) ->
            let rec free_list = function
                | []      -> false
                | e :: es -> free_var v e || free_list es
             in free_list el

let rec find loc x = function
  | []             -> complain (x ^ " is not defined at " ^ string_of_loc loc)
  | (y, v) :: rest -> if x = y then v else find loc x rest

let inferred = ref []
let save_var loc = function
  | (_, [])            -> internal_err ("Typing environment destroyed at " ^ string_of_loc loc)
  | (e, (x,tx) :: env) -> (inferred := (loc, x, tx) :: !inferred; (e, env))

let rec print_list f = function
    | [] -> ()
    | x :: xs -> let _ = print_string (f x) in print_list f xs

let no_loc (var, set) = "() " ^ var ^ ": " ^ pp_set "no_loc" set ^ "\n"

let with_loc (loc, var, set) = "(" ^ string2_of_loc loc ^ ") "
                            ^ var ^ ": " ^ pp_set "with_loc" set
                            ^ dbg_str ("  [" ^ set_reftree "with_loc" set ^ "]")

let show_types () = print_list with_loc (!inferred)

(* errors *)
let expecting env e ex_set ac_set  =
    let loc    = loc_of_expr e             in
    let loc    = string_of_loc loc         in
    let e      = string_of_expr e          in
    let expect = pp_set "expecting" ex_set in
    let actual = pp_set "expecting" ac_set in
    let _      = show_types()              in
    let _      = print_list no_loc env     in
    complain ("\nERROR at location " ^ loc
                ^ "\nExpression " ^ e ^ "\nhas type " ^ actual
                ^ ", but expecting " ^ expect)

let equality env (e1, set1) (e2, set2) =
    let loc1     = loc_of_expr e1         in
    let loc2     = loc_of_expr e2         in
    let loc1_str = string_of_loc loc1     in
    let loc2_str = string_of_loc loc2     in
    let e1_str   = string_of_expr e1      in
    let e2_str   = string_of_expr e2      in
    let t1_str   = pp_set "equality" set1 in
    let t2_str   = pp_set "equality" set2 in
    complain ("\nERROR, equality reserved for int and bool only: \n"
                ^ "at location "      ^ loc1_str
                ^ "\nexpression "     ^ e1_str
                ^ "\nhas type "       ^ t1_str
                ^ " and at location " ^ loc2_str
                ^ "\nexpression "     ^ e2_str
                ^ "\nhas type "       ^ t2_str)

let unequal env loc set1 set2 =
    let loc_str = string_of_loc loc     in
    let t1_str  = pp_set "unequal" set1 in
    let t2_str  = pp_set "unequal" set2 in
    let _       = show_types()          in
    let _       = print_list no_loc env in
    complain ("\nERROR near location " ^ loc_str
                ^ "\nExpecting type " ^ t1_str
                ^ " to be equal to type" ^ t2_str)

let eqs = ref []

(* the idea is that eventually, enough inherited information will be
 * provided so that
 * INVARIANT:
 *      either  the type of a variable is inferred
 *      or      the variable IS NOT USED in the program [could prove it] *)

let basic_check (env, e, expect, t) = 
    let _    = debug (string_of_infer t)     in
    let tref = get_tref "basic_check" expect in
    if !tref = t then () else
    match !tref, t with
    | INFnone, _
    | INFequal, INFequal
    | INFequal, INFbool
    | INFequal, INFint   -> tref := t
    | _                  -> expecting env e expect (mk_set t)

let rec infer (env, expect, e) =
    match e with

    | Unit loc -> (basic_check (env, e, expect, INFunit); (e, env))
    | What loc -> (basic_check (env, e, expect, INFint ); (e, env))

    | Integer (loc, vlu) -> (basic_check (env, e, expect, INFint ); (e,env))
    | Boolean (loc, vlu) -> (basic_check (env, e, expect, INFbool); (e,env))

    | Var (loc, x) ->
        let  _ = debug "VAR"    in
        let tx = find loc x env in
        if  unifiable (expect, tx)
            then (unify (expect,tx); (e,env))
            else expecting env e expect tx

    | Seq (loc, es) ->
        let _ = debug "SEQ" in
        let rec infer_seq = function
          | ([], env)    -> internal_err "empty sequence found in parsed AST"
          | ([e], env)   -> let (e,env)  = infer (env, expect, e)    in ([e], env)
          | (e::es, env) -> let (e,env)  = infer (env, mk_none(), e) in
                            let (es,env) = infer_seq (es, env)       in (e::es,env) in
        let (es, env) = infer_seq (es, env) in (Seq (loc, es), env)

    | While (loc, e1, e2) ->
        let _    = debug "WHILE"                 in
        let tref = get_tref "infer/While" expect in
        ((match !tref with
        | INFunit  -> ()
        | INFnone  -> tref := INFunit
        | _        -> expecting env e expect (mk_unit()));
        let (e1, env) = infer (env, mk_bool(), e1) in
        let (e2, env) = infer (env, mk_unit(), e2) in
        (While (loc, e1, e2), env))

    | Ref (loc, e) ->
        let _    = debug "REF"                 in
        let tref = get_tref "infer/Ref" expect in
        let expect' = match !tref with
            | INFref t -> t
            | INFnone  -> let t = mk_none() in
                          (tref := INFref t; t)
            | _        -> expecting env e expect (mk_none()) in

        let (e,env) = infer (env, expect', e) in (Ref (loc, e), env)

    | Deref (loc, e) ->
            let _ = debug "DEREF"                       in
            let (e,env) = infer (env, mk_ref expect, e) in
            (Deref (loc,e), env)

    (* order - e2 before e1 - is chosen arbitrarily, mainly to make code elegant *)
    | Assign (loc, e1, e2) ->
        let _ = debug "ASSIGN"                    in
        let tref = get_tref "infer/Assign" expect in
        ((match !tref with
        | INFunit -> ()
        | INFnone -> tref := INFunit
        | t       -> expecting env e expect (mk_unit()));
        let t2 = mk_none()                        in
        let (e2,env) = infer (env, t2, e2)        in
        let (e1,env) = infer (env, mk_ref t2, e1) in
        (Assign (loc, e1, e2), env))

    | UnaryOp (loc, uop, e) ->
        let  _     = debug "UNARY"                   in
        let tref   = get_tref "infer/UnaryOp" expect in
        let wanted = match uop, !tref with
            | NEG, INFint   -> mk_int()
            | NEG, INFnone
            | NEG, INFequal -> (tref := INFint; mk_int())
            | NEG, t        -> expecting env e expect (mk_int())

            | NOT, INFbool  -> mk_bool()
            | NOT, INFequal
            | NOT, INFnone  -> (tref := INFbool; mk_bool())
            | NOT, t        -> expecting env e expect (mk_bool()) in

        let (e,env) = infer (env, wanted, e) in (UnaryOp (loc, uop, e), env)

    (* this deserves some comments *)
    | Op (loc, e1, bop, e2) ->
        let  _     = debug "OP"  in
        (* the RESULT type we want *)
        let wanted = match bop with
            | ADD | SUB | MUL | DIV | MOD      -> INFint
            | LT  | AND | OR  | EQI | EQB | EQ -> INFbool in

        (* should match the type we are expecting *)
        let check t = if wanted = t then () else expecting env e (mk_set t) (mk_set wanted) in
        let tref    = get_tref "infer/Op" expect in
        let _ = match !tref with
            | INFint   -> check INFint
            | INFbool  -> check INFbool
            | INFnone
            | INFequal -> tref := wanted
            | _        -> expecting env e expect (mk_set wanted) in

        (* with the appropriate type of ARGUMENTS *)
        let t1, t2 = match bop with
            | ADD | SUB | MUL | EQI
            | DIV | MOD | LT  -> mk_int(), mk_int()
            | AND | OR  | EQB -> mk_bool(), mk_bool()
            | EQ -> mk_equal(), mk_equal() in

        (* so once we have inferred, we check the equality case *)
        let (e1,env) = infer (env, t1, e1) in
        let (e2,env) = infer (env, t2, e2) in

        (* equality inference is hard :( *)
        let tr1 = get_tref "infer/Op" t1 in
        let tr2 = get_tref "infer/Op" t2 in
        (match bop, !tr1, !tr2 with
            | EQ, INFequal, INFint   -> (tr1 := INFint;
                                        (Op(loc, e1, EQI, e2), env))
            | EQ, INFint, INFequal   -> (tr2 := INFint;
                                        (Op(loc, e1, EQI, e2), env))
            | EQ, INFint, INFint     -> (Op(loc, e1, EQI, e2), env)

            | EQ, INFequal, INFbool  -> (tr1 := INFbool;
                                        (Op(loc, e1, EQB, e2), env))
            | EQ, INFbool,INFequal   -> (tr2 := INFbool;
                                        (Op(loc, e1, EQB, e2), env))
            | EQ, INFbool, INFbool   -> (Op(loc, e1, EQB, e2), env)

            | EQ, INFequal, INFequal -> (eqs := (loc, e1, t1, e2, t2) :: !eqs;
                                        (Op(loc, e1, EQ,  e2), env))
            | EQ, _, _               -> equality env (e1, t1) (e2, t2)
            | _, _, _                -> (Op (loc, e1, bop, e2), env))

    | If (loc, e1, e2, e3) ->
        let  _       = debug "IF"                 in
        let (e1,env) = infer (env, mk_bool(), e1) in
        let (e2,env) = infer (env, expect, e2)      in
        let (e3,env) = infer (env, expect, e3)      in
        (If(loc, e1, e2, e3), env)

    | Pair (loc, e1, e2) ->
        let  _     = debug "PAIR"                 in
        let tref   = get_tref "infer/Pair" expect in
        let t1, t2 = match !tref with
            | INFproduct (t1, t2) -> (t1, t2)
            | INFnone -> let t1,t2 = mk_none(), mk_none() in
                         (tref := INFproduct(t1,t2); (t1,t2))
            | _       -> expecting env e expect (mk_prod (mk_none()) (mk_none())) in
        let (e1,env) = infer (env, t1, e1) in
        let (e2,env) = infer (env, t2, e2) in
        (Pair(loc, e1, e2), env)

    | Fst (loc, e) ->
        let  _      = debug "FST" in
        let (e,env) = infer (env, mk_prod expect (mk_none()), e) in
        (Fst (loc,e), env)

    | Snd (loc, e) ->
        let  _      = debug "SND" in
        let (e,env) = infer (env, mk_prod (mk_none()) expect, e) in
        (Snd (loc,e), env)

    (* since we do not have the ability to have user-defined constructors, we
     * differentiate amongst different union types with type annotations :( *)
    | Inl (loc, te_t2, e1) ->
        let  _   = debug "INL"                 in
        let ann  = to_set te_t2                in
        let tref = get_tref "infer/Inl" expect in
        let t1   = match !tref with
            | INFunion (t1, t2) ->
                if unifiable (t2, ann)
                    then (unify (t2,ann); t1)
                    else unequal env loc t2 ann
            | INFnone -> let t1 = mk_none() in
                         (tref := INFunion (t1, ann); t1)
            | _       -> expecting env e expect (mk_union (mk_none()) (mk_none())) in

            let (e1,env) = infer (env, t1, e1) in
            (Inl (loc, te_t2, e1), env)

    | Inr (loc, te_t1, e2) ->
        let  _   = debug "INR"                 in
        let ann  = to_set te_t1                in
        let tref = get_tref "infer/Inr" expect in
        let t2   = match !tref with
            | INFunion (t1, t2) ->
                if unifiable (t1, ann)
                    then (unify (t1,ann); t2)
                    else unequal env loc t1 ann
            | INFnone -> let t2 = mk_none() in
                         (tref := INFunion(ann, t2); t2)
            | _       -> expecting env e expect (mk_union (mk_none()) (mk_none())) in

        let (e1,env) = infer (env, t2, e2) in
        (Inr (loc, te_t1, e1), env)

    (* for variable binding expressions, each is responsible for taking its
     * bound variable off of the env - done using save_var *)
    | Case (loc, e, (x,l), (y,r)) ->
            let  _      = debug "CASE"                                    in
            let tx, ty  = mk_none(), mk_none()                            in
            let (e,env) = infer (env, mk_union tx ty, e)                  in
            let (l,env) = save_var loc (infer ((x,tx) :: env, expect, l)) in
            let (r,env) = save_var loc (infer ((y,ty) :: env, expect, r)) in
            (Case (loc, e, (x,l), (y,r)), env)

    | Lambda (loc, (x, b)) ->
            let  _     = debug "LAMBDA" in
            let tref   = get_tref "infer/Lambda" expect in
            let tx, tb = match !tref with
                | INFarrow (tx, tb) -> (tx, tb)
                | INFnone           -> let tx, tb = mk_none(), mk_none() in
                                       (tref := INFarrow(tx,tb); (tx,tb))
                | _ -> expecting env e expect (mk_arr (mk_none()) (mk_none())) in
            let (b,env) = save_var loc (infer ((x,tx) :: env, tb, b)) in
            (Lambda (loc, (x,b)), env)

    | App (loc, f, arg) ->
            let  _        = debug "APP"                         in
            let t_arg     = mk_none()                           in
            let (f,env)   = infer (env, mk_arr t_arg expect, f) in
            let (arg,env) = infer (env, t_arg, arg)             in
            (App (loc, f, arg), env)

    | Let (loc, x, e1, e2) ->
            let  _       = debug ("LET: " ^ x)                in
            let tx       = mk_none()                          in
            let (e2,env) = infer ((x,tx) :: env, expect, e2)    in
            let (e1,env) = save_var loc (infer (env, tx, e1)) in
            (Let(loc, x, e1, e2), env)

    | LetFun (loc, f, (x, body), e) ->
            let  _         = debug ("LETFUN: " ^ f ^ ", " ^ x)   in
            let tx, tb     = mk_none(), mk_none()                in
            let tf         = mk_arr tx tb                        in

            let (e,env)    = infer ((f,tf) :: env, expect, e)      in
            let (b,env)    = infer ((x,tx) :: env, tb, body)     in
            let (body,env) = save_var loc (save_var loc (b,env)) in

            ((if free_var f body
                then LetRecFun(loc, f, (x,body), e)
                else LetFun(loc, f, (x,body), e)),   env)

    | LetRecFun (_, _, _, _)     -> internal_err "LetRecFun found in parsed AST"


(* Second pass for translating EQ into EQI or EQB *)
let rec trans (e',eq) exp =
    match exp with
    | Op(loc, e1, op, e2) -> if e'=exp then Op (loc, e1, eq, e2)
                                       else Op (loc, trans (e',eq) e1, op, trans (e',eq) e2)

    | Unit _ | What _ | Var (_, _) | Integer (_, _) | Boolean (_, _) -> exp

    | UnaryOp(loc, op, e) -> UnaryOp(loc, op, trans (e',eq) e)
    | Fst(loc, e)         -> Fst(loc, trans (e',eq) e)
    | Snd(loc, e)         -> Snd(loc, trans (e',eq) e)
    | Inl(loc, t, e)      -> Inl(loc, t, trans (e',eq) e)
    | Lambda(loc, (x, e)) -> Lambda(loc, (x, trans (e',eq) e))
    | Ref(loc, e)         -> Ref(loc, trans (e',eq) e)
    | Deref(loc, e)       -> Deref(loc, trans (e',eq) e)
    | Inr(loc, t, e)      -> Inr(loc, t, trans (e',eq) e)

    | If(loc, e1, e2, e3) -> let e1' = trans (e',eq) e1 in
                             let e2' = trans (e',eq) e2 in
                             let e3' = trans (e',eq) e3 in
                             If(loc, e1', e2', e3')

    | Pair(loc, e1, e2)   -> let e1' = trans (e',eq) e1 in
                             let e2' = trans (e',eq) e2 in
                             Pair(loc, trans (e',eq) e1', trans (e',eq) e2')

    | Seq (loc, el)       -> Seq(loc, List.map (trans (e',eq)) el)
    | While (loc, e1, e2) -> let e1' = trans (e',eq) e1 in
                             let e2' = trans (e',eq) e2 in
                             While(loc, e1', e2')

    | Assign(loc, e1, e2) -> let e1' = trans (e',eq) e1 in
                             let e2' = trans (e',eq) e2 in
                             Assign(loc, e1', e2')

    | App(loc, e1, e2)    -> let e1' = trans (e',eq) e1 in
                             let e2' = trans (e',eq) e2 in
                             App(loc, e1', e2')

    | Let(loc, x, e1, e2) -> let e1' = trans (e',eq) e1 in
                             let e2' = trans (e',eq) e2 in
                             Let(loc, x, e1', e2')

    | LetFun(loc, f, (x, e1), e2)      -> let e1' = trans (e',eq) e1 in
                                          let e2' = trans (e',eq) e2 in
                                          LetFun(loc, f, (x, e1'), e2')

    | LetRecFun(loc, f, (x, e1), e2)   -> let e1' = trans (e',eq) e1 in
                                          let e2' = trans (e',eq) e2 in
                                          LetRecFun(loc, f, (x, e1'), e2')

    | Case(loc, e, (x1, e1), (x2, e2)) -> let e1' = trans (e',eq) e1 in
                                          let e2' = trans (e',eq) e2 in
                                          Case(loc, trans (e',eq) e, (x1, e1'), (x2, e2'))

let select_op (loc, e1, set1, e2, set2) =
    let t1 = get_tref "select_op" set1 in
    let t2 = get_tref "select_op" set2 in
    let show eqtype =
        print_string ("(" ^ string_of_loc loc ^ ") inferred "
                          ^ string_of_oper eqtype ^ "\n") in

    match (!t1, !t2) with
    | INFequal, INFint  | INFint, INFequal  | INFint, INFint
        -> (show EQI; (Op(loc, e1, EQ, e2), EQI))
    | INFequal, INFbool | INFbool, INFequal | INFbool, INFbool
        -> (show EQB; (Op(loc, e1, EQ, e2), EQB))
    | t1, t2            ->  equality [] (e1, set1) (e2, set2)


(* this is function that is run for static analysis *)
let check e =
    let start   = mk_none()                 in
    let e, _    = infer ([], start, e)      in
    let updates = List.map select_op (!eqs) in
    begin
        show_types();
        print_string
        ("PROGRAM TYPE: "
            ^ pp_set "check" start
            ^ dbg_str ("  [" ^ set_reftree "check" start ^ "]"));
        List.fold_right trans updates e
    end
