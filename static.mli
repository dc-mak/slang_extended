val dbg : bool ref

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

val infer :(Past.var * infer_set ref) list * infer_set ref * Past.expr
            -> Past.expr * (Past.var * infer_set ref) list

val check : Past.expr -> Past.expr 
