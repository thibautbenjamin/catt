open Kernel

type tyR =
  | Letin_ty of Var.t * tmR * tyR
  | Obj
  | Arr of tmR * tmR
and tmR =
  | Letin_tm of Var.t * tmR * tmR
  | Var of Var.t
  | Sub of tmR * (tmR * bool) list * int option
  | Meta

val string_of_ty : tyR -> string
val string_of_tm : tmR -> string
val string_of_sub : (tmR * bool) list -> string
val remove_let_tm : tmR -> tmR
val remove_let_ty : tyR -> tyR
val var_in_ty : Var.t -> tyR  -> bool
val infer_susp_tm : (Var.t * tyR) list ->  tmR -> tmR
val infer_susp_ty : (Var.t * tyR) list -> tyR -> tyR
