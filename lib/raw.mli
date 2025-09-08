open Common
open Raw_types

val string_of_ty : tyR -> string
val string_of_tm : tmR -> string
val string_of_sub : subR -> string
val remove_let_tm : tmR -> tmR
val remove_let_ty : tyR -> tyR
val var_in_ty : Var.t -> tyR -> bool
val infer_susp_tm : (Var.t * tyR) list -> tmR -> tmR
val infer_susp_ty : (Var.t * tyR) list -> tyR -> tyR
val dim_tm : (Var.t * tyR) list -> tmR -> int
