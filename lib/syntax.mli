type ty =
  | Letin_ty of Common.Var.t * tm * ty
  | Obj
  | Arr of tm * tm
and tm =
  | Letin_tm of Common.Var.t * tm * tm
  | Var of Common.Var.t
  | Sub of tm * (tm list) * int option * (int list)

val string_of_ty : ty -> string
val string_of_tm : tm -> string
val string_of_sub : tm list -> int list -> int -> string
val remove_let_tm : tm -> tm
val remove_let_ty : ty -> ty
val var_in_ty : Common.Var.t -> ty  -> bool
