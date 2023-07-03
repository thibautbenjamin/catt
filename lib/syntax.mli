open Common

type ty =
  | Letin_ty of Var.t * tm * ty
  | Obj
  | Arr of tm * tm
and tm =
  | Letin_tm of Var.t * tm * tm
  | Var of Var.t
  | Sub of tm * (tm list) * (int list)

val string_of_ty : ty -> string
val string_of_tm : tm -> string
val remove_let_tm : tm -> tm
val remove_let_ty : ty -> ty
