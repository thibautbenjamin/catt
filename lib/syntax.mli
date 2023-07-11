type ty =
  | Letin_ty of Common.Var.t * tm * ty
  | Obj
  | Arr of tm * tm
and tm =
  | Letin_tm of Common.Var.t * tm * tm
  | Var of Common.Var.t
  | Sub of tm * (tm * bool) list * int option
  | Meta
  | Nat of Common.Var.t * tm * tm

val string_of_ty : ty -> string
val string_of_tm : tm -> string
val string_of_sub : (tm * bool) list -> string
val remove_let_tm : tm -> tm
val remove_let_ty : ty -> ty
val var_in_ty : Common.Var.t -> ty  -> bool
val infer_susp_tm : (Common.Var.t * ty) list ->  tm -> tm
val infer_susp_ty : (Common.Var.t * ty) list -> ty -> ty
