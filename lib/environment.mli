open Common

type value =
  | Coh of ps * ty
  | Tm of ctx * tm

type t

val add_let : Var.t -> ctx -> tm -> unit
val add_let_check : Var.t -> ctx -> tm -> ty -> unit
val add_coh : Var.t -> ps -> ty -> unit
val val_var : Var.t -> value
