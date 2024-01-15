open Kernel
open Kernel.Unchecked_types

type value =
  | Coh of Coh.t
  | Tm of ctx * tm

type t

val add_let : Var.t -> ctx -> ?ty:ty -> tm -> tm * ty
val add_coh : Var.t -> ps -> ty -> Coh.t
val val_var : Var.t -> value
val dim_output : Var.t -> int
val dim_input : Var.t -> int
