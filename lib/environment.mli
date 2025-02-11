open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

type value = Coh of Coh.t | Tm of Tm.t
type t

val builtin_to_value : Raw_types.builtin -> value
val value_ty : value -> ty
val value_to_string : value -> string
val add_let : Var.t -> ctx -> ?ty:ty -> tm -> tm * ty
val add_value : Var.t -> value -> value * ty
val add_coh : Var.t -> ps -> ty -> Coh.t
val val_var : Var.t -> value
val dim_output : Var.t -> int
val dim_input : Var.t -> int
val reset : unit -> unit
