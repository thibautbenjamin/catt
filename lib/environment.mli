open Common
module Tbl (Strictness : StrictnessLv)
  : sig
    open Kernel.Kernel(Strictness)
    open Unchecked_types

    type value =
      | Coh of Coh.t
      | Tm of ctx * tm
  end

module Environment (Strictness : StrictnessLv)
  : sig
    open Tbl(Strictness)
    open Kernel.Kernel(Strictness)
    open Unchecked_types

    val add_let : Var.t -> ctx -> ?ty:ty -> tm -> string * string
    val add_coh : Var.t -> ps -> ty -> string
    val val_var : Var.t -> value
    val dim_output : Var.t -> int
    val dim_input : Var.t -> int
  end
