open Common

module type S = sig
  module K : KernelExt.S
  open K

  val builtin_to_value : Raw_types.builtin -> value
  val value_ty : value -> ty
  val value_to_string : value -> string
  val add_let : Var.t -> ctx -> ?ty:ty -> tm -> tm * ty
  val add_value : Var.t -> value -> value * ty
  val add_coh : Var.t -> ps -> ty -> Coh.t
  val val_var : Var.t -> value
  val dim_output : Var.t -> int
  val dim_input : Var.t -> int

  module Suspension : module type of Suspension.Make (K)
  module Functorialisation : module type of Functorialisation.Make (K)
  module Opposite : module type of Opposite.Make (K)
  module Inverse : module type of Inverse.Make (K)
  module Builtin : module type of Builtin.Make (K)
  module Cones : module type of Cones.Make (K)
  module Cylinders : module type of Cylinders.Make (K)
  module Eh : module type of Eh.Make (K)
  module Cubical_composite : module type of Cubical_composite.Make (K)
end

type envValue =
  | Val :
      (module KernelExt.S with type Coh.t = 'a and type Tm.t = 'b)
      * ('a, 'b) pvalue
      -> envValue

val find : Var.t -> envValue list

module Make (_ : KernelExt.S) : S
