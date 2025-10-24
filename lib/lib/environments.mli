open Common

module type S = sig
  module CurrentTheory : Theory.S
  include module type of Kernel.Make (CurrentTheory)

  module Environment : sig
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
    val forall : (Var.t -> unit) -> unit
  end

  module Suspension : module type of Suspension.Make (CurrentTheory)

  module Functorialisation :
      module type of Functorialisation.Make (CurrentTheory)

  module Opposite : module type of Opposite.Make (CurrentTheory)
  module Inverse : module type of Inverse.Make (CurrentTheory)
  module Builtin : module type of Builtin.Make (CurrentTheory)
  module Cones : module type of Cones.Make (CurrentTheory)
  module Cylinders : module type of Cylinders.Make (CurrentTheory)
  module Eh : module type of Eh.Make (CurrentTheory)

  module Cubical_composite :
      module type of Cubical_composite.Make (CurrentTheory)
end

val store_environment : (module S) -> unit
val find_environment : Var.t -> (module S) list

module Make (_ : Theory.S) : S
