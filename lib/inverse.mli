open Common
module Inverse (Strictness : StrictnessLv)
  : sig
    open Kernel.Kernel(Strictness)
    open Unchecked_types

    val compute_inverse : tm -> tm
    val compute_witness : tm -> tm
end
