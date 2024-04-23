open Common
module M (S : StrictnessLv)
  : sig
    open Kernel.M(S)
    open Unchecked_types

    val compute_inverse : tm -> tm
    val compute_witness : tm -> tm
end
