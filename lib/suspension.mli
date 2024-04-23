open Common
module M (S : StrictnessLv)
  :sig
    open Kernel.M(S)
    open Unchecked_types

    val ps : int option -> ps -> ps
    val ty : int option -> ty -> ty
    val tm : int option -> tm -> tm
    val sub_ps : int option -> sub_ps -> sub_ps
    val ctx : int option -> ctx -> ctx
    val coh : int option -> Coh.t -> Coh.t
  end
