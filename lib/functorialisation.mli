open Common
module M (S : StrictnessLv)
  :sig
    open Kernel.M(S)
    open Unchecked_types

    val coh : Coh.t -> functorialisation_data -> Coh.t
    val coh_all : Coh.t -> Coh.t
    val tm : ctx -> tm -> functorialisation_data -> ctx * tm
  end
