open Common
module Functorialisation (Strictness : StrictnessLv)
  :sig
    open Kernel.Kernel(Strictness)
    open Unchecked_types

    val coh : Coh.t -> functorialisation_data -> Coh.t
    val coh_all : Coh.t -> Coh.t
    val tm : ctx -> tm -> functorialisation_data -> ctx * tm
  end
