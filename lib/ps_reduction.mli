open Common
module Ps_reduction (Strictness : StrictnessLv)
  : sig
    open Kernel.Kernel(Strictness)
    open Unchecked_types

    val reduce : int -> ps -> ps
    val reduction_sub : ps -> sub_ps
    val coh : Coh.t -> Coh.t
  end
