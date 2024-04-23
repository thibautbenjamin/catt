open Common
module M (S : StrictnessLv)
  : sig
    open Kernel.M(S)
    open Unchecked_types

    val reduce : int -> ps -> ps
    val reduction_sub : ps -> sub_ps
    val coh : Coh.t -> Coh.t
  end
