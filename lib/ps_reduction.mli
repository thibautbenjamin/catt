open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

val reduce : int -> ps -> ps
val reduction_sub : ps -> sub_ps
val coh : Coh.t -> Coh.t
