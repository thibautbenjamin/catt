open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

val ctx : int -> ctx
val telescope : int -> tm
val checked : int -> Tm.t
