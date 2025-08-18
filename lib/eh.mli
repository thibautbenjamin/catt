open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

val eh : int -> int -> int -> constr
val full_eh : int -> int -> int -> constr
val eh_Tm : int -> int -> int -> Tm.t
val full_eh_Tm : int -> int -> int -> Tm.t
