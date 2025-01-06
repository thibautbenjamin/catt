open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

val eh_ctx : int -> ctx
val eh : int -> int -> int -> Construct.constr
val full_eh : int -> int -> int -> Construct.constr
