open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

val gamma : int -> int -> ctx
val delta : int -> ctx
val pad : int -> int -> int -> tm
val padded : int -> int -> int -> tm
val bpad : int -> tm
val bpadded : int -> tm
val bpad_0 : int -> tm
val bpadded_0 : int -> tm
