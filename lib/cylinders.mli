open Kernel
open Unchecked_types.Unchecked_types(Coh)(Tm)

module Cylinder : sig
  val ctx : int -> ctx
end

module Codim1 : sig
  val ctx : int -> ctx
end

val compose : int -> int -> int -> Tm.t
