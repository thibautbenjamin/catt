module Make (Theory : Theory.S) : sig
  open Kernel.Make(Theory)

  val ctx : int -> ctx
  val telescope : int -> tm
  val checked : int -> Tm.t
end
