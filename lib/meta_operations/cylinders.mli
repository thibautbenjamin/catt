module Make (Theory : Theory.S) : sig
  open Kernel.Make(Theory)

  val compose : int -> int -> int -> Tm.t
  val stacking : int -> Tm.t
end
