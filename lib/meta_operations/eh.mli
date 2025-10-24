module Make (Theory : Theory.S) : sig
  open Kernel.Make(Theory)

  val eh : int -> int -> int -> Tm.t
  val full_eh : int -> int -> int -> Tm.t
end
