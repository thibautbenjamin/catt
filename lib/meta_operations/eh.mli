module Make (K : KernelExt.S) : sig
  open K

  val eh : int -> int -> int -> Tm.t
  val full_eh : int -> int -> int -> Tm.t
end
