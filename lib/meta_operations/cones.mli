module Make (K : KernelExt.S) : sig
  open K

  val compose : int -> int -> int -> Tm.t
end
