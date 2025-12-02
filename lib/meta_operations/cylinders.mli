module Make (K : KernelExt.S) : sig
  open K

  val compose : int -> int -> int -> Tm.t
  val stacking : int -> Tm.t
end
