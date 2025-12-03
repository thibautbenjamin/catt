module Make (K : KernelExt.S) : sig
  open K

  val ctx : int -> ctx
  val telescope : int -> tm
  val checked : int -> Tm.t
end
