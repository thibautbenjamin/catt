open Common

module Make (K : KernelExt.S) : sig
  open K

  val reduce : int -> ps -> ps
  val reduction_sub : ps -> sub_ps
  val coh : Coh.t -> Coh.t
end
