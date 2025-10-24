open Common

module Make (Theory : Theory.S) : sig
  open Kernel.Make(Theory)

  val reduce : int -> ps -> ps
  val reduction_sub : ps -> sub_ps
  val coh : Coh.t -> Coh.t
end
