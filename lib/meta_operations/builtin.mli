open Common
open Raw_types

module Make (Theory : Theory.S) : sig
  open Kernel.Make(Theory)

  val wcomp : tm * ty -> int -> tm * ty -> tm * ty
  val ps_comp : int -> ps
  val comp_n : int -> Coh.t
  val comp : subR -> bool -> Coh.t
  val arity_comp : subR -> bool -> int
  val id : unit -> Coh.t
  val assoc : Coh.t
  val unbiased_unitor : ps -> tm -> Coh.t
  val intch_comp_nm_coh : int -> int -> Coh.t
end
