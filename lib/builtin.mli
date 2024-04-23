open Raw_types
open Common
module M (S : StrictnessLv)
: sig
  open Kernel.M(S)
  open Unchecked_types

  val ps_comp : int -> ps
  val comp_n : int -> Coh.t
  val comp : subR -> Coh.t
  val id : Coh.t
  val unbiased_unitor : ps -> tm -> Coh.t

  (* returns the associator pairing up the middle two cells of a composite of
     (2*k) 1-cells. The argument is the integer k *)
  val middle_associator : int -> Coh.t

  (* returns the unitor cancelling the identity in the middle of a composite of
     (2*k+1) 1-cells. The argument is the integer k *)
  val middle_unitor : int -> Coh.t

  (* returns the whiskering rewriting the middle term of a composite of (2*k+1)
     1-cells. The argument is the integer k *)
  val middle_rewrite : int -> Coh.t
end
