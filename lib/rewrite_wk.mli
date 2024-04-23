open Unchecked_types

module M (Coh : sig type t end)
  : sig
    open Unchecked_types(Coh)

    val nf : tm -> tm
  end
