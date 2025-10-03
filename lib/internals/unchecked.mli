open Common
open Unchecked_types

module Unchecked (Coh : sig
  type t
end) (Tm : sig
  type t
end) : sig
  open Unchecked_types(Coh)(Tm)
  open Signatures.Signatures(Coh)(Tm)

  module Make (_ : sig
    val forget : Coh.t -> ps * Unchecked_types(Coh)(Tm).ty * pp_data
    val check : ps -> ty -> pp_data -> Coh.t
  end) (_ : sig
    val develop : Tm.t -> Unchecked_types(Coh)(Tm).tm

    val apply :
      (Unchecked_types(Coh)(Tm).ctx -> Unchecked_types(Coh)(Tm).ctx) ->
      (Unchecked_types(Coh)(Tm).tm -> Unchecked_types(Coh)(Tm).tm) ->
      (pp_data -> pp_data) ->
      Tm.t ->
      Tm.t * Unchecked_types(Coh)(Tm).sub
  end) : UncheckedS
end
