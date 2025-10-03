open Common
open Unchecked_types

module Syntax (CohT : sig
  type t
end) (TmT : sig
  type t
end) =
struct
  open Unchecked_types (CohT) (TmT)

  module Make (Coh : sig
    val forget : CohT.t -> ps * Unchecked_types(CohT)(TmT).ty * pp_data
    val check : ps -> ty -> pp_data -> CohT.t
    val to_string : ?unroll:bool -> CohT.t -> string
    val func_data : CohT.t -> (Var.t * int) list list
    val is_equal : CohT.t -> CohT.t -> bool
  end) (Tm : sig
    val develop : TmT.t -> Unchecked_types(CohT)(TmT).tm
    val func_data : TmT.t -> (Var.t * int) list list option
    val name : TmT.t -> string option
    val full_name : TmT.t -> string option
    val ctx : TmT.t -> ctx
    val is_equal : TmT.t -> TmT.t -> bool

    val apply :
      (Unchecked_types(CohT)(TmT).ctx -> Unchecked_types(CohT)(TmT).ctx) ->
      (Unchecked_types(CohT)(TmT).tm -> Unchecked_types(CohT)(TmT).tm) ->
      (pp_data -> pp_data) ->
      TmT.t ->
      TmT.t * Unchecked_types(CohT)(TmT).sub
  end) =
  struct
    include Unchecked_types (CohT) (TmT)
    module U = Unchecked.Unchecked (CohT) (TmT)
    module Unchecked = U.Make (Coh) (Tm)
    module D = Display_maps.DisplayMaps (CohT) (TmT)
    module Display_maps = D.Make (Coh) (Tm)
    module P = Printing.Printing (CohT) (TmT) (Unchecked)
    module Printing = P.Make (Coh) (Tm)
    module E = Equality.Equality (CohT) (TmT)
    module Equality = E.Make (Coh) (Tm)
  end
end
