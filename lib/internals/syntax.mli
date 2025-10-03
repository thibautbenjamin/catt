open Unchecked_types
open Signatures
open Common

module Syntax : functor
  (CohT : sig
     type t
   end)
  (TmT : sig
     type t
   end)
  -> sig
  open Unchecked_types(CohT)(TmT)
  open Signatures(CohT)(TmT)

  module Make : functor
    (_ : sig
       val forget : CohT.t -> ps * ty * pp_data
       val check : ps -> ty -> pp_data -> CohT.t
       val to_string : ?unroll:bool -> CohT.t -> string
       val func_data : CohT.t -> (Var.t * int) list list
       val is_equal : CohT.t -> CohT.t -> bool
     end)
    (_ : sig
       val develop : TmT.t -> tm
       val func_data : TmT.t -> (Var.t * int) list list option
       val name : TmT.t -> string option
       val full_name : TmT.t -> string option
       val ctx : TmT.t -> ctx
       val is_equal : TmT.t -> TmT.t -> bool

       val apply :
         (ctx -> ctx) ->
         (tm -> tm) ->
         (pp_data -> pp_data) ->
         TmT.t ->
         TmT.t * sub
     end)
    -> sig
    include module type of Unchecked_types (CohT) (TmT)
    module Unchecked : UncheckedS
    module Display_maps : DisplayMapsS
    module Printing : PrintingS
    module Equality : EqualityS
  end
end
