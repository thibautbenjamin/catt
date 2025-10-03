open Common
open Unchecked_types

module Printing (Coh : sig
  type t
end) (Tm : sig
  type t
end) (_ : sig
  val tm_apply_sub :
    Unchecked_types(Coh)(Tm).tm ->
    Unchecked_types(Coh)(Tm).sub ->
    Unchecked_types(Coh)(Tm).tm
end) : sig
  open Unchecked_types(Coh)(Tm)
  open Signatures.Signatures(Coh)(Tm)

  module Make (_ : sig
    val to_string : ?unroll:bool -> Coh.t -> string
    val func_data : Coh.t -> (Var.t * int) list list
    val forget : Coh.t -> ps * ty * pp_data
    val is_equal : Coh.t -> Coh.t -> bool
  end) (_ : sig
    val func_data : Tm.t -> (Var.t * int) list list option
    val name : Tm.t -> string option
    val full_name : Tm.t -> string option
    val develop : Tm.t -> tm
    val ctx : Tm.t -> ctx
    val is_equal : Tm.t -> Tm.t -> bool
  end) : PrintingS
end
