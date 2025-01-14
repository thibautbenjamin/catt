open Common
open Unchecked_types

module Printing (Coh : sig
  type t
end) (Tm : sig
  type t
end) : sig
  open Unchecked_types(Coh)(Tm)

  module Make (_ : sig
    val to_string : ?unroll:bool -> Coh.t -> string
    val func_data : Coh.t -> (Var.t * int) list list
    val forget : Coh.t -> ps * ty * pp_data
    val is_equal : Coh.t -> Coh.t -> bool
  end) (_ : sig
    val func_data : Tm.t -> (Var.t * int) list list
    val name : Tm.t -> string
    val full_name : Tm.t -> string
    val develop : Tm.t -> tm
    val ctx : Tm.t -> ctx
    val is_equal : Tm.t -> Tm.t -> bool
  end) : sig
    val ps_to_string : ps -> string
    val ty_to_string : ty -> string
    val tm_to_string : tm -> string
    val sub_ps_to_string : ?func:(Var.t * int) list list -> sub_ps -> string
    val ctx_to_string : ctx -> string
    val sub_to_string : ?func:(Var.t * int) list list -> sub -> string
    val sub_to_string_debug : sub -> string
    val meta_ctx_to_string : meta_ctx -> string
    val full_name : pp_data -> string
    val pp_data_to_string : ?print_func:bool -> pp_data -> string
    val print_kolmogorov : tm -> string
  end
end
