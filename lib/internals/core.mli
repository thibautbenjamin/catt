open Common

module type S = sig
  module PS : sig
    type t
  end

  module Coh : sig
    type t
    type innertm

    val suspend : t -> t
    val forget : t -> ps * (t, innertm) ty * pp_data
    val to_string : ?unroll:bool -> t -> string
    val func_data : t -> (Var.t * int) list list
    val is_equal : t -> t -> bool
  end

  module Tm : sig
    type t

    val develop : t -> (Coh.t, t) tm
    val func_data : t -> (Var.t * int) list list option
    val name : t -> string option
    val full_name : t -> string option
    val ctx : t -> (Coh.t, t) ctx
    val is_equal : t -> t -> bool

    val check :
      (Coh.t, t) ctx -> ?ty:(Coh.t, t) ty -> ?name:pp_data -> (Coh.t, t) tm -> t

    val ty : t -> (Coh.t, t) ty
    val forget : t -> (Coh.t, t) tm

    val apply :
      ((Coh.t, t) ctx -> (Coh.t, t) ctx) ->
      ((Coh.t, t) tm -> (Coh.t, t) tm) ->
      (pp_data -> pp_data) ->
      t ->
      t * (Coh.t, t) sub
  end
end
