open Common

module Make (_ : Theory.S) : sig
  module rec Coh : sig
    type t
    type innertm = Tm.t

    val ps : t -> PS.t
    val forget : t -> ps * (Coh.t, Tm.t) ty * pp_data
    val suspend : t -> t
    val is_equal : t -> t -> bool
    val check_equal : t -> t -> unit
    val is_inv : t -> bool
    val to_string : ?unroll:bool -> t -> string
    val dim : t -> int
    val src : t -> (Coh.t, Tm.t) tm
    val tgt : t -> (Coh.t, Tm.t) tm
    val check : ps -> (Coh.t, Tm.t) ty -> pp_data -> t
    val ty : t -> Ty.t

    val check_noninv :
      ps -> (Coh.t, Tm.t) tm -> (Coh.t, Tm.t) tm -> pp_data -> t

    val check_inv : ps -> (Coh.t, Tm.t) tm -> (Coh.t, Tm.t) tm -> pp_data -> t

    val noninv_srctgt :
      t -> (Coh.t, Tm.t) tm * (Coh.t, Tm.t) tm * (Coh.t, Tm.t) ty

    val func_data : t -> (Var.t * int) list list

    val apply_ps :
      (ps -> ps) ->
      ((Coh.t, Tm.t) ty -> (Coh.t, Tm.t) ty) ->
      (pp_data -> pp_data) ->
      t ->
      t

    val apply :
      ((Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) ctx) ->
      ((Coh.t, Tm.t) ty -> (Coh.t, Tm.t) ty) ->
      (pp_data -> pp_data) ->
      t ->
      t * (Coh.t, Tm.t) sub
  end

  and Ty : sig
    type t = private { c : Ctx.t; e : expr; unchecked : (Coh.t, Tm.t) ty }
    and expr = Obj | Arr of t * Tm.t * Tm.t
  end

  and Tm : sig
    type expr = Var of Var.t | Coh of Coh.t * Sub.t | App of Tm.t * Sub.t

    and t = private {
      ty : Ty.t;
      e : expr;
      unchecked : (Coh.t, t) tm;
      mutable developped : (Coh.t, t) tm option;
      name : pp_data option;
    }

    val ty : t -> (Coh.t, Tm.t) ty
    val forget : t -> (Coh.t, Tm.t) tm
    val constr : t -> (Coh.t, Tm.t) constr
    val ctx : t -> (Coh.t, Tm.t) ctx
    val name : t -> string option
    val full_name : t -> string option
    val func_data : t -> (Var.t * int) list list option
    val of_coh : Coh.t -> t
    val develop : t -> (Coh.t, Tm.t) tm
    val pp_data : t -> pp_data option
    val to_string : t -> string
    val is_equal : t -> t -> bool

    val check :
      (Coh.t, t) ctx -> ?ty:(Coh.t, t) ty -> ?name:pp_data -> (Coh.t, t) tm -> t

    val apply :
      ((Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) ctx) ->
      ((Coh.t, Tm.t) tm -> (Coh.t, Tm.t) tm) ->
      (pp_data -> pp_data) ->
      t ->
      t * (Coh.t, Tm.t) sub
  end

  and Sub : sig
    type t
  end

  and Ctx : sig
    type t

    val check : (Coh.t, Tm.t) ctx -> t
  end

  and PS : sig
    exception Invalid

    type t = ps

    val mk : Ctx.t -> t
  end

  module Core : Core.S with type Coh.t = Coh.t with type Tm.t = Tm.t
  include module type of Syntax.Make (Core)

  val check_term : Ctx.t -> ?ty:ty -> ?name:pp_data -> tm -> Tm.t
  val check_constr : ?name:pp_data -> ctx -> constr -> Tm.t
  val check_coh : ps -> ty -> pp_data -> Coh.t
  val check_sub : ctx -> sub -> ctx -> unit
end
