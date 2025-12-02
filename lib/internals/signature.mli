open Common

module type TmS = sig
  type checked_coh
  type checked_sub
  type checked_ty
  type checked_ctx

  type expr =
    | Var of Var.t
    | Coh of checked_coh * checked_sub
    | App of t * checked_sub

  and t

  val typ : t -> checked_ty
  val ty : t -> (checked_coh, t) pty
  val checked_ty : t -> checked_ty
  val forget : t -> (checked_coh, t) ptm
  val constr : t -> (checked_coh, t) pconstr
  val ctx : t -> (checked_coh, t) pctx
  val name : t -> string option
  val full_name : t -> string option
  val func_data : t -> (Var.t * int) list list option
  val of_coh : checked_coh -> t
  val preimage : t -> checked_sub -> t
  val develop : t -> (checked_coh, t) ptm
  val pp_data : t -> pp_data option
  val to_string : t -> string
  val is_equal : t -> t -> bool
  val apply_sub : t -> checked_sub -> t
  val to_var : t -> Var.t
  val expr : t -> expr

  val check_in_ctx :
    checked_ctx -> ?ty:checked_ty -> ?name:pp_data -> (checked_coh, t) ptm -> t

  val check :
    (checked_coh, t) pctx ->
    ?ty:(checked_coh, t) pty ->
    ?name:pp_data ->
    (checked_coh, t) ptm ->
    t

  val apply :
    ((checked_coh, t) pctx -> (checked_coh, t) pctx) ->
    ((checked_coh, t) ptm -> (checked_coh, t) ptm) ->
    (pp_data -> pp_data) ->
    t ->
    t * (checked_coh, t) psub
end

module type CohS = sig
  type t
  type innertm
  type checked_ps
  type checked_tm
  type checked_ty

  val ps : t -> checked_ps
  val forget : t -> ps * (t, checked_tm) pty * pp_data
  val suspend : t -> t
  val is_equal : t -> t -> bool
  val check_equal : t -> t -> unit
  val is_inv : t -> bool
  val to_string : ?unroll:bool -> t -> string
  val dim : t -> int
  val src : t -> (t, checked_tm) ptm
  val tgt : t -> (t, checked_tm) ptm
  val check : ps -> (t, checked_tm) pty -> pp_data -> t
  val ty : t -> checked_ty

  val check_noninv :
    ps -> (t, checked_tm) ptm -> (t, checked_tm) ptm -> pp_data -> t

  val check_inv :
    ps -> (t, checked_tm) ptm -> (t, checked_tm) ptm -> pp_data -> t

  val noninv_srctgt :
    t -> (t, checked_tm) ptm * (t, checked_tm) ptm * (t, checked_tm) pty

  val func_data : t -> (Var.t * int) list list

  val apply_ps :
    (ps -> ps) ->
    ((t, checked_tm) pty -> (t, checked_tm) pty) ->
    (pp_data -> pp_data) ->
    t ->
    t

  val apply :
    ((t, checked_tm) pctx -> (t, checked_tm) pctx) ->
    ((t, checked_tm) pty -> (t, checked_tm) pty) ->
    (pp_data -> pp_data) ->
    t ->
    t * (t, checked_tm) psub
end

module type TyS = sig
  type checked_tm
  type checked_coh
  type checked_ctx
  type checked_sub
  type t
  type expr = Obj | Arr of t * checked_tm * checked_tm

  val check : checked_ctx -> (checked_coh, checked_tm) pty -> t
  val apply_sub : t -> checked_sub -> t
  val ctx : t -> checked_ctx
  val check_equal : t -> t -> unit
  val morphism : checked_tm -> checked_tm -> t
  val to_string : t -> string
  val dim : t -> int
  val is_equal : t -> t -> bool
  val forget : t -> (checked_coh, checked_tm) pty
  val expr : t -> expr

  val check_with_ctx :
    (checked_coh, checked_tm) pctx -> (checked_coh, checked_tm) pty -> t
end

module type PSS = sig
  type t = ps
  type inner_ctx
  type checked_sub

  val to_string : t -> string
  val mk : inner_ctx -> t
  val source : t -> checked_sub
  val target : t -> checked_sub
  val bdry : t -> t
  val is_equal : t -> t -> bool
end

module type CtxS = sig
  type checked_ty
  type checked_coh
  type checked_tm
  type checked_ps

  type t = private {
    c : (Common.Var.t * checked_ty) list;
    unchecked : (checked_coh, checked_tm) pctx;
  }

  val check : (checked_coh, checked_tm) pctx -> t
  val to_string : t -> string
  val forget : t -> (checked_coh, checked_tm) pctx
  val is_equal : t -> t -> bool
  val check_equal : t -> t -> unit
  val ty_var : t -> Var.t -> checked_ty
  val domain : t -> Var.t list
  val of_ps : checked_ps -> t
  val check_notin : t -> Var.t -> unit
  val extend : t -> expl:bool -> Var.t -> (checked_coh, checked_tm) pty -> t
  val empty : unit -> t
end

module type SubS = sig
  type checked_tm
  type checked_ctx
  type checked_coh

  type t = private {
    list : checked_tm list;
    src : checked_ctx;
    tgt : checked_ctx;
    unchecked : (checked_coh, checked_tm) psub;
  }

  val check : checked_ctx -> (checked_coh, checked_tm) psub -> checked_ctx -> t

  val check_to_ps :
    checked_ctx -> (checked_coh, checked_tm) psub_ps -> Common.ps -> t

  val forget : t -> (checked_coh, checked_tm) psub
  val src : t -> checked_ctx
  val tgt : t -> checked_ctx
end
