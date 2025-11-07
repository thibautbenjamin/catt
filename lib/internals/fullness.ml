open Std
open Common

module type FArgs = sig
  module Theory : Theory.S

  module Coh : sig
    type t
  end

  module Ctx : sig
    type t

    val domain : t -> Var.t list
  end

  module rec Sub : sig
    type t = private {
      list : Tm.t list;
      src : Ctx.t;
      tgt : Ctx.t;
      unchecked : (Coh.t, Tm.t) sub;
    }
  end

  and Ty : sig
    type t = private { c : Ctx.t; e : expr; unchecked : (Coh.t, Tm.t) ty }
    and expr = Obj | Arr of t * Tm.t * Tm.t

    val dim : t -> int
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

    val preimage : t -> Sub.t -> t
  end

  module PS : sig
    type t

    val source : t -> Sub.t
    val target : t -> Sub.t
  end
end

module Make (A : FArgs) = struct
  open A

  type res = Inv | NonInv of Tm.t * Tm.t | No

  let rec tm_free_vars (tm : Tm.t) =
    let fvty = ty_free_vars tm.ty in
    match tm.e with
    | Var x -> x :: fvty
    | Coh (_, sub) | App (_, sub) -> sub_free_vars sub

  and ty_free_vars (ty : Ty.t) =
    match ty.e with
    | Obj -> []
    | Arr (t, u, v) ->
        List.unions [ ty_free_vars t; tm_free_vars u; tm_free_vars v ]

  and sub_free_vars (s : Sub.t) = List.concat (List.map tm_free_vars s.list)

  let ty_contains_all_vars (t : Ty.t) =
    List.included (Ctx.domain t.c) (ty_free_vars t)

  let tm_contains_all_vars (t : Tm.t) =
    List.included (Ctx.domain t.ty.c) (tm_free_vars t)

  let is_inv_dim t =
    match Theory.theory.invertibility with
    | None -> false
    | Some d when d >= Ty.dim t -> false
    | _ -> true

  let check_full_inv t =
    if is_inv_dim t || ty_contains_all_vars t then Inv else No

  let check_full_noninv ps (t : Ty.t) =
    match t.e with
    | Obj -> No
    | Arr (_, src, tgt) -> (
        try
          let src_inclusion = PS.source ps in
          let src = Tm.preimage src src_inclusion in
          if not (tm_contains_all_vars src) then No
          else
            let tgt_inclusion = PS.target ps in
            let tgt = Tm.preimage tgt tgt_inclusion in
            if not (tm_contains_all_vars tgt) then No else NonInv (src, tgt)
        with NotInImage -> No)

  let check ps t =
    match check_full_inv t with
    | Inv -> Inv
    | NonInv _ -> assert false
    | No -> check_full_noninv ps t
end
