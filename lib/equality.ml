open Std
open Common
open Unchecked_types

module Equality (CohT : sig
  type t
end) (TmT : sig
  type t
end) =
struct
  open Unchecked_types (CohT) (TmT)

  module Make (Coh : sig
    val forget : CohT.t -> ps * Unchecked_types(CohT)(TmT).ty * pp_data
    val to_string : CohT.t -> string
    val func_data : CohT.t -> (Var.t * int) list list
    val check_equal : CohT.t -> CohT.t -> unit
    val check : ps -> ty -> pp_data -> CohT.t
  end) (Tm : sig
    val func_data : TmT.t -> (Var.t * int) list list
    val develop : TmT.t -> Unchecked_types(CohT)(TmT).tm
    val name : TmT.t -> string

    val apply :
      (Unchecked_types(CohT)(TmT).ctx -> Unchecked_types(CohT)(TmT).ctx) ->
      (Unchecked_types(CohT)(TmT).tm -> Unchecked_types(CohT)(TmT).tm) ->
      (pp_data -> pp_data) ->
      TmT.t ->
      TmT.t * Unchecked_types(CohT)(TmT).sub
  end) =
  struct
    module P = Printing.Printing (CohT) (TmT)
    module Printing = P.Make (Coh) (Tm)
    module U = Unchecked.Unchecked (CohT) (TmT)
    module Unchecked = U.Make (Coh) (Tm)

    let rec check_equal_ps ps1 ps2 =
      match (ps1, ps2) with
      | Br [], Br [] -> ()
      | Br (ps1 :: l1), Br (ps2 :: l2) ->
          check_equal_ps ps1 ps2;
          List.iter2 check_equal_ps l1 l2
      | Br [], Br (_ :: _) | Br (_ :: _), Br [] ->
          raise
            (NotEqual (Printing.ps_to_string ps1, Printing.ps_to_string ps2))

    let rec check_equal_ty ty1 ty2 =
      match (ty1, ty2) with
      | Meta_ty i, Meta_ty j ->
          if i <> j then raise (NotEqual (string_of_int i, string_of_int j))
      | Obj, Obj -> ()
      | Arr (ty1, u1, v1), Arr (ty2, u2, v2) ->
          check_equal_ty ty1 ty2;
          check_equal_tm u1 u2;
          check_equal_tm v1 v2
      | Obj, Arr _
      | Arr _, Obj
      | Meta_ty _, Obj
      | Meta_ty _, Arr _
      | Obj, Meta_ty _
      | Arr _, Meta_ty _ ->
          raise
            (NotEqual (Printing.ty_to_string ty1, Printing.ty_to_string ty2))

    and check_equal_tm tm1 tm2 =
      match (tm1, tm2) with
      | Var v1, Var v2 -> Var.check_equal v1 v2
      | Meta_tm i, Meta_tm j ->
          if i <> j then raise (NotEqual (string_of_int i, string_of_int j))
      | Coh (coh1, s1), Coh (coh2, s2) ->
          Coh.check_equal coh1 coh2;
          check_equal_sub_ps s1 s2
      (* Define check_equal_sub and Tm.develop *)
      | App (t1, s1), App (t2, s2) when t1 == t2 -> check_equal_sub s1 s2
      | App (t, s), ((Coh _ | App _ | Var _) as tm2)
      | ((Coh _ | Var _) as tm2), App (t, s) ->
          let c = Tm.develop t in
          check_equal_tm (Unchecked.tm_apply_sub c s) tm2
      | Var _, Coh _
      | Coh _, Var _
      | Meta_tm _, Var _
      | Meta_tm _, Coh _
      | Var _, Meta_tm _
      | Coh _, Meta_tm _
      | App _, Meta_tm _
      | Meta_tm _, App _ ->
          raise
            (NotEqual (Printing.tm_to_string tm1, Printing.tm_to_string tm2))

    and check_equal_sub_ps s1 s2 =
      List.iter2 (fun (t1, _) (t2, _) -> check_equal_tm t1 t2) s1 s2

    and check_equal_sub s1 s2 =
      List.iter2 (fun (_, (t1, _)) (_, (t2, _)) -> check_equal_tm t1 t2) s1 s2

    let rec check_equal_ctx ctx1 ctx2 =
      match (ctx1, ctx2) with
      | [], [] -> ()
      | (v1, (t1, _)) :: c1, (v2, (t2, _)) :: c2 ->
          Var.check_equal v1 v2;
          check_equal_ty t1 t2;
          check_equal_ctx c1 c2
      | _ :: _, [] | [], _ :: _ ->
          raise
            (NotEqual (Printing.ctx_to_string ctx1, Printing.ctx_to_string ctx2))

    let check_equal_ty ty1 ty2 =
      if ty1 == ty2 then () else check_equal_ty ty1 ty2

    let check_equal_tm tm1 tm2 =
      if tm1 == tm2 then () else check_equal_tm tm1 tm2

    let check_equal_sub_ps s1 s2 =
      if s1 == s2 then () else check_equal_sub_ps s1 s2

    let check_equal_ctx ctx1 ctx2 =
      if ctx1 == ctx2 then () else check_equal_ctx ctx1 ctx2
  end
end
