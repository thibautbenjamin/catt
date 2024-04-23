open Common
module M (S : StrictnessLv)
= struct
  module type UnifSig =
  sig
    open Kernel.M(S)
    open Unchecked_types

    val ctx : ctx -> meta_ctx -> ctx
    val ty : ctx -> meta_ctx -> ty -> ctx * ty
    val tm : ctx -> meta_ctx -> tm -> ctx * tm
  end

  module Kernel = Kernel.M(S)
  module Unchecked = Kernel.Unchecked
  module Translate_raw = Translate_raw.M(S)
  module Infer_suspension = Infer_suspension.M(S)

  let unif_module =
    match S.lv with
    | Wk -> (module Unif_wk.M(S) : UnifSig)
    | Su -> (module Unif_su.M(S) : UnifSig)

  module Unif = (val unif_module)

  let ctx c =
    let c,meta_ctx = Translate_raw.ctx c in
    Io.info ~v:2
      (lazy (Printf.sprintf "elaborating context %s" (Unchecked.ctx_to_string c)));
    let c = Unif.ctx c meta_ctx in
    Io.info ~v:4
      (lazy (Printf.sprintf "elaborated context:%s" (Unchecked.ctx_to_string c)));
    c

  let preprocess_ty ctx ty =
    let ty = Raw.remove_let_ty ty in
    if !Settings.implicit_suspension then
      Infer_suspension.ty ctx ty
    else ty

  let preprocess_tm ctx tm =
    let tm = Raw.remove_let_tm tm in
    if !Settings.implicit_suspension then
      Infer_suspension.tm ctx tm
    else tm

  let rec preprocess_ctx = function
    | [] -> []
    | (v,t)::c ->
      let c = preprocess_ctx c in
      (v, preprocess_ty c t)::c


  let ty c ty =
    try
      let c = preprocess_ctx c in
      let ty = preprocess_ty c ty in
      let c = ctx c in
      let ty, meta_ctx = Translate_raw.ty ty in
      Unif.ty c meta_ctx ty
    with
      Error.UnknownId(s) -> raise (Error.unknown_id s)

  let tm c tm =
    try
      let c = preprocess_ctx c in
      let tm = preprocess_tm c tm in
      let c = ctx c in
      let tm, meta_ctx = Translate_raw.tm tm in
      Unif.tm c meta_ctx tm
    with
      Error.UnknownId(s) -> raise (Error.unknown_id s)

  let ty_in_ps ps t =
    try
      let ps = preprocess_ctx ps in
      let t = preprocess_ty ps t in
      let ps = ctx ps in
      let t, meta_ctx = Translate_raw.ty t in
      let t = Unif.ty ps meta_ctx t
      in
      let _, names,_ = Unchecked.db_levels ps in
      Kernel.ctx_to_ps ps,
      Unchecked.rename_ty (snd t) names
    with
      Error.UnknownId(s) -> raise (Error.unknown_id s)


end
