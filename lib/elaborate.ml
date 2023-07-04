open Common

module Constraints = struct
  type t = {ty : (int * ty) list; tm : (int * tm) list}

  let empty = {ty = []; tm = []}

  let rec combine c1 c2 =
    let add_ty (i,ty) c =
      match List.assoc_opt i c.ty with
      | None -> {ty = (i,ty)::c.ty; tm = c.tm}
      | Some t -> combine (unify_ty ty t) c
    in
    let add_tm (i,tm) c =
      match List.assoc_opt i c.tm with
      | None -> {ty = c.ty; tm = (i,tm) :: c.tm}
      | Some t -> combine (unify_tm tm t) c
    in
    let c1 =
      List.fold_left (fun c (i,ty) -> add_ty (i,ty) c) c2 c1.ty
    in List.fold_left (fun c (i,tm) -> add_tm (i,tm) c) c2 c1.tm

and unify_ty ty1 ty2 =
  match ty1, ty2 with
  | Obj, Obj -> empty
  | Arr(a1,u1,v1), Arr(a2,u2,v2) ->
    combine (unify_ty a1 a2)
      (combine
         (unify_tm u1 u2)
         (unify_tm v1 v2))
  | Meta_ty i, ty2 -> {ty = [(i, ty2)]; tm = []}
  | ty1, Meta_ty i -> {ty = [(i, ty1)]; tm = []}
  | Arr(_,_,_), Obj | Obj, Arr(_,_,_) ->
    raise (Error.NotUnifiable
             (Unchecked.ty_to_string ty1, Unchecked.ty_to_string ty2))
and unify_tm tm1 tm2 =
  match tm1, tm2 with
  | Var v1, Var v2 when v1 = v2 -> empty
  | Coh(ps1,t1,s1), Coh(ps2,t2,s2) when ps1 = ps2 && t1 = t2 ->
    unify_sub s1 s2
  | Meta_tm i, tm2 -> {ty = []; tm = [(i, tm2)]}
  | tm1, Meta_tm i -> {ty = []; tm = [(i, tm1)]}
  | Var _, Coh _ | Coh _, Var _ | Var _, Var _ | Coh _ , Coh _ ->
    raise (Error.NotUnifiable
             (Unchecked.tm_to_string tm1, Unchecked.tm_to_string tm2))
and unify_sub s1 s2 =
  match s1, s2 with
  | [],[] -> empty
  | t1::s1, t2::s2 -> combine (unify_tm t1 t2) (unify_sub s1 s2)
  | [], _::_ | _::_,[] ->
    raise (Error.NotUnifiable
             (Unchecked.sub_ps_to_string s1, Unchecked.sub_ps_to_string s2))

  (* constraint solving algorithm*)
  let resolve c = c
end

let rec replace_meta_ty (l : Constraints.t) ty =
  match ty with
  | Meta_ty i -> List.assoc i l.ty
  | Obj -> Obj
  | Arr(a,u,v) ->
    Arr (replace_meta_ty l a, replace_meta_tm l u, replace_meta_tm l v)
and replace_meta_tm l tm =
  match tm with
  | Meta_tm i -> List.assoc i l.tm
  | Var v -> Var v
  | Coh(ps,t,s) -> Coh(ps,t, List.map (replace_meta_tm l) s)

let meta_ty ctx ty =
  let ctx = Kernel.Ctx.check ctx in
  match ty with
  | Obj -> Obj
  | Arr(a,u,v) ->
    let tu = Kernel.(Ty.forget (Tm.(typ (check ctx u)))) in
    let tv = Kernel.(Ty.forget (Tm.(typ (check ctx u)))) in
    let cst =
      Constraints.combine
        (Constraints.unify_ty a tu)
        (Constraints.unify_ty a tv)
    in
    let a = replace_meta_ty (Constraints.resolve cst) a in
    Arr(a,u,v)
  | Meta_ty _ -> assert false

let ctx c =
  let c = Translate_raw.ctx c in
  let rec close_metas c =
    match c with
    | [] -> []
    | (x,(t,expl))::c ->
      let c = close_metas c in
      (x, (meta_ty c t, expl))::c
  in close_metas c

let ty c ty =
  let ty = Syntax.remove_let_ty ty in
  meta_ty c (Translate_raw.ty ty)

let tm tm =
  let tm = Syntax.remove_let_tm tm in
  Translate_raw.tm tm

let ty_in_ps ps t =
  let t = Syntax.remove_let_ty t in
  let t = Translate_raw.ty t in
  let ps = ctx ps in
  let ps, names,_ = Unchecked.db_levels ps in
  let db_t = Unchecked.rename_ty t names in
  meta_ty ps db_t

let ps p =
  let p = ctx p in
  Kernel.PS.(forget (mk (Kernel.Ctx.check p)))
