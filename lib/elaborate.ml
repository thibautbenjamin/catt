open Common

module Constraints = struct
  type t = {ty : (int * ty) list; tm : (int * tm) list}

  let _to_string c =
    let rec print_ty =
      function
      | [] -> ""
      | (i,t)::c ->
        Printf.sprintf "%s (_ty%i = %s)"
          (print_ty c)
          i
          (Unchecked.ty_to_string t)
    in
    let rec print_tm =
      function
      | [] -> ""
      | (i,t)::c ->
        Printf.sprintf "%s (_tm%i = %s)"
          (print_tm c)
          i
          (Unchecked.tm_to_string t)
    in
    Printf.sprintf "[%s] [%s]" (print_ty c.ty) (print_tm c.tm)

  let empty = {ty = []; tm = []}

  let rec combine c1 c2 =
    let add_ty (i,ty) c =
      match List.assoc_opt i c.ty with
      | None -> {ty = (i,ty)::c.ty; tm = c.tm}
      | Some t when t = Meta_ty i -> c
      | Some t -> combine (unify_ty ty t) c
    in
    let add_tm (i,tm) c =
      match List.assoc_opt i c.tm with
      | None -> {ty = c.ty; tm = (i,tm) :: c.tm}
      | Some t when t = Meta_tm i -> c
      | Some t -> combine (unify_tm tm t) c
    in
    let rec combine_list c1 c2 =
      match c1.ty, c1.tm with
      | [], [] -> c2
      | (i,ty)::cty, tm -> combine_list {ty = cty; tm} (add_ty (i,ty) c2)
      | [], (i,tm)::ctm -> combine_list {ty = []; tm = ctm} (add_tm (i,tm) c2)
    in combine_list c1 c2
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

  let rec combine_all = function
    | [] -> empty
    | h::csts -> combine h (combine_all csts)

  let rec substitute_ty l ty =
    match ty with
    | Meta_ty i -> List.assoc i l.ty
    | Obj -> Obj
    | Arr(a,u,v) ->
      Arr (substitute_ty l a, substitute_tm l u, substitute_tm l v)
  and substitute_tm l tm =
    match tm with
    | Meta_tm i -> List.assoc i l.tm
    | Var v -> Var v
    | Coh(ps,t,s) -> Coh(ps,t, List.map (substitute_tm l) s)

  let resolve c =
    {ty = List.map (fun (i,ty) -> i, substitute_ty c ty) c.ty;
     tm = List.map (fun (i,ty) -> i, substitute_tm c ty) c.tm}
end

module Constraints_typing = struct

  let rec tm ctx meta_ctx t =
    Io.info ~v:4 "constraint typing term %s in ctx %s, meta_ctx %s"
      (Unchecked.tm_to_string t)
      (Unchecked.ctx_to_string ctx)
      (Unchecked.meta_ctx_to_string meta_ctx);
      match t with
    | Var v -> fst (List.assoc v ctx), Constraints.empty
    | Meta_tm i -> List.assoc i meta_ctx, Constraints.empty
    | Coh(ps,t,s) ->
      let s, ps = Unchecked.sub_ps_to_sub s ps in
      let cst = sub ctx meta_ctx s ps in
      Unchecked.ty_apply_sub t s, cst
  and sub src meta_ctx s tgt =
    match s,tgt with
    | [],[] -> Constraints.empty
    | (_,u)::s, (_,(t,_))::c ->
      let cstt = ty tgt meta_ctx t in
      let ty,cstu = tm src meta_ctx u in
      Constraints.combine_all
        [cstt;
          cstu;
         Constraints.unify_ty ty (Unchecked.ty_apply_sub t s);
         sub src meta_ctx s c]
    |[],_::_ | _::_, [] -> assert false
  and ty ctx meta_ctx ty =
    Io.info ~v:4 "constraint typing type %s in ctx %s, meta_ctx %s"
      (Unchecked.ty_to_string ty)
      (Unchecked.ctx_to_string ctx)
      (Unchecked.meta_ctx_to_string meta_ctx);
    match ty with
    | Obj -> Constraints.empty
    | Arr(a,u,v) ->
      let tu, cstu = tm ctx meta_ctx u in
      let tv, cstv = tm ctx meta_ctx v in
        Constraints.combine_all
          [cstu;
           cstv;
           Constraints.unify_ty a tu;
           Constraints.unify_ty a tv]
    | Meta_ty _ -> Constraints.empty

  let rec ctx c meta_ctx =
    match c with
    | [] -> Constraints.empty
    | (_,(t,_))::c ->
      Constraints.combine
        (ty c meta_ctx t)
        (ctx c meta_ctx)
end

let ctx c =
  let c,meta_ctx = Translate_raw.ctx c in
  let cst = Constraints_typing.ctx c meta_ctx in
  let cst = Constraints.resolve cst in
  List.map (fun (x,(t,expl)) -> (x,(Constraints.substitute_ty cst t, expl))) c

let ty c ty =
  let ty = Syntax.remove_let_ty ty in
  let ty, meta_ctx = Translate_raw.ty ty in
  let cst = Constraints_typing.ty c meta_ctx ty in
  Constraints.substitute_ty (Constraints.resolve cst) ty

let tm c tm =
  let tm = Syntax.remove_let_tm tm in
  let tm, meta_ctx = Translate_raw.tm tm in
  let _,cst = Constraints_typing.tm c meta_ctx tm in
  Constraints.substitute_tm (Constraints.resolve cst) tm

let ty_in_ps ps t =
  let t = Syntax.remove_let_ty t in
  let t, meta_ctx = Translate_raw.ty t in
  let cst = Constraints_typing.ty ps meta_ctx t in
  let t = Constraints.substitute_ty (Constraints.resolve cst) t in
  let _, names,_ = Unchecked.db_levels ps in
  Unchecked.rename_ty t names

let ps p =
  Kernel.PS.(forget (mk (Kernel.Ctx.check p)))
