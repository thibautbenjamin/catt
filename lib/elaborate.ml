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

  let  combine c1 c2 =
    {ty = List.append c1.ty c2.ty;
     tm = List.append c1.tm c2.tm}

  let rec  unify_ty ty1 ty2 =
    match ty1, ty2 with
    | Obj, Obj -> empty
    | Arr(a1,u1,v1), Arr(a2,u2,v2) ->
      combine (unify_ty a1 a2)
        (combine
           (unify_tm u1 u2)
           (unify_tm v1 v2))
    | Meta_ty i, ty2 -> {ty = [(i, ty2)]; tm = []}
    | ty1, Meta_ty i -> {ty = [(i, ty1)]; tm = []}
    | Arr(_,_,_), Obj ->
      raise Error.NeedSuspension
    | Obj, Arr(_,_,_) ->
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
    | Meta_ty i ->
      begin
        match List.assoc_opt i l.ty with
        | Some a -> a
        | None -> Meta_ty i
      end
    | Obj -> Obj
    | Arr(a,u,v) ->
      Arr (substitute_ty l a, substitute_tm l u, substitute_tm l v)
  and substitute_tm l tm =
    match tm with
    | Meta_tm i ->
      begin
        match List.assoc_opt i l.tm with
        | Some u -> u
        | None -> Meta_tm i
      end
    | Var v -> Var v
    | Coh(ps,t,s) -> Coh(ps,t, List.map (substitute_tm l) s)

  let rec has_no_meta_tm = function
    | Var _ -> true
    | Coh(_,_,s) -> List.for_all (fun tm -> has_no_meta_tm tm) s
    | Meta_tm _ -> false

  let rec has_no_meta_ty = function
    | Obj -> true
    | Arr (a,u,v) -> has_no_meta_ty a && has_no_meta_tm u && has_no_meta_tm v
    | Meta_ty _ -> false

  let resolve c : t =
    let rec select_next_known l knowns =
      match l with
      | [] -> raise Error.CouldNotSolve
      | (i,a) :: l ->
        match List.assoc_opt i knowns with
        | Some b -> a,l,b
        | None -> select_next_known l knowns
    in
    let rec select_next p = function
      | [] -> raise Not_found
      | (i,a) :: l when p a -> (i,a), l
      | x::l -> let (pair,rest) = select_next p l in pair, x::rest
    in
    let resolve_next_ty c knowns =
      try
        let (i,ty), csty = select_next has_no_meta_ty c.ty in
        let tmp_cst = {ty = [(i,ty)]; tm = []} in
        let new_cst =
          {ty = List.map (fun (i,ty) -> i, substitute_ty tmp_cst ty) csty;
           tm = List.map (fun (i,ty) -> i, substitute_tm tmp_cst ty) c.tm}
        in
        let known_ty_cst =
          match List.assoc_opt i knowns.ty with
          | Some t -> Unchecked.check_equal_ty t ty; knowns.ty
          | None -> (i,ty)::knowns.ty
        in
        new_cst,{ty=known_ty_cst; tm=knowns.tm}
      with Not_found ->
        let ty, csty, known_ty = select_next_known c.ty knowns.ty in
        let derived_cst = unify_ty ty known_ty in
        combine derived_cst {ty = csty; tm=c.tm}, knowns
    in
    let resolve_next_tm c knowns =
      try
        let (i,tm), cstm = select_next has_no_meta_tm c.tm in
        let tmp_cst = {tm = [(i,tm)]; ty = []} in
        let new_cst =
          {ty = List.map (fun (i,ty) -> i, substitute_ty tmp_cst ty) c.ty;
           tm = List.map (fun (i,ty) -> i, substitute_tm tmp_cst ty) cstm}
        in
        let known_tm_cst =
          match List.assoc_opt i knowns.tm with
          | Some t -> Unchecked.check_equal_tm t tm; knowns.tm
          | None -> (i,tm)::knowns.tm
        in
        new_cst,{tm=known_tm_cst; ty=knowns.ty}
      with Not_found ->
        let tm, cstm, known_tm = select_next_known c.tm knowns.tm in
        let derived_cst = unify_tm tm known_tm in
        combine derived_cst {tm = cstm; ty=c.ty}, knowns
    in
    let rec exhaust_constraints_tm c res =
      match c.tm with
      | _::_ ->
        let c,res = resolve_next_tm c res in
        exhaust_constraints_tm c res
      | [] -> res,c
    in
    let rec exhaust_constraints_ty c res =
      match c.ty with
      | _::_ ->
        let c,res = resolve_next_ty c res in
        exhaust_constraints_ty c res
      | [] -> res,c
    in
    let tm_solve,c = (exhaust_constraints_tm c empty) in
    fst (exhaust_constraints_ty c tm_solve)
end

module Constraints_typing = struct

  let rec tm ctx meta_ctx t =
    Io.info ~v:4 "constraint typing term %s in ctx %s, meta_ctx %s"
      (Unchecked.tm_to_string t)
      (Unchecked.ctx_to_string ctx)
      (Unchecked.meta_ctx_to_string meta_ctx);
      match t with
    | Var v -> t, fst (List.assoc v ctx), Constraints.empty
    | Meta_tm i -> t, List.assoc i meta_ctx, Constraints.empty
    | Coh(ps,t,s) as tm0 ->
      try
        let s, ps = Unchecked.sub_ps_to_sub s ps in
        let s,cst = sub ctx meta_ctx s ps in
        tm0, Unchecked.ty_apply_sub t s, cst
      with
        Error.NeedSuspension ->
        if !Settings.implicit_suspension then
          let ps = Suspension.ps (Some 1) ps in
          let t = Suspension.ty (Some 1) t in
          let s,meta = Translate_raw.sub_to_suspended s in
          tm ctx (List.append meta meta_ctx) (Coh(ps,t,s))
        else
          raise Error.NotValid
  and sub src meta_ctx s tgt =
    match s,tgt with
    | [],[] -> [], Constraints.empty
    | (x,u)::s, (_,(t,_))::c ->
      let _,cstt = ty tgt meta_ctx t in
      let u,ty,cstu = tm src meta_ctx u in
      let s,csts = sub src meta_ctx s c in
      (x,u)::s,
      Constraints.combine_all
        [cstt;
          cstu;
         Constraints.unify_ty ty (Unchecked.ty_apply_sub t s);
         csts]
    |[],_::_ | _::_, [] -> assert false
  and ty ctx meta_ctx t =
    Io.info ~v:4 "constraint typing type %s in ctx %s, meta_ctx %s"
      (Unchecked.ty_to_string t)
      (Unchecked.ctx_to_string ctx)
      (Unchecked.meta_ctx_to_string meta_ctx);
    match t with
    | Obj -> Obj, Constraints.empty
    | Arr(a,u,v) ->
      let u, tu, cstu = tm ctx meta_ctx u in
      let v, tv, cstv = tm ctx meta_ctx v in
      let a,csta = ty ctx meta_ctx a in
      Arr (a,u,v),
        Constraints.combine_all
          [cstu;
           cstv;
           csta;
           Constraints.unify_ty a tu;
           Constraints.unify_ty a tv]
    | Meta_ty _ -> t, Constraints.empty

  let rec ctx c meta_ctx =
    match c with
    | [] -> [], Constraints.empty
    | (x,(t,expl))::c ->
      let t,cstt = ty c meta_ctx t in
      let c,cstc = ctx c meta_ctx in
      (x,(t,expl))::c,
      Constraints.combine cstc cstt
end

let ctx c =
  let c,meta_ctx = Translate_raw.ctx c in
  let c,cst = Constraints_typing.ctx c meta_ctx in
  Io.info ~v:4 "inferred constraints:%s" (Constraints._to_string cst);
  let cst = Constraints.resolve cst in
  List.map (fun (x,(t,expl)) -> (x,(Constraints.substitute_ty cst t, expl))) c

let ty c ty =
  let ty = Syntax.remove_let_ty ty in
  let ty, meta_ctx = Translate_raw.ty ty in
  let ty,cst = Constraints_typing.ty c meta_ctx ty in
  Constraints.substitute_ty (Constraints.resolve cst) ty

let tm c tm =
  let tm = Syntax.remove_let_tm tm in
  let tm, meta_ctx = Translate_raw.tm tm in
  let tm,_,cst = Constraints_typing.tm c meta_ctx tm in
  Constraints.substitute_tm (Constraints.resolve cst) tm

let ty_in_ps ps t =
  let t = Syntax.remove_let_ty t in
  let t, meta_ctx = Translate_raw.ty t in
  let t,cst = Constraints_typing.ty ps meta_ctx t in
  Io.info ~v:4 "inferred constraints:%s" (Constraints._to_string cst);
  let t = Constraints.substitute_ty (Constraints.resolve cst) t in
  let _, names,_ = Unchecked.db_levels ps in
  Unchecked.rename_ty t names

let ps p =
  Kernel.PS.(forget (mk (Kernel.Ctx.check p)))
