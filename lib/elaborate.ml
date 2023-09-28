open Std
open Kernel
open Kernel.Unchecked_types

exception NotUnifiable of string * string

module Queue = Base.Queue

module Constraints = struct
  type t = {ty : (ty * ty) Queue.t; tm : (tm * tm) Queue.t}

  let create () = {ty = Queue.create(); tm = Queue.create()}

  let _to_string c =
    let print_ty =
      Queue.fold
        c.ty
        ~init:""
        ~f:(fun s (ty1,ty2) ->
            Printf.sprintf "%s (%s = %s)"
              s
              (Unchecked.ty_to_string ty1)
              (Unchecked.ty_to_string ty2))
    in
    let print_tm =
      Queue.fold
        c.tm
        ~init:""
        ~f:(fun s (tm1, tm2) ->
            Printf.sprintf "%s (%s = %s)"
              s
              (Unchecked.tm_to_string tm1)
              (Unchecked.tm_to_string tm2))
    in
    Printf.sprintf "[%s] [%s]" print_ty print_tm

  let rec  unify_ty cst ty1 ty2 =
    match ty1, ty2 with
    | Obj, Obj -> ()
    | Arr(a1,u1,v1), Arr(a2,u2,v2) ->
      unify_ty cst a1 a2;
      unify_tm cst u1 u2;
      unify_tm cst v1 v2
    | Meta_ty _, _
    | _, Meta_ty _ -> Queue.enqueue  cst.ty (ty1, ty2)
    | Arr(_,_,_), Obj
    | Obj, Arr(_,_,_) ->
      raise (NotUnifiable (Unchecked.ty_to_string ty1, Unchecked.ty_to_string ty2))
  and unify_tm cst tm1 tm2 =
    match tm1, tm2 with
    | Var v1, Var v2 when v1 = v2 -> ()
    | Coh(coh1,s1), Coh(coh2,s2) ->
      begin
        try
          Unchecked.check_equal_coh coh1 coh2;
          unify_sub cst s1 s2
        with Invalid_argument _ ->
          raise (NotUnifiable (Unchecked.coh_to_string coh1, Unchecked.coh_to_string coh2))
      end
    | Meta_tm _, _
    | _, Meta_tm _ -> Queue.enqueue cst.tm (tm1, tm2)
    | Var _, Coh _ | Coh _, Var _ | Var _, Var _ ->
      raise (NotUnifiable (Unchecked.tm_to_string tm1, Unchecked.tm_to_string tm2))
  and unify_sub cst s1 s2 =
    match s1, s2 with
    | [],[] -> ()
    | t1::s1, t2::s2 -> unify_tm cst t1 t2; unify_sub cst s1 s2
    | [], _::_ | _::_,[] ->
      raise (NotUnifiable (Unchecked.sub_ps_to_string s1, Unchecked.sub_ps_to_string s2))

type mgu = { uty : (int * ty) list; utm : (int * tm) list }

let  combine_mgu m1 m2 =
  {uty = List.append m1.uty m2.uty;
   utm = List.append m1.utm m2.utm}

let rec ty_replace_meta_ty (i,ty') ty =
  match ty with
  | Meta_ty j when i = j -> ty'
  | Meta_ty _ -> ty
  | Obj -> Obj
  | Arr(a,u,v) ->
    Arr (ty_replace_meta_ty (i,ty') a, u, v)

let rec tm_replace_meta_tm (i,tm') tm =
  match tm with
  | Meta_tm j when i = j -> tm'
  | Meta_tm _ -> tm
  | Var v -> Var v
  | Coh(c,s) -> Coh(c, List.map (tm_replace_meta_tm (i,tm')) s)

let rec ty_replace_meta_tm (i,tm') ty =
  match ty with
  | Meta_ty _ -> ty
  | Obj -> Obj
  | Arr(a,u,v) ->
    Arr (ty_replace_meta_tm (i,tm') a,
         tm_replace_meta_tm (i,tm') u,
         tm_replace_meta_tm (i,tm') v)

let queue_map_both f =
  Queue.map ~f:(fun (x,y) -> (f x, f y))

let cst_replace_ty (i,ty) c =
  {ty = queue_map_both (ty_replace_meta_ty (i,ty)) c.ty; tm = c.tm}

let cst_replace_tm (i,tm) c =
  let ty_replace = ty_replace_meta_tm (i,tm) in
  let tm_replace = tm_replace_meta_tm (i,tm) in
  {ty = queue_map_both ty_replace c.ty;
   tm = queue_map_both tm_replace c.tm}

let mgu_replace_ty (i,ty) l =
  {uty = List.map_right (ty_replace_meta_ty (i,ty)) l.uty; utm = l.utm}

let mgu_replace_tm (i,tm) l =
  let ty_replace = ty_replace_meta_tm (i,tm) in
  let tm_replace = tm_replace_meta_tm (i,tm) in
  {uty = List.map_right ty_replace l.uty;
   utm = List.map_right tm_replace l.utm}

let substitute_ty l ty =
  let ty =
    List.fold_left (fun ty (i,tm) -> ty_replace_meta_tm (i,tm) ty) ty l.utm
  in
  List.fold_left (fun ty (i,ty') -> ty_replace_meta_ty (i,ty') ty) ty l.uty

let substitute_tm l tm =
  List.fold_left (fun tm (i,tm') -> tm_replace_meta_tm (i,tm') tm) tm l.utm

  (* Martelli-Montanari algorithm *)
  let resolve_one_step c knowns =
    match Queue.dequeue c.ty with
    | Some (ty1,ty2) ->
      begin
        match ty1,ty2 with
        | Meta_ty i, Meta_ty j when i = j -> c, knowns
        | Meta_ty i, ty | ty, Meta_ty i ->
          let c = cst_replace_ty (i,ty) c in
          let knowns = mgu_replace_ty (i,ty) knowns in
          c,{uty = (i,ty)::knowns.uty; utm = knowns.utm}
        | ty1, ty2 ->
          unify_ty c ty1 ty2;
          c, knowns
      end
    | None ->
      match Queue.dequeue c.tm with
      | Some (tm1,tm2) ->
        begin
          match tm1,tm2 with
          | Meta_tm i, Meta_tm j when i = j -> c, knowns
          | Meta_tm i, tm | tm, Meta_tm i ->
            let c = cst_replace_tm (i,tm) c in
            let knowns = mgu_replace_tm (i,tm) knowns in
            c,{uty = knowns.uty; utm = (i,tm)::knowns.utm}
          | tm1, tm2 ->
            unify_tm c tm1 tm2;
            c, knowns
        end
      | None -> Error.fatal "resolving empty constraints"

  let resolve c =
    let rec aux c knowns =
      if Queue.is_empty c.tm && Queue.is_empty c.ty then knowns
      else
        let c,knowns = resolve_one_step c knowns in
        aux c knowns
    in aux c {uty = []; utm = []}
end

module Constraints_typing = struct

  let rec tm ctx meta_ctx t cst =
    Io.info ~v:4
      (lazy
        (Printf.sprintf
           "constraint typing term %s in ctx %s, meta_ctx %s"
           (Unchecked.tm_to_string t)
           (Unchecked.ctx_to_string ctx)
           (Unchecked.meta_ctx_to_string meta_ctx)));
      match t with
    | Var v -> t, fst (List.assoc v ctx)
    | Meta_tm i -> t, List.assoc i meta_ctx
    | Coh(c,s)-> let ps,ty,_ = Unchecked.coh_data c in
      let s,tgt = Unchecked.sub_ps_to_sub s ps in
      let s = sub ctx meta_ctx s tgt cst in
      Coh(c,(List.map snd s)), Unchecked.ty_apply_sub ty s
  and sub src meta_ctx s tgt cst =
    Io.info ~v:4
      (lazy
        (Printf.sprintf
           "constraint typing substitution %s in ctx %s, \
            target %s, meta_ctx %s"
           (Unchecked.sub_to_string s)
           (Unchecked.ctx_to_string src)
           (Unchecked.ctx_to_string tgt)
           (Unchecked.meta_ctx_to_string meta_ctx)));
    match s,tgt with
    | [],[] -> []
    | (x,u)::s, (_,(t,_))::c ->
      let u,ty= tm src meta_ctx u cst in
      let s = sub src meta_ctx s c cst in
      Constraints.unify_ty cst ty (Unchecked.ty_apply_sub t s);
      (x,u)::s
    |[],_::_ | _::_, [] -> Error.fatal "wrong number of arguments"
  and ty ctx meta_ctx t cst =
    Io.info ~v:4
      (lazy
        (Printf.sprintf
           "constraint typing type %s in ctx %s, meta_ctx %s"
           (Unchecked.ty_to_string t)
           (Unchecked.ctx_to_string ctx)
           (Unchecked.meta_ctx_to_string meta_ctx)));
    match t with
    | Obj -> Obj
    | Arr(a,u,v) ->
      let u, tu = tm ctx meta_ctx u cst in
      let v, tv = tm ctx meta_ctx v cst in
      let a = ty ctx meta_ctx a cst in
      Constraints.unify_ty cst a tu;
      Constraints.unify_ty cst a tv;
      Arr (a,u,v)
    | Meta_ty _ -> t

  let rec ctx c meta_ctx =
    match c with
    | [] -> [], {Constraints.uty=[]; utm=[]}
    | (x,(t,expl))::c ->
      let c,known_mgu = ctx c meta_ctx in
      let t = Constraints.substitute_ty known_mgu t in
      let cstt = Constraints.create () in
      let t = ty c meta_ctx t cstt in
      let new_mgu = Constraints.resolve cstt in
      let t = Constraints.substitute_ty new_mgu t in
      (x,(t,expl))::c,
      Constraints.combine_mgu known_mgu new_mgu
end

let ctx c =
  let c,meta_ctx = Translate_raw.ctx c in
  let c,_ = Constraints_typing.ctx c meta_ctx in
  Io.info ~v:4
    (lazy
      (Printf.sprintf
         "elaborated context:%s" (Unchecked.ctx_to_string c)));
  c

let preprocess_ty ctx ty =
  let ty = Raw.remove_let_ty ty in
  if !Settings.implicit_suspension then
    Raw.infer_susp_ty ctx ty
  else ty

let preprocess_tm ctx tm =
  let tm = Raw.remove_let_tm tm in
  if !Settings.implicit_suspension then
    Raw.infer_susp_tm ctx tm
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
    let cst = Constraints.create () in
    try
      let ty = Constraints_typing.ty c meta_ctx ty cst in
      c,Constraints.substitute_ty (Constraints.resolve cst) ty
    with
    | NotUnifiable(x,y) -> Error.unsatisfiable_constraints
                             ("type: "^(Unchecked.ty_to_string ty))
                             (Printf.sprintf "could not unify %s and %s" x y)
  with
    Error.UnknownId(s) -> raise (Error.unknown_id s)

let tm c tm =
  try
    let c = preprocess_ctx c in
    let tm = preprocess_tm c tm in
    let c = ctx c in
    let tm, meta_ctx = Translate_raw.tm tm in
    let cst = Constraints.create () in
    try
      let tm,_ = Constraints_typing.tm c meta_ctx tm cst in
      Io.info ~v:4
        (lazy
          (Printf.sprintf
             "inferred constraints:%s" (Constraints._to_string cst)));
      c,Constraints.substitute_tm (Constraints.resolve cst) tm
    with
    | NotUnifiable(x,y) -> Error.unsatisfiable_constraints
                             ("term: "^(Unchecked.tm_to_string tm))
                             (Printf.sprintf "could not unify %s and %s" x y)
  with
    Error.UnknownId(s) -> raise (Error.unknown_id s)

let ty_in_ps ps t =
  try
    let ps = preprocess_ctx ps in
    let t = preprocess_ty ps t in
    let ps = ctx ps in
    let t, meta_ctx = Translate_raw.ty t in
    let cst = Constraints.create () in
    let t =
      try
        let t = Constraints_typing.ty ps meta_ctx t cst in
        Io.info ~v:4
          (lazy
            (Printf.sprintf
               "inferred constraints:%s" (Constraints._to_string cst)));
        Constraints.substitute_ty (Constraints.resolve cst) t
      with
      | NotUnifiable(x,y) -> Error.unsatisfiable_constraints
                               ("type: "^(Unchecked.ty_to_string t))
                               (Printf.sprintf "could not unify %s and %s" x y)
    in
    let _, names,_ = Unchecked.db_levels ps in
    Kernel.PS.(forget (mk (Kernel.Ctx.check ps))),
    Unchecked.rename_ty t names
  with
    Error.UnknownId(s) -> raise (Error.unknown_id s)
