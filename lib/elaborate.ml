open Std
open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

exception NotUnifiable of string * string

module Queue = Base.Queue

module Constraints = struct
  type t = { ty : (ty * ty) Queue.t; tm : (tm * tm) Queue.t }

  let create () = { ty = Queue.create (); tm = Queue.create () }

  let _to_string c =
    let print_ty =
      Queue.fold c.ty ~init:"" ~f:(fun s (ty1, ty2) ->
          Printf.sprintf "%s (%s = %s)" s
            (Unchecked.ty_to_string ty1)
            (Unchecked.ty_to_string ty2))
    in
    let print_tm =
      Queue.fold c.tm ~init:"" ~f:(fun s (tm1, tm2) ->
          Printf.sprintf "%s (%s = %s)" s
            (Unchecked.tm_to_string tm1)
            (Unchecked.tm_to_string tm2))
    in
    Printf.sprintf "[%s] [%s]" print_ty print_tm

  let rec unify_ty cst ty1 ty2 =
    match (ty1, ty2) with
    | Obj, Obj -> ()
    | Arr (a1, u1, v1), Arr (a2, u2, v2) ->
        unify_ty cst a1 a2;
        unify_tm cst u1 u2;
        unify_tm cst v1 v2
    | Meta_ty _, _ | _, Meta_ty _ -> Queue.enqueue cst.ty (ty1, ty2)
    | Arr (_, _, _), Obj | Obj, Arr (_, _, _) ->
        raise
          (NotUnifiable (Unchecked.ty_to_string ty1, Unchecked.ty_to_string ty2))

  and unify_tm cst tm1 tm2 =
    match (tm1, tm2) with
    | Meta_tm _, Meta_tm _ when tm1 = tm2 -> ()
    | Meta_tm _, _ | _, Meta_tm _ -> Queue.enqueue cst.tm (tm1, tm2)
    | Var v1, Var v2 when v1 = v2 -> ()
    | Coh (coh1, s1), Coh (coh2, s2) -> (
        try
          Coh.check_equal coh1 coh2;
          unify_sub_ps cst s1 s2
        with Invalid_argument _ ->
          raise (NotUnifiable (Coh.to_string coh1, Coh.to_string coh2)))
    | App (t1,s1), App(t2,s2) when t1 == t2 -> unify_sub cst s1 s2
    | App (t,s) , (App _ | Coh _ as tm2)
    | (Coh _ as tm2), App (t,s) ->
      unify_tm cst (Unchecked.tm_apply_sub (Tm.develop t) s) tm2
    | Var _, Coh _ | Coh _, Var _ | Var _, Var _  | App _, Var _ | Var _, App _ ->
        raise
          (NotUnifiable (Unchecked.tm_to_string tm1, Unchecked.tm_to_string tm2))

  and unify_sub cst s1 s2 =
     match (s1, s2) with
    | [], [] -> ()
    | (_, t1) :: s1, (_, t2) :: s2 ->
        unify_tm cst t1 t2;
        unify_sub cst s1 s2
    | [], _ :: _ | _ :: _, [] ->
        raise
          (NotUnifiable
             (Unchecked.sub_to_string s1, Unchecked.sub_to_string s2))

  and unify_sub_ps cst s1 s2 =
    match (s1, s2) with
    | [], [] -> ()
    | (t1, _) :: s1, (t2, _) :: s2 ->
        unify_tm cst t1 t2;
        unify_sub_ps cst s1 s2
    | [], _ :: _ | _ :: _, [] ->
        raise
          (NotUnifiable
             (Unchecked.sub_ps_to_string s1, Unchecked.sub_ps_to_string s2))

  type mgu = { uty : (int * ty) list; utm : (int * tm) list }

  let combine_mgu m1 m2 =
    { uty = List.append m1.uty m2.uty; utm = List.append m1.utm m2.utm }

  let rec ty_replace_meta_ty (i, ty') ty =
    match ty with
    | Meta_ty j when i = j -> ty'
    | Meta_ty _ -> ty
    | Obj -> Obj
    | Arr (a, u, v) -> Arr (ty_replace_meta_ty (i, ty') a, u, v)

  let rec tm_replace_meta_tm (i, tm') tm =
    match tm with
    | Meta_tm j when i = j -> tm'
    | Meta_tm _ -> tm
    | Var v -> Var v
    | Coh (c, s) ->
        Coh
          ( c,
            List.map (fun (t, expl) -> (tm_replace_meta_tm (i, tm') t, expl)) s
          )
    | App (t, s) ->
      App (t, List.map (fun (x,t) -> (x, tm_replace_meta_tm (i, tm') t)) s)

  let rec ty_replace_meta_tm (i, tm') ty =
    match ty with
    | Meta_ty _ -> ty
    | Obj -> Obj
    | Arr (a, u, v) ->
        Arr
          ( ty_replace_meta_tm (i, tm') a,
            tm_replace_meta_tm (i, tm') u,
            tm_replace_meta_tm (i, tm') v )

  let queue_map_both f = Queue.map ~f:(fun (x, y) -> (f x, f y))

  let cst_replace_ty (i, ty) c =
    { ty = queue_map_both (ty_replace_meta_ty (i, ty)) c.ty; tm = c.tm }

  let cst_replace_tm (i, tm) c =
    let ty_replace = ty_replace_meta_tm (i, tm) in
    let tm_replace = tm_replace_meta_tm (i, tm) in
    { ty = queue_map_both ty_replace c.ty; tm = queue_map_both tm_replace c.tm }

  let mgu_replace_ty (i, ty) l =
    { uty = List.map_right (ty_replace_meta_ty (i, ty)) l.uty; utm = l.utm }

  let mgu_replace_tm (i, tm) l =
    let ty_replace = ty_replace_meta_tm (i, tm) in
    let tm_replace = tm_replace_meta_tm (i, tm) in
    {
      uty = List.map_right ty_replace l.uty;
      utm = List.map_right tm_replace l.utm;
    }

  let substitute_ty l ty =
    let ty =
      List.fold_left (fun ty (i, tm) -> ty_replace_meta_tm (i, tm) ty) ty l.utm
    in
    List.fold_left (fun ty (i, ty') -> ty_replace_meta_ty (i, ty') ty) ty l.uty

  let substitute_tm l tm =
    List.fold_left (fun tm (i, tm') -> tm_replace_meta_tm (i, tm') tm) tm l.utm

  (* Martelli-Montanari algorithm *)
  let resolve_one_step c knowns =
    match Queue.dequeue c.ty with
    | Some (ty1, ty2) -> (
        match (ty1, ty2) with
        | Meta_ty i, Meta_ty j when i = j -> (c, knowns)
        | Meta_ty i, ty | ty, Meta_ty i ->
            let c = cst_replace_ty (i, ty) c in
            let knowns = mgu_replace_ty (i, ty) knowns in
            (c, { uty = (i, ty) :: knowns.uty; utm = knowns.utm })
        | ty1, ty2 ->
            unify_ty c ty1 ty2;
            (c, knowns))
    | None -> (
        match Queue.dequeue c.tm with
        | Some (tm1, tm2) -> (
            match (tm1, tm2) with
            | Meta_tm i, Meta_tm j when i = j -> (c, knowns)
            | Meta_tm i, tm | tm, Meta_tm i ->
                let c = cst_replace_tm (i, tm) c in
                let knowns = mgu_replace_tm (i, tm) knowns in
                (c, { uty = knowns.uty; utm = (i, tm) :: knowns.utm })
            | tm1, tm2 ->
                unify_tm c tm1 tm2;
                (c, knowns))
        | None -> Error.fatal "resolving empty constraints")

  let resolve c =
    let rec aux c knowns =
      if Queue.is_empty c.tm && Queue.is_empty c.ty then knowns
      else
        let c, knowns = resolve_one_step c knowns in
        aux c knowns
    in
    aux c { uty = []; utm = [] }
end

module Constraints_typing = struct
  let rec tm ctx meta_ctx t cst =
    Io.info ~v:5
      (lazy
        (Printf.sprintf "constraint typing term %s in ctx %s, meta_ctx %s"
           (Unchecked.tm_to_string t)
           (Unchecked.ctx_to_string ctx)
           (Unchecked.meta_ctx_to_string meta_ctx)));
    match t with
    | Var v -> (
        try (t, fst (List.assoc v ctx))
        with Not_found ->
          Error.fatal
            (Printf.sprintf "variable %s not found in context" (Var.to_string v))
        )
    | Meta_tm i -> (t, List.assoc i meta_ctx)
    | Coh (c, s) ->
        let ps, ty, _ = Coh.forget c in
        let tgt = Unchecked.ps_to_ctx ps in
        let s1 = Unchecked.sub_ps_to_sub s in
        let s1 = sub ctx meta_ctx s1 tgt cst in
        ( Coh (c, List.map2 (fun (_, t) (_, expl) -> (t, expl)) s1 s),
          Unchecked.ty_apply_sub ty s1 )
    | App (t, s) ->
      let tgt = Tm.ctx t in
      let ty = Ty.forget (Tm.typ t) in
      let s = sub ctx meta_ctx s tgt cst in
      (App (t, s), Unchecked.ty_apply_sub ty s)

  and sub src meta_ctx s tgt cst =
    Io.info ~v:5
      (lazy
        (Printf.sprintf
           "constraint typing substitution %s in ctx %s, target %s, meta_ctx %s"
           (Unchecked.sub_to_string s)
           (Unchecked.ctx_to_string src)
           (Unchecked.ctx_to_string tgt)
           (Unchecked.meta_ctx_to_string meta_ctx)));
    match (s, tgt) with
    | [], [] -> []
    | (x, u) :: s, (_, (t, _)) :: c ->
        let u, ty = tm src meta_ctx u cst in
        let s = sub src meta_ctx s c cst in
        Constraints.unify_ty cst ty (Unchecked.ty_apply_sub t s);
        (x, u) :: s
    | [], _ :: _ | _ :: _, [] -> Error.fatal "wrong number of arguments"

  and ty ctx meta_ctx t cst =
    Io.info ~v:5
      (lazy
        (Printf.sprintf "constraint typing type %s in ctx %s, meta_ctx %s"
           (Unchecked.ty_to_string t)
           (Unchecked.ctx_to_string ctx)
           (Unchecked.meta_ctx_to_string meta_ctx)));
    match t with
    | Obj -> Obj
    | Arr (a, u, v) ->
        let u, tu = tm ctx meta_ctx u cst in
        let v, tv = tm ctx meta_ctx v cst in
        let a = ty ctx meta_ctx a cst in
        Constraints.unify_ty cst a tu;
        Constraints.unify_ty cst a tv;
        Arr (a, u, v)
    | Meta_ty _ -> t

  let tm ctx meta_ctx t cst = fst (tm ctx meta_ctx t cst)

  let rec ctx c meta_ctx =
    match c with
    | [] -> ([], { Constraints.uty = []; utm = [] })
    | (x, (t, expl)) :: c ->
        let c, known_mgu = ctx c meta_ctx in
        let t = Constraints.substitute_ty known_mgu t in
        let cstt = Constraints.create () in
        let t = ty c meta_ctx t cstt in
        let new_mgu = Constraints.resolve cstt in
        let t = Constraints.substitute_ty new_mgu t in
        ((x, (t, expl)) :: c, Constraints.combine_mgu known_mgu new_mgu)
end

let preprocess_ty ctx ty =
  let ty = Raw.remove_let_ty ty in
  if !Settings.implicit_suspension then Raw.infer_susp_ty ctx ty else ty

let preprocess_tm ctx tm =
  let tm = Raw.remove_let_tm tm in
  if !Settings.implicit_suspension then Raw.infer_susp_tm ctx tm else tm

let rec preprocess_ctx = function
  | [] -> []
  | (v, t) :: c ->
      let c = preprocess_ctx c in
      (v, preprocess_ty c t) :: c

let solve_cst ~elab_fn ~print_fn ~kind x =
  let name = kind ^ ": " ^ print_fn x in
  Io.info ~v:2 (lazy (Printf.sprintf "inferring constraints for %s" name));
  try
    let x = elab_fn x in
    Io.info ~v:3 (lazy (Printf.sprintf "%s elaborated to %s" kind (print_fn x)));
    x
  with NotUnifiable (a, b) ->
    Error.unsatisfiable_constraints name
      (Printf.sprintf "could not unify %s and %s" a b)

let ctx c =
  let c, meta_ctx = Translate_raw.ctx c in
  let elab_fn c = fst (Constraints_typing.ctx c meta_ctx) in
  solve_cst ~elab_fn ~print_fn:Unchecked.ctx_to_string ~kind:"context" c

let elab_ty ctx meta_ctx ty =
  let cst = Constraints.create () in
  let x = Constraints_typing.ty ctx meta_ctx ty cst in
  Io.info ~v:4
    (lazy
      (Printf.sprintf "inferred constraints:%s" (Constraints._to_string cst)));
  let x = Constraints.substitute_ty (Constraints.resolve cst) x in
  x

let elab_tm ctx meta_ctx tm =
  let cst = Constraints.create () in
  let x = Constraints_typing.tm ctx meta_ctx tm cst in
  Io.info ~v:4
    (lazy
      (Printf.sprintf "inferred constraints:%s" (Constraints._to_string cst)));
  let x = Constraints.substitute_tm (Constraints.resolve cst) x in
  x

let ty c ty =
  try
    let c = preprocess_ctx c in
    let ty = preprocess_ty c ty in
    let c = ctx c in
    let ty, meta_ctx = Translate_raw.ty ty in
    let elab_fn ty = elab_ty c meta_ctx ty in
    let print_fn = Unchecked.ty_to_string in
    (c, solve_cst ~elab_fn ~print_fn ~kind:"type" ty)
  with Error.UnknownId s -> raise (Error.unknown_id s)

let tm c tm =
  try
    let c = preprocess_ctx c in
    let tm = preprocess_tm c tm in
    let c = ctx c in
    let tm, meta_ctx = Translate_raw.tm tm in
    let elab_fn tm = elab_tm c meta_ctx tm in
    let print_fn = Unchecked.tm_to_string in
    (c, solve_cst ~elab_fn ~print_fn ~kind:"term" tm)
  with Error.UnknownId s -> raise (Error.unknown_id s)

let ty_in_ps ps t =
  try
    let ps = preprocess_ctx ps in
    let t = preprocess_ty ps t in
    let ps = ctx ps in
    let t, meta_ctx = Translate_raw.ty t in
    let t =
      let elab_fn ty = elab_ty ps meta_ctx ty in
      solve_cst ~elab_fn ~print_fn:Unchecked.ty_to_string ~kind:"type" t
    in
    try
      let _, names, _ = Unchecked.db_levels ps in
      ( Kernel.PS.(forget (mk (Kernel.Ctx.check ps))),
        Unchecked.rename_ty t names )
    with
    | Kernel.PS.Invalid -> raise (Error.invalid_ps (Unchecked.ctx_to_string ps))
    | DoubledVar x -> raise (Error.doubled_var (Unchecked.ctx_to_string ps) x)
  with Error.UnknownId s -> raise (Error.unknown_id s)
