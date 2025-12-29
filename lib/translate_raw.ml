open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)
open Raw_types
open Common

exception WrongNumberOfArguments

let rec head_susp = function
  | VarR _ -> 0
  | Sub (_, _, None, _) -> 0
  | Sub (_, _, Some susp, _) -> susp
  | Op (_, t) | Inverse t | Unit t | ISR (_, t) -> head_susp t
  | Meta | BuiltinR _ | Letin_tm _ -> Error.fatal "ill-formed term"
  | CoindR _ | RecR _ | CanR _ | LIH | RIH ->
      Error.fatal "no need to suspend invertibility structures"

let rec replace_ih v0 v1 tm =
  match tm with
  | LIH -> VarR v0
  | RIH -> VarR v1
  | VarR _ -> tm
  | Sub (tm, sub, susp, f) ->
      Sub
        ( replace_ih v0 v1 tm,
          List.map (fun (t, i) -> (replace_ih v0 v1 t, i)) sub,
          susp,
          f )
  | Op (op, t) -> Op (op, replace_ih v0 v1 t)
  | Inverse t -> Inverse (replace_ih v0 v1 t)
  | Unit t -> Unit (replace_ih v0 v1 t)
  | ISR (inv, t) -> ISR (inv, replace_ih v0 v1 t)
  | CanR (t, tms) -> CanR (replace_ih v0 v1 t, List.map (replace_ih v0 v1) tms)
  | Meta | BuiltinR _ | Letin_tm _ -> Error.fatal "ill-formed term"
  | CoindR _ | RecR _ ->
      Error.fatal "no need to suspend invertibility structures"

(* inductive translation on terms and types without let_in *)
let rec tm t =
  let make_coh coh s susp expl =
    let coh = Suspension.coh susp coh in
    let ps, _, _ = Coh.forget coh in
    let func = find_functorialisation s (Unchecked.ps_to_ctx ps) expl in
    let t = Functorialisation.coh_successively coh func in
    let ctx = Tm.ctx t in
    let s, meta_types = sub s ctx expl in
    (App (t, s), meta_types)
  in
  let make_app tm s susp expl =
    let tm = Suspension.checked_tm susp tm in
    let ctx = Tm.ctx tm in
    let func = find_functorialisation s ctx expl in
    let t = Functorialisation.tm tm func in
    let ctx = Tm.ctx t in
    let s, meta_types = sub s ctx expl in
    (App (t, s), meta_types)
  in
  match t with
  | VarR v -> (Var v, [])
  | Sub (VarR v, s, susp, expl) -> (
      match Environment.val_var v with
      | Coh coh -> make_coh coh s susp expl
      | Tm t ->
          let t = Suspension.checked_tm susp t in
          let c = Tm.ctx t in
          let func = find_functorialisation s c expl in
          let t = Functorialisation.tm t func in
          let c = Tm.ctx t in
          let s, meta_types = sub s c expl in
          (App (t, s), meta_types))
  | Sub (BuiltinR b, s, susp, expl) -> (
      match b with
      | Comp ->
          let coh = Builtin.comp s expl in
          make_coh coh s susp expl
      | Id ->
          let coh = Builtin.id () in
          make_coh coh s susp expl
      | Conecomp (n, k, m) ->
          let tm = Cones.compose n m k in
          make_app tm s susp expl
      | Cylcomp (n, k, m) ->
          let tm = Cylinders.compose n m k in
          make_app tm s susp expl
      | Cylstack n ->
          let tm = Cylinders.stacking n in
          make_app tm s susp expl)
  | Op (l, t) ->
      let offset = head_susp t in
      let t, meta = tm t in
      (Opposite.tm t (List.map (fun x -> x + offset) l), meta)
  | Inverse t ->
      let t, meta_ctx = tm t in
      (Inverse.compute_inverse t, meta_ctx)
  | Unit t ->
      let t, meta_ctx = tm t in
      (Inverse.compute_witness t, meta_ctx)
  | ISR (inv, t) ->
      let t, meta_ctx = tm t in
      (IS (inv, t), meta_ctx)
  | CanR (t, tms) ->
      let t, meta = tm t in
      let rec translate_list meta tms =
        match tms with
        | [] -> ([], meta)
        | t :: tms ->
            let t, meta_t = tm t in
            let tms, meta = translate_list (List.append meta_t meta) tms in
            (t :: tms, meta)
      in
      let tms, meta = translate_list meta tms in
      (Can (t, tms), meta)
  | CoindR (t0, t1, t2, t3, t4, t5, t6) ->
      let t0, meta_0 = tm t0 in
      let t1, meta_1 = tm t1 in
      let t2, meta_2 = tm t2 in
      let t3, meta_3 = tm t3 in
      let t4, meta_4 = tm t4 in
      let t5, meta_5 = tm t5 in
      let t6, meta_6 = tm t6 in
      ( Coind (t0, t1, t2, t3, t4, t5, t6),
        List.concat [ meta_0; meta_1; meta_2; meta_3; meta_4; meta_5; meta_6 ]
      )
  | RecR (t0, t1, t2, t3, t4, t5, t6) ->
      let t0, meta_0 = tm t0 in
      let t1, meta_1 = tm t1 in
      let t2, meta_2 = tm t2 in
      let t3, meta_3 = tm t3 in
      let t4, meta_4 = tm t4 in
      let v0 = Var.fresh () in
      let v1 = Var.fresh () in
      let t5, meta_5 = tm (replace_ih v0 v1 t5) in
      let v2 = Var.fresh () in
      let v3 = Var.fresh () in
      let t6, meta_6 = tm (replace_ih v2 v3 t6) in
      ( Rec (t0, t1, t2, t3, t4, (v0, v1, t5), (v2, v3, t6)),
        List.concat [ meta_0; meta_1; meta_2; meta_3; meta_4; meta_5; meta_6 ]
      )
  | LIH | RIH -> assert false
  | Meta ->
      let m, meta_type = Meta.new_tm () in
      (m, [ meta_type ])
  | Sub (Letin_tm _, _, _, _)
  | Sub (Sub _, _, _, _)
  | Sub (Meta, _, _, _)
  | Sub (Op _, _, _, _)
  | Sub (Inverse _, _, _, _)
  | Sub (Unit _, _, _, _)
  | Sub (ISR _, _, _, _)
  | Sub (CanR _, _, _, _)
  | Sub (CoindR _, _, _, _)
  | Sub (RecR _, _, _, _)
  | Sub (LIH, _, _, _)
  | Sub (RIH, _, _, _)
  | BuiltinR _ | Letin_tm _ ->
      Error.fatal "ill-formed term"

and sub s tgt expl =
  match (s, tgt) with
  | [], [] -> ([], [])
  | (t, i) :: s, (x, (_, e)) :: tgt
    when e || expl || !Settings.explicit_substitutions ->
      let t, meta_types_t = tm t in
      let fmetas, meta_types_f, tgt = meta_functed_arg i tgt in
      let s, meta_types_s = sub s tgt expl in
      let meta_types =
        List.concat [ meta_types_t; meta_types_f; meta_types_s ]
      in
      ((x, (t, e)) :: List.append fmetas s, meta_types)
  | (_ :: _ as s), (x, (_, e)) :: tgt ->
      let t, meta_type = Meta.new_tm () in
      let s, meta_types_s = sub s tgt expl in
      ((x, (t, e)) :: s, meta_type :: meta_types_s)
  | [], (x, (_, false)) :: tgt ->
      let t, meta_type = Meta.new_tm () in
      let s, meta_types_s = sub [] tgt expl in
      ((x, (t, false)) :: s, meta_type :: meta_types_s)
  | _ :: _, [] | [], _ :: _ -> raise WrongNumberOfArguments

and find_functorialisation s tgt expl =
  match (s, tgt) with
  | [], [] -> []
  | (_, i) :: s, (x, (_, e)) :: tgt
    when e || expl || !Settings.explicit_substitutions ->
      (x, i) :: find_functorialisation s tgt expl
  | (_ :: _ as s), (_, (_, _)) :: tgt -> find_functorialisation s tgt expl
  | [], (_, (_, false)) :: _ -> []
  | _ :: _, [] | [], _ :: _ -> raise WrongNumberOfArguments

and meta_functed_arg i ctx =
  match (i, ctx) with
  | 0, tgt -> ([], [], tgt)
  | _, (y, _) :: (x, _) :: ctx ->
      let src, meta_types_src = Meta.new_tm () in
      let tgt, meta_types_tgt = Meta.new_tm () in
      let fmetas, meta_types, ctx = meta_functed_arg (i - 1) ctx in
      ( (y, (tgt, false)) :: (x, (src, false)) :: fmetas,
        meta_types_tgt :: meta_types_src :: meta_types,
        ctx )
  | _, _ -> raise WrongNumberOfArguments

let tm t =
  try tm t
  with WrongNumberOfArguments ->
    Error.parsing_error
      ("term: " ^ Raw.string_of_tm t)
      "wrong number of arguments provided"

let ty ty =
  match ty with
  | ObjR -> (Obj, [])
  | ArrR (u, v) ->
      let (tu, meta_types_tu), (tv, meta_types_tv) = (tm u, tm v) in
      (Arr (Meta.new_ty (), tu, tv), List.append meta_types_tu meta_types_tv)
  | Letin_ty _ -> Error.fatal "letin_ty constructor cannot appear here"
  | InvR u ->
      let tu, meta_ctx = tm u in
      (Inv (Meta.new_ty (), tu), meta_ctx)

let ty t =
  try ty t
  with WrongNumberOfArguments ->
    Error.parsing_error
      ("type: " ^ Raw.string_of_ty t)
      "wrong number of arguments provided"

let ctx c =
  let rec mark_explicit c after =
    match c with
    | [] -> []
    | (v, t) :: c ->
        let expl =
          not (List.exists (fun (_, ty) -> Raw.var_in_ty v ty) after)
        in
        (v, (t, expl)) :: mark_explicit c ((v, t) :: after)
  in
  let rec list c =
    match c with
    | [] -> ([], [])
    | (v, (t, expl)) :: c ->
        let c, meta_c = list c in
        let t, meta_ty = ty t in
        ((v, (t, expl)) :: c, List.append meta_ty meta_c)
  in
  list (mark_explicit c [])

let rec sub_to_suspended = function
  | [] ->
      let (m1, mc1), (m0, mc0) = (Meta.new_tm (), Meta.new_tm ()) in
      ([ (m1, false); (m0, false) ], [ mc1; mc0 ])
  | t :: s ->
      let s, m = sub_to_suspended s in
      (t :: s, m)
