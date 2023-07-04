open Common

exception WrongNumberOfArguments

let meta_namer_ty = ref 0
let meta_namer_tm = ref 0

let new_meta_ty () =
  let meta = Meta_ty !meta_namer_ty in
  meta_namer_ty := !meta_namer_ty + 1; meta
let new_meta_tm () =
  let i = !meta_namer_tm in
  let meta = Meta_tm i in
  meta_namer_tm := !meta_namer_tm + 1;
  meta, (i, new_meta_ty())

(* inductive translation on terms and types without let_in *)
let rec tm tm =
  match tm with
  | Syntax.Var v -> Var v, []
  | Syntax.Sub(Var v, s, _) ->
     begin
       match Environment.val_var v with
       | Coh(ps, ty) ->
         let s, meta_types = sub_ps s ps in
         Coh(ps,ty,s), meta_types
       | Tm(c,t) ->
          let s, meta_types = sub s c in
          Unchecked.tm_apply_sub t s, meta_types
     end;
  | Syntax.Sub (Letin_tm _,_,_) | Sub(Sub _,_,_) | Letin_tm _ -> assert false
and sub_ps s ps =
  let sub,meta_types = sub s (Unchecked.ps_to_ctx ps) in
  List.map snd sub, meta_types
and sub s tgt =
  match s,tgt with
  | [],[] -> [], []
  | t::s, (x,(_, true))::tgt ->
    let t, meta_types_t = tm t in
    let s,meta_types_s = sub s tgt in
    (x, t)::s, List.append meta_types_t meta_types_s
  | t::s, (x,(_, false))::tgt when !Settings.explicit_substitutions ->
    let t, meta_types_t = tm t in
    let s,meta_types_s = sub s tgt in
    (x, t)::s, List.append meta_types_t meta_types_s
  | s , (x,(_, false))::tgt ->
    let t, meta_type = new_meta_tm() in
    let s,meta_types_s = sub s tgt in
    (x, t)::s, meta_type::meta_types_s
  | _::_, [] |[],_::_ -> raise WrongNumberOfArguments

let ty ty =
  match ty with
  | Syntax.Obj -> Obj,[]
  | Syntax.Arr(u,v) ->
     let (tu, meta_types_tu), (tv, meta_types_tv) = tm u, tm v in
     Arr(new_meta_ty(),tu, tv), List.append meta_types_tu meta_types_tv
  | Syntax.Letin_ty _ -> assert false

let ctx c =
  let rec mark_explicit c after =
    match c  with
    | [] -> []
    | (v,t) :: c ->
      let
        expl = not (List.exists (fun (_,ty) -> Syntax.var_in_ty v ty) after)
      in
      (v,(t,expl)) :: mark_explicit c ((v,t)::after)
  in
  let rec list c =
    match c with
    | [] -> [],[]
    | (v,(t,expl)) :: c ->
      let c, meta_c = list c in
      let t, meta_ty = ty t in
      (v, (t,expl)) :: c, List.append meta_ty meta_c
  in list (mark_explicit c [])
