open Common

exception WrongNumberOfArguments

let meta_namer_ty = ref 0
let meta_namer_tm = ref 0

let new_meta_ty () =
  let meta = Meta_ty !meta_namer_ty in
  meta_namer_ty := !meta_namer_ty + 1; meta
let new_meta_tm () =
  let meta = Meta_tm !meta_namer_tm in
  meta_namer_tm := !meta_namer_tm + 1; meta

(* inductive translation on terms and types without let_in *)
let rec tm tm =
  match tm with
  | Syntax.Var v -> Var v
  | Syntax.Sub(Var v, s, _) ->
     begin
       match Environment.val_var v with
       | Coh(ps, ty) -> Coh(ps,ty,sub_ps s ps)
       | Tm(c,t) ->
          let s = sub s c in
          Unchecked.tm_apply_sub t s
     end;
  | Syntax.Sub (Letin_tm _,_,_) | Sub(Sub _,_,_) | Letin_tm _ -> assert false
and sub_ps s ps =
  List.map snd (sub s (Unchecked.ps_to_ctx ps))
and sub s tgt =
  match s,tgt with
  | [],[] -> []
  | t::s, (x,(_, true))::tgt -> (x, tm t)::(sub s tgt)
  | t::s, (x,(_, false))::tgt when !Settings.explicit_substitutions ->
    (x, tm t)::(sub s tgt)
  | s , (x,(_, false))::tgt ->
    (x, new_meta_tm())::(sub s tgt)
  | _::_, [] |[],_::_ -> raise WrongNumberOfArguments

let ty ty =
  match ty with
  | Syntax.Obj -> Obj
  | Syntax.Arr(u,v) ->
     let tu, tv = tm u, tm v in
     Arr(new_meta_ty(),tu, tv)
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
    | [] -> []
    | (v,(t,expl)) :: c ->
      let c = list c in
      (v, (ty t,expl)) :: c
  in list (mark_explicit c [])
