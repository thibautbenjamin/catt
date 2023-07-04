open Common

exception WrongNumberOfArguments

let meta_namer = ref 0

let new_meta () =
  let meta = Meta !meta_namer in
  meta_namer := !meta_namer + 1; meta

(* inductive translation on terms and types without let_in *)
let rec tm ctx tm =
  match tm with
  | Syntax.Var v -> Var v
  | Syntax.Sub(Var v, s, _) ->
     begin
       match Environment.val_var v with
       | Coh(ps, ty) -> Coh(ps,ty,sub_ps ctx s ps)
       | Tm(c,t) ->
          let s = sub ctx s c in
          Unchecked.tm_apply_sub t s
     end;
  | Syntax.Sub (Letin_tm _,_,_) | Sub(Sub _,_,_) | Letin_tm _ -> assert false
and sub_ps ctx s ps =
  List.map snd (sub ctx s (Unchecked.ps_to_ctx ps))
and sub src s tgt =
  match s,tgt with
  | [],[] -> []
  | t::s, (x,(_, true))::tgt -> (x, tm src t)::(sub src s tgt)
  | t::s, (x,(_, false))::tgt when !Settings.explicit_substitutions ->
    (x, tm src t)::(sub src s tgt)
  | s , (x,(_, false))::tgt ->
    (x, new_meta())::(sub src s tgt)
  | _::_, [] |[],_::_ -> raise WrongNumberOfArguments

let ty ctx ty =
  match ty with
  | Syntax.Obj -> Obj
  | Syntax.Arr(u,v) ->
     let tu, tv = tm ctx u, tm ctx v in
     let u = Kernel.Tm.check ctx tu in
     let a = Kernel.(Ty.forget (Tm.typ u)) in
     Arr(a,tu,tv)
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
      let kc = Kernel.Ctx.check c in
      (v, (ty kc t,expl)) :: c
  in list (mark_explicit c [])
