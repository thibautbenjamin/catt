open Common

exception WrongNumberOfArguments

let meta_namer = ref 0

let new_meta () =
  let meta = Meta !meta_namer in
  meta_namer := !meta_namer + 1; meta

(* inductive translation on terms and types without let_in *)
let rec tm_red ctx tm =
  match tm with
  | Syntax.Var v -> Var v
  | Syntax.Sub(Var v, s, _) ->
     begin
       match Environment.val_var v with
       | Coh(ps, ty) -> Coh(ps,ty,sub_ps_red ctx s ps)
       | Tm(c,t) ->
          let s = sub_red ctx s c in
          Unchecked.tm_apply_sub t s
     end;
  | Syntax.Sub (Letin_tm _,_,_) | Sub(Sub _,_,_) | Letin_tm _ -> assert false
and sub_ps_red ctx s ps =
  List.map snd (sub_red ctx s (Unchecked.ps_to_ctx ps))
and sub_red src s tgt =
  match s,tgt with
  | [],[] -> []
  | t::s, (x,(_, true))::tgt -> (x, tm_red src t)::(sub_red src s tgt)
  | (t::tail) as s, (x,(_, false))::tgt ->
    if !Settings.explicit_substitutions then
      (x, tm_red src t)::(sub_red src tail tgt)
    else (x, new_meta())::(sub_red src s tgt)
  | _::_, [] |[],_::_ -> raise WrongNumberOfArguments

let ty_red ctx ty =
  match ty with
  | Syntax.Obj -> Obj
  | Syntax.Arr(u,v) ->
     let tu, tv = tm_red ctx u, tm_red ctx v in
     let u = Kernel.Tm.check ctx tu in
     let a = Kernel.(Ty.forget (Tm.typ u)) in
     Arr(a,tu,tv)
  | Syntax.Letin_ty _ -> assert false

(* TODO: fix explicitness of arguments *)
let rec ctx = function
  | [] -> []
  | (v,t) :: c ->
     let c = ctx c in
     let kc = Kernel.Ctx.check c in
     (v, (ty_red kc t, true)) :: c

let ty c ty =
  let ty = Syntax.remove_let_ty ty in
  ty_red (Kernel.Ctx.check c) ty

let tm c tm =
  let tm = Syntax.remove_let_tm tm in
  tm_red (Kernel.Ctx.check c) tm

let ty_in_ps ps t =
  let t = Syntax.remove_let_ty t in
  let ps = ctx ps in
  let t = ty_red (Kernel .Ctx.check ps) t in
  let _, names,_ = Unchecked.db_levels ps in
  let t = Unchecked.rename_ty t names in
  t

let ps p =
  let p = ctx p in
  Kernel.PS.(forget (mk (Kernel.Ctx.check p)))
