open Kernel
open Kernel.Unchecked_types
open Raw_types

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
  let make_coh coh s susp =
    let coh = Suspension.coh susp coh in
    let coh = Functorialisation.coh coh (List.map snd s) in
    let ps,_,_ = Coh.forget coh in
    let s, meta_types = sub_ps s ps in
    Coh(coh,s), meta_types
  in
  match tm with
  | VarR v -> Var v, []
  | Sub(VarR v, s, susp) ->
    begin
      match Environment.val_var v with
      | Coh coh -> make_coh coh s susp
      | Tm(c,t) ->
        let c = Suspension.ctx susp c in
        let t = Suspension.tm susp t in
        let c,t = Functorialisation.tm c t (List.map snd s) in
        let s, meta_types = sub s c in
        Unchecked.tm_apply_sub t s, meta_types
    end;
  | Builtin(name,s,susp) ->
    let builtin_coh =
      match name with
      | Comp -> Builtin.comp s
      | Id -> Builtin.id
    in make_coh builtin_coh s susp
  | Meta -> let m,meta_type = new_meta_tm() in (m,[meta_type])
  | Sub (Letin_tm _,_,_) | Sub(Sub _,_,_) | Sub(Meta,_,_)
  | Sub(Builtin _, _,_) | Letin_tm _ -> Error.fatal("ill-formed term")
and sub_ps s ps =
  let tgt = Unchecked.ps_to_ctx ps in
  let rec aux s tgt =
    match s,tgt with
    | [],[] -> [],[]
    | (t,_)::s, (_,(_, true))::tgt ->
      let t,meta_types_t = tm t in
      let s,meta_types_s = aux s tgt in
      (t, true)::s,  List.append meta_types_t meta_types_s
    | (t,_)::s, (_,(_, false))::tgt when !Settings.explicit_substitutions ->
      let t,meta_types_t = tm t in
      let s,meta_types_s = aux s tgt in
      (t, false)::s,  List.append meta_types_t meta_types_s
    | s, (_,(_,false))::tgt ->
      let t,meta_type = new_meta_tm() in
      let s,meta_types_s = aux s tgt in
      (t, false)::s, meta_type::meta_types_s
    | _::_, [] |[],_::_ -> raise WrongNumberOfArguments
  in aux s tgt
and sub s  tgt  =
  match s,tgt with
  | [],[] -> [],[]
  | (t,_)::s, (x,(_, e))::tgt when e || !Settings.explicit_substitutions ->
    let t, meta_types_t = tm t in
    let s,meta_types_s = sub s tgt in
    (x,t)::s,  List.append meta_types_t meta_types_s
  | (_::_) as s , (x,(_,_))::tgt ->
    let t, meta_type = new_meta_tm() in
    let s,meta_types_s = sub s tgt in
    (x, t)::s, meta_type::meta_types_s
  | [], (x,(_,false))::tgt ->
    let t, meta_type = new_meta_tm() in
    let s,meta_types_s = sub [] tgt in
    (x, t)::s, meta_type::meta_types_s
  | _::_, [] |[],_::_ -> raise WrongNumberOfArguments

let tm t =
  try tm t with
  | WrongNumberOfArguments ->
    Error.parsing_error
      ("term: " ^ (Raw.string_of_tm t))
      "wrong number of arguments provided"

let ty ty =
  match ty with
  | ObjR -> Obj,[]
  | ArrR(u,v) ->
     let (tu, meta_types_tu), (tv, meta_types_tv) = tm u, tm v in
     Arr(new_meta_ty(),tu, tv), List.append meta_types_tu meta_types_tv
  | Letin_ty _ -> Error.fatal ("letin_ty constructor cannot appear here")

let ty t =
  try ty t with
  | WrongNumberOfArguments ->
    Error.parsing_error
      ("type: " ^ (Raw.string_of_ty t))
      "wrong number of arguments provided"


let ctx c =
  let rec mark_explicit c after =
    match c  with
    | [] -> []
    | (v,t) :: c ->
      let
        expl = not (List.exists (fun (_,ty) -> Raw.var_in_ty v ty) after)
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

let rec sub_to_suspended = function
  | [] ->
    let (m1,mc1),(m0,mc0) = new_meta_tm(), new_meta_tm() in
    [ m1, false; m0, false], [mc1; mc0]
  | t::s -> let s,m = sub_to_suspended s in t::s, m
