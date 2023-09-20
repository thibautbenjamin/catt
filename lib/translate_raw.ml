open Kernel
open Kernel.Unchecked_types
open Raw_types

exception WrongNumberOfArguments
exception FunctorialiseWithExplicit

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

let list_functorialised s c =
  if not !Settings.explicit_substitutions then
    let rec list s c =
      match s,c with
      | [],[] -> [],[]
      | (t,true)::s, (x,(_, true))::tgt ->
        let s,func = list s tgt in
        t::s, x::func
      | (t,false)::s, (_,(_, true))::tgt ->
        let s,func = list s tgt in
        t::s, func
      | s , (_,(_, false))::tgt ->
        list s tgt
      | _::_, [] |[],_::_ -> raise WrongNumberOfArguments
    in list s c
  else
    let rec ensure_no_func = function
      | [] -> []
      | (_,true)::_ -> raise FunctorialiseWithExplicit
      | (t,false)::s -> t::(ensure_no_func s)
    in ensure_no_func s,[]

(* inductive translation on terms and types without let_in *)
let rec tm tm =
  let make_coh coh s susp =
    let coh = Suspension.coh susp coh in
    let ps,ty =
      match coh with
      | Cohdecl (ps,ty) -> ps,ty
      | Cohchecked coh -> Coh.forget coh
    in
    let ctx = Unchecked.ps_to_ctx ps in
    let s,l = list_functorialised s ctx in
    let
      coh,ps =
      if l <> [] then Functorialisation.coh ps ty l else coh,ps
    in
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
        let s,l = list_functorialised s c in
        let c,t =
          if l <> [] then Functorialisation.tm c t l else c,t
        in
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
  | Sub(Builtin _, _,_) | Letin_tm _ -> assert false
and sub_ps s ps =
  let sub,meta_types = sub s (Unchecked.ps_to_ctx ps) in
  List.map snd sub, meta_types
and sub s  tgt  =
  match s,tgt with
  | [],[] -> [],[]
  | t::s, (x,(_, true))::tgt ->
    let t, meta_types_t = tm t in
    let s,meta_types_s = sub s tgt in
    (x,t)::s,  List.append meta_types_t meta_types_s
  | t::s, (x,(_, false))::tgt when !Settings.explicit_substitutions ->
    let t, meta_types_t = tm t in
    let s,meta_types_s = sub s tgt in
    (x, t)::s, List.append meta_types_t meta_types_s
  | s , (x,(_, false))::tgt ->
    let t, meta_type = new_meta_tm() in
    let s,meta_types_s = sub s tgt in
    (x, t)::s, meta_type::meta_types_s
  | _::_, [] |[],_::_ -> raise WrongNumberOfArguments

let tm t =
  try tm t with
  | FunctorialiseWithExplicit ->
    Error.functorialisation
      ("term: "^(Raw.string_of_tm t))
      "cannot compute functorialisation with explicit arguments"
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
  | Letin_ty _ -> assert false


let ty t =
  try ty t with
  | FunctorialiseWithExplicit ->
    Error.functorialisation
      ("type: "^(Raw.string_of_ty t))
      "cannot compute functorialisation with explicit arguments"

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
    [ m1; m0], [mc1; mc0]
  | t::s -> let s,m = sub_to_suspended s in t::s, m
