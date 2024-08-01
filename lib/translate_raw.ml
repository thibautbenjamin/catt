open Kernel
open Unchecked_types.Unchecked_types(Coh)
open Raw_types

exception WrongNumberOfArguments

(* inductive translation on terms and types without let_in *)
let rec tm t =
  let make_coh coh s susp =
    let coh = Suspension.coh susp coh in
    let ps,_,_ = Coh.forget coh in
    let func = find_functorialisation s (Unchecked.ps_to_ctx ps) in
    let coh,ctx = Functorialisation.coh_successively coh func in
    let s, meta_types = sub s ctx in
    Unchecked.tm_apply_sub coh s, meta_types
  in
  match t with
  | VarR v -> Var v, []
  | Sub(VarR v, s, susp) ->
    begin
      match Environment.val_var v with
      | Coh coh -> make_coh coh s susp
      | Tm(c,t) ->
        let c = Suspension.ctx susp c in
        let t = Suspension.tm susp t in
        let func = find_functorialisation s c in
        let t,c = Functorialisation.tm c t func in
        let s, meta_types = sub s c in
        Unchecked.tm_apply_sub t s, meta_types
    end;
  | Sub (BuiltinR b,s,susp) ->
    let builtin_coh =
      match b with
      | Comp -> Builtin.comp s
      | Id -> Builtin.id
    in make_coh builtin_coh s susp
  | Op(l,t) -> let t,meta = tm t in Opposite.tm t l, meta
  | Inverse t ->
    let t,meta_ctx = tm t in
    Inverse.compute_inverse t,meta_ctx
  | Unit t ->
    let t,meta_ctx = tm t in
    Inverse.compute_witness t, meta_ctx
  | Meta -> let m,meta_type = Meta.new_tm() in (m,[meta_type])
  | Sub (Letin_tm _,_,_) | Sub(Sub _,_,_) | Sub(Meta,_,_)
  | Sub(Op _,_,_) | Sub (Inverse _,_,_) | Sub(Unit _,_,_)
  | BuiltinR _ | Letin_tm _ -> Error.fatal("ill-formed term")
and sub s tgt =
  match s,tgt with
  | [],[] -> [],[]
  | (t,i)::s, (x,(_, e))::tgt when e || !Settings.explicit_substitutions ->
    let t, meta_types_t = tm t in
    let fmetas, meta_types_f,tgt = meta_functed_arg i tgt in
    let s, meta_types_s = sub s tgt in
    let meta_types = List.concat [meta_types_t; meta_types_f; meta_types_s] in
    (x,t)::(List.append fmetas s), meta_types
  | (_::_) as s , (x,(_,_))::tgt ->
    let t, meta_type = Meta.new_tm() in
    let s, meta_types_s = sub s tgt in
    (x, t)::s, meta_type::meta_types_s
  | [], (x,(_,false))::tgt ->
    let t, meta_type = Meta.new_tm() in
    let s, meta_types_s = sub [] tgt in
    (x, t)::s, meta_type::meta_types_s
  | _::_, [] |[],_::_ -> raise WrongNumberOfArguments
and find_functorialisation s tgt =
  match s,tgt with
  | [],[] -> []
  | (_,i)::s, (x,(_, e))::tgt when e || !Settings.explicit_substitutions ->
    (x,i)::(find_functorialisation s tgt)
  | (_::_) as s , (_,(_,_))::tgt -> find_functorialisation s tgt
  | [], (_,(_,false))::_ -> []
  | _::_, [] |[],_::_ -> raise WrongNumberOfArguments
and meta_functed_arg i ctx =
  match i,ctx with
  | 0,tgt -> [],[],tgt
  | _,(y,_)::(x,_)::ctx ->
    let src, meta_types_src = Meta.new_tm () in
    let tgt, meta_types_tgt = Meta.new_tm () in
    let fmetas, meta_types,_ = meta_functed_arg (i-1) ctx in
    (y,tgt)::(x,src)::fmetas, meta_types_tgt::meta_types_src::meta_types, ctx
  | _,_ -> raise WrongNumberOfArguments

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
     Arr(Meta.new_ty(),tu, tv), List.append meta_types_tu meta_types_tv
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
    let (m1,mc1),(m0,mc0) = Meta.new_tm(), Meta.new_tm() in
    [ m1, false; m0, false], [mc1; mc0]
  | t::s -> let s,m = sub_to_suspended s in t::s, m
