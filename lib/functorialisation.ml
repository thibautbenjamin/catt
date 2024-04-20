open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

exception FunctorialiseMeta
exception WrongNumberOfArguments

let builtin_comp :
  (int -> Coh.t) ref =
  ref (fun _ -> Error.fatal "Uninitialised forward reference")

let builtin_whisk :
  (int -> int -> int -> Coh.t) ref =
  ref (fun _ -> Error.fatal "Uninitialised forward reference")

let builtin_whisk_sub_ps :
  (int -> tm -> ty -> tm -> ty -> sub_ps) ref =
  ref (fun _ -> Error.fatal "Uninitialised forward reference")

let ps_reduce :
  (int -> ps -> ps) ref =
  ref (fun _ -> Error.fatal "Uninitialised forward reference")

let ps_reduction_sub :
  (ps -> sub_ps) ref =
  ref (fun _ -> Error.fatal "Uninitialised forward reference")

(*
   Takes a functorialisation data with a context and produces 2 pieces
   of data :
   - a list containing all variables that should be functorialised at least once
   - a new functorialisation data with all integers decreased by one indicating
   the functorialisation that are left to perform after functorialising
   all the adequate variables once
*)
let list_functorialised c l =
  let exp = !Settings.explicit_substitutions in
  let rec list c l =
    match c,l,exp with
    | [],[],_ -> [],[]
    | (x,(_, true))::tgt, xf::l, _ ->
      let func, next = list tgt l in
      (if xf > 0 then x::func else func), (xf-1)::next
    | _::tgt, _::l, true -> list tgt l
    | _::tgt, f::l, false -> list tgt (f::l)
    | (_,(_, false))::tgt, [], false -> list tgt []
    | (_,(_, false))::_, [], true
    | _::_,[],_ |[],_::_,_ -> raise WrongNumberOfArguments
  in list c l

(* compute a new functorialisation data from an old functorialisation
   data and a list of variables to be functorialised. This also needs
   a context as argument, to establish the connection between the name
   f the variables and their positions as locally maximal variables. *)
let add_functorialisation c func l =
  let rec add c func =
    match c,func with
    | [],func -> func
    | (x,(_,true))::c,i::func when List.mem x l -> (i+1)::(add c func)
    | (_,(_,true))::c,i::func -> i::(add c func)
    | (_,_)::c,func -> (add c func)
  in
  let rec make c =
    match c with
    | [] -> []
    | (x,(_,true))::c when List.mem x l -> +1::(make c)
    | (_,(_,true))::c -> 0::(make c)
    | (_,_)::c -> (make c)
  in
  match func with
  | None -> make c
  | Some func -> add c func


(*
   Given a context, a ps-substitution and a list of variables, returns
   the list of all variables in the context whose corresponding term
   in the substitution contains a variable from the input list
*)
let rec find_places ctx s l =
  match ctx,s with
  | [], [] -> []
  | (x,_)::c,  (t,_)::s when Unchecked.tm_contains_vars t l -> x::(find_places c s l)
  | _::c, _::s -> find_places c s l
  | [],_::_ | _::_,[] -> Error.fatal "functorialisation in a non-existant place"

(* Invariant maintained:
    src_prod returns a term of same dimension as tm
*)
let rec src_prod t l tgt_subst f_vars tm tm_t d n cc =
    match t with
    | Arr(ty',src,_tgt) when Unchecked.tm_contains_vars src l ->
        let whisk = !builtin_whisk n 0 (d-n-1) in
        let ps,whisk_ty,_ = (Coh.forget whisk) in
        let prod, prod_ty = src_prod ty' l tgt_subst f_vars tm tm_t d (n-1) cc in
        let ty_f = (ty ty' l tgt_subst f_vars src cc) in
        let src_f = fst (List.hd (tm_one_step src l tgt_subst f_vars true cc)) in
        let sub_ps = !builtin_whisk_sub_ps (d-n-1) src_f ty_f prod prod_ty in
        let sub = fst (Unchecked.sub_ps_to_sub sub_ps ps) in
        let _ = check_term cc (Coh(whisk, sub_ps)) in
        (Coh(whisk, sub_ps), Unchecked.ty_apply_sub whisk_ty sub)
    | Arr(_,_,_) | Obj -> (tm, tm_t)
    | _ -> raise FunctorialiseMeta
and tgt_prod t l tgt_subst f_vars tm tm_t d n cc =
    match t with
    | Arr(ty',_src,tgt) when Unchecked.tm_contains_vars tgt l ->
        let whisk = !builtin_whisk n (d-n-1) 0 in
        let ps,whisk_ty,_ = (Coh.forget whisk) in
        let prod, prod_ty = tgt_prod ty' l tgt_subst f_vars tm tm_t d (n-1) cc in
        let ty_f = (ty ty' l tgt_subst f_vars tgt cc) in
        let tgt_f = fst (List.hd (tm_one_step tgt l tgt_subst f_vars true cc)) in
        let sub_ps = !builtin_whisk_sub_ps 0 prod prod_ty tgt_f ty_f in
        let sub = fst (Unchecked.sub_ps_to_sub sub_ps ps) in
        let _ = check_term cc (Coh(whisk, sub_ps)) in
        (Coh(whisk, sub_ps), Unchecked.ty_apply_sub whisk_ty sub)
    | Arr(_,_,_) | Obj -> (tm, tm_t)
    | _ -> raise FunctorialiseMeta
and ty t l tgt_subst f_vars tm cc =
  let d = Unchecked.dim_ty t in
  let tm_incl = Unchecked.tm_apply_sub tm tgt_subst in
  let t_incl = Unchecked.ty_apply_sub t tgt_subst in
  let src, src_t = tgt_prod t l tgt_subst f_vars tm t d (d-1) cc in
  let tgt, _tgt_t = src_prod t l tgt_subst f_vars tm_incl t_incl d (d-1) cc in
  Arr (src_t, src, tgt)

and ctx c l =
  match c with
  | [] -> [],[],[]
  | (x,(t,expl))::c when List.mem x l ->
     let c,tgt_subst,f_vars = ctx c l in
     let x' = Var.fresh() in
     let xf = Var.fresh() in
     let c_ext = (x',((Unchecked.ty_apply_sub t tgt_subst),false))::(x,(t,false))::c in
     let tgt_subst = (x,Var x')::tgt_subst in
     let tf = ty t l tgt_subst f_vars (Var x) (Ctx.check c_ext) in
     (xf,(tf,expl))::c_ext,
     tgt_subst,
     (x, (Var x',Var xf))::f_vars
  | (x,a)::c -> let c,tgt_subst,f_terms = ctx c l in (x,a)::c, tgt_subst,f_terms

(*
   Functorialisation of a coherence once with respect to a list of
   variables
*)
and coh_one_step coh l =
  let ps,t,(name,susp,func) = Coh.forget coh in
  let c = Unchecked.ps_to_ctx ps in
  let ctxf,tgt_subst,f_vars = ctx c l in
  let _,names,_ = Unchecked.db_levels ctxf in
  let psf = PS.forget (PS.mk (Ctx.check ctxf)) in
  let ty = ty t l tgt_subst f_vars (Coh(coh,Unchecked.identity_ps ps)) (Ctx.check ctxf) in
  let ty = Unchecked.rename_ty ty names in
  let pp_data = (name,susp,Some(add_functorialisation c func l)) in
  check_coh psf ty pp_data

(*
   Functorialisation a term once with respect to a list of triples.
   Returns a list containing the functorialise term followed by its
   target and its source.
 *)
and tm_one_step t l tgt_subst f_vars expl cc =
  if (not (Unchecked.tm_contains_vars t l)) then [t,expl]
  else
  match t with
  | Var v ->
    begin
      match List.assoc_opt v f_vars with
      | Some (v',vf) -> [vf, true; v', false; Var v, false]
      | None -> [Var v, expl]
    end
  | Coh(c,s) ->
    begin
      match f_vars with
      | _::_ ->
        let ps,_,_ = Coh.forget c in
        let cohf =
          let places = find_places (Unchecked.ps_to_ctx ps) s (List.map fst f_vars) in
          coh_one_step c places
        in
        let sf = sub s l tgt_subst f_vars cc in
        let s' = List.map (fun (t,expl) -> Unchecked.tm_apply_sub t tgt_subst ,expl) s in
        [Coh(cohf,sf), true; Coh(c,s'), false; Coh(c,s), false]
      | [] -> [Coh(c,s), expl]
    end
  | Meta_tm _ -> (raise FunctorialiseMeta)
and sub s l tgt_subst f_vars cc =
  match s with
  | [] -> []
  | (t, expl)::s ->
    List.append
      (tm_one_step t l tgt_subst f_vars expl cc)
      (sub s l tgt_subst f_vars cc)

(*
   Functorialisation a term possibly multiple times with respect to a
   functorialisation data
*)
let rec tm c t s =
  let l, next = list_functorialised c s in
  if l <> [] then
    let c,tgt_subst,f_vars = ctx c l in
    let t = fst (List.hd (tm_one_step t l tgt_subst f_vars true (Ctx.check c))) in
    tm c t next
  else c,t

(*
   Functorialisation of a coherence possibly multiple times, with
   respect to a functorialisation data
*)
let rec coh c s =
  let ps,_,_ = Coh.forget c in
  let ctx = Unchecked.ps_to_ctx ps in
  let l, next = list_functorialised ctx s in
  if l <> [] then coh (coh_one_step c l) next else c

(*
   Functorialisation of a coherence: exposed function
*)
let coh c s =
  try coh c s
  with
  | FunctorialiseMeta ->
    Error.functorialisation
      ("coherence: " ^ Coh.to_string c)
      (Printf.sprintf "cannot functorialise meta-variables")
  | WrongNumberOfArguments ->
    Error.parsing_error
      ("coherence: " ^ Coh.to_string c)
      "wrong number of arguments provided"

(*
   Functorialisation of a coherence once with respect to every maximal
   argument
*)
let coh_all c =
  let func_data_all ps =
    let rec func_data n ps =
      match ps,n with
      | Br [],0 -> [1]
      | Br [],_ -> [0]
      | Br (ps::l),n -> List.append (func_data (n-1) ps) (List.concat (List.map (func_data (n-1)) l))
    in func_data (Unchecked.dim_ps ps) ps
  in
  let ps,_,_ = Coh.forget c in
  let l = func_data_all ps in
  coh c l

(*
   Functorialisation a term: exposed function
*)
let tm c t s =
  try tm c t s
  with
  | FunctorialiseMeta ->
    Error.functorialisation
      ("term: " ^ Unchecked.tm_to_string t)
      (Printf.sprintf "cannot functorialise meta-variables")
  | WrongNumberOfArguments ->
    Error.parsing_error
      ("term: " ^ (Unchecked.tm_to_string t))
      "wrong number of arguments provided"
