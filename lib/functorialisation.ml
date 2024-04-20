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
    | [],[] -> []
    | (x,_)::c,i::func when List.mem x l -> (i+1)::0::0::(add c func)
    | (_,_)::c,i::func -> i::(add c func)
    | _,_ -> assert false
  in
  let rec make c =
    match c with
    | [] -> []
    | (x,_)::c when List.mem x l -> 1::0::0::(make c)
    | (_,_)::c -> 0::(make c)
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

let rec tgt_subst l =
    match l with
    | [] -> []
    | v::tl -> (v,Var(Var.Plus v))::(tgt_subst tl)

(* Invariant maintained:
    src_prod returns a term of same dimension as tm
*)
let rec src_prod t l tm tm_t d n cc =
    match t with
    | Arr(ty',src,_tgt) when Unchecked.tm_contains_vars src l ->
        let whisk = !builtin_whisk n 0 (d-n-1) in
        let ps,whisk_ty,_ = (Coh.forget whisk) in
        let prod, prod_ty = src_prod ty' l tm tm_t d (n-1) cc in
        let ty_f = (ty ty' l src cc) in
        let src_f = fst (List.hd (tm_one_step src l true cc)) in
        let sub_ps = !builtin_whisk_sub_ps (d-n-1) src_f ty_f prod prod_ty in
        let sub = fst (Unchecked.sub_ps_to_sub sub_ps ps) in
        let _ = check_term cc (Coh(whisk, sub_ps)) in
        (Coh(whisk, sub_ps), Unchecked.ty_apply_sub whisk_ty sub)
    | Arr(_,_,_) | Obj -> (tm, tm_t)
    | _ -> raise FunctorialiseMeta
and tgt_prod t l tm tm_t d n cc =
    match t with
    | Arr(ty',_src,tgt) when Unchecked.tm_contains_vars tgt l ->
        let whisk = !builtin_whisk n (d-n-1) 0 in
        let ps,whisk_ty,_ = (Coh.forget whisk) in
        let prod, prod_ty = tgt_prod ty' l tm tm_t d (n-1) cc in
        let ty_f = (ty ty' l tgt cc) in
        let tgt_f = fst (List.hd (tm_one_step tgt l true cc)) in
        let sub_ps = !builtin_whisk_sub_ps 0 prod prod_ty tgt_f ty_f in
        let sub = fst (Unchecked.sub_ps_to_sub sub_ps ps) in
        let _ = check_term cc (Coh(whisk, sub_ps)) in
        (Coh(whisk, sub_ps), Unchecked.ty_apply_sub whisk_ty sub)
    | Arr(_,_,_) | Obj -> (tm, tm_t)
    | _ -> raise FunctorialiseMeta
and ty t l tm cc =
  let d = Unchecked.dim_ty t in
  let tgt_incl = tgt_subst l in
  let tm_incl = Unchecked.tm_apply_sub tm tgt_incl in
  let t_incl = Unchecked.ty_apply_sub t tgt_incl in
  let src, src_t = tgt_prod t l tm t d (d-1) cc in
  let tgt, _tgt_t = src_prod t l tm_incl t_incl d (d-1) cc in
  Arr (src_t, src, tgt)

and ctx c l =
  match c with
  | [] -> []
  | (x,(t,expl))::c when List.mem x l ->
     let c_ext = (Var.Plus(x),(Unchecked.ty_apply_sub t (tgt_subst l),false))::(x,(t,false))::(ctx c l) in
     let tf = ty t l (Var x) (Ctx.check c_ext) in
     (Var.Bridge(x),(tf,expl))::c_ext
  | (x,a)::c -> (x,a)::(ctx c l)

(* Interchange needed for source of depth-1 non-inv coh *)
and intch_src coh _s l tgt_subst f_vars cc =
    (* Setup *)
    let ps,coh_ty,name = Coh.forget coh in
    let _ = Printf.printf "Sub: %s\n" (String.concat ", " (List.rev (List.map Var.to_string l))) in
    let _ = Printf.printf "Sub: %s\n" (String.concat ", " (List.rev (List.map (fun (x,_) -> Var.to_string x) f_vars))) in
    let d = Unchecked.dim_ps ps in
    (* Construct preimage locations *)
    let ps_bdry = Unchecked.ps_bdry ps in
    let tgt_incl_ps = Unchecked.ps_tgt ps in
    let _tgt_incl,ctx_bdry = Unchecked.sub_ps_to_sub tgt_incl_ps ps_bdry in
    let tgt_l = find_places ctx_bdry tgt_incl_ps l in
    let _ = Printf.printf "TGT L %d %d\n" (List.length tgt_l) (List.length l) in
    (* Construct ps_bdry_f *)
    let ctx_bdry_f,tgt_subst_bdry,f_vars_bdry = ctx ctx_bdry tgt_l in
    let ps_bdry_f = PS.forget (PS.mk (Ctx.check ctx_bdry_f)) in
    let bdry_f_db = Unchecked.db_level_sub_inv ctx_bdry_f in
    let _ = Printf.printf "PROBLEMATIC SUB: %s\n" (Unchecked.sub_ps_to_string tgt_incl_ps) in
    let tgt_incl_f = sub tgt_incl_ps l tgt_subst f_vars cc in
    (* Construct composite context *)
    let _ = Printf.printf "PS: %s %s %s %s\n%!" (Unchecked.ps_to_string ps) (Unchecked.ps_to_string ps_bdry_f) (Unchecked.ps_to_string ps_bdry) (Unchecked.ps_to_string (Unchecked.ps_bdry ps_bdry_f)) in
    let ps_comp,i1_ps,i2_ps = Unchecked.ps_compose (d-1) ps ps_bdry_f in
    let _ = Printf.printf "Resulting subs: %d %d %d %d, %s\n%!" (List.length i1_ps) (List.length (Unchecked.identity_ps ps)) (List.length i2_ps) (List.length (Unchecked.identity_ps ps_bdry_f)) (Unchecked.sub_ps_to_string (Unchecked.identity_ps (Br[]))) in
    let i1,_ = Unchecked.sub_ps_to_sub i1_ps ps in
    let i2,_ = Unchecked.sub_ps_to_sub i2_ps ps_bdry_f in
    (* Construct source (t[i1]) * (tgt_f[i2]) *)
    let src,tgt,ty_base = Coh.noninv_srctgt coh in
    let tgt_f_ty = ty ty_base tgt_l tgt_subst_bdry f_vars_bdry tgt (Ctx.check ctx_bdry) in
    let tgt_f_ty = Unchecked.ty_apply_sub tgt_f_ty bdry_f_db in
    let tgt_f = fst (List.hd (tm_one_step tgt tgt_l tgt_subst_bdry f_vars_bdry true (Ctx.check ctx_bdry))) in
    let tgt_f = Unchecked.tm_apply_sub tgt_f bdry_f_db in
    let _ = Printf.printf "Term: %s, func %s, ty: %s, len %d\n" (Unchecked.tm_to_string tgt) (Unchecked.tm_to_string tgt_f) (Unchecked.ty_to_string tgt_f_ty) (List.length f_vars_bdry) in
    let coh_src_coh = !builtin_whisk (d-1) 0 0 in
    let coh_src_ps,_,_ = Coh.forget coh_src_coh in
    let coh_src_sub_ps = !builtin_whisk_sub_ps 0 (Coh(coh,i1_ps)) (Unchecked.ty_apply_sub coh_ty i1) (Unchecked.tm_apply_sub tgt_f i2) (Unchecked.ty_apply_sub tgt_f_ty i2) in
    let coh_src = Coh(coh_src_coh,coh_src_sub_ps) in
    let _ = Printf.printf "SRC COH %s, len %d %d\n%!" (Unchecked.tm_to_string coh_src) (List.length coh_src_sub_ps) (List.length (Unchecked.identity_ps coh_src_ps)) in
    let _ = check_term (Ctx.check (Unchecked.ps_to_ctx ps_comp)) coh_src in
    (* Construct reduced context *)
    let ps_red = !ps_reduce (d-1) ps in
    let ps_red_comp,_j1,_ = Unchecked.ps_compose (d-1) ps_red ps_bdry_f in
    let ps_comp_red = !ps_reduce (d-1) ps_red_comp in
    let ps_comp_red_sub_ps = !ps_reduction_sub ps_red_comp in
    (* Construct biased reduction sub from ps_comp to ps_comp_red *)
    let ps_red_incl_sub_ps = Unchecked.sub_ps_apply_sub (!ps_reduction_sub ps) i1 in
    let ps_comp_red_ind_sub_ps = Unchecked.pullback_up (d-1) ps_red ps_bdry_f ps_red_incl_sub_ps i2_ps in
    (* Construct target (comp ps_comp_red tgt tgt) *)
    let coh_tgt_coh = (Coh.check_noninv ps_comp_red src tgt ((Unchecked.full_name name)^"_red",0,None)) in
    let _ = Printf.printf "TGT COH len %d %d\n%!" (List.length ps_comp_red_ind_sub_ps) (List.length (Unchecked.identity_ps ps_red_comp)) in
    let coh_tgt_sub_ps = Unchecked.sub_ps_apply_sub ps_comp_red_sub_ps (fst (Unchecked.sub_ps_to_sub ps_comp_red_ind_sub_ps ps_red_comp)) in
    let _ = Printf.printf "PS: %s %s %s, SUBS: %s || %s\n%!" (Unchecked.ps_to_string ps_comp) (Unchecked.ps_to_string ps_comp_red) (Unchecked.ps_to_string ps_red_comp) (Unchecked.sub_ps_to_string ps_comp_red_sub_ps) (Unchecked.sub_ps_to_string ps_comp_red_ind_sub_ps) in
    let coh_tgt = Coh(coh_tgt_coh, coh_tgt_sub_ps) in
    let _ = Printf.printf "TGT COH %s, ctx: %s, len %d %d\n%!" (Unchecked.tm_to_string coh_tgt) (Unchecked.ctx_to_string (Unchecked.ps_to_ctx ps_comp)) (List.length coh_tgt_sub_ps) (List.length (Unchecked.identity_ps ps_comp_red)) in
    let _ = check_term (Ctx.check (Unchecked.ps_to_ctx ps_comp)) coh_tgt in
    (* Construct map into pullback *)
    let ps_comp_sub_ps = Unchecked.pullback_up (d-1) ps ps_bdry_f (Unchecked.identity_ps ps) tgt_incl_f in
    (* Construct final coherence *)
    let intch = Coh(Coh.check_inv ps_comp coh_src coh_tgt ("intch_src",0,None),ps_comp_sub_ps) in
    let _ = Printf.printf "INTCH COH %s, len %d %d\n%!" (Unchecked.tm_to_string intch) (List.length ps_comp_sub_ps) (List.length (Unchecked.identity_ps ps_comp)) in
    let _ = check_term cc intch in
    let _ = Printf.printf "=========== DONE =============\n%!" in
    intch
(*
   Functorialisation of a coherence once with respect to a list of
   variables
*)
and coh_one_step coh l =
  let ps,t,(name,susp,func) = Coh.forget coh in
  let c = Unchecked.ps_to_ctx ps in
  let ctxf = ctx c l in
  let _,names,_ = Unchecked.db_levels ctxf in
  let psf = PS.forget (PS.mk (Ctx.check ctxf)) in
  let ty = ty t l (Coh(coh,Unchecked.identity_ps ps)) (Ctx.check ctxf) in
  let ty = Unchecked.rename_ty ty names in
  let pp_data = (name,susp,Some(add_functorialisation c func l)) in
  check_coh psf ty pp_data

(*
   Functorialisation a term once with respect to a list of triples.
   Returns a list containing the functorialise term followed by its
   target and its source.
 *)
and tm_one_step t l expl cc =
  if (not (Unchecked.tm_contains_vars t l)) then [t,expl]
  else
  match t with
  | Var v -> [Var(Var.Bridge(v)), true; Var(Var.Plus(v)), false; Var v, false]
  | Coh(c,s) ->
    begin
        let ps,_,_ = Coh.forget c in
        let cohf =
          let places = find_places (Unchecked.ps_to_ctx ps) s l in
          coh_one_step c places
        in
        let sf = sub s l cc in
        let tgt_incl = tgt_subst l in
        let s' = List.map (fun (t,expl) -> Unchecked.tm_apply_sub t tgt_incl,expl) s in
        [Coh(cohf,sf), true; Coh(c,s'), false; Coh(c,s), false]
    end
  | Meta_tm _ -> (raise FunctorialiseMeta)
and sub s l cc =
  match s with
  | [] -> []
  | (t, expl)::s ->
    List.append
      (tm_one_step t l expl cc)
      (sub s l cc)

(*
   Functorialisation a term possibly multiple times with respect to a
   functorialisation data
*)
let intch_test c t =
  let d = Unchecked.dim_ctx c in
  let l = List.filter_map (fun x -> if Unchecked.dim_ty (fst (snd x)) >= d-1 then Some(fst x) else None) c in
  (* let l,_next = list_functorialised c s in *)
  if l <> [] then
    let t = match t with
      | Coh(coh,s) -> begin
          let _ = Printf.printf "SUB: %s\n" (Unchecked.sub_ps_to_string s) in
          let ps,_,_ = Coh.forget coh in
          let l = find_places (Unchecked.ps_to_ctx ps) s l in
          let c,tgt_subst,f_vars = ctx (Unchecked.ps_to_ctx ps) l in
          (intch_src coh s l tgt_subst f_vars (Ctx.check c))
        end
      | _ -> assert false
    in c,t
  else c,t

let rec tm c t s =
  let l, next = list_functorialised c s in
  if l <> [] then
    let c = ctx c l in
    let t = fst (List.hd (tm_one_step t l true (Ctx.check c))) in
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
