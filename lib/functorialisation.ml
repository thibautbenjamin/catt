open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

exception FunctorialiseMeta
exception WrongNumberOfArguments

let builtin_ccomp :
  (int -> tm) ref =
  ref (fun _ -> Error.fatal "Uninitialised forward reference")

module Memo = struct
  let tbl_whisk = Hashtbl.create 97

  let find_whisk i f =
    try Hashtbl.find tbl_whisk i with
    | Not_found ->
      let res = f i in
      Hashtbl.add tbl_whisk i res;
      res
end


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

(* returns the n-composite of a (n+j)-cell with a (n+k)-cell *)
let rec whisk n j k =
  let build_whisk t =
    let n,j,k = t in
    let comp = Builtin.comp_n 2 in
    let func_data = [k;j] in
    Suspension.coh (Some(n)) (coh comp func_data)
  in
  Memo.find_whisk (n,j,k) build_whisk

(*
  How long should substitutions for whisk be?
  (whisk 0 0 0) requires ps-context (x(f)y(g)z) so 2+1+1+1
  (whisk n 0 0) requires 2*(n+1)+1+1+1
  (whisk n j 0) requires (2*(n+1))+((2*j)+1)+1+1
  (whisk n 0 k) requires (2*(n+1))+1+(2*k+1)+1

  Assuming ty1 has right dimension, we just need to know k
*)
and whisk_sub_ps k t1 ty1 t2 ty2 =
  let rec take n l =
    match l with
    | h::t when n > 0 -> h::(take (n-1) t)
    | _ -> [] in
  let sub_base = Unchecked.ty_to_sub_ps ty1 in
  let sub_ext = take (2*k+1) (Unchecked.ty_to_sub_ps ty2) in
  List.concat [[(t2,true)];sub_ext;[(t1,true)];sub_base]


(* Invariant maintained:
    src_prod returns a term of same dimension as tm
*)
and src_prod t l tm tm_t d n ctxf =
  match t with
  | Arr(ty',src,_tgt) when Unchecked.tm_contains_vars src l ->
    let whisk = whisk n 0 (d-n-1) in
    let ps,whisk_ty,_ = Coh.forget whisk in
    let prod, prod_ty = src_prod ty' l tm tm_t d (n-1) ctxf in
    let ty_f = ty ty' l src ctxf in
    let src_f = tm_one_step_tm src l ctxf in
    let sub_ps = whisk_sub_ps (d-n-1) src_f ty_f prod prod_ty in
    let sub = fst (Unchecked.sub_ps_to_sub sub_ps ps) in
    let _ = check_term (Ctx.check ctxf) (Coh(whisk, sub_ps)) in
    (Coh(whisk, sub_ps), Unchecked.ty_apply_sub whisk_ty sub)
  | Arr(_,_,_) | Obj -> (tm, tm_t)
  | _ -> raise FunctorialiseMeta
and tgt_prod t l tm tm_t d n ctxf =
  match t with
  | Arr(ty',_src,tgt) when Unchecked.tm_contains_vars tgt l ->
    let whisk = whisk n (d-n-1) 0 in
    let ps,whisk_ty,_ = Coh.forget whisk in
    let prod, prod_ty = tgt_prod ty' l tm tm_t d (n-1) ctxf in
    let ty_f = ty ty' l tgt ctxf in
    let tgt_f = tm_one_step_tm tgt l ctxf in
    let sub_ps = whisk_sub_ps 0 prod prod_ty tgt_f ty_f in
    let sub = fst (Unchecked.sub_ps_to_sub sub_ps ps) in
    let _ = check_term (Ctx.check ctxf) (Coh(whisk, sub_ps)) in
    (Coh(whisk, sub_ps), Unchecked.ty_apply_sub whisk_ty sub)
  | Arr(_,_,_) | Obj -> (tm, tm_t)
  | _ -> raise FunctorialiseMeta
and ty t l tm ctxf =
  let d = Unchecked.dim_ty t in
  let tgt_subst = tgt_subst l in
  let tm_incl = Unchecked.tm_apply_sub tm tgt_subst in
  let t_incl = Unchecked.ty_apply_sub t tgt_subst in
  let src, src_t = tgt_prod t l tm t d (d-1) ctxf in
  let tgt, _tgt_t = src_prod t l tm_incl t_incl d (d-1) ctxf in
  Arr (src_t, src, tgt)

and ctx c l =
  match c with
  | [] -> []
  | (x,(t,expl))::c when List.mem x l ->
    let c_ext = (Var.Plus(x),(Unchecked.ty_apply_sub t (tgt_subst l),false))::(x,(t,false))::(ctx c l) in
    let tf = ty t l (Var x) c_ext in
    (Var.Bridge(x),(tf,expl))::c_ext
  | (x,a)::c -> (x,a)::(ctx c l)

(* Interchange needed for source of depth-1 non-inv coh *)
(*
https://q.uiver.app/#q=WzAsOCxbMSwwLCJcXHBhcnRpYWxcXEdhbW1hIl0sWzIsMSwiXFxvdmVycmlnaHRhcnJvd3tcXHBhcnRpYWxcXEdhbW1hfV57WF9cXHRhdX0iXSxbMCwzLCJcXEdhbW1hIl0sWzAsMSwiXFxHYW1tYV57cmVkfSJdLFsxLDIsIlxcRGVsdGEiXSxbMSwzLCJcXFBoaSJdLFszLDIsIlxcRGVsdGFee3JlZH0iXSxbMSw0LCJcXG92ZXJyaWdodGFycm93e1xcR2FtbWF9XlgiXSxbMCwxLCJcXHNpZ21hIl0sWzAsMiwiXFx0YXUiLDEseyJsYWJlbF9wb3NpdGlvbiI6NzAsImN1cnZlIjo1fV0sWzMsMiwiXFxyaG9fXFxHYW1tYSIsMl0sWzAsMywiXFx0YXVfciIsMV0sWzEsNCwial8yIiwxXSxbMyw0LCJqXzEiLDFdLFs0LDAsIiIsMCx7InN0eWxlIjp7Im5hbWUiOiJjb3JuZXIifX1dLFs0LDUsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsyLDUsImlfMSIsMV0sWzEsNSwiaV8yIiwxXSxbNSwwLCIiLDEseyJzdHlsZSI6eyJuYW1lIjoiY29ybmVyIn19XSxbNiw0LCJcXHJob19cXERlbHRhIiwxLHsiY3VydmUiOjF9XSxbMiw3XSxbMSw3LCJcXG92ZXJyaWdodGFycm93e1xcdGF1fV5YIiwxLHsiY3VydmUiOi0zfV0sWzUsNywiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d
 *)
and intch_src coh l ctxf =
  (* Setup *)
  let gamma,coh_ty,name = Coh.forget coh in
  let d = Unchecked.dim_ps gamma in
  (* Construct preimage locations *)
  let bdry = Unchecked.ps_bdry gamma in
  let tau = Unchecked.ps_tgt gamma in
  let _,bdry_c = Unchecked.sub_ps_to_sub tau bdry in
  let l_tau = find_places bdry_c tau l in
  (* Construct ps_bdry_f *)
  let bdry_f_ctx = ctx bdry_c l_tau in
  let bdry_f_db = Unchecked.db_level_sub_inv bdry_f_ctx in
  let bdry_f = PS.forget (PS.mk (Ctx.check bdry_f_ctx)) in
  let tau_f = sub tau l ctxf in
  (* Construct composite context *)
  let phi,i1_ps,i2_ps = Unchecked.ps_compose (d-1) gamma bdry_f in
  let i1,_ = Unchecked.sub_ps_to_sub i1_ps gamma in
  let i2,_ = Unchecked.sub_ps_to_sub i2_ps bdry_f in
  (* Construct source (t[i1]) * (tgt_f[i2]) *)
  let src,tgt,ty_base = Coh.noninv_srctgt coh in
  let tgt_f_ty = ty ty_base l_tau tgt bdry_c in
  let tgt_f_ty = Unchecked.ty_apply_sub (Unchecked.ty_apply_sub tgt_f_ty bdry_f_db) i2 in
  let tgt_f = tm_one_step_tm tgt l_tau bdry_f_ctx in
  let tgt_f = Unchecked.tm_apply_sub (Unchecked.tm_apply_sub tgt_f bdry_f_db) i2 in
  let coh_src_sub_ps = whisk_sub_ps 0 (Coh(coh,i1_ps)) (Unchecked.ty_apply_sub coh_ty i1) tgt_f tgt_f_ty in
  let coh_src = Coh(whisk (d-1) 0 0,coh_src_sub_ps) in
  let _ = check_term (Ctx.check (Unchecked.ps_to_ctx phi)) coh_src in
  (* Construct reduced context *)
  let gamma_red = Ps_reduction.reduce (d-1) gamma in
  let delta,_,_ = Unchecked.ps_compose (d-1) gamma_red bdry_f in
  let delta_red = Ps_reduction.reduce (d-1) delta in
  let rho_delta = Ps_reduction.reduction_sub delta in
  (* Construct biased reduction sub from phi to delta_red *)
  let rho_gamma_i1 = Unchecked.sub_ps_apply_sub (Ps_reduction.reduction_sub gamma) i1 in
  let delta_ind = Unchecked.pullback_up (d-1) gamma_red bdry_f rho_gamma_i1 i2_ps in
  (* Construct target (comp delta_red src tgt) *)
  let coh_tgt_coh = Coh.check_noninv delta_red src tgt ((Unchecked.full_name name)^"_red",0,None) in
  let coh_tgt_sub_ps = Unchecked.sub_ps_apply_sub rho_delta (fst (Unchecked.sub_ps_to_sub delta_ind delta)) in
  let coh_tgt = Coh(coh_tgt_coh, coh_tgt_sub_ps) in
  let _ = check_term (Ctx.check (Unchecked.ps_to_ctx phi)) coh_tgt in
  (* Construct map into pullback *)
  let phi_ind_sub_ps = Unchecked.pullback_up (d-1) gamma bdry_f (Unchecked.identity_ps gamma) tau_f in
  let phi_ind,_ = Unchecked.sub_ps_to_sub phi_ind_sub_ps phi in
  (* Construct final coherence *)
  let intch_coh = Coh.check_inv phi coh_src coh_tgt ("intch_src",0,None) in
  let _,intch_ty,_ = Coh.forget intch_coh in
  let intch = Coh(intch_coh,phi_ind_sub_ps) in
  let _ = check_term (Ctx.check ctxf) intch in
  intch, Unchecked.ty_apply_sub intch_ty phi_ind
(*
https://q.uiver.app/#q=WzAsOCxbMSwwLCJcXHBhcnRpYWxcXEdhbW1hIl0sWzIsMSwiXFxvdmVycmlnaHRhcnJvd3tcXHBhcnRpYWxcXEdhbW1hfV57WF9cXHRhdX0iXSxbMCwzLCJcXEdhbW1hIl0sWzAsMSwiXFxHYW1tYV57cmVkfSJdLFsxLDIsIlxcRGVsdGEiXSxbMSwzLCJcXFBoaSJdLFszLDIsIlxcRGVsdGFee3JlZH0iXSxbMSw0LCJcXG92ZXJyaWdodGFycm93e1xcR2FtbWF9XlgiXSxbMCwxLCJcXHNpZ21hIl0sWzAsMiwiXFx0YXUiLDEseyJsYWJlbF9wb3NpdGlvbiI6NzAsImN1cnZlIjo1fV0sWzMsMiwiXFxyaG9fXFxHYW1tYSIsMl0sWzAsMywiXFx0YXVfciIsMV0sWzEsNCwial8yIiwxXSxbMyw0LCJqXzEiLDFdLFs0LDAsIiIsMCx7InN0eWxlIjp7Im5hbWUiOiJjb3JuZXIifX1dLFs0LDUsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsyLDUsImlfMSIsMV0sWzEsNSwiaV8yIiwxXSxbNSwwLCIiLDEseyJzdHlsZSI6eyJuYW1lIjoiY29ybmVyIn19XSxbNiw0LCJcXHJob19cXERlbHRhIiwxLHsiY3VydmUiOjF9XSxbMiw3XSxbMSw3LCJcXG92ZXJyaWdodGFycm93e1xcdGF1fV5YIiwxLHsiY3VydmUiOi0zfV0sWzUsNywiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d
 *)
and intch_tgt coh l ctxf =
  (* Setup *)
  let gamma,coh_ty,name = Coh.forget coh in
  let d = Unchecked.dim_ps gamma in
  (* Construct preimage locations *)
  let bdry = Unchecked.ps_bdry gamma in
  let sigma = Unchecked.ps_src gamma in
  let _,bdry_c = Unchecked.sub_ps_to_sub sigma bdry in
  let l_sigma = find_places bdry_c sigma l in
  (* Construct ps_bdry_f *)
  let bdry_f_ctx = ctx bdry_c l_sigma in
  let bdry_f_db = Unchecked.db_level_sub_inv bdry_f_ctx in
  let bdry_f = PS.forget (PS.mk (Ctx.check bdry_f_ctx)) in
  let sigma_f = sub sigma l ctxf in
  (* Construct composite context *)
  let phi,i1_ps,i2_ps = Unchecked.ps_compose (d-1) bdry_f gamma in
  let i1,_ = Unchecked.sub_ps_to_sub i1_ps bdry_f in
  let i2,_ = Unchecked.sub_ps_to_sub i2_ps gamma in
  (* Construct target (src_f[i1]) * (t[i2]) *)
  let src,tgt,ty_base = Coh.noninv_srctgt coh in
  let src_f_ty = ty ty_base l_sigma src bdry_c in
  let src_f_ty = Unchecked.ty_apply_sub (Unchecked.ty_apply_sub src_f_ty bdry_f_db) i1 in
  let src_f = tm_one_step_tm src l_sigma bdry_f_ctx in
  let src_f = Unchecked.tm_apply_sub (Unchecked.tm_apply_sub src_f bdry_f_db) i1 in
  let coh_tgt_sub_ps = whisk_sub_ps 0 src_f src_f_ty (Coh(coh,i2_ps)) (Unchecked.ty_apply_sub coh_ty i2) in
  let coh_tgt = Coh(whisk (d-1) 0 0,coh_tgt_sub_ps) in
  let _ = check_term (Ctx.check (Unchecked.ps_to_ctx phi)) coh_tgt in
  (* Construct reduced context *)
  let gamma_red = Ps_reduction.reduce (d-1) gamma in
  let delta,_,_ = Unchecked.ps_compose (d-1) bdry_f gamma_red in
  let delta_red = Ps_reduction.reduce (d-1) delta in
  let rho_delta = Ps_reduction.reduction_sub delta in
  (* Construct biased reduction sub from phi to delta_red *)
  let rho_gamma_i2 = Unchecked.sub_ps_apply_sub (Ps_reduction.reduction_sub gamma) i2 in
  let delta_ind = Unchecked.pullback_up (d-1) bdry_f gamma_red i1_ps rho_gamma_i2 in
  (* Construct source (comp delta_red src tgt) *)
  let coh_src_coh = Coh.check_noninv delta_red src tgt ((Unchecked.full_name name)^"_red",0,None) in
  let coh_src_sub_ps = Unchecked.sub_ps_apply_sub rho_delta (fst (Unchecked.sub_ps_to_sub delta_ind delta)) in
  let coh_src = Coh(coh_src_coh, coh_src_sub_ps) in let _ = check_term (Ctx.check (Unchecked.ps_to_ctx phi)) coh_src in
  (* Construct map into pullback *)
  let phi_ind_sub_ps = Unchecked.pullback_up (d-1) bdry_f gamma sigma_f (Unchecked.sub_ps_apply_sub (Unchecked.identity_ps gamma) (tgt_subst l)) in
  let phi_ind,_ = Unchecked.sub_ps_to_sub phi_ind_sub_ps phi in
  (* Construct final coherence *)
  let intch_coh = Coh.check_inv phi coh_src coh_tgt ("intch_tgt",0,None) in
  let _,intch_ty,_ = Coh.forget intch_coh in
  let intch = Coh(intch_coh,phi_ind_sub_ps) in
  let _ = check_term (Ctx.check ctxf) intch in
  intch, Unchecked.ty_apply_sub intch_ty phi_ind
and bridge_depth_1 src_sub tgt_sub l ctxf =
  match src_sub,tgt_sub with
  | [],[] -> []
  | (src,expl)::src_tl,(tgt,_)::tgt_l ->
    begin try
        let _ = Unchecked.check_equal_tm src tgt in
        (src,expl)::(bridge_depth_1 src_tl tgt_l l ctxf)
      with NotEqual(_) ->
        let (_,ty,_),src_sub = match src with
          | Coh(c,s) -> Coh.forget c,s
          | _ -> assert false in
        let d = Unchecked.dim_ty ty in
        let src_bridge = fst (List.nth src_sub 2) in
        let inner_sub,arity = match src_bridge with
          | Coh(_,s) -> s,((List.length s)-(2*d))/2+1
          | _ -> assert false in
        let linear_ps,_,_ = Coh.forget (Builtin.comp_n arity) in
        let linear_ctx = Unchecked.ps_to_ctx linear_ps in
        let linear_ctxf = ctx linear_ctx (List.map fst linear_ctx) in
        let _ = check_term (Ctx.check linear_ctxf) (Unchecked.tm_apply_sub (Opposite.tm (!builtin_ccomp arity) [2]) (Unchecked.db_level_sub linear_ctxf)) in
        let ccomp = Suspension.tm (Some(d-1)) (Opposite.tm (!builtin_ccomp arity) [2]) in
        let inner_subf = sub inner_sub l ctxf in
        let inner_subf_norm = Unchecked.list_to_db_level_sub (List.map fst inner_subf) in
        let bridge = Unchecked.tm_apply_sub ccomp inner_subf_norm in
        let _ = check_term (Ctx.check ctxf) bridge in
        (bridge,expl)::(tgt,false)::(src,false)::(bridge_depth_1 src_tl tgt_l l ctxf)
    end
  | _,_ -> assert false
and coh_depth_1 coh l ctxf =
  let intch_src,intch_src_ty = intch_src coh l ctxf in
  let intch_tgt,intch_tgt_ty = intch_tgt coh l ctxf in
  let base_ty,inner_src,inner_tgt,final_tgt = match intch_src_ty,intch_tgt_ty with
    | Arr(b,_,s), Arr(_,t,t') -> b,s,t,t'
    | _,_ -> assert false in
  let c,src_sub_ps,tgt_sub_ps = match inner_src,inner_tgt with
    | Coh(c,s), Coh(_,s') -> c,s,s'
    | _,_ -> assert false in
  let ps,_,_ = Coh.forget c in
  let src_sub,_ctx = Unchecked.sub_ps_to_sub src_sub_ps ps in
  let tgt_sub,_ = Unchecked.sub_ps_to_sub tgt_sub_ps ps in
  let coh_l = List.filter_map (fun (s,t) -> try Unchecked.check_equal_tm (snd s) (snd t); None with NotEqual _ -> Some(fst s)) (List.combine src_sub tgt_sub) in
  let cohf = coh_one_step c coh_l in
  let bridge = bridge_depth_1 src_sub_ps tgt_sub_ps l ctxf in
  let middle = Coh(cohf,bridge) in
  (* Combine *)
  let comp_sub_ps = List.concat [[intch_tgt,true;final_tgt,false;middle,true;inner_tgt,false;intch_src,true];Unchecked.ty_to_sub_ps intch_src_ty] in
  let comp = Suspension.coh (Some((Unchecked.dim_ty base_ty))) (Builtin.comp_n 3) in
  Coh(comp, comp_sub_ps)

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
  let ty = ty t l (Coh(coh,Unchecked.identity_ps ps)) ctxf in
  let ty = Unchecked.rename_ty ty names in
  let pp_data = (name,susp,Some(add_functorialisation c func l)) in
  check_coh psf ty pp_data

and coh_general coh l ctxf =
  let ps,_,_ = Coh.forget coh in
  let id = Unchecked.identity_ps ps in
  let c = Unchecked.ps_to_ctx ps in
  let depth0 = List.for_all
      (fun (x,(_,e)) -> (not(List.mem x l)) || e) c in
  let cohf = if depth0 then
      let sf = sub id l ctxf in
      let cohf = coh_one_step coh l in
      Coh(cohf,sf)
    else
      coh_depth_1 coh l ctxf
  in
  let _ = check_term (Ctx.check ctxf) cohf in
  cohf

(*
   Functorialisation a term once with respect to a list of triples.
   Returns a list containing the functorialise term followed by its
   target and its source.
 *)
and tm_one_step t l expl ctxf =
  if (not (Unchecked.tm_contains_vars t l)) then [t,expl]
  else
    match t with
    | Var v -> [Var (Var.Bridge v), expl; Var (Var.Plus v), false; Var v, false]
    | Coh(coh,s) ->
      begin
        let t' = Unchecked.tm_apply_sub t (tgt_subst l) in
        let sf = sub s l ctxf in
        let ps,_,_ = Coh.forget coh in
        let psc = Unchecked.ps_to_ctx ps in
        let places = find_places psc s l in
        let pscf = ctx psc places in
        let cohf = coh_general coh places pscf in
        let subf = Unchecked.list_to_sub (List.map fst sf) pscf in
        let tm = Unchecked.tm_apply_sub cohf subf in
        [tm, expl; t', false; t, false]
      end
    | Meta_tm _ -> (raise FunctorialiseMeta)
and tm_one_step_tm t l ctxf = fst (List.hd (tm_one_step t l true ctxf))
and sub s l ctxf =
  match s with
  | [] -> []
  | (t, expl)::s ->
    List.append
      (tm_one_step t l expl ctxf)
      (sub s l ctxf)

(*
   Functorialisation of a coherence possibly multiple times, with
   respect to a functorialisation data
*)
and coh c s =
  let ps,_,_ = Coh.forget c in
  let ctx = Unchecked.ps_to_ctx ps in
  let l, next = list_functorialised ctx s in
  if l <> [] then coh (coh_one_step c l) next else c

let rec tm c t s =
  let l, next = list_functorialised c s in
  if l <> [] then
    let c = ctx c l in
    let t = tm_one_step_tm t l c in
    tm c t next
  else c,t

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
