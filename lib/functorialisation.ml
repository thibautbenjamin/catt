open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

exception FunctorialiseMeta
exception WrongNumberOfArguments

let cubical_comp = ref (fun _ -> Error.fatal "Uninitialised forward reference")
let depth1_interchanger_src = ref (fun _ -> Error.fatal "Uninitialised forward reference")
let depth1_interchanger_tgt = ref (fun _ -> Error.fatal "Uninitialised forward reference")
let depth1_bridge_sub = ref (fun _ -> Error.fatal "Uninitialised forward reference")

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
and src_prod t l tm tm_t d n =
  match t with
  | Arr(ty',src,_tgt) when Unchecked.tm_contains_vars src l ->
    let whisk = whisk n 0 (d-n-1) in
    let ps,whisk_ty,_ = Coh.forget whisk in
    let prod, prod_ty = src_prod ty' l tm tm_t d (n-1) in
    let ty_f = ty ty' l src in
    let src_f = tm_one_step_tm src l in
    let sub_ps = whisk_sub_ps (d-n-1) src_f ty_f prod prod_ty in
    let sub = fst (Unchecked.sub_ps_to_sub sub_ps ps) in
    (Coh(whisk, sub_ps), Unchecked.ty_apply_sub whisk_ty sub)
  | Arr(_,_,_) | Obj -> (tm, tm_t)
  | _ -> raise FunctorialiseMeta
and tgt_prod t l tm tm_t d n =
  match t with
  | Arr(ty',_src,tgt) when Unchecked.tm_contains_vars tgt l ->
    let whisk = whisk n (d-n-1) 0 in
    let ps,whisk_ty,_ = Coh.forget whisk in
    let prod, prod_ty = tgt_prod ty' l tm tm_t d (n-1) in
    let ty_f = ty ty' l tgt in
    let tgt_f = tm_one_step_tm tgt l in
    let sub_ps = whisk_sub_ps 0 prod prod_ty tgt_f ty_f in
    let sub = fst (Unchecked.sub_ps_to_sub sub_ps ps) in
    (Coh(whisk, sub_ps), Unchecked.ty_apply_sub whisk_ty sub)
  | Arr(_,_,_) | Obj -> (tm, tm_t)
  | _ -> raise FunctorialiseMeta
and ty t l tm =
  let d = Unchecked.dim_ty t in
  let tgt_subst = tgt_subst l in
  let tm_incl = Unchecked.tm_apply_sub tm tgt_subst in
  let t_incl = Unchecked.ty_apply_sub t tgt_subst in
  let src, src_t = tgt_prod t l tm t d (d-1) in
  let tgt, _tgt_t = src_prod t l tm_incl t_incl d (d-1) in
  Arr (src_t, src, tgt)

and ctx c l =
  match c with
  | [] -> []
  | (x,(t,expl))::c when List.mem x l ->
    let ty_tgt = Unchecked.ty_apply_sub t (tgt_subst l) in
    let tf = ty t l (Var x) in
    (Var.Bridge(x),(tf,expl))::(Var.Plus(x),(ty_tgt,false))::(x,(t,false))::(ctx c l)
  | (x,a)::c -> (x,a)::(ctx c l)

and coh_depth_1 coh l =
  let intch_src,intch_src_ty = !depth1_interchanger_src coh l in
  let intch_tgt,intch_tgt_ty = !depth1_interchanger_tgt coh l in
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
  let bridge = !depth1_bridge_sub src_sub_ps tgt_sub_ps l in
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
  let ty = ty t l (Coh(coh,Unchecked.identity_ps ps)) in
  let ty = Unchecked.rename_ty ty names in
  let pp_data = (name,susp,Some(add_functorialisation c func l)) in
  check_coh psf ty pp_data

and coh_general coh l =
  let ps,_,_ = Coh.forget coh in
  let id = Unchecked.identity_ps ps in
  let c = Unchecked.ps_to_ctx ps in
  let depth0 = List.for_all
      (fun (x,(_,e)) -> (not(List.mem x l)) || e) c in
  let cohf = if depth0 then
      let sf = sub id l in
      let cohf = coh_one_step coh l in
      Coh(cohf,sf)
    else
      coh_depth_1 coh l
  in cohf

(*
   Functorialisation a term once with respect to a list of triples.
   Returns a list containing the functorialise term followed by its
   target and its source.
 *)
and tm_one_step t l expl =
  if (not (Unchecked.tm_contains_vars t l)) then [t,expl]
  else
    match t with
    | Var v -> [Var (Var.Bridge v), expl; Var (Var.Plus v), false; Var v, false]
    | Coh(coh,s) ->
      begin
        let t' = Unchecked.tm_apply_sub t (tgt_subst l) in
        let sf = sub s l in
        let ps,_,_ = Coh.forget coh in
        let psc = Unchecked.ps_to_ctx ps in
        let places = find_places psc s l in
        let pscf = ctx psc places in
        let cohf = coh_general coh places in
        let subf = Unchecked.list_to_sub (List.map fst sf) pscf in
        let tm = Unchecked.tm_apply_sub cohf subf in
        [tm, expl; t', false; t, false]
      end
    | Meta_tm _ -> (raise FunctorialiseMeta)
and tm_one_step_tm t l = fst (List.hd (tm_one_step t l true))
and sub s l =
  match s with
  | [] -> []
  | (t, expl)::s ->
    List.append
      (tm_one_step t l expl)
      (sub s l)

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
    let t = tm_one_step_tm t l in
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
