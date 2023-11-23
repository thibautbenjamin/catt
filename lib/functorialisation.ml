open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

exception NonMaximal of string
exception FunctorialiseMeta
exception WrongNumberOfArguments

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

(*
   Functorialisation of a context wrt a variable. For contexts,
   successive functorialisation operations commute. Returns the
   functorialised context as well as a triple indicating the variable
   that got functorialised, its copy and the new variable representing
   the higher cell from the original to the copy
*)
let ctx_one_var c x =
  let x',xf = Unchecked.two_fresh_vars c in
  let rec find c =
    match c with
    | [] -> Error.fatal "computing functorialisation with respect to an unknown variable"
    | (y,(t, true))::c when x = y ->
      (xf, (Arr(t,Var x,Var x'), true)) ::
      (x', (t, false)) ::
      (y, (t, false)) :: c
    | (y,(_, false))::_ when x = y ->
      raise (NonMaximal (Var.to_string x))
    | a::c -> a::(find c)
  in find c, (x, (Var x', Var xf))

(*
   Functorialisation of a context with respect to a list of variables.
   Returns a functorialised context and a list of triplets
*)
let ctx_one_step c l =
  List.fold_left
    (fun (c,assocs) x -> let c,p = ctx_one_var c x in c, p::assocs)
    (c,[])
    l

let target_subst l =
  List.map (fun (x,(y,_)) -> (x,y)) l

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
   Functorialisation of a coherence once with respect to a list of
   variables
*)
let coh_one_step_codim0 coh l =
  let ps,_,(name,susp,func) = Coh.forget coh in
  let ctx_base = Unchecked.ps_to_ctx ps in
  let ctx,_ = ctx_one_step (Unchecked.ps_to_ctx ps) l in
  let tm = Coh (coh,(Unchecked.identity_ps ps)) in
  let newf = add_functorialisation ctx_base func l in
  Coh.check_noninv (PS.forget (PS.mk (Ctx.check ctx))) tm tm (name,susp,Some newf)

(*
   Given a context, a substitution and a list of variables, returns
   the list of all variables in the context whose corresponding term
   in the substitution contains a variable from the input list
*)
let rec find_places ctx s l =
  match ctx,s with
  | [], [] -> []
  | (x,(_,true))::c,  (t,_)::s when Unchecked.tm_contains_vars t l -> x::(find_places c s l)
  | _::c, _::s -> find_places c s l
  | [],_::_ | _::_,[] -> Error.fatal "functorialisation in a non-existant place"

(*
   Functorialisation a term once with respect to a list of triples.
   Returns a list containing the functorialise term followed by its
   target and its source.
*)
let rec tm_one_step_codim0 t l expl=
  match t with
  | Var v ->
    begin
      match List.assoc_opt v l with
      | Some (v',vf) -> [vf, true; v', false; Var v, false]
      | None -> [Var v, expl]
    end
  | Coh(c,s) ->
    begin
      if List.exists (fun (x,_) -> Unchecked.tm_contains_var t x) l
      then
        let ps,_,_ = Coh.forget c in
        let cohf =
          let places = find_places (Unchecked.ps_to_ctx ps) s (List.map fst l) in
          coh_one_step_codim0 c places
        in
        let sf = sub s l in
        let l' = target_subst l in
        let s' = List.map (fun (t,expl) -> Unchecked.tm_apply_sub t l', expl) s in
        [Coh(cohf,sf), true;Coh(c,s'), false;Coh(c,s), false]
      else [Coh(c,s), expl]
    end
  | Meta_tm _ -> (raise FunctorialiseMeta)
and sub s l =
  match s with
  | [] -> []
  | (t, expl)::s -> List.append (tm_one_step_codim0 t l expl) (sub s l)

(*
   Functorialisation a term possibly multiple times with respect to a
   functorialisation data
*)
let rec tm_codim0 c t s =
  let l, next = list_functorialised c s in
  if l <> [] then
    let c,assocs = ctx_one_step c l in
    let t = fst (List.hd (tm_one_step_codim0 t assocs true)) in
    tm_codim0 c t next
  else c,t

(*
   Codim 1
   Functorialisation of a coherence once with respect to a list of
   variables
*)
let coh_one_step_codim1 coh l =
  let ps_base,ty,(name,susp,func) = Coh.forget coh in
  let ty_base,src,tgt = match ty with
    | Arr(ty_base,src,tgt) -> ty_base,src,tgt
    | Meta_ty _ -> Error.fatal "functorialising coherence with meta type"
    | Obj ->
      Error.functorialisation
        ("type: " ^ Unchecked.ty_to_string ty)
        (Printf.sprintf "attempted to functorialise a coherence of type *")
  in let ctx_base = Unchecked.ps_to_ctx ps_base in
  let ctx,assocs = ctx_one_step ctx_base l in
  let ps = Kernel.PS.(forget (mk (Kernel.Ctx.check ctx))) in
  let _, names,_ = Unchecked.db_levels ctx in
  let subst = target_subst assocs in
  let src_f = fst (List.hd (tm_one_step_codim0 src assocs true)) in
  let tgt_f = fst (List.hd (tm_one_step_codim0 tgt assocs true)) in
  let n = Unchecked.dim_ty ty in
  let comp2 = Suspension.coh (Some (n-1)) (Builtin.comp_n 2) in
  let coh_src = Coh(coh, (Unchecked.identity_ps ps_base)) in
  let coh_tgt = Unchecked.tm_apply_sub coh_src subst in
  let src_incl = Unchecked.tm_apply_sub src subst in
  let tgt_incl = Unchecked.tm_apply_sub tgt subst in
  let comp_src_sub = ([(tgt_f,true);(tgt_incl,false);(coh_src,true);(tgt,false);(src,false)]) @ (Unchecked.ty_to_sub_ps ty_base)
  in
  let comp_tgt_sub = [(coh_tgt,true);(tgt_incl,false);(src_f,true);(src_incl,false);(src,false)] @ (Unchecked.ty_to_sub_ps ty_base) in
  let comp_src = Coh(comp2, comp_src_sub) in
  let comp_tgt = Coh(comp2, comp_tgt_sub) in
  let ty = Arr (ty, comp_src, comp_tgt) in
  let ty = Unchecked.rename_ty ty names in
  Io.debug "About to check source term";
  let _ = check_term (Ctx.check ctx) comp_src in
  Io.debug "About to check target term";
  let _ = check_term (Ctx.check ctx) comp_tgt in
  let newf = add_functorialisation ctx_base func l in
  Io.debug "About to check whole thing";
  check_coh ps ty (name,susp, Some newf)

let dim_var ctx v =
  let (ty,_) = List.assoc v ctx in
  Unchecked.dim_ty ty

let contains_codim1 ctx l d =
  List.exists (fun v -> dim_var ctx v = d-1) l

let _tm_codim1 _c t _s =
  let _coh, _sub = match t with
    | Coh(coh, sub) -> coh, sub
    | _ ->
      Error.functorialisation
        ("term: " ^ Unchecked.tm_to_string t)
        (Printf.sprintf "attempted to functorialise a term which is not a coherence")
  in
  Error.fatal "codim 1 functorialisation for terms not yet implemented"

(*
   Functorialisation of a coherence possibly multiple times, with
   respect to a functorialisation data
*)
let rec coh c s =
  let ps,ty,_ = Coh.forget c in
  let d = Unchecked.dim_ty ty in
  let ctx = Unchecked.ps_to_ctx ps in
  let l, next = list_functorialised ctx s in
  if contains_codim1 ctx l d then
    coh (coh_one_step_codim1 c l) next
  else if l <> [] then
    coh (coh_one_step_codim0 c l) next
  else c


(*
   Functorialisation of a coherence: exposed function
*)
let coh c s =
  try
    coh c s
  with
    NonMaximal x ->
    Error.functorialisation
      ("coherence: " ^ Coh.to_string c)
      (Printf.sprintf "trying to functorialise with respect to variable %s which is not maximal" x)
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
  try tm_codim0 c t s
  with
  | NonMaximal x ->
    Error.functorialisation
      ("term: " ^ Unchecked.tm_to_string t)
      (Printf.sprintf "cannot functorialise with respect to variable %s which is not maximal" x)
  | FunctorialiseMeta ->
    Error.functorialisation
      ("term: " ^ Unchecked.tm_to_string t)
      (Printf.sprintf "cannot functorialise meta-variables")
  | WrongNumberOfArguments ->
    Error.parsing_error
      ("term: " ^ (Unchecked.tm_to_string t))
      "wrong number of arguments provided"
