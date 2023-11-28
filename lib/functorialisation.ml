open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

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

let ty_contains_vars t l =
  match t with
  | Obj -> false
  | Arr(_,u,v) ->
    Unchecked.tm_contains_vars u l ||
    Unchecked.tm_contains_vars v l
  | _ -> assert false

let rec ty t l tgt_subst f_vars tm =
  if ty_contains_vars t l then
    let t_base,src,tgt =
      match t with
      | Arr(ty,src,tgt) -> ty,src,tgt
      | _ -> assert false
    in
    let src_f = fst (List.hd (tm_one_step_codim0 src tgt_subst f_vars true)) in
    let tgt_f = fst (List.hd (tm_one_step_codim0 tgt tgt_subst f_vars true)) in
    let n = Unchecked.dim_ty t_base in
    let comp2 = Suspension.coh (Some n) (Builtin.comp_n 2) in
    let coh_tgt = Unchecked.tm_apply_sub tm tgt_subst in
    let src_incl = Unchecked.tm_apply_sub src tgt_subst in
    let tgt_incl = Unchecked.tm_apply_sub tgt tgt_subst in
    let sub_base = Unchecked.ty_to_sub_ps t_base in
    let comp_src_sub = (tgt_f,true)::(tgt_incl,false)::(tm,true)::(tgt,false)::(src,false)::sub_base
    in
    let comp_tgt_sub = (coh_tgt,true)::(tgt_incl,false)::(src_f,true)::(src_incl,false)::(src,false)::sub_base in
    let comp_src = Coh(comp2, comp_src_sub) in
    let comp_tgt = Coh(comp2, comp_tgt_sub) in
    Arr (t_base, comp_src, comp_tgt)
  else
    let tm_f = Unchecked.tm_apply_sub tm (tgt_subst) in
    Arr (t, tm, tm_f)

and ctx c l =
  match c with
  | [] -> [],[],[]
  | (x,(t,expl))::c when List.mem x l ->
     let c,tgt_subst,f_vars = ctx c l in
     let x' = Var.fresh() in
     let xf = Var.fresh() in
     let tgt_subst = (x,Var x')::tgt_subst in
     let tf = ty t l tgt_subst f_vars (Var x) in
     (xf,(tf,expl))::(x',(t,false))::(x,(t,false))::c,
     tgt_subst,
     (x, (Var x',Var xf))::f_vars
  | (x,a)::c -> let c,tgt_subst,f_terms = ctx c l in (x,a)::c, tgt_subst,f_terms

(*
   Functorialisation of a coherence once with respect to a list of
   variables
*)
and coh_one_step coh l =
  Utils.coh_transformation
    ~compute_ps_ty:
      (fun p t ->
         let new_ctx,tgt_subst,f_vars = ctx (Unchecked.ps_to_ctx p) l in
         let ty = ty t l tgt_subst f_vars (Coh(coh,Unchecked.identity_ps p)) in
         new_ctx,ty)
    ~compute_name:(fun ctx (name,susp,func) ->
        let newf = add_functorialisation ctx func l in
        (name,susp, Some newf))
    coh

(*
   Functorialisation a term once with respect to a list of triples.
   Returns a list containing the functorialise term followed by its
   target and its source.
 *)
and tm_one_step_codim0 t tgt_subst f_vars expl =
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
        let sf = sub s tgt_subst f_vars in
        let s' = List.map (fun (t,expl) -> Unchecked.tm_apply_sub t tgt_subst ,expl) s in
        [Coh(cohf,sf), true; Coh(c,s'), false; Coh(c,s), false]
      | [] -> [Coh(c,s), expl]
    end
  | Meta_tm _ -> (raise FunctorialiseMeta)
and sub s tgt_subst f_vars =
  match s with
  | [] -> []
  | (t, expl)::s ->
    List.append
      (tm_one_step_codim0 t tgt_subst f_vars expl)
      (sub s tgt_subst f_vars)

(*
   Functorialisation a term possibly multiple times with respect to a
   functorialisation data
*)
and tm_codim0 c t s =
  let l, next = list_functorialised c s in
  if l <> [] then
    let c,tgt_subst,f_vars = ctx c l in
    let t = fst (List.hd (tm_one_step_codim0 t tgt_subst f_vars true)) in
    tm_codim0 c t next
  else c,t

let _tm_codim1 _c t _s =
  let _coh, _sub =
    match t with
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
  let ps,_,_ = Coh.forget c in
  let ctx = Unchecked.ps_to_ctx ps in
  let l, next = list_functorialised ctx s in
  if l <> [] then
    coh (coh_one_step c l) next
  else c


(*
   Functorialisation of a coherence: exposed function
*)
let coh c s =
  try
    coh c s
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
  try tm_codim0 c t s
  with
  | FunctorialiseMeta ->
    Error.functorialisation
      ("term: " ^ Unchecked.tm_to_string t)
      (Printf.sprintf "cannot functorialise meta-variables")
  | WrongNumberOfArguments ->
    Error.parsing_error
      ("term: " ^ (Unchecked.tm_to_string t))
      "wrong number of arguments provided"
