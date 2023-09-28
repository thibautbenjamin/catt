open Kernel
open Kernel.Unchecked_types

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
let list_functorialised l c =
  let rec list l c =
    match l,c with
    | [],[] -> [],[]
    | xf::l, (x,(_, true))::tgt ->
      let func,next_func_data = list l tgt in
      let func = if  xf > 0  then x::func else func in
      func,(xf-1)::next_func_data
    | (f::l), (_,(_, false))::tgt ->
      if !Settings.explicit_substitutions
      then list l tgt
      else list (f::l) tgt
    | [], (_,(_, false))::tgt ->
      if !Settings.explicit_substitutions
      then raise WrongNumberOfArguments
      else list [] tgt
    | _::_, [] |[],_::_ -> raise WrongNumberOfArguments
  in list l c

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

(*
   Functorialisation of a coherence once with respect to a list of
   variables
*)
let coh_one_step ps ty l =
  let ctx_base = Unchecked.ps_to_ctx ps in
  let ctx,assocs = ctx_one_step ctx_base l in
  let tm = Coh (Cohdecl(ps,ty),(Unchecked.identity_ps ctx_base)) in
  let tm_f = Unchecked.tm_apply_sub tm (target_subst assocs) in
  let ty = Arr (ty, tm, tm_f) in
  let ps = Kernel.PS.(forget (mk (Kernel.Ctx.check ctx))) in
  let _, names,_ = Unchecked.db_levels ctx in
  let ty = Unchecked.rename_ty ty names in
  ps,ty

(*
   Functorialisation of a coherence possibly multiple times, with
   respect to a functorialisation data
*)
let rec coh (ps,ty) s =
  let ct = Unchecked.ps_to_ctx ps in
  let l,next = list_functorialised s ct in
  if l <> [] then coh (coh_one_step ps ty l) next
  else ps,ty

(*
   Functorialisation of a coherence: exposed function
*)
let coh c s =
  let ps,ty = Unchecked.coh_data c in
  try let ps,ty = coh (ps,ty) s in Cohdecl(ps,ty)
  with
    NonMaximal x ->
    Error.functorialisation
      ("coherence: " ^ Unchecked.coh_to_string(Cohdecl(ps,ty)))
      (Printf.sprintf "trying to functorialise with respect to variable %s which is not maximal" x)

(*
   Given a context, a substitution and a list of variables, returns
   the list of all variables in the context whose corresponding term
   in the substitution contains a variable from the input list
*)
let rec find_places ctx s l =
  match ctx,s with
  | [], [] -> []
  | (x,(_,true))::c,  t::s when Unchecked.tm_contains_vars t l -> x::(find_places c s l)
  | _::c, _::s -> find_places c s l
  | [],_::_ | _::_,[] -> Error.fatal "functorialisation in a non-existant place"

(*
   Functorialisation a term once with respect to a list of triples.
   Returns a list containing the functorialise term followed by its
   target and its source.
*)
let rec tm_one_step t l =
  match t with
  | Var v ->
    begin
      match List.assoc_opt v l with
      | Some (v',vf) -> [vf; v'; Var v]
      | None -> [Var v]
    end
  | Coh(c,s) ->
    begin
      match l with
      | _::_ ->
        let ps = match c with
          | Cohdecl(ps,_) -> ps
          | Cohchecked c -> fst (Coh.forget c)
        in
        let cohf =
          let places = find_places (Unchecked.ps_to_ctx ps) s (List.map fst l) in
          let ps,ty = Unchecked.coh_data c in
          let ps,ty = coh_one_step ps ty places in
          Cohdecl(ps,ty)
        in
        let sf = sub s l in
        let l' = target_subst l in
        let s' = List.map (fun t -> Unchecked.tm_apply_sub t l') s in
        [Coh(cohf,sf);Coh(c,s');Coh(c,s)]
      | [] -> [Coh(c,s)]
    end
  | Meta_tm _ -> (raise FunctorialiseMeta)
and sub s l =
  match s with
  | [] -> []
  | t::s -> List.append (tm_one_step t l) (sub s l)

(*
   Functorialisation a term possibly mutliple times with respect to a
   functorialisation data
*)
let rec tm c t s =
  let l,next = list_functorialised s c in
  if l <> [] then
    let c,assocs = ctx_one_step c l in
    tm c (List.hd (tm_one_step t assocs)) next
  else c,t

(*
   Functorialisation a term: exposed function
*)
let tm c t s =
  try tm c t s
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
