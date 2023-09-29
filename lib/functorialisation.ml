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
let coh_one_step coh l =
  let ps,ty,(name,susp,func) = Unchecked.coh_data coh in
  let ctx_base = Unchecked.ps_to_ctx ps in
  let ctx,assocs = ctx_one_step ctx_base l in
  let tm = Coh (Cohdecl(ps,ty,(name,susp,func)),(Unchecked.identity_ps ctx_base)) in
  let tm_f = Unchecked.tm_apply_sub tm (target_subst assocs) in
  let ty = Arr (ty, tm, tm_f) in
  let ps = Kernel.PS.(forget (mk (Kernel.Ctx.check ctx))) in
  let _, names,_ = Unchecked.db_levels ctx in
  let ty = Unchecked.rename_ty ty names in
  let newf = add_functorialisation ctx_base func l in
  Cohdecl (ps,ty, (name,susp, Some newf))


(*
   Functorialisation of a coherence possibly multiple times, with
   respect to a functorialisation data
*)
let rec coh c s =
  let ps,_,_ = Unchecked.coh_data c in
  let ct = Unchecked.ps_to_ctx ps in
  let l, next = list_functorialised ct s in
  if l <> [] then coh (coh_one_step c l) next
  else c

(*
   Functorialisation of a coherence: exposed function
*)
let coh c s =
  try coh c s
  with
    NonMaximal x ->
    Error.functorialisation
      ("coherence: " ^ Unchecked.coh_to_string c)
      (Printf.sprintf "trying to functorialise with respect to variable %s which is not maximal" x)

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
let rec tm_one_step t l expl=
  match t with
  | Var v ->
    begin
      match List.assoc_opt v l with
      | Some (v',vf) -> [vf, true; v', false; Var v, false]
      | None -> [Var v, expl]
    end
  | Coh(c,s) ->
    begin
      match l with
      | _::_ ->
        let ps,_,_ = Unchecked.coh_data c in
        let cohf =
          let places = find_places (Unchecked.ps_to_ctx ps) s (List.map fst l) in
          coh_one_step c places
        in
        let sf = sub s l in
        let l' = target_subst l in
        let s' = List.map (fun (t,expl) -> Unchecked.tm_apply_sub t l',expl) s in
        [Coh(cohf,sf), true; Coh(c,s'), false; Coh(c,s), false]
      | [] -> [Coh(c,s), expl]
    end
  | Meta_tm _ -> (raise FunctorialiseMeta)
and sub s l =
  match s with
  | [] -> []
  | (t, expl)::s -> List.append (tm_one_step t l expl) (sub s l)

(*
   Functorialisation a term possibly mutliple times with respect to a
   functorialisation data
*)
let rec tm c t s =
  let l, next = list_functorialised c s in
  if l <> [] then
    let c,assocs = ctx_one_step c l in
    let t = fst (List.hd (tm_one_step t assocs true)) in
    tm c t next
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
