open Kernel
open Kernel.Unchecked_types

exception NonMaximal of string
exception FunctorialiseMeta
exception WrongNumberOfArguments

let list_functorialised l c =
  let rec list l c =
    match l,c with
    | [],[] -> []
    | xf::l, (x,(_, true))::tgt ->
      let func = list l tgt in
      (x,xf)::func
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

let ctx c l =
  List.fold_left
    (fun (c,assocs) (x,i) ->
       if i > 0 then
         let c,p = ctx_one_var c x in c, p::assocs
       else
         c, assocs)
    (c,[])
    l

let target_subst l =
  List.map (fun (x,(y,_)) -> (x,y)) l

let coh coh s =
  let ps,ty = Unchecked.coh_data coh in
  let ct = Unchecked.ps_to_ctx ps in
  let l = list_functorialised s ct in
  if List.exists (fun (_,i) -> i > 0) l then
    try
      let ctx_base = Unchecked.ps_to_ctx ps in
      let ctx,assocs = ctx ctx_base l in
      let tm = Coh (Cohdecl(ps,ty),(Unchecked.identity_ps ctx_base)) in
      let tm_f = Unchecked.tm_apply_sub tm (target_subst assocs) in
      let ty = Arr (ty, tm, tm_f) in
      let ps = Kernel.PS.(forget (mk (Kernel.Ctx.check ctx))) in
      let _, names,_ = Unchecked.db_levels ctx in
      let ty = Unchecked.rename_ty ty names in
      Cohdecl(ps, ty)
    with
      NonMaximal x ->
      Error.functorialisation
        ("coherence: " ^ Unchecked.coh_to_string(Cohdecl(ps,ty)))
        (Printf.sprintf "trying to functorialise with respect to variable %s which is not maximal" x)
  else coh

let rec find_places ctx s l =
  match ctx,s with
  | [], [] -> []
  | (_,(_,true))::c,  t::s when Unchecked.tm_contains_vars t l -> 1::(find_places c s l)
  | (_,(_,true))::c,  _::s -> 0::(find_places c s l)
  | _::c, _::s -> find_places c s l
  | [],_::_ | _::_,[] -> Error.fatal "functorialisation in a non-existant place"

let rec tm t l =
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
         coh c places
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
  | t::s -> List.append (tm t l) (sub s l)

let tm c t s =
  try
    let l = list_functorialised s c in
    let c,assocs = ctx c l in
    c,List.hd (tm t assocs)
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
