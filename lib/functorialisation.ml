open Kernel
open Kernel.Unchecked_types

exception NonMaximal of string
exception FunctorialiseMeta

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

let coh ps ty l =
  try
    let ctx_base = Unchecked.ps_to_ctx ps in
    let ctx,assocs = ctx ctx_base l in
    let tm = Coh (Cohdecl(ps,ty),(Unchecked.identity_ps ctx_base)) in
    let tm_f = Unchecked.tm_apply_sub tm (target_subst assocs) in
    let ty = Arr (ty, tm, tm_f) in
    let ps = Kernel.PS.(forget (mk (Kernel.Ctx.check ctx))) in
    let _, names,_ = Unchecked.db_levels ctx in
    let ty = Unchecked.rename_ty ty names in
    Cohdecl(ps, ty),ps
  with
  NonMaximal x ->
    Error.functorialisation
      ("coherence: " ^ Unchecked.coh_to_string(Cohdecl(ps,ty)))
      (Printf.sprintf "trying to functorialise with respect to variable %s which is not maximal" x)


let rec find_places ctx s l =
  match ctx,s with
  | [], [] -> []
  | (x,_)::c,  t::s when Unchecked.tm_contains_vars t l -> (x,1)::(find_places c s l)
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
        let cohf,_ =
          match c with
          | Cohdecl (ps,ty) ->
            let places = find_places (Unchecked.ps_to_ctx ps) s (List.map fst l) in
            coh ps ty places
          | Cohchecked c ->
            let ps,ty = Coh.forget c in
            let places = find_places (Unchecked.ps_to_ctx ps) s (List.map fst l) in
            coh ps ty places
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

let tm c t l =
  try
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
