open Kernel
open Kernel.Unchecked_types

let ctx_one_var c x =
  let x',xf = Unchecked.two_fresh_vars c in
  let rec find c =
    match c with
    | [] -> raise (Error.UnknownFunctorialisation (Var.to_string x))
    | (y,(t, true))::c when x = y ->
      (xf, (Arr(t,Var x,Var x'), true)) ::
      (x', (t, false)) ::
      (y, (t, false)) :: c
    | (y,(_, false))::_ when x = y ->
      raise (Error.NonMaximalFunctorialisation (Var.to_string x))
    | a::c -> a::(find c)
  in find c, (x, (Var x', Var xf))

let ctx c l =
  List.fold_left
    (fun (c,assocs) x -> let c,p = ctx_one_var c x in c, p::assocs)
    (c,[])
    l

let target_subst l =
  List.map (fun (x,(y,_)) -> (x,y)) l

let coh ps ty l =
  let ctx_base = Unchecked.ps_to_ctx ps in
  let ctx,assocs = ctx ctx_base l in
  let tm = Coh (Cohdecl(ps,ty),(Unchecked.identity_ps ctx_base)) in
  let tm_f = Unchecked.tm_apply_sub tm (target_subst assocs) in
  let ty = Arr (ty, tm, tm_f) in
  let ps = Kernel.PS.(forget (mk (Kernel.Ctx.check ctx))) in
  let _, names,_ = Unchecked.db_levels ctx in
  let ty = Unchecked.rename_ty ty names in
  Cohdecl(ps, ty),ps

let rec find_places ctx s l =
  match ctx,s with
  | [], [] -> []
  | (x,_)::c,  t::s when Unchecked.tm_contains_vars t l -> x::(find_places c s l)
  | _::c, _::s -> find_places c s l
  | [],_::_ | _::_,[] -> assert false

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
  | Meta_tm _ -> assert false
and sub s l =
  match s with
  | [] -> []
  | t::s -> List.append (tm t l) (sub s l)

let tm c t l =
  let c,assocs = ctx c l in
  c,List.hd (tm t assocs)
