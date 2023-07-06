open Common

let ctx_one_var c x =
  let z1,z2 = Unchecked.two_fresh_vars c in
  let rec find c =
    match c with
    | [] -> raise (Error.UnknownFunctorialisation (Var.to_string x))
    | (y,(t, true))::c when x = y ->
      (z2, (Arr(t,Var x,Var z1), true)) ::
      (z1, (t, false)) ::
      (y, (t, false)) :: c
    | (y,(_, false))::_ when x = y ->
      raise (Error.NonMaximalFunctorialisation (Var.to_string x))
    | a::c -> a::(find c)
  in find c, (x, Var z1)

let ctx c l =
  List.fold_left
    (fun (c,assocs) x -> let c,p = ctx_one_var c x in c, p::assocs)
    (c,[])
    l

let coh ps ty l =
  let ctx_base = Unchecked.ps_to_ctx ps in
  let ctx,assocs = ctx ctx_base l in
  let tm = Coh (ps,ty,(Unchecked.identity_ps ctx_base)) in
  let tm_f = Unchecked.tm_apply_sub tm assocs in
  let ty = Arr (ty, tm, tm_f) in
  let ps = Kernel.PS.(forget (mk (Kernel.Ctx.check ctx))) in
  let _, names,_ = Unchecked.db_levels ctx in
  let ty = Unchecked.rename_ty ty names in
  ps, ty

let tm _t _c _l = assert false
