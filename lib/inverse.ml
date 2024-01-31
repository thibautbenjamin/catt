open Kernel
open Unchecked_types.Unchecked_types(Coh)

exception NotInvertible of string
exception CohNonInv

let coh c =
  let ps,ty,(name,susp,func) = Coh.forget c in
  if (not (Coh.is_inv c)) then raise CohNonInv;
  let ty_inv = match ty with
    | Obj | Meta_ty _ -> assert false
    | Arr (a,u,v) -> Arr (a,v,u)
  in
  check_coh ps ty_inv (name^"^-1",susp,func)

let rec compute_inverse t =
  match t with
  | Var x -> raise (NotInvertible (Var.to_string x))
  | Meta_tm _ -> t (* Not sure about this case *)
  | Coh(c,sub) ->
    try
      let c_inv = coh c in Coh (c_inv, sub)
    with CohNonInv ->
      let ps,_,_ = Coh.forget c in
      let d = Unchecked.dim_ps ps in
      let sub, pctx = Unchecked.sub_ps_to_sub sub ps in
      let sub_inv = sub_inv sub pctx d in
      let equiv = Opposite.equiv_op_ps ps [d] in
      let coh = Opposite.coh c [d] in
      Coh(coh, Unchecked.sub_ps_apply_sub equiv sub_inv)
and sub_inv s ps i =
  match s,ps with
  | [], [] -> []
  | (x,t)::sub, (_,(ty,_))::ctx when Unchecked.dim_ty ty = i ->
    (x,compute_inverse t)::(sub_inv sub ctx i)
  | (x,t)::sub, _::ctx ->
    (x,t)::(sub_inv sub ctx i)
  | _,_ -> assert false

let compute_inverse t =
  try compute_inverse t with
  | NotInvertible s ->
      Error.inversion
        ("term: " ^ (Unchecked.tm_to_string t))
        (Printf.sprintf "term %s is not invertible" s)
