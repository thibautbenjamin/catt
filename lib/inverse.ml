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

let compute_inverse t =
  match t with
  | Var x -> raise (NotInvertible (Var.to_string x))
  | Meta_tm _ -> t (* Not sure about this case *)
  | Coh(c,sub) ->
     try
      let c_inv = coh c in Coh (c_inv, sub)
    with CohNonInv -> assert false

let compute_inverse t =
  try compute_inverse t with
  | NotInvertible s -> Error.inversion ("term: " ^ (Unchecked.tm_to_string t)) s
