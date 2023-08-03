open Kernel
open Unchecked_types.Unchecked_types(Coh)

exception NotInvertible of string

let compute_inverse t =
  match t with
  | Var x -> raise (NotInvertible (Var.to_string x))
  | Meta_tm _ -> t (* Not sure about this case *)
  | Coh(coh,sub) ->
    let ps,ty,(name,susp,func) = Coh.forget coh in
    if Coh.is_inv coh then
      let ty_inv = match ty with
        | Obj | Meta_ty _ -> assert false
        | Arr (a,u,v) -> Arr (a,v,u)
      in
      let coh_inv = check_coh ps ty_inv (name^"^-1",susp,func)  in
      Coh(coh_inv, sub)
    else assert false

let compute_inverse t =
  try compute_inverse t with
  | NotInvertible s -> Error.inversion ("term: " ^ (Unchecked.tm_to_string t)) s
