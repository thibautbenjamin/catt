type value =
  | Coh of Unchecked.ps * Unchecked.ty
  | Tm of Unchecked.ctx * Unchecked.tm

type t = (Variables.var, value) Hashtbl.t

let env : t = Hashtbl.create 70

let add_let v c t =
  Hashtbl.add env v (Tm (c,t))

let add_coh v ps ty =
  Hashtbl.add env v (Coh (ps,ty))


let val_var v =
  Hashtbl.find env v
