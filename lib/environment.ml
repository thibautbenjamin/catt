open Common

type value =
  | Coh of ps * ty
  | Tm of ctx * tm

type t = (Var.t, value) Hashtbl.t

let env : t = Hashtbl.create 70

let add_let v c ?ty t =
  let kc = Kernel.Ctx.check c in
  let tm = Kernel.Tm.check kc ?ty t in
  Io.info ~v:2
    (lazy
      (Printf.sprintf
         "defined term %s of type %s"
         (Unchecked.tm_to_string t)
         (Unchecked.ty_to_string (Kernel.(Ty.forget (Tm.typ tm))))));
  Hashtbl.add env v (Tm (c,t))

let add_coh v ps ty =
  ignore(Kernel.Coh.check ps ty []);
  Io.info ~v:2
    (lazy
      (Printf.sprintf
         "defined coherence %s"
         (Var.to_string v)));
  Hashtbl.add env v (Coh (ps,ty))

let val_var v =
  Hashtbl.find env v
