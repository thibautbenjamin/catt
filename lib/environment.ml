open Common

type value =
  | Coh of ps * ty
  | Tm of ctx * tm

type t = (Var.t, value) Hashtbl.t

let env : t = Hashtbl.create 70

let add_let v c t =
  let kc = Kernel.Ctx.check c in
  let tm = Kernel.Tm.check kc t in
  Io.info "defined term %s of type %s"
    (Unchecked.tm_to_string t)
    (Unchecked.ty_to_string (Kernel.(Ty.forget (Tm.typ tm))));
  Hashtbl.add env v (Tm (c,t))

let add_let_check v c tm ty =
  let kc = Kernel.Ctx.check c in
  ignore(Kernel.Tm.check kc ~ty tm);
  Io.info "defined term %s of type %s"
    (Unchecked.tm_to_string tm)
    (Unchecked.ty_to_string ty);
  Hashtbl.add env v (Tm (c,tm))

let add_coh v ps ty =
  ignore(Kernel.Coh.check ps ty []);
  Io.info "defined coherence %s"
    (Var.to_string v);
  Hashtbl.add env v (Coh (ps,ty))

let val_var v =
  Hashtbl.find env v
