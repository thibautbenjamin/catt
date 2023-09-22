open Kernel
open Kernel.Unchecked_types

type value =
  | Coh of Coh.t
  | Tm of ctx * tm

type v = {value : value; dim_input : int; dim_output : int}

type t = (Var.t, v) Hashtbl.t

let env : t = Hashtbl.create 70

let add_let v c ?ty t =
  let kc = Kernel.Ctx.check c in
  let tm = Kernel.check_term kc ?ty t in
  let ty = Kernel.(Ty.forget (Tm.typ tm)) in
  let dim_input = Unchecked.dim_ctx c in
  let dim_output = Unchecked.dim_ty ty in
  Io.info ~v:2
    (lazy
      (Printf.sprintf
         "defined term %s of type %s"
         (Unchecked.tm_to_string t)
         (Unchecked.ty_to_string ty)));
  Hashtbl.add env v ({value = Tm (c,t); dim_input; dim_output});
  (t,ty)

let add_coh v ps ty =
  let coh = check_coh (Cohdecl(ps,ty,Var.to_string v)) in
  let dim_input = Unchecked.dim_ps ps in
  let dim_output = Unchecked.dim_ty ty in
  Io.info ~v:2
    (lazy
      (Printf.sprintf
         "defined coherence %s"
         (Var.to_string v)));
  Hashtbl.add env v ({value = Coh coh; dim_input; dim_output});
  Cohchecked coh

let find v =
  try Hashtbl.find env v
  with Not_found -> raise (Error.UnknownId (Var.to_string(v)))

let val_var v =
  (find v).value

let dim_output v =
  (find v).dim_output

let dim_input v =
  (find v).dim_input
