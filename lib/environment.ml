open Common
open Raw_types
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

type value = Coh of Coh.t | Tm of Tm.t

let builtin_to_value b =
  match b with
  | Comp -> Coh (Builtin.comp_n 1)
  | Id -> Coh (Builtin.id ())
  | Conecomp (n, k, m) -> Tm (Cones.compose n m k)
  | Cylcomp (n, k, m) -> Tm (Cylinders.compose n m k)
  | Cylstack n -> Tm (Cylinders.stacking n)

let value_ty v =
  match v with
  | Coh c ->
      let _, ty, _ = Coh.forget c in
      ty
  | Tm t -> Tm.ty t

let value_ctx v =
  match v with
  | Coh c ->
      let ps, _, _ = Coh.forget c in
      Unchecked.ps_to_ctx ps
  | Tm t -> Tm.ctx t

let value_to_string v =
  match v with Coh c -> Coh.to_string c | Tm t -> Tm.name t

type v = { value : value; dim_input : int; dim_output : int }
type t = (Var.t, v) Hashtbl.t

let env : t = Hashtbl.create 70
let reset () = Hashtbl.clear env

let add_let v c ?ty t =
  try
    let pp_data = (Var.to_string v, 0, []) in
    let kc = Kernel.Ctx.check c in
    let tm = Kernel.check_term kc pp_data ?ty t in
    let ty = Kernel.(Ty.forget (Tm.typ tm)) in
    let dim_input = Unchecked.dim_ctx c in
    let dim_output = Unchecked.dim_ty ty in
    Io.info ~v:4
      (lazy
        (Printf.sprintf "term %s of type %s added to environment"
           (Unchecked.tm_to_string t)
           (Unchecked.ty_to_string ty)));
    Hashtbl.add env v { value = Tm tm; dim_input; dim_output };
    (t, ty)
  with DoubledVar x -> Error.doubled_var (Unchecked.ctx_to_string c) x

let add_coh v ps ty =
  let coh = check_coh ps ty (Var.to_string v, 0, []) in
  let dim_input = Unchecked.dim_ps ps in
  let dim_output = Unchecked.dim_ty ty in
  Io.info ~v:4
    (lazy
      (Printf.sprintf "coherence %s added to environment" (Var.to_string v)));
  Hashtbl.add env v { value = Coh coh; dim_input; dim_output };
  coh

let find v =
  try Hashtbl.find env v
  with Not_found -> raise (Error.UnknownId (Var.to_string v))

let add_value v value =
  let ty = value_ty value in
  let dim_input = Unchecked.dim_ctx (value_ctx value) in
  let dim_output = Unchecked.dim_ty ty in
  Io.info ~v:4
    (lazy
      (Printf.sprintf "term %s of type %s added to environment"
         (value_to_string value)
         (Unchecked.ty_to_string ty)));
  Hashtbl.add env v { value; dim_input; dim_output };
  (value, ty)

let val_var v = (find v).value
let dim_output v = (find v).dim_output
let dim_input v = (find v).dim_input
