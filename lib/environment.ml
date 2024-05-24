open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh)

type value = Coh of Coh.t | Tm of ctx * tm
type v = { value : value; dim_input : int; dim_output : int }
type t = (Var.t, v) Hashtbl.t

let env : t = Hashtbl.create 70
let reset () = Hashtbl.clear env

let add_let v c ?ty t =
  try
    let kc = Kernel.Ctx.check c in
    let tm = Kernel.check_term kc ?ty t in
    let ty = Kernel.(Ty.forget (Tm.typ tm)) in
    let dim_input = Unchecked.dim_ctx c in
    let dim_output = Unchecked.dim_ty ty in
    Io.info ~v:4
      (lazy
        (Printf.sprintf "term %s of type %s added to environment"
           (Unchecked.tm_to_string t)
           (Unchecked.ty_to_string ty)));
    Hashtbl.add env v { value = Tm (c, t); dim_input; dim_output };
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

let val_var v = (find v).value
let dim_output v = (find v).dim_output
let dim_input v = (find v).dim_input
