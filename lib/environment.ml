open Common
module Tbl (Strictness : StrictnessLv)
= struct
  module Kernel = Kernel.Kernel(Strictness)
  module Unchecked = Kernel.Unchecked
  open Kernel.Unchecked_types

  type value =
    | Coh of Kernel.Coh.t
    | Tm of ctx * tm

  type v = {value : value; dim_input : int; dim_output : int}

  type t = (Var.t, v) Hashtbl.t
end

let env_wk : Tbl(Wk).t = Hashtbl.create 70

module Environment (Strictness : StrictnessLv)
= struct
  module Kernel = Kernel.Kernel(Strictness)
  module Unchecked = Kernel.Unchecked

  (* This declaration is only well typed thanks to
     the invariant that there is only one module per
     strictness level, hence the use of Obj.magic *)
  let env : Tbl(Strictness).t =
    match Strictness.lv with
    | Wk -> Obj.magic(env_wk)

  let add_let v c ?ty t =
    let ty = Kernel.check_term c ?ty t in
    let dim_input = Unchecked.dim_ctx c in
    let dim_output = Unchecked.dim_ty ty in
    Io.info ~v:4
      (lazy
        (Printf.sprintf
           "term %s of type %s added to environment"
           (Unchecked.tm_to_string t)
           (Unchecked.ty_to_string ty)));
    Hashtbl.add env v ({value = Tm (c,t); dim_input; dim_output});
    (Unchecked.tm_to_string t,Unchecked.ty_to_string ty)

  let add_coh v ps ty =
    let coh = Kernel.check_coh ps ty (Var.to_string v, 0, None) in
    let dim_input = Unchecked.dim_ps ps in
    let dim_output = Unchecked.dim_ty ty in
    Io.info ~v:4
      (lazy
        (Printf.sprintf
           "coherence %s added to environment"
           (Var.to_string v)));
    Hashtbl.add env v ({value = Coh coh; dim_input; dim_output});
    Kernel.coh_to_string coh

  let find v =
    try Hashtbl.find env v
    with Not_found -> raise (Error.UnknownId (Var.to_string(v)))

  let val_var v =
    (find v).value

  let dim_output v =
    (find v).dim_output

  let dim_input v =
    (find v).dim_input
end
