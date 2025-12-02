open Common
open Raw_types

module type S = sig
  module K : KernelExt.S
  open K

  val builtin_to_value : Raw_types.builtin -> value
  val value_ty : value -> ty
  val value_to_string : value -> string
  val add_let : Var.t -> ctx -> ?ty:ty -> tm -> tm * ty
  val add_value : Var.t -> value -> value * ty
  val add_coh : Var.t -> ps -> ty -> Coh.t
  val val_var : Var.t -> value
  val dim_output : Var.t -> int
  val dim_input : Var.t -> int

  module Suspension : module type of Suspension.Make (K)
  module Functorialisation : module type of Functorialisation.Make (K)
  module Opposite : module type of Opposite.Make (K)
  module Inverse : module type of Inverse.Make (K)
  module Builtin : module type of Builtin.Make (K)
  module Cones : module type of Cones.Make (K)
  module Cylinders : module type of Cylinders.Make (K)
  module Eh : module type of Eh.Make (K)
  module Cubical_composite : module type of Cubical_composite.Make (K)
end

type envValue =
  | Val :
      (module KernelExt.S with type Coh.t = 'a and type Tm.t = 'b)
      * ('a, 'b) pvalue
      -> envValue

module Value (K : KernelExt.S) = struct
  open K
  module Builtin = Builtin.Make (K)
  module Cones = Cones.Make (K)
  module Cylinders = Cylinders.Make (K)
  module Eh = Eh.Make (K)

  let value_ty v =
    match v with
    | VCoh c ->
        let _, ty, _ = Coh.forget c in
        ty
    | VTm t -> Tm.ty t

  let value_to_string v =
    match v with VCoh c -> Coh.to_string c | VTm t -> Tm.to_string t
end

type v = { value : envValue; dim_input : int; dim_output : int }
type t = (Var.t, v) Hashtbl.t

let env : t = Hashtbl.create 70

let add v value =
  let dim_input, dim_output =
    match value with
    | Val ((module K), VTm t) ->
        (K.Unchecked.dim_ctx (K.Tm.ctx t), K.Unchecked.dim_ty (K.Tm.ty t))
    | Val ((module K), VCoh c) ->
        let ps, ty, _ = K.Coh.forget c in
        (K.Unchecked.dim_ps ps, K.Unchecked.dim_ty ty)
  in
  Io.info ~v:4
    (lazy (Printf.sprintf "Value %s added to environment" (Var.to_string v)));
  Hashtbl.add env v { value; dim_input; dim_output }

let find_infos v =
  try Hashtbl.find_all env v
  with Not_found -> raise (Error.UnknownId (Var.to_string v))

let find v = List.map (fun v -> v.value) (find_infos v)

module Make (K : KernelExt.S) = struct
  module K = K
  open K
  module Suspension = Suspension.Make (K)
  module Functorialisation = Functorialisation.Make (K)
  module Opposite = Opposite.Make (K)
  module Inverse = Inverse.Make (K)
  module Builtin = Builtin.Make (K)
  module Cones = Cones.Make (K)
  module Cylinders = Cylinders.Make (K)
  module Eh = Eh.Make (K)
  module Cubical_composite = Cubical_composite.Make (K)
  module Value = Value (K)

  let builtin_to_value b =
    match b with
    | Comp -> VCoh (Builtin.comp_n 1)
    | Id -> VCoh (Builtin.id ())
    | Conecomp (n, k, m) -> VTm (Cones.compose n m k)
    | Cylcomp (n, k, m) -> VTm (Cylinders.compose n m k)
    | Cylstack n -> VTm (Cylinders.stacking n)
    | Eh_half (n, k, l) -> VTm (Eh.eh n k l)
    | Eh_full (n, k, l) -> VTm (Eh.full_eh n k l)

  let value_ty = Value.value_ty
  let value_to_string = Value.value_to_string

  let add_let v c ?ty t =
    try
      let pp_data = (Var.to_string v, 0, []) in
      let kc = Ctx.check c in
      let tm = check_term kc ?ty ~name:pp_data t in
      let ty = Tm.ty tm in
      add v
        (Val
           ( (module K : KernelExt.S with type Coh.t = Coh.t and type Tm.t = Tm.t),
             VTm tm ));
      (t, ty)
    with DoubledVar x -> Error.doubled_var (Printing.ctx_to_string c) x

  let add_coh v ps ty =
    let coh = check_coh ps ty (Var.to_string v, 0, []) in
    add v
      (Val
         ( (module K : KernelExt.S with type Coh.t = Coh.t and type Tm.t = Tm.t),
           VCoh coh ));
    coh

  let add_value v value =
    let ty = Value.value_ty value in
    add v
      (Val
         ( (module K : KernelExt.S with type Coh.t = Coh.t and type Tm.t = Tm.t),
           value ));
    (value, ty)

  (* INVARIANT: There is always at most one kernel for a single theory, so if
  we find in the environment a kernel with the same theory as the ambient one,
  it is the same, hence the use of Obj.magic *)
  let find v =
    let rec find_theory l =
      match l with
      | [] -> raise (Error.UnknownId (Var.to_string v))
      | [ { value = Val ((module K'), value); dim_output; dim_input } ]
        when K'.theory = K.theory ->
          (Obj.magic value, dim_output, dim_input)
      | _ :: l -> find_theory l
    in
    find_theory (find_infos v)

  let val_var v =
    let value, _, _ = find v in
    value

  let dim_output v =
    let _, d, _ = find v in
    d

  let dim_input v =
    let _, _, d = find v in
    d
end
