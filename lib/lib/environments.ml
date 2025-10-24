open Common
open Raw_types

module type S = sig
  module CurrentTheory : Theory.S
  include module type of Kernel.Make (CurrentTheory)

  module Environment : sig
    type value = Coh of Coh.t | Tm of Tm.t
    type t

    val builtin_to_value : Raw_types.builtin -> value
    val value_ty : value -> ty
    val value_to_string : value -> string
    val add_let : Var.t -> ctx -> ?ty:ty -> tm -> tm * ty
    val add_value : Var.t -> value -> value * ty
    val add_coh : Var.t -> ps -> ty -> Coh.t
    val val_var : Var.t -> value
    val dim_output : Var.t -> int
    val dim_input : Var.t -> int
    val forall : (Var.t -> unit) -> unit
  end

  module Suspension : module type of Suspension.Make (CurrentTheory)

  module Functorialisation :
      module type of Functorialisation.Make (CurrentTheory)

  module Opposite : module type of Opposite.Make (CurrentTheory)
  module Inverse : module type of Inverse.Make (CurrentTheory)
  module Builtin : module type of Builtin.Make (CurrentTheory)
  module Cones : module type of Cones.Make (CurrentTheory)
  module Cylinders : module type of Cylinders.Make (CurrentTheory)
  module Eh : module type of Eh.Make (CurrentTheory)

  module Cubical_composite :
      module type of Cubical_composite.Make (CurrentTheory)
end

let known_environments : (Var.t, (module S) list) Hashtbl.t = Hashtbl.create 77

let update_known_environments (v : Var.t) env =
  let module Env = (val env : S) in
  let list = Hashtbl.find_opt known_environments v in
  match list with
  | None -> Hashtbl.add known_environments v [ env ]
  | Some list ->
      let rec replace list =
        match list with
        | [] -> [ env ]
        | known_env :: list ->
            let module KnownEnv = (val known_env : S) in
            if KnownEnv.CurrentTheory.theory == Env.CurrentTheory.theory then
              env :: list
            else known_env :: replace list
      in
      Hashtbl.replace known_environments v (replace list)

let store_environment environment =
  Io.debug "updating the known environments";
  let open (val environment : S) in
  Environment.forall (fun v -> update_known_environments v environment)

let find_environment v =
  Io.debug "trying to find the variable %s" (Var.to_string v);
  let res = Hashtbl.find known_environments v in
  Io.debug "found environment";
  res

module Make (CurrentTheory : Theory.S) = struct
  module CurrentTheory = CurrentTheory
  include Kernel.Make (CurrentTheory)
  module Suspension = Suspension.Make (CurrentTheory)
  module Functorialisation = Functorialisation.Make (CurrentTheory)
  module Opposite = Opposite.Make (CurrentTheory)
  module Inverse = Inverse.Make (CurrentTheory)
  module Builtin = Builtin.Make (CurrentTheory)
  module Cones = Cones.Make (CurrentTheory)
  module Cylinders = Cylinders.Make (CurrentTheory)
  module Eh = Eh.Make (CurrentTheory)
  module Cubical_composite = Cubical_composite.Make (CurrentTheory)

  let () =
    if !CurrentTheory.environment_created then
      Error.fatal "Environment already created for the theory"
    else CurrentTheory.environment_created := true

  module Environment = struct
    type value = Coh of Coh.t | Tm of Tm.t

    let builtin_to_value b =
      match b with
      | Comp -> Coh (Builtin.comp_n 1)
      | Id -> Coh (Builtin.id ())
      | Conecomp (n, k, m) -> Tm (Cones.compose n m k)
      | Cylcomp (n, k, m) -> Tm (Cylinders.compose n m k)
      | Cylstack n -> Tm (Cylinders.stacking n)
      | Eh_half (n, k, l) -> Tm (Eh.eh n k l)
      | Eh_full (n, k, l) -> Tm (Eh.full_eh n k l)

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
      match v with Coh c -> Coh.to_string c | Tm t -> Tm.to_string t

    type v = { value : value; dim_input : int; dim_output : int }
    type t = (Var.t, v) Hashtbl.t

    let env : t = Hashtbl.create 70

    let add_let v c ?ty t =
      try
        let pp_data = (Var.to_string v, 0, []) in
        let kc = Ctx.check c in
        let tm = check_term kc ?ty ~name:pp_data t in
        let ty = Ty.forget (Tm.typ tm) in
        let dim_input = Unchecked.dim_ctx c in
        let dim_output = Unchecked.dim_ty ty in
        Io.info ~v:4
          (lazy
            (Printf.sprintf "term %s of type %s added to environment"
               (Printing.tm_to_string t) (Printing.ty_to_string ty)));
        Hashtbl.add env v { value = Tm tm; dim_input; dim_output };
        (t, ty)
      with DoubledVar x -> Error.doubled_var (Printing.ctx_to_string c) x

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
             (value_to_string value) (Printing.ty_to_string ty)));
      Hashtbl.add env v { value; dim_input; dim_output };
      (value, ty)

    let val_var v = (find v).value
    let dim_output v = (find v).dim_output
    let dim_input v = (find v).dim_input
    let forall f = Hashtbl.iter (fun x _ -> f x) env
  end
end
