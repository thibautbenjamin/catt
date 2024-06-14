open Names
open EConstr
open Evd
open Catt
open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

let run_catt_on_file f =
  Prover.reset();
  match Prover.parse_file f with
  | Ok f -> Command.exec ~loop_fn:Prover.loop f
  | Error () -> ()

let rec catt_var_to_coq_name v =
  match v with
  | Var.Db i -> "catt_db_" ^ (string_of_int i)
  | Var.Name s -> "catt_name_" ^ s
  | Var.New i -> "catt_new_" ^ (string_of_int i)
  | Var.Plus v -> (catt_var_to_coq_name v) ^ "_plus"
  | Var.Bridge v -> (catt_var_to_coq_name v) ^ "_bridge"

let c_Q env sigma =
  let gr = Coqlib.lib_ref "core.eq.type" in
  Evd.fresh_global env sigma gr

let rec find_db ctx x =
  match ctx with
  | [] -> Error.fatal "variable not found"
  | (y,_)::_ when x = y -> 1
  | _::ctx -> 1 + find_db ctx x

module Translate : sig
  val tm : Environ.env -> evar_map -> ctx -> tm -> evar_map * econstr
end = struct

  let rec ctx_to_lambda obj_type eq_type ctx inner_tm =
    match ctx with
    | [] ->
      EConstr.mkLambda(nameR (Names.Id.of_string "catt_Obj"),
                       obj_type,
                       inner_tm)
    | (x,(ty,_))::ctx ->
      ctx_to_lambda
        obj_type
        eq_type
        ctx
        (EConstr.mkLambda
           (nameR (Names.Id.of_string (catt_var_to_coq_name x)),
            ty_to_lambda obj_type eq_type ctx ty,
            inner_tm))
  and ty_to_lambda obj_type eq_type ctx ty =
    match ty with
    | Obj -> EConstr.mkRel ((List.length ctx) + 1)
    | Arr(ty,u,v) ->
      let ty = ty_to_lambda obj_type eq_type ctx ty in
      let u = tm_to_lambda obj_type eq_type ctx u in
      let v = tm_to_lambda obj_type eq_type  ctx v in
      EConstr.mkApp (eq_type, [| ty; u; v |])
    | Meta_ty _ -> Error.fatal "unresolved meta type variable"
  and tm_to_lambda obj_type eq_type ctx tm =
    match tm with
    | Var x -> EConstr.mkRel (find_db ctx x)
    | _ -> Error.fatal "only variables are supported for now"

  let tm env sigma ctx tm =
    let sigma,obj_type = Evarutil.new_Type sigma in
    let sigma, eq_type = c_Q env sigma in
    let tm = tm_to_lambda obj_type eq_type ctx tm in
    sigma, ctx_to_lambda obj_type eq_type ctx tm
end

let catt_tm file tm_names =
  run_catt_on_file file;
  let register_tm tm_name =
    let ctx,tm =
      match Environment.val_var (Var.Name tm_name) with
      | Coh _ -> assert false
      | Tm (ctx,tm) -> ctx,tm
    in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let sigma, body = Translate.tm env sigma ctx tm in
    let sigma, body = Typing.solve_evars env sigma body in
    let body = Evarutil.nf_evar sigma body in
    let info = Declare.Info.make () in
    let cinfo =
      Declare.CInfo.make
        ~name:Id.(of_string ("catt_"^tm_name))
        ~typ:None ()
    in
    let gr = Declare.declare_definition
        ~info
        ~cinfo
        ~opaque:false
        ~body
        sigma
    in
    Coqlib.register_ref
      ("catt."^tm_name)
      gr
  in
  List.iter register_tm tm_names
