open Names
open EConstr
open Catt
open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

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

let tm_to_lambda env sigma ctx tm =
  let sigma,obj_type = Evarutil.new_Type sigma in
  let sigma, eq_type = c_Q env sigma in
  let rec ctx_to_lambda ctx inner_tm =
    match ctx with
    | [] ->
      EConstr.mkLambda(nameR (Names.Id.of_string "catt_Obj"),
                       obj_type,
                       inner_tm)
    | (x,(ty,_))::ctx ->
      ctx_to_lambda
        ctx
        (EConstr.mkLambda
           (nameR (Names.Id.of_string (catt_var_to_coq_name x)),
            ty_to_lambda ctx ty,
            inner_tm))
  and ty_to_lambda ctx ty =
    match ty with
    | Obj -> EConstr.mkRel ((List.length ctx) + 1)
    | Arr(ty,u,v) ->
      let ty = ty_to_lambda ctx ty in
      let u = tm_to_lambda ctx u in
      let v = tm_to_lambda ctx v in
      EConstr.mkApp (eq_type, [| ty; u; v |])
    | Meta_ty _ -> Error.fatal "unresolved meta type variable"
  and tm_to_lambda ctx tm =
    match tm with
    | Var x -> EConstr.mkRel (find_db ctx x)
    | _ -> Error.fatal "only variables are supported for now"
  in
  sigma, ctx_to_lambda ctx (tm_to_lambda ctx tm)

let ctx = [(Var.Db 2, (Arr(Obj,Var (Var.Db 0), Var (Var.Db 1)), true)); (Var.Db 1, (Obj, true)); (Var.Db 0, (Obj, true))]
let tm = Var (Var.Db 2)

let catt_tm () =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, body = tm_to_lambda env sigma ctx tm in
  let sigma, body = Typing.solve_evars env sigma body in
  let body = Evarutil.nf_evar sigma body in
  let info = Declare.Info.make () in
  let cinfo = Declare.CInfo.make ~name:Id.(of_string "catt_comp") ~typ:None () in
  let gr = Declare.declare_definition
      ~info
      ~cinfo
      ~opaque:false
      ~body
      sigma
  in
  Coqlib.register_ref
    "catt.test"
    gr
