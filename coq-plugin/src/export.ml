open Names
open Context
open Catt
open Kernel
open Unchecked_types.Unchecked_types(Coh)


let c_Q env sigma =
  let gr = Coqlib.lib_ref "core.eq.type" in
  Evd.fresh_global env sigma gr

let c_R env sigma =
  let gr = Coqlib.lib_ref "core.eq.refl" in
  Evd.fresh_global env sigma gr

let rec find_db ctx x =
  match ctx with
  | [] -> assert false
  | (y,_)::_ when x = y -> 1
  | _::ctx -> 1 + find_db ctx x

let tm_to_lambda env sigma ctx tm =
  let sigma, obj_type = Evarutil.new_Type sigma in
  let sigma, eq_type = c_Q env sigma in
  (* let sigma, eq_refl = c_R env sigma in *)
  let rec ctx_to_lambda ctx inner_tm =
    match ctx with
    | [] ->
      EConstr.mkLambda(nameR (Names.Id.of_string "Obj"),
                       obj_type,
                       inner_tm)
    | (x,(ty,_))::ctx ->
      ctx_to_lambda
        ctx
        (EConstr.mkLambda
           (nameR (Names.Id.of_string (Var.to_string x)),
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
    | Meta_ty _ -> assert false
  and tm_to_lambda ctx tm =
    match tm with
    | Var x -> EConstr.mkRel (find_db ctx x)
    | _ -> assert false
  in
  sigma, ctx_to_lambda ctx (tm_to_lambda ctx tm)



let body sigma =
  let sigma, type_obj =
    Evarutil.new_Type sigma
  in
  let body =
    EConstr.mkLambda(nameR (Names.Id.of_string "Obj"), EConstr.mkRel 1,
                     EConstr.mkRel 1)
  in
  let body =
    EConstr.mkLambda(nameR (Names.Id.of_string "Obj"), type_obj,
                     body)
  in
  sigma, body

let ctx = [(Var.Db 0, (Obj, true))]
let tm = Var (Var.Db 0)

let example () =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, body = tm_to_lambda env sigma ctx tm in
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
