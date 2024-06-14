open Names
open Context
open Evd
open Catt
open Kernel
open Unchecked_types.Unchecked_types(Coh)

let run_catt_on_file f =
  Prover.reset();
  Command.exec ~loop_fn:Prover.loop (Prover.parse_file f)

let catt_var_to_coq_name v =
  match v with
  | Var.Db i -> "catt_db_" ^ (string_of_int i)
  | Var.Name s -> "catt_name_" ^ s
  | Var.New i -> "catt_new_" ^ (string_of_int i)

let c_Q env sigma =
  let gr = Coqlib.lib_ref "core.eq.type" in
  Evd.fresh_global env sigma gr

let c_R env sigma =
  let gr = Coqlib.lib_ref "core.eq.refl" in
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

let example file tm_names =
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


  (* and coh_to_lambda env sigma obj_type eq_type refl coh = *)
  (*   let ps,ty,_ = Coh.forget coh in *)
  (*   let ctx = Unchecked.ps_to_ctx ps in *)
  (*   let max_vars = [Var.Db 2; Var.Db 4] in *)
  (*   let max_vars = *)
  (*     List.map *)
  (*       (fun x -> (Names.(Name.mk_name (Id.of_string (catt_var_to_coq_name x))))) *)
  (*       max_vars *)
  (*   in *)
  (*   let ty = ty_to_lambda sigma obj_type eq_type refl ctx ty in *)
  (*   let *)
  (*     (eq_ind,universe),_ = Inductiveops.find_inductive env sigma eq_type *)
  (*   in *)
  (*   (\* let refl = match constr with *\) *)
  (*   (\*     | [x] -> x *\) *)
  (*   (\*     | _ -> assert false *\) *)
  (*   (\* in *\) *)
  (*   let rec body max_vars ret = *)
  (*     match max_vars with *)
  (*     | [] -> refl *)
  (*     | m::max_vars -> *)
  (*       let last_var = {binder_name = m; binder_relevance = Relevant} in *)
  (*       let case_info = Inductiveops.make_case_info env eq_ind Relevant RegularStyle in *)
  (*       let constructors = [| refl |] in *)
  (*       let case_return = [|last_var|], ret in *)
  (*       let case_invert = Constr.NoInvert in *)
  (*       let case_branches = [| ([|last_var|], body max_vars ret) |] in *)
  (*       let constructor = refl in *)
  (*       let pcase = (case_info, *)
  (*                    universe, *)
  (*                    constructors, *)
  (*                    case_return, *)
  (*                    case_invert, *)
  (*                    constructor, *)
  (*                    case_branches) in *)
  (*       EConstr.mkCase pcase in *)
  (*   ctx_to_lambda sigma obj_type eq_type refl ctx (body max_vars ty) *)
