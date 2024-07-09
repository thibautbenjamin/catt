open Names
open Context
open Evd
open Pp
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
  val coh : Environ.env -> evar_map -> Coh.t -> evar_map * econstr
end = struct

  let catt_to_coq_db ctx var =
    match var with
    | Var.Db n -> EConstr.mkRel (List.length ctx - n)
    | _ -> assert false

  let rec induction_vars ctx =
    match ctx with
    | [] -> []
    | (_,(_,false))::ctx -> induction_vars ctx
    | (x,(ty,true))::ctx ->
      match ty with
      | Obj -> []
      | Meta_ty _ -> Error.fatal "unresolved meta variable"
      | Arr(ty,s,_) ->
        match s with
        | Var s -> (x,s,ty)::induction_vars ctx
        | _ -> assert false

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

  let coh_to_lambda env sigma obj_type eq_type refl coh =
    let ps,ty,_ = Coh.forget coh in
    let ctx = Unchecked.ps_to_ctx ps in
    let max_vars = induction_vars ctx in
    let src,ty = match ty with
      | Arr(ty,s,_) -> (tm_to_lambda obj_type eq_type ctx s,
                        ty_to_lambda obj_type eq_type ctx ty)
      | Obj | Meta_ty _ -> assert false
    in
    let (eq_ind,univ),_ = Inductiveops.find_inductive env sigma eq_type in
    let catt_to_coq_db = catt_to_coq_db ctx in
    let rec body max_vars ret =
      match max_vars with
      | [] ->
        EConstr.mkApp (refl, [|ty; src |])
      | (m,s,ty_m)::max_vars ->
        let v1 = {binder_name = Names.Name.Anonymous;
                  binder_relevance = Relevant}
        in
        let m_coq = catt_to_coq_db m in
        let s_coq = catt_to_coq_db s in
        let ty_m_coq = ty_to_lambda obj_type eq_type ctx ty_m in
        let ret = EConstr.mkApp (eq_type,
                                 [| EConstr.Vars.liftn 2 0 ty;
                                    EConstr.Vars.liftn 2 0 src;
                                    EConstr.mkRel 2|])
        in
        let case_return = [| v1; v1 |], ret in
        let case_branches =  [| ([| |], body max_vars ret) |] in
        let pcase = (Inductiveops.make_case_info env eq_ind Relevant RegularStyle,
                     univ,
                     [| ty_m_coq; s_coq |], (* parameters of inductive type *)
                     case_return,
                     Constr.NoInvert,
                     m_coq , (* match m_coq in ... *)
                     case_branches) in
        EConstr.mkCase pcase in
    ctx_to_lambda obj_type eq_type ctx (body max_vars ty)

  let coh env sigma coh =
    let sigma,obj_type = Evarutil.new_Type sigma in
    let sigma, eq_type = c_Q env sigma in
    let sigma, refl = c_R env sigma in
    sigma, coh_to_lambda env sigma obj_type eq_type refl coh

  (* let coh env sigma _ = *)
  (*   let sigma, base_type = Evarutil.new_Type sigma in *)
  (*   let sigma, eq_type = c_Q env sigma in *)
  (*   let sigma, refl = c_R env sigma in *)
  (*   let *)
  (*     (eq_ind,universe),_ = Inductiveops.find_inductive env sigma eq_type *)
  (*   in *)
  (*   let a = Names.Id.of_string "a" in *)
  (*   let abind = {binder_name = Names.Name.mk_name a; binder_relevance = Relevant} in *)
  (*   let b = Names.Id.of_string "b" in *)
  (*   let bbind = {binder_name = Names.Name.mk_name b; binder_relevance = Relevant} in *)
  (*   let ret = EConstr.mkApp (eq_type, [| EConstr.mkRel 8; EConstr.mkRel 6; EConstr.mkRel 2|]) in *)
  (*   let case_info = Inductiveops.make_case_info env eq_ind Relevant RegularStyle in *)
  (*   let constructors = [| EConstr.mkRel 6; EConstr.mkRel 4 |] in *)
  (*   let case_return = [| bbind; abind |], ret in *)
  (*   let case_invert = Constr.NoInvert in *)
  (*   let case_branches = [| ([| |], EConstr.mkApp (refl, [| EConstr.mkRel 6; EConstr.mkRel 4|])) |] in *)
  (*   let constructor = EConstr.mkRel 1 in *)
  (*   let pcase = (case_info, *)
  (*                universe, *)
  (*                constructors, *)
  (*                case_return, *)
  (*                case_invert, *)
  (*                constructor, *)
  (*                case_branches) in *)
  (*   let body = EConstr.mkCase pcase in *)
  (*   sigma, *)
  (*   EConstr.mkLambda( *)
  (*     nameR (Names.Id.of_string "A"), *)
  (*     base_type, *)
  (*     EConstr.mkLambda( *)
  (*       nameR (Names.Id.of_string "x"), *)
  (*       EConstr.mkRel 1, *)
  (*       EConstr.mkLambda( *)
  (*         nameR (Names.Id.of_string "y"), *)
  (*         EConstr.mkRel 2, *)
  (*         EConstr.mkLambda( *)
  (*           nameR (Names.Id.of_string "f"), *)
  (*           EConstr.mkApp (eq_type, [| EConstr.mkRel 3; *)
  (*                                      EConstr.mkRel 2; *)
  (*                                      EConstr.mkRel 1 |]), *)
  (*           EConstr.mkLambda( *)
  (*             nameR (Names.Id.of_string "z"), *)
  (*             EConstr.mkRel 4, *)
  (*              EConstr.mkLambda( *)
  (*                nameR (Names.Id.of_string "g"), *)
  (*                EConstr.mkApp (eq_type, [| EConstr.mkRel 5; *)
  (*                                           EConstr.mkRel 3; *)
  (*                                           EConstr.mkRel 1 |]), *)
  (*                body *)
  (*              )))))) *)
end

let example file tm_names =
  run_catt_on_file file;
  let register_tm tm_name =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let sigma,body =
      match Environment.val_var (Var.Name tm_name) with
      | Coh c -> Translate.coh env sigma c
      | Tm (ctx,tm) -> Translate.tm env sigma ctx tm
    in
    let _ = Feedback.msg_debug
      (str "body:" ++
       (Printer.pr_econstr_env env sigma body))
    in
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
