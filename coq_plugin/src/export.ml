open Names
open Context
open Evd
(* open Pp *)
open Catt
open Common
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
    | Var.Db n -> let l = (List.length ctx - n) in EConstr.mkRel l, l
    | _ -> assert false

  let induction_vars ps =
    let rec find_vars_list lv start l onto =
      match l with
      | [] -> start+1, onto
      | ps::l ->
        let start, varsl = find_vars_list lv start l onto in
        find_vars_ps lv (start+1) ps varsl
    and find_vars_ps lv start ps onto =
      let onto =
        if lv > 0
        then (Var.Db start)::onto
        else onto
      in
      match ps with
      | Br l  -> find_vars_list (lv+1) start l onto
    in
    snd (find_vars_ps 0 0 ps [])

  let induction_data list_vars ctx =
    let find_data var =
      match fst (List.assoc var ctx) with
      | Obj -> assert false
      | Meta_ty _ -> Error.fatal "unresolved meta variable"
      | Arr(ty,s,_) ->
        match s with
        | Var s -> (var,s,ty)
        | _ -> assert false
    in List.map find_data list_vars

  (* let rec print_list l = *)
  (*   match l with *)
  (*   | [] -> "" *)
  (*   | t::l -> (Var.to_string t) ^", " ^ (print_list l) *)

  (* Abstract a locally maximal variable and its target. Crucially uses that a
  target of a locally maximal variable must occurs just before said variable *)
  let abstract env sigma econstr i_lm =
    let lm = Names.Id.of_string "lm" in
    let tgt = Names.Id.of_string "tm_tgt" in
    let econstr = EConstr.Vars.lift 2 econstr in
    let econstr =
      EConstr.Vars.substnl
        [EConstr.mkVar lm; EConstr.mkVar tgt]
        (i_lm + 1)
        econstr
    in
    let econstr = EConstr.Vars.subst_vars sigma [lm; tgt] econstr in
    let econstr = EConstr.Vars.liftn 2 (i_lm + 2) econstr in
    econstr

  let instantiate econstr tysrc src refl =
    EConstr.Vars.substl [EConstr.mkApp (refl,[|tysrc; src|]); src] econstr

  let rec ctx_to_lambda env sigma obj_type eq_type refl ctx inner_tm =
    match ctx with
    | [] ->
      sigma,
      EConstr.mkLambda(nameR (Names.Id.of_string "catt_Obj"),
                       obj_type,
                       inner_tm)
    | (x,(ty,_))::ctx ->
      let sigma,ty = ty_to_lambda env sigma obj_type eq_type refl ctx ty in
      let id_lambda = Names.Id.of_string (catt_var_to_coq_name x) in
      let lambda = EConstr.mkLambda (nameR id_lambda, ty, inner_tm) in
      ctx_to_lambda env sigma obj_type eq_type refl ctx lambda
  and ty_to_lambda env (sigma : Evd.evar_map) obj_type eq_type refl ctx ty =
    match ty with
    | Obj -> sigma, EConstr.mkRel ((List.length ctx) + 1)
    | Arr(ty,u,v) ->
      let sigma, ty = ty_to_lambda env sigma obj_type eq_type refl ctx ty in
      let sigma, u = tm_to_lambda env sigma obj_type eq_type refl ctx u in
      let sigma, v = tm_to_lambda env sigma obj_type eq_type refl ctx v in
      sigma, EConstr.mkApp (eq_type, [| ty; u; v |])
    | Meta_ty _ -> Error.fatal "unresolved type meta-variable"
  and tm_to_lambda env (sigma : Evd.evar_map) obj_type eq_type refl ctx tm =
    match tm with
    | Var x -> sigma, EConstr.mkRel (find_db ctx x)
    | Coh(c,s) ->
      let sigma,c = coh_to_lambda env sigma eq_type refl c in
      let sigma,s = sub_ps_to_lambda env sigma obj_type eq_type refl ctx s in
      sigma, EConstr.mkApp(c,s)
    | Meta_tm _ -> Error.fatal "unresolved term meta-variable"
  and sub_ps_to_lambda env sigma obj_type eq_type refl ctx sub_ps =
    let l = List.length sub_ps in
    let array = Array.make (l + 1) (EConstr.mkRel 0) in
    let rec set_next i (sigma : Evd.evar_map) sub_ps =
      match sub_ps with
      | [] -> Array.set array 0 (EConstr.mkRel ((List.length ctx) + 1)); sigma
      | (t,_)::s ->
        let sigma, tm = tm_to_lambda env sigma obj_type eq_type refl ctx t in
        Array.set array i tm;
        set_next (i-1) sigma s
    in set_next l sigma sub_ps, array
  and coh_to_lambda env sigma eq_type refl coh =
    let sigma, obj_type = Evarutil.new_Type sigma in
    let ps,ty,_ = Coh.forget coh in
    let ctx = Unchecked.ps_to_ctx ps in
    let l_ind = induction_vars ps in
    (* Io.debug "====== translation of coherence %s === ===" (Coh.to_string coh); *)
    (* Io.debug "  ps: %s" (Unchecked.ps_to_string ps); *)
    (* Io.debug "  context: %s" (Unchecked.ctx_to_string ctx); *)
    (* Io.debug "  induction list: %s" (print_list l_ind); *)
    let l_ind = induction_data l_ind ctx in
    let sigma,ty = ty_to_lambda env sigma obj_type eq_type refl ctx ty in
    let (eq_ind,univ),_ = Inductiveops.find_inductive env sigma eq_type in
    let catt_to_coq_db = catt_to_coq_db ctx in
    let rec body l_ind ty =
      match l_ind with
      | [] ->
        let (_,args) = EConstr.destApp sigma ty in
        EConstr.mkApp (refl, [|args.(0); args.(1)|])
      | (m,s_m,ty_m)::l_ind ->
        let v1 = {binder_name = Names.Name.Anonymous;
                  binder_relevance = Relevant}
        in
        let m_coq,i_lm = catt_to_coq_db m in
        let s_coq,_ = catt_to_coq_db s_m in
        let sigma,ty_m_coq = ty_to_lambda env sigma obj_type eq_type refl ctx ty_m in
        let ty = abstract env sigma ty i_lm in
        let case_return = [| v1; v1 |], ty in
        let ty = instantiate ty ty_m_coq s_coq refl in
        let case_branches =  [| ([| |], body l_ind ty) |] in
        let pcase = (Inductiveops.make_case_info env eq_ind Relevant RegularStyle,
                     univ,
                     [| ty_m_coq; s_coq |], (* parameters of inductive type *)
                     case_return,
                     Constr.NoInvert,
                     m_coq , (* match m_coq in ... *)
                     case_branches) in
        EConstr.mkCase pcase in
    ctx_to_lambda env sigma obj_type eq_type refl ctx (body l_ind ty)

  let tm env sigma ctx tm =
    let sigma, obj_type = Evarutil.new_Type sigma in
    let sigma, eq_type = c_Q env sigma in
    let sigma, refl = c_R env sigma in
    let sigma, tm = tm_to_lambda env sigma obj_type eq_type refl ctx tm in
    ctx_to_lambda env sigma obj_type eq_type refl ctx tm

  let coh env sigma coh =
    let sigma, eq_type = c_Q env sigma in
    let sigma, refl = c_R env sigma in
    coh_to_lambda env sigma eq_type refl coh
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
    (* let _ = Feedback.msg_debug *)
    (*   (str "body:" ++ *)
    (*    (Printer.pr_econstr_env env sigma body)) *)
    (* in *)
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
