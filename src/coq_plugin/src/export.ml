open Names
open EConstr
open Evd
open Catt
open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

let run_catt_on_file f =
  Prover.reset ();
  match Prover.parse_file f with
  | Ok f -> Command.exec ~loop_fn:Prover.loop f
  | Error () -> ()

let rec catt_var_to_coq_name v =
  match v with
  | Var.Db i -> string_of_int i
  | Var.Name s -> s
  | Var.New i -> string_of_int i
  | Var.Plus v -> catt_var_to_coq_name v ^ "_plus"
  | Var.Bridge v -> catt_var_to_coq_name v ^ "_bridge"

let c_Q env sigma =
  let gr = Coqlib.lib_ref "core.eq.type" in
  Evd.fresh_global env sigma gr

let c_R env sigma =
  let gr = Coqlib.lib_ref "core.eq.refl" in
  Evd.fresh_global env sigma gr

let rec find_db ctx x =
  match ctx with
  | [] -> Error.fatal "variable not found"
  | (y, _) :: _ when x = y -> 1
  | _ :: ctx -> 1 + find_db ctx x

let tbl_names : (string, unit) Hashtbl.t = Hashtbl.create 97
let counter = ref 0

let uniquify_name s =
  let s =
  match Hashtbl.find_opt tbl_names s with
  | Some () ->
    incr counter;
    (s ^ "_Uniq" ^(string_of_int !counter))
  | None -> s
  in Hashtbl.add tbl_names s (); s

let clean_name s =
  let s = Str.global_replace (Str.regexp "\\^-1") "_inv" s in
  let s = Str.global_replace (Str.regexp "\\.") "db" s in
  let s = Str.global_replace (Str.regexp ",") "F" s in
  let s = Str.global_replace (Str.regexp " ") "" s in
  let s = Str.global_replace (Str.regexp "_func") "" s in
  let s = Str.global_replace (Str.regexp "@") "at" s in
  let s = Str.global_replace (Str.regexp "\\-") "minus" s in
  let s = Str.global_replace (Str.regexp "/") "or" s in
  let s = Str.global_replace (Str.regexp "~") "_bridge" s in
  let s = 
  String.map
    (fun c ->
        match c with
        | '!' -> 'S'
        | '{' | '}' | '[' | ']' | '(' | ')' -> '_'
        | c -> c)
    s
  in uniquify_name s

module Translate : sig
  val tm : ?name : string -> Environ.env -> evar_map -> Tm.t -> unit
  val coh : ?name : string -> Environ.env -> evar_map -> Coh.t -> unit
end = struct
  let tbl : (Environment.value, string) Hashtbl.t = Hashtbl.create 97

  let retrieve_lambda value sigma =
    let build_econstr name =
      let gr = Coqlib.lib_ref ("catt_" ^ name) in
      let env = Global.env () in
      let sigma, econstr = Evd.fresh_global env sigma gr in
      (env, sigma, econstr)
    in
    Option.map build_econstr (Hashtbl.find_opt tbl value)

  let register name sigma body value =
    let env = Global.env() in 
    let sigma, body = Typing.solve_evars env sigma body in
    let body = Evarutil.nf_evar sigma body in
    let info = Declare.Info.make () in
    let cinfo =
      Declare.CInfo.make ~name:Id.(of_string ("catt_" ^ name)) ~typ:None ()
    in
    let gr =
      Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma
    in
    Coqlib.register_ref ("catt_" ^ name) gr;
    let env = Global.env () in
    let sigma, econstr = Evd.fresh_global env sigma gr in
    let _ = Hashtbl.add tbl value name in
    (env, sigma, econstr)

  let catt_to_coq_db ctx var =
    match var with
    | Var.Db n ->
        let l = List.length ctx - n in
        (EConstr.mkRel l, l)
    | _ -> assert false

  (* list of variables to successively eliminate, in order *)
  let induction_vars ps =
    let rec find_vars_list lv start l onto =
      match l with
      | [] -> (start + 1, onto)
      | ps :: l ->
          let start, varsl = find_vars_list lv start l onto in
          find_vars_ps lv (start + 1) ps varsl
    and find_vars_ps lv start ps onto =
      let onto = if lv > 0 then Var.Db start :: onto else onto in
      match ps with Br l -> find_vars_list (lv + 1) start l onto
    in
    snd (find_vars_ps 0 0 ps [])

  (* give the source and type of each variable *)
  let induction_data list_vars ctx =
    let find_data var =
      match fst (List.assoc var ctx) with
      | Obj -> assert false
      | Meta_ty _ -> Error.fatal "unresolved meta variable"
      | Arr (ty, s, _) -> (
          match s with Var s -> (var, s, ty) | _ -> assert false)
    in
    List.map find_data list_vars

  (* Abstract a locally maximal variable and its target. Crucially uses that a
     target of a locally maximal variable must occurs just before said variable *)
  let abstract env sigma econstr i_lm =
    let lm = Names.Id.of_string "lm" in
    let tgt = Names.Id.of_string "tm_tgt" in
    let econstr = EConstr.Vars.lift 2 econstr in
    let econstr =
      EConstr.Vars.substnl
        [ EConstr.mkVar lm; EConstr.mkVar tgt ]
        (i_lm + 1) econstr
    in
    let econstr = EConstr.Vars.subst_vars sigma [ lm; tgt ] econstr in
    let econstr = EConstr.Vars.liftn 2 (i_lm + 2) econstr in
    econstr

  let instantiate econstr tysrc src refl =
    EConstr.Vars.substl [ EConstr.mkApp (refl, [| tysrc; src |]); src ] econstr

  (* translate a catt context into a coq lambda abstraction *)
  let rec ctx_to_lambda env sigma obj_type eq_type refl ctx inner_tm =
    match ctx with
    | [] ->
        ( sigma,
          EConstr.mkLambda
            (nameR (Names.Id.of_string "A"), obj_type, inner_tm) )
    | (x, (ty, _)) :: ctx ->
        let env, sigma, ty =
          ty_to_econstr env sigma obj_type eq_type refl ctx ty
        in
        let id_lambda = Names.Id.of_string (catt_var_to_coq_name x) in
        let lambda = EConstr.mkLambda (nameR id_lambda, ty, inner_tm) in
        ctx_to_lambda env sigma obj_type eq_type refl ctx lambda

  (* translate a catt type into a coq type *)
  and ty_to_econstr env sigma obj_type eq_type refl ctx ty =
    match ty with
    | Obj -> (env, sigma, EConstr.mkRel (List.length ctx + 1))
    | Arr (ty, u, v) ->
        let env, sigma, ty =
          ty_to_econstr env sigma obj_type eq_type refl ctx ty
        in
        let env, sigma, u =
          tm_to_econstr env sigma obj_type eq_type refl ctx u
        in
        let env, sigma, v =
          tm_to_econstr env sigma obj_type eq_type refl ctx v
        in
        (env, sigma, EConstr.mkApp (eq_type, [| ty; u; v |]))
    | Meta_ty _ -> Error.fatal "unresolved type meta-variable"

  (* translate a catt term into a coq term *)
  and tm_to_econstr env sigma obj_type eq_type refl ctx tm =
    match tm with
    | Var x -> (env, sigma, EConstr.mkRel (find_db ctx x))
    | Coh (c, s) ->
        let env, sigma, c = coh_to_lambda env sigma obj_type eq_type refl c in
        let env, sigma, s =
          sub_ps_to_econstr_array env sigma obj_type eq_type refl ctx s
        in
        (env, sigma, EConstr.mkApp (c, s))
    | App (tm, s) ->
        let env, sigma, tm = tm_to_lambda env sigma obj_type eq_type refl tm in
        let env, sigma, s =
          sub_to_econstr_array env sigma obj_type eq_type refl ctx s
        in
        (env, sigma, EConstr.mkApp (tm, s))
    | Meta_tm _ -> Error.fatal "unresolved term meta-variable"

  (* translate a catt substitution into a list of function application
     arguments in coq *)
  and sub_ps_to_econstr_array env sigma obj_type eq_type refl ctx sub_ps =
    let l = List.length sub_ps in
    let array = Array.make (l + 1) (EConstr.mkRel 0) in
    let rec set_next i env sigma sub_ps =
      match sub_ps with
      | [] ->
          Array.set array 0 (EConstr.mkRel (List.length ctx + 1));
          (env, sigma)
      | (t, _) :: s ->
          let env, sigma, tm =
            tm_to_econstr env sigma obj_type eq_type refl ctx t
          in
          Array.set array i tm;
          set_next (i - 1) env sigma s
    in
    let env, sigma = set_next l env sigma sub_ps in
    (env, sigma, array)

  (* translate a catt substitution into a list of function application
     arguments in coq *)
  and sub_to_econstr_array env sigma obj_type eq_type refl ctx sub =
    let l = List.length sub in
    let array = Array.make (l + 1) (EConstr.mkRel 0) in
    let rec set_next i env sigma sub =
      match sub with
      | [] ->
          Array.set array i (EConstr.mkRel (List.length ctx + 1));
          (env, sigma)
      | (x, (t, _)) :: s ->
          let env, sigma, tm =
            tm_to_econstr env sigma obj_type eq_type refl ctx t
          in
          Array.set array i tm;
          set_next (i - 1) env sigma s
    in
    let env, sigma = set_next l env sigma sub in
    (env, sigma, array)

  (* translate a coherence into a coq function term *)
  and coh_to_lambda ?name env sigma obj_type eq_type refl coh =
    let value = Environment.Coh coh in
    match retrieve_lambda value sigma with
    | Some res -> res
    | None ->
        let ps, ty, coh_name = Coh.forget coh in
        let name =
          match name with
          | Some name -> name
          | None -> clean_name (Printing.full_name coh_name)
        in
        let ctx = Unchecked.ps_to_ctx ps in
        let l_ind = induction_vars ps in
        let l_ind = induction_data l_ind ctx in
        let env, sigma, ty =
          ty_to_econstr env sigma obj_type eq_type refl ctx ty
        in
        let (eq_ind, univ), _ = Inductiveops.find_inductive env sigma eq_type in
        let catt_to_coq_db = catt_to_coq_db ctx in
        let rec body l_ind ty =
          match l_ind with
          | [] ->
              let _, args = EConstr.destApp sigma ty in
              EConstr.mkApp (refl, [| args.(0); args.(1) |])
          | (m, s_m, ty_m) :: l_ind ->
              let v1 =
                {
                  Context.binder_name = Names.Name.Anonymous;
                  Context.binder_relevance = ERelevance.relevant;
                }
              in
              (* m_coq is the coq variable on which to do the match *)
              let m_coq, i_lm = catt_to_coq_db m in
              let s_coq, _ = catt_to_coq_db s_m in
              let env, sigma, ty_m_coq =
                ty_to_econstr env sigma obj_type eq_type refl ctx ty_m
              in
              let ty = abstract env sigma ty i_lm in
              let case_return = (([| v1; v1 |], ty), ERelevance.relevant) in
              let ty = instantiate ty ty_m_coq s_coq refl in
              let case_branches = [| ([||], body l_ind ty) |] in
              let pcase =
                ( Inductiveops.make_case_info env eq_ind RegularStyle,
                  univ,
                  [| ty_m_coq; s_coq |],
                  (* parameters of inductive type *)
                  case_return,
                  Constr.NoInvert,
                  m_coq,
                  (* match m_coq in ... *)
                  case_branches )
              in
              EConstr.mkCase pcase
        in
        let sigma, body =
          ctx_to_lambda env sigma obj_type eq_type refl ctx (body l_ind ty)
        in
        register ("coh_" ^ name) sigma body value

  and tm_to_lambda ?name env sigma obj_type eq_type refl tm =
    let value = Environment.Tm tm in
    match retrieve_lambda value sigma with
    | Some res -> res
    | None ->
        let name =
          match name with
          | Some name -> clean_name name
          | None -> clean_name (Tm.full_name tm)
        in
        let ctx = Tm.ctx tm in
        let tm = Tm.develop tm in
        let env, sigma, tm =
          tm_to_econstr env sigma obj_type eq_type refl ctx tm
        in
        let sigma, body =
          ctx_to_lambda env sigma obj_type eq_type refl ctx tm
        in
        register ("tm_" ^ name) sigma body value

  let tm ?name env sigma tm =
    let sigma, obj_type = Evarutil.new_Type sigma in
    let sigma, eq_type = c_Q env sigma in
    let sigma, refl = c_R env sigma in
    ignore (tm_to_lambda ?name env sigma obj_type eq_type refl tm)

  let coh ?name env sigma coh =
    let sigma, obj_type = Evarutil.new_Type sigma in
    let sigma, eq_type = c_Q env sigma in
    let sigma, refl = c_R env sigma in
    ignore (coh_to_lambda ?name env sigma obj_type eq_type refl coh)
end

let catt_tm file tm_names =
  run_catt_on_file file;
  let register_tm name =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    match Environment.val_var (Var.Name name) with
    | Coh c -> Translate.coh ~name env sigma c
    | Tm tm -> Translate.tm ~name env sigma tm
  in
  List.iter register_tm tm_names
