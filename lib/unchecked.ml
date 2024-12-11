open Std
open Common
open Unchecked_types

module Unchecked (CohT : sig
  type t
end) (TmT : sig
  type t
end) =
struct
  open Unchecked_types (CohT) (TmT)

  module Make (Coh : sig
    val forget : CohT.t -> ps * Unchecked_types(CohT)(TmT).ty * pp_data
    val to_string : CohT.t -> string
    val func_data : CohT.t -> (Var.t * int) list list
    val check_equal : CohT.t -> CohT.t -> unit
    val check : ps -> ty -> pp_data -> CohT.t
  end) (Tm : sig
    val name : TmT.t -> string
    val func_data : TmT.t -> (Var.t * int) list list
    val develop : TmT.t -> Unchecked_types(CohT)(TmT).tm

    val apply :
      (Unchecked_types(CohT)(TmT).ctx -> Unchecked_types(CohT)(TmT).ctx) ->
      (Unchecked_types(CohT)(TmT).tm -> Unchecked_types(CohT)(TmT).tm) ->
      (pp_data -> pp_data) ->
      TmT.t ->
      TmT.t
  end) =
  struct
    let sub_ps_to_sub s =
      let rec aux s =
        match s with
        | [] -> ([], 0)
        | (t, e) :: s ->
            let s, i = aux s in
            ((Var.Db i, (t, e)) :: s, i + 1)
      in
      fst (aux s)

    let rec tm_do_on_variables tm f =
      match tm with
      | Var v -> f v
      | Meta_tm i -> Meta_tm i
      | Coh (c, s) -> Coh (c, sub_ps_do_on_variables s f)
      | App (t, s) -> App (t, sub_do_on_variables s f)

    and sub_do_on_variables s f =
      List.map (fun (v, (t, e)) -> (v, (tm_do_on_variables t f, e))) s

    and sub_ps_do_on_variables s f =
      List.map (fun (t, expl) -> (tm_do_on_variables t f, expl)) s

    let rec ty_do_on_variables ty f =
      match ty with
      | Meta_ty i -> Meta_ty i
      | Obj -> Obj
      | Arr (a, u, v) ->
          Arr
            ( ty_do_on_variables a f,
              tm_do_on_variables u f,
              tm_do_on_variables v f )

    let var_apply_sub v s =
      match List.assoc_opt v s with Some (t, _) -> t | None -> Var v

    let tm_apply_sub tm s = tm_do_on_variables tm (fun v -> var_apply_sub v s)
    let ty_apply_sub ty s = ty_do_on_variables ty (fun v -> var_apply_sub v s)

    let sub_ps_apply_sub s1 s2 =
      sub_ps_do_on_variables s1 (fun v -> var_apply_sub v s2)

    let sub_apply_sub s1 s2 =
      List.map (fun (v, (t, e)) -> (v, (tm_apply_sub t s2, e))) s1

    let ty_apply_sub_ps ty s = ty_apply_sub ty (sub_ps_to_sub s)
    let tm_apply_sub_ps tm s = tm_apply_sub tm (sub_ps_to_sub s)
    let sub_ps_apply_sub_ps sub_ps s = sub_ps_apply_sub sub_ps (sub_ps_to_sub s)

    let var_rename v r =
      match List.assoc_opt v r with Some t -> t | None -> Var v

    let tm_rename tm r = tm_do_on_variables tm (fun v -> var_rename v r)
    let ty_rename ty r = ty_do_on_variables ty (fun v -> var_rename v r)
    let sub_ps_rename s r = sub_ps_do_on_variables s (fun v -> var_rename v r)

    let rec var_sub_preimage v s =
      match s with
      | [] -> raise NotInImage
      | (w, (Var v', _)) :: _ when v = v' -> Var w
      | _ :: s -> var_sub_preimage v s

    let tm_sub_preimage tm s =
      tm_do_on_variables tm (fun v -> var_sub_preimage v s)

    let ty_sub_preimage ty s =
      ty_do_on_variables ty (fun v -> var_sub_preimage v s)

    (* rename is applying a variable to de Bruijn levels substitutions *)
    let rename_var v l =
      try Var (Db (fst (List.assoc v l)))
      with Not_found ->
        Error.fatal
          (Printf.sprintf "variable %s not found in context" (Var.to_string v))

    let rename_ty ty l = ty_do_on_variables ty (fun v -> rename_var v l)
    let rename_tm tm l = tm_do_on_variables tm (fun v -> rename_var v l)

    let rec db_levels c =
      match c with
      | [] -> ([], [], -1)
      | (x, (t, expl)) :: c ->
          let c, l, max = db_levels c in
          if List.mem_assoc x l then raise (DoubledVar (Var.to_string x))
          else
            let lvl = max + 1 in
            ( (Var.Db lvl, (rename_ty t l, expl)) :: c,
              (x, (lvl, expl)) :: l,
              lvl )

    let db_level_sub c =
      let _, names, _ = db_levels c in
      List.map (fun (t, (n, expl)) -> (Var.Db n, (Var t, expl))) names

    let db_level_sub_inv c =
      let _, names, _ = db_levels c in
      List.map (fun (t, (n, expl)) -> (t, (Var (Var.Db n), expl))) names

    (* Definition of FreePos(B):
       - in the paper, we define the bipointed verison with suspension and wedge
       - here we don't need the left point, as it is always the DeBruijn level 0,\
         however, we need the right point. We also need to rename every variable in\
         the right of a wedge, to avoid name clashes. To help with this, we also \
         carry around the maximal variable of a context. Given a function f, f_rp\
         is the name of the rightpointed variant, giving the right point and the\
         maximal variable.
    *)

    type ctx_bp = { ctx : ctx; max : int; rp : int }
    type sub_ps_bp = { sub_ps : sub_ps; l : tm; r : tm }

    let suspend_ps ps = Br [ ps ]
    let suspend_pp_data = function name, susp, func -> (name, susp + 1, func)

    let rec suspend_ty = function
      | Obj -> Arr (Obj, Var (Db 0), Var (Db 1))
      | Arr (a, v, u) -> Arr (suspend_ty a, suspend_tm v, suspend_tm u)
      | Meta_ty _ -> Error.fatal "meta-variables should be resolved"

    and suspend_tm = function
      | Var v -> Var (Var.suspend v)
      | Coh (c, s) -> Coh (suspend_coh c, suspend_sub_ps s)
      | App (t, s) ->
          let t = Tm.apply suspend_ctx suspend_tm suspend_pp_data t in
          App (t, suspend_sub s)
      | Meta_tm _ -> Error.fatal "meta-variables should be resolved"

    and suspend_coh c =
      let p, t, pp_data = Coh.forget c in
      Coh.check (suspend_ps p) (suspend_ty t) (suspend_pp_data pp_data)

    and suspend_sub_ps = function
      | [] -> [ (Var (Var.Db 1), false); (Var (Var.Db 0), false) ]
      | (t, expl) :: s -> (suspend_tm t, expl) :: suspend_sub_ps s

    and suspend_sub = function
      | [] ->
          [
            (Var.Db 1, (Var (Var.Db 1), false));
            (Var.Db 0, (Var (Var.Db 0), false));
          ]
      | (v, (t, e)) :: s -> (Var.suspend v, (suspend_tm t, e)) :: suspend_sub s

    and suspend_ctx_rp ctx =
      match ctx with
      | [] ->
          let ctx = [ (Var.Db 1, (Obj, false)); (Var.Db 0, (Obj, false)) ] in
          { ctx; max = 1; rp = 1 }
      | (v, (t, expl)) :: c -> (
          let c = suspend_ctx_rp c in
          let v = Var.suspend v in
          match v with
          | Var.Db i ->
              {
                ctx = (v, (suspend_ty t, expl)) :: c.ctx;
                max = max i c.max;
                rp = c.rp;
              }
          | _ ->
              {
                ctx = (v, (suspend_ty t, expl)) :: c.ctx;
                max = c.max;
                rp = c.rp;
              })

    and suspend_ctx ctx = (suspend_ctx_rp ctx).ctx

    let rec dim_ps = function Br [] -> 0 | Br l -> 1 + max_list_ps l

    and max_list_ps = function
      | [] -> 0
      | p :: l -> max (dim_ps p) (max_list_ps l)

    let var_inr_wedge v ctx_bp =
      match v with
      | Var.Db j -> if j = 0 then Var.Db ctx_bp.rp else Var.Db (j + ctx_bp.max)
      | _ -> Error.fatal "expecting a de-bruijn level"

    let ty_inr_wedge ty ctx_bp =
      ty_do_on_variables ty (fun v -> Var (var_inr_wedge v ctx_bp))

    let tm_inr_wedge tm ctx_bp =
      tm_do_on_variables tm (fun v -> Var (var_inr_wedge v ctx_bp))

    let rec ps_to_ctx_rp ps =
      match ps with
      | Br [] -> { ctx = [ (Var.Db 0, (Obj, true)) ]; rp = 0; max = 0 }
      | Br l ->
          let _, ctx = canonical_inclusions l in
          ctx

    and canonical_inclusions l =
      match l with
      | [] -> Error.fatal "empty inclusions"
      | [ ps ] ->
          ( [ suspend_sub_ps (identity_ps ps) ],
            suspend_ctx_rp (ps_to_ctx_rp ps).ctx )
      | ps :: l ->
          let id = suspend_sub_ps (identity_ps ps) in
          let ctx_ps = suspend_ctx_rp (ps_to_ctx_rp ps).ctx in
          let incls, ctx_base = canonical_inclusions l in
          let ctx_bp =
            {
              ctx = append_onto_ctx ctx_ps ctx_base;
              rp = ctx_ps.rp + ctx_base.max;
              max = ctx_ps.max + ctx_base.max;
            }
          in
          let incl = List.map (fun (t, e) -> (tm_inr_wedge t ctx_base, e)) id in
          (incl :: incls, ctx_bp)

    and append_onto_ctx ctx base =
      let rec aux = function
        | [] -> Error.fatal "empty context in wedge"
        | [ _ ] -> base.ctx
        | (v, (t, expl)) :: ctx ->
            let t = ty_inr_wedge t base in
            let v = var_inr_wedge v base in
            (v, (t, expl)) :: aux ctx
      in
      aux ctx.ctx

    and identity_ps ps =
      match ps with
      | Br [] -> [ (Var (Var.Db 0), true) ]
      | Br l ->
          let incls, _ = canonical_inclusions l in
          wedge_sub_ps incls

    and wedge_sub_ps l = wedge_sub_ps_bp (List.map sub_ps_to_sub_ps_bp l)

    and wedge_sub_ps_bp l =
      let lp = (List.last l).l in
      List.fold_right
        (fun s sub -> List.append s.sub_ps ((s.r, false) :: sub))
        l
        [ (lp, false) ]

    and sub_ps_to_sub_ps_bp sub_ps =
      match sub_ps with
      | [] | [ _ ] ->
          Error.fatal "bipointed substitution need at least two points"
      | [ (r, _); (l, _) ] -> { sub_ps = []; l; r }
      | t :: s ->
          let s = sub_ps_to_sub_ps_bp s in
          { sub_ps = t :: s.sub_ps; l = s.l; r = s.r }

    let canonical_inclusions l =
      let incls, _ = canonical_inclusions l in
      incls

    let tbl_ps_to_ctx : (ps, ctx) Hashtbl.t = Hashtbl.create 7829

    let ps_to_ctx ps =
      match Hashtbl.find_opt tbl_ps_to_ctx ps with
      | Some ctx -> ctx
      | None ->
          let ctx = (ps_to_ctx_rp ps).ctx in
          Hashtbl.add tbl_ps_to_ctx ps ctx;
          ctx

    let suspwedge_subs_ps list_subs list_ps =
      let incls = canonical_inclusions list_ps in
      wedge_sub_ps
        (List.map2
           (fun s i -> sub_ps_apply_sub (suspend_sub_ps s) (sub_ps_to_sub i))
           list_subs incls)

    let opsuspwedge_subs_ps list_subs list_ps =
      let rec swap_bp sub =
        match sub with
        | [] | [ _ ] -> Error.fatal "wedge without two basepoints"
        | [ r; l ] -> [ l; r ]
        | t :: sub -> t :: swap_bp sub
      in
      let incls = canonical_inclusions list_ps in
      wedge_sub_ps
        (List.map2
           (fun s i ->
             sub_ps_apply_sub (swap_bp (suspend_sub_ps s)) (sub_ps_to_sub i))
           (List.rev list_subs) (List.rev incls))

    let rec ps_bdry i ps =
      match ps with
      | Br [] -> Br []
      | Br _ when i <= 0 -> Br []
      | Br l -> Br (List.map (ps_bdry (i - 1)) l)

    let rec ps_src i ps =
      match (i, ps) with
      | 0, _ -> [ (Var (Var.Db 0), true) ]
      | _, Br [] -> [ (Var (Var.Db 0), true) ]
      | i, Br l -> suspwedge_subs_ps (List.map (ps_src (i - 1)) l) l

    let rec ps_tgt i ps =
      match (i, ps) with
      | 0, ps ->
          let c = ps_to_ctx_rp ps in
          [ (Var (Var.Db c.rp), true) ]
      | _, Br [] -> [ (Var (Var.Db 0), true) ]
      | i, Br l -> suspwedge_subs_ps (List.map (ps_tgt (i - 1)) l) l

    let ps_bdry ps = ps_bdry (dim_ps ps - 1) ps
    let ps_src ps = ps_src (dim_ps ps - 1) ps
    let ps_tgt ps = ps_tgt (dim_ps ps - 1) ps

    let rec ps_compose i ps1 ps2 =
      match (i, ps1, ps2) with
      | 0, Br l1, Br l2 ->
          let i1 = identity_ps (Br l1) in
          let i2 = identity_ps (Br l2) in
          let ctx_bp = ps_to_ctx_rp ps1 in
          let i2 = List.map (fun (x, e) -> (tm_inr_wedge x ctx_bp, e)) i2 in
          (Br (List.append l2 l1), i1, i2)
      | _, Br [], Br [] ->
          let s = identity_ps ps1 in
          (ps1, s, s)
      | i, Br l1, Br l2 -> (
          try
            let list = List.map2 (ps_compose (i - 1)) l1 l2 in
            let lps = List.map (fun (x, _, _) -> x) list in
            let li1 = List.map (fun (_, x, _) -> x) list in
            let li2 = List.map (fun (_, _, x) -> x) list in
            (Br lps, suspwedge_subs_ps li1 lps, suspwedge_subs_ps li2 lps)
          with Invalid_argument _ ->
            Error.fatal
              "composition of pasting schemes only allowed when \
               theirboundaries match up")

    let rec pullback_up i ps1 ps2 s1 s2 =
      match (i, ps1, ps2, s1, s2) with
      | 0, _, _, s1, s2 ->
          let rec append s2 =
            match s2 with
            | [] -> Error.fatal "substitution to pasting scheme cannot be empty"
            | [ _ ] -> s1
            | t :: s2 -> t :: append s2
          in
          append s2
      | _, Br [], Br [], _, _ -> s1
      | i, Br l1, Br l2, s1, s2 ->
          let incls1 = canonical_inclusions l1 in
          let incls2 = canonical_inclusions l2 in
          let s1 = sub_ps_to_sub s1 in
          let s2 = sub_ps_to_sub s2 in
          let ls =
            List.map4
              (fun ps1 ps2 i1 i2 ->
                let s1 = sub_ps_to_sub_ps_bp (sub_ps_apply_sub i1 s1) in
                let s2 = sub_ps_to_sub_ps_bp (sub_ps_apply_sub i2 s2) in
                let hom_sub = pullback_up (i - 1) ps1 ps2 s1.sub_ps s2.sub_ps in
                { sub_ps = hom_sub; l = s1.l; r = s1.r })
              l1 l2 incls1 incls2
          in
          wedge_sub_ps_bp ls

    module Printing = struct
      let rec func_to_string func =
        let rec print_list = function
          | [] -> ""
          | [ (x, n) ] -> Printf.sprintf "(%s,%d)" (Var.to_string x) n
          | (x, n) :: l ->
              Printf.sprintf "%s (%s,%d)" (print_list l) (Var.to_string x) n
        in
        match func with
        | [] -> ""
        | l :: func ->
            Printf.sprintf "%s[%s]" (func_to_string func) (print_list l)

      let rec bracket i s =
        if i <= 0 then s else Printf.sprintf "[%s]" (bracket (i - 1) s)

      let rec ps_to_string = function
        | Br l ->
            Printf.sprintf "[%s]"
              (List.fold_left
                 (fun s ps -> Printf.sprintf "%s%s" (ps_to_string ps) s)
                 "" l)

      let rec ty_to_string = function
        | Meta_ty i -> Printf.sprintf "_ty%i" i
        | Obj -> "*"
        | Arr (a, u, v) ->
            if !Settings.verbosity >= 3 then
              Printf.sprintf "%s | %s -> %s" (ty_to_string a) (tm_to_string u)
                (tm_to_string v)
            else Printf.sprintf "%s -> %s" (tm_to_string u) (tm_to_string v)

      and tm_to_string = function
        | Var v -> Var.to_string v
        | Meta_tm i -> Printf.sprintf "_tm%i" i
        | Coh (c, s) ->
            if not !Settings.unroll_coherences then
              let func = Coh.func_data c in
              Printf.sprintf "(%s%s)" (Coh.to_string c)
                (sub_ps_to_string ~func s)
            else Printf.sprintf "%s[%s]" (Coh.to_string c) (sub_ps_to_string s)
        | App (t, s) ->
            let func = Tm.func_data t in
            let str_s, expl = sub_to_string ~func s in
            let expl_str = if expl then "@" else "" in
            Printf.sprintf "(%s%s%s)" expl_str (Tm.name t) str_s

      and sub_ps_to_string ?(func = []) s =
        match func with
        | [] -> sub_ps_to_string_nofunc s
        | func :: _ -> sub_ps_to_string_func s func

      and sub_ps_to_string_nofunc s =
        match s with
        | [] -> ""
        | (t, expl) :: s ->
            if expl || !Settings.print_explicit_substitutions then
              Printf.sprintf "%s %s" (sub_ps_to_string s) (tm_to_string t)
            else sub_ps_to_string s

      and sub_ps_to_string_func s func =
        let rec print s =
          match s with
          | (t, true) :: s ->
              let str, x = print s in
              let arg =
                match List.assoc_opt (Var.Db x) func with
                | None -> tm_to_string t
                | Some i -> bracket i (tm_to_string t)
              in
              (Printf.sprintf "%s %s" str arg, x + 1)
          | (t, false) :: s ->
              let str, x = print s in
              let str =
                if !Settings.print_explicit_substitutions then
                  Printf.sprintf "%s %s" str (tm_to_string t)
                else str
              in
              (str, x + 1)
          | [] -> ("", 0)
        in
        fst (print s)

      and sub_to_string ?(func = []) sub =
        match func with
        | [] -> (sub_to_string_nofunc sub, false)
        | func :: _ ->
            let s, b = sub_to_string_func sub func in
            (" " ^ s, b)

      and sub_to_string_nofunc sub =
        match sub with
        | [] -> ""
        | (_, (t, expl)) :: s ->
            if expl || !Settings.print_explicit_substitutions then
              Printf.sprintf "%s %s" (sub_to_string_nofunc s) (tm_to_string t)
            else sub_to_string_nofunc s

      and sub_to_string_func s func =
        let arg_to_string t b =
          if b || !Settings.print_explicit_substitutions then tm_to_string t
          else "_"
        in
        let rec string_list s needs_expl skip =
          match s with
          | [] when skip <= 0 -> ([], needs_expl)
          | (x, (t, e)) :: s when skip <= 0 -> (
              match List.assoc_opt x func with
              | None ->
                  let l, b = string_list s needs_expl 0 in
                  ((arg_to_string t e, e) :: l, b)
              | Some i ->
                  let l, b = string_list s (needs_expl || not e) (2 * i) in
                  ((bracket i (arg_to_string t e), e) :: l, b))
          | _ :: s -> string_list s needs_expl (skip - 1)
          | [] ->
              Error.fatal
                "functorialised arguments present in inconsistent places"
        in
        let str, needs_expl = string_list s false 0 in
        let str =
          List.rev_map
            (fun (tm, e) -> if e || needs_expl then Some tm else None)
            str
        in
        (String.concat " " (List.filter_map Fun.id str), needs_expl)

      and sub_to_string_debug sub =
        match sub with
        | [] -> ""
        | (x, (t, _)) :: s ->
            Printf.sprintf "%s (%s, %s)" (sub_to_string_debug s)
              (Var.to_string x) (tm_to_string t)

      let pp_data_to_string ?(print_func = false) (name, susp, func) =
        let susp_name =
          if susp > 0 then Printf.sprintf "!%i%s" susp name else name
        in
        match func with
        | [] -> susp_name
        | _ :: [] when not print_func -> susp_name
        | _ :: func when not print_func ->
            susp_name ^ "_func" ^ func_to_string func
        | func -> susp_name ^ "_func" ^ func_to_string func

      let rec ctx_to_string = function
        | [] -> ""
        | (x, (t, true)) :: c ->
            Printf.sprintf "%s (%s: %s)" (ctx_to_string c) (Var.to_string x)
              (ty_to_string t)
        | (x, (t, false)) :: c ->
            Printf.sprintf "%s {%s: %s}" (ctx_to_string c) (Var.to_string x)
              (ty_to_string t)

      let rec meta_ctx_to_string = function
        | [] -> ""
        | (i, t) :: c ->
            Printf.sprintf "%s (_tm%i: %s)" (meta_ctx_to_string c) i
              (ty_to_string t)

      let full_name name = pp_data_to_string ~print_func:true name
    end

    let ps_to_string = Printing.ps_to_string
    let ty_to_string = Printing.ty_to_string
    let tm_to_string = Printing.tm_to_string
    let ctx_to_string = Printing.ctx_to_string
    let sub_ps_to_string = Printing.sub_ps_to_string
    let sub_to_string ?func s = fst (Printing.sub_to_string ?func s)
    let sub_to_string_debug = Printing.sub_to_string_debug
    let meta_ctx_to_string = Printing.meta_ctx_to_string
    let pp_data_to_string = Printing.pp_data_to_string
    let full_name = Printing.full_name

    let rec check_equal_ps ps1 ps2 =
      match (ps1, ps2) with
      | Br [], Br [] -> ()
      | Br (ps1 :: l1), Br (ps2 :: l2) ->
          check_equal_ps ps1 ps2;
          List.iter2 check_equal_ps l1 l2
      | Br [], Br (_ :: _) | Br (_ :: _), Br [] ->
          raise (NotEqual (ps_to_string ps1, ps_to_string ps2))

    let rec check_equal_ty ty1 ty2 =
      match (ty1, ty2) with
      | Meta_ty i, Meta_ty j ->
          if i <> j then raise (NotEqual (string_of_int i, string_of_int j))
      | Obj, Obj -> ()
      | Arr (ty1, u1, v1), Arr (ty2, u2, v2) ->
          check_equal_ty ty1 ty2;
          check_equal_tm u1 u2;
          check_equal_tm v1 v2
      | Obj, Arr _
      | Arr _, Obj
      | Meta_ty _, Obj
      | Meta_ty _, Arr _
      | Obj, Meta_ty _
      | Arr _, Meta_ty _ ->
          raise (NotEqual (ty_to_string ty1, ty_to_string ty2))

    and check_equal_tm tm1 tm2 =
      match (tm1, tm2) with
      | Var v1, Var v2 -> Var.check_equal v1 v2
      | Meta_tm i, Meta_tm j ->
          if i <> j then raise (NotEqual (string_of_int i, string_of_int j))
      | Coh (coh1, s1), Coh (coh2, s2) ->
          Coh.check_equal coh1 coh2;
          check_equal_sub_ps s1 s2
      (* Define check_equal_sub and Tm.develop *)
      | App (t1, s1), App (t2, s2) when t1 == t2 -> check_equal_sub s1 s2
      | App (t, s), ((Coh _ | App _ | Var _) as tm2)
      | ((Coh _ | Var _) as tm2), App (t, s) ->
          let c = Tm.develop t in
          check_equal_tm (tm_apply_sub c s) tm2
      | Var _, Coh _
      | Coh _, Var _
      | Meta_tm _, Var _
      | Meta_tm _, Coh _
      | Var _, Meta_tm _
      | Coh _, Meta_tm _
      | App _, Meta_tm _
      | Meta_tm _, App _ ->
          raise (NotEqual (tm_to_string tm1, tm_to_string tm2))

    and check_equal_sub_ps s1 s2 =
      List.iter2 (fun (t1, _) (t2, _) -> check_equal_tm t1 t2) s1 s2

    and check_equal_sub s1 s2 =
      List.iter2 (fun (_, (t1, _)) (_, (t2, _)) -> check_equal_tm t1 t2) s1 s2

    let rec check_equal_ctx ctx1 ctx2 =
      match (ctx1, ctx2) with
      | [], [] -> ()
      | (v1, (t1, _)) :: c1, (v2, (t2, _)) :: c2 ->
          Var.check_equal v1 v2;
          check_equal_ty t1 t2;
          check_equal_ctx c1 c2
      | _ :: _, [] | [], _ :: _ ->
          raise (NotEqual (ctx_to_string ctx1, ctx_to_string ctx2))

    let check_equal_ty ty1 ty2 =
      if ty1 == ty2 then () else check_equal_ty ty1 ty2

    let check_equal_tm tm1 tm2 =
      if tm1 == tm2 then () else check_equal_tm tm1 tm2

    let check_equal_sub_ps s1 s2 =
      if s1 == s2 then () else check_equal_sub_ps s1 s2

    let check_equal_ctx ctx1 ctx2 =
      if ctx1 == ctx2 then () else check_equal_ctx ctx1 ctx2

    let rec tm_contains_var t x =
      match t with
      | Var v -> v = x
      | Coh (_, s) -> List.exists (fun (t, _) -> tm_contains_var t x) s
      | App (_, s) -> List.exists (fun (_, (t, _)) -> tm_contains_var t x) s
      | Meta_tm _ -> Error.fatal "meta-variables should be resolved"

    let rec ty_contains_var a x =
      match a with
      | Obj -> false
      | Arr (a, t, u) ->
          tm_contains_var t x || tm_contains_var u x || ty_contains_var a x
      | Meta_ty _ -> Error.fatal "meta-variables should be resolved"

    let tm_contains_vars t l = List.exists (tm_contains_var t) l

    let rec list_to_sub s ctx =
      match (s, ctx) with
      | t :: s, (x, (_, expl)) :: ctx -> (x, (t, expl)) :: list_to_sub s ctx
      | [], [] -> []
      | _ -> raise WrongNumberOfArguments

    let list_to_db_level_sub l =
      let rec aux l =
        match l with
        | [] -> ([], 0)
        | t :: l ->
            let s, n = aux l in
            ((Var.Db n, t) :: s, n + 1)
      in
      fst (aux l)

    let rec dim_ty = function
      | Obj -> 0
      | Arr (a, _, _) -> 1 + dim_ty a
      | Meta_ty _ -> Error.fatal "meta-variables should be resolved"

    let rec dim_ctx = function
      | [] -> 0
      | (_, (t, _)) :: c -> max (dim_ctx c) (dim_ty t)

    let rec ty_to_sub_ps a =
      match a with
      | Obj -> []
      | Arr (a, u, v) -> (v, false) :: (u, false) :: ty_to_sub_ps a
      | Meta_ty _ ->
          Error.fatal
            "substitution can only be computed afterresolving the type"

    let coh_to_sub_ps t =
      match t with
      | Coh (coh, s) ->
          let _, ty, _ = Coh.forget coh in
          let sub = sub_ps_to_sub s in
          (t, true) :: ty_to_sub_ps (ty_apply_sub ty sub)
      | _ -> Error.fatal "can only convert coh to sub ps"

    let sub_to_sub_ps ps s = sub_ps_apply_sub (identity_ps ps) s
  end
end
