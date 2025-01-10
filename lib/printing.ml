open Common
open Unchecked_types

module Printing (CohT : sig
  type t
end) (TmT : sig
  type t
end) =
struct
  open Unchecked_types (CohT) (TmT)

  module Make (Coh : sig
    val to_string : CohT.t -> string
    val func_data : CohT.t -> (Var.t * int) list list
  end) (Tm : sig
    val func_data : TmT.t -> (Var.t * int) list list
    val name : TmT.t -> string
    (* val develop : TmT.t -> Unchecked_types(CohT)(TmT).tm *)
  end) =
  struct
    module Regular = struct
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
            if !Settings.unroll_coherences then
              Printf.sprintf "%s[%s]" (Coh.to_string c) (sub_ps_to_string s)
            else
              let func = Coh.func_data c in
              Printf.sprintf "(%s%s)" (Coh.to_string c)
                (sub_ps_to_string ~func s)
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

    (* module Kolmogorov = struct *)
    (*   let rec ps_to_string = function *)
    (*     | Br l -> *)
    (*         Printf.sprintf "[%s]" *)
    (*           (List.fold_left *)
    (*              (fun s ps -> Printf.sprintf "%s%s" (ps_to_string ps) s) *)
    (*              "" l) *)

    (*   let rec ty_to_string decls = function *)
    (*     | Meta_ty i -> assert false *)
    (*     | Obj -> ("*", decls) *)
    (*     | Arr (_, u, v) -> *)
    (*         let u, decls = tm_to_string decls u in *)
    (*         let v, decls = tm_to_string decls v in *)
    (*         (Printf.sprintf "%s -> %s" u v, decls) *)

    (*   and tm_to_string decls = function *)
    (*     | Var v -> (Var.to_string v, decls) *)
    (*     | Meta_tm i -> assert false *)
    (*     | Coh (c, s) -> *)
    (*         Printf.sprintf "%s[%s]" (Coh.to_string c) (sub_ps_to_string decls s) *)
    (*     | App (t, s) -> *)
    (*         let t = Tm.develop t in *)
    (*         tm_to_string decls (Unchecked.tm_apply_sub t s) *)

    (*   and sub_ps_to_string decls s = *)
    (*     match s with *)
    (*     | [] -> ("", decls) *)
    (*     | (t, expl) :: s -> *)
    (*         if expl then *)
    (*           let t, decls = tm_to_string decls t in *)
    (*           let s, decls = sub_ps_to_string decls s in *)
    (*           (Printf.sprintf "%s %s" s t, decls) *)
    (*         else sub_ps_to_string decls s *)
    (* end *)

    let ps_to_string = Regular.ps_to_string
    let ty_to_string = Regular.ty_to_string
    let tm_to_string = Regular.tm_to_string
    let ctx_to_string = Regular.ctx_to_string
    let sub_ps_to_string = Regular.sub_ps_to_string
    let sub_to_string ?func s = fst (Regular.sub_to_string ?func s)
    let sub_to_string_debug = Regular.sub_to_string_debug
    let meta_ctx_to_string = Regular.meta_ctx_to_string
    let pp_data_to_string = Regular.pp_data_to_string
    let full_name = Regular.full_name
  end
end
