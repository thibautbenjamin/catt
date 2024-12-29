open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

exception FunctorialiseMeta
exception NotClosed
exception Unsupported

let coh_depth1 = ref (fun _ -> Error.fatal "Uninitialised forward reference")

module Memo = struct
  let tbl_whisk = Hashtbl.create 97

  let find_whisk i f =
    try Hashtbl.find tbl_whisk i
    with Not_found ->
      let res = f i in
      Hashtbl.add tbl_whisk i res;
      res
end

let check_upwards_closed ctx l =
  let closed =
    List.for_all
      (fun x ->
        List.for_all
          (fun (y, (ty, _)) ->
            (not (Unchecked.ty_contains_var ty x)) || List.mem y l)
          ctx)
      l
  in
  if not closed then raise NotClosed

let check_codim1 c n l =
  let is_comdim1 =
    List.for_all
      (fun x ->
        let ty, _ = List.assoc x c in
        Unchecked.dim_ty ty >= n - 1)
      l
  in
  if not is_comdim1 then raise Unsupported

let rec next_round l =
  match l with
  | [] -> ([], [])
  | (_, 0) :: l ->
      let vars, left = next_round l in
      (vars, left)
  | (v, n) :: l when n >= 1 ->
      let vars, left = next_round l in
      (v :: vars, (Var.Bridge v, n - 1) :: left)
  | _ -> Error.fatal "cannot functorialise a negative number of times."

let pp_data_rename pp names =
  let name, susp, func = pp in
  let rec rename f =
    match f with
    | [] -> []
    | (x, i) :: f -> (Display_maps.var_apply_sub x names, i) :: rename f
  in
  (name, susp, List.map rename func)

(* Functorialised coherences with respect to locally maximal variables are
   coherences. This function updates the list of variables in the resulting
   coherence that come from a functorialisation *)
let pp_data l (name, susp, func) =
  let func =
    let is_mergeable =
      match func with
      | [] -> false
      | f :: _ ->
          List.for_all
            (fun x ->
              match List.assoc_opt x f with
              | None -> false
              | Some k -> List.for_all (fun (_, n) -> n <= k) f)
            l
    in
    if is_mergeable then
      let f, func =
        match func with [] -> assert false | f :: func -> (f, func)
      in
      let rec add_in func v =
        match func with
        | [] -> [ (Var.Bridge v, 1) ]
        | (w, n) :: func when v = w -> (Var.Bridge v, n + 1) :: func
        | (w, n) :: func -> (w, n) :: add_in func v
      in
      let rec add_all func l =
        match l with [] -> func | v :: l -> add_all (add_in func v) l
      in
      add_all f l :: func
    else List.map (fun x -> (Var.Bridge x, 1)) l :: func
  in
  (name, susp, func)

(*
   Given a context, a ps-substitution and a list of variables, returns
   the list of all variables in the context whose corresponding term
   in the substitution contains a variable from the input list
*)
let rec preimage ctx s l =
  match (ctx, s) with
  | [], [] -> []
  | (x, _) :: c, (t, _) :: s when Unchecked.tm_contains_vars t l ->
      x :: preimage c s l
  | _ :: c, _ :: s -> preimage c s l
  | [], _ :: _ | _ :: _, [] ->
      Error.fatal "functorialisation in a non-existant place"

let rec tgt_renaming l =
  match l with [] -> [] | v :: tl -> (v, Var (Var.Plus v)) :: tgt_renaming tl

(* returns the n-composite of a (n+j)-cell with a (n+k)-cell *)
let rec whisk n j k =
  let build_whisk t =
    let n, j, k = t in
    let comp = Builtin.comp_n 2 in
    let func_data = [ (Var.Db 4, k); (Var.Db 2, j) ] in
    let whisk = coh_successively comp func_data in
    Suspension.checked_tm (Some n) whisk
  in
  Memo.find_whisk (n, j, k) build_whisk

(*
  How long should substitutions for whisk be?
  (whisk 0 0 0) requires ps-context (x(f)y(g)z) so 2+1+1+1
  (whisk n 0 0) requires 2*(n+1)+1+1+1
  (whisk n j 0) requires (2*(n+1))+((2*j)+1)+1+1
  (whisk n 0 k) requires (2*(n+1))+1+(2*k+1)+1

  Assuming ty1 has right dimension, we just need to know k
*)
and whisk_sub_ps k t1 ty1 t2 ty2 =
  let rec take n l =
    match l with h :: t when n > 0 -> h :: take (n - 1) t | _ -> []
  in
  let sub_base = Unchecked.ty_to_sub_ps ty1 in
  let sub_ext = take ((2 * k) + 1) (Unchecked.ty_to_sub_ps ty2) in
  List.concat [ [ (t2, true) ]; sub_ext; [ (t1, true) ]; sub_base ]

(*
  wcomp is the whiskered binary composite
  wcomp (f,fty) n (g,gty) means f *_n g

  Since it has access to both fty and gty it can automatically infer j and k
  Therefore the only dimension parameter it needs is n
  This API takes and returns pairs (tm*ty) meaning it can be easily nested
  (wcomp f 0 (wcomp g 0 h)) = f *_0 (g *_0 h)
*)
and wcomp (f, fty) n (g, gty) =
  let j = Unchecked.dim_ty fty - n - 1 in
  let k = Unchecked.dim_ty gty - n - 1 in
  let whisk = whisk n j k in
  let whisk_sub_ps = whisk_sub_ps k f fty g gty in
  let whisk_sub = Unchecked.sub_ps_to_sub whisk_sub_ps in
  (App (whisk, whisk_sub), Unchecked.ty_apply_sub_ps (Tm.ty whisk) whisk_sub_ps)

(* Invariant maintained:
    src_prod returns a term of same dimension as tm
*)
and src_prod t l tm tm_t d n =
  match t with
  | Arr (ty', src, _tgt) when Unchecked.tm_contains_vars src l ->
      let prod = src_prod ty' l tm tm_t d (n - 1) in
      let ty_f = ty ty' l src in
      let src_f = tm_one_step_tm src l in
      wcomp (src_f, ty_f) n prod
  | Arr (_, _, _) | Obj -> (tm, tm_t)
  | _ -> raise FunctorialiseMeta

and tgt_prod t l tm tm_t d n =
  match t with
  | Arr (ty', _src, tgt) when Unchecked.tm_contains_vars tgt l ->
      let prod = tgt_prod ty' l tm tm_t d (n - 1) in
      let ty_f = ty ty' l tgt in
      let tgt_f = tm_one_step_tm tgt l in
      wcomp prod n (tgt_f, ty_f)
  | Arr (_, _, _) | Obj -> (tm, tm_t)
  | _ -> raise FunctorialiseMeta

and ty t l tm =
  let d = Unchecked.dim_ty t in
  let tgt_renaming = tgt_renaming l in
  let tm_incl = Unchecked.tm_rename tm tgt_renaming in
  let t_incl = Unchecked.ty_rename t tgt_renaming in
  let src, src_t = tgt_prod t l tm t d (d - 1) in
  let tgt, _tgt_t = src_prod t l tm_incl t_incl d (d - 1) in
  Arr (src_t, src, tgt)

and ctx c l =
  match c with
  | [] -> []
  | (x, (t, expl)) :: c when List.mem x l ->
      let ty_tgt = Unchecked.ty_rename t (tgt_renaming l) in
      let tf = ty t l (Var x) in
      (Var.Bridge x, (tf, expl))
      :: (Var.Plus x, (ty_tgt, false))
      :: (x, (t, false))
      :: ctx c l
  | (x, a) :: c -> (x, a) :: ctx c l

(* Functorialisation of a coherence once with respect to a list of
   variables *)
and coh_depth0 coh l =
  let ps, t, pp = Coh.forget coh in
  let ctxf = ctx (Unchecked.ps_to_ctx ps) l in
  let names = Unchecked.db_level_sub_inv ctxf in
  let psf = PS.forget (PS.mk (Ctx.check ctxf)) in
  let ty = ty t l (Coh (coh, Unchecked.identity_ps ps)) in
  let ty = Unchecked.ty_apply_sub ty names in
  let pp = pp_data l pp in
  let pp = pp_data_rename pp names in
  (check_coh psf ty pp, names)

and coh coh l =
  let ps, ty, _ = Coh.forget coh in
  let c = Unchecked.ps_to_ctx ps in
  check_upwards_closed c l;
  let depth0 = List.for_all (fun (x, (_, e)) -> e || not (List.mem x l)) c in
  if depth0 then
    let coh, names = coh_depth0 coh l in
    (Tm.of_coh coh, names)
  else (
    check_codim1 c (Unchecked.dim_ty ty) l;
    (!coh_depth1 coh l, []))

and coh_successively c l =
  let l, next = next_round l in
  if l = [] then
    let ps, _, pp_data = Coh.forget c in
    let id = Unchecked.identity_ps ps in
    check_term (Ctx.check (Unchecked.ps_to_ctx ps)) pp_data (Coh (c, id))
  else
    let cohf, names = coh c l in
    let next =
      List.map (fun (x, i) -> (Display_maps.var_apply_sub x names, i)) next
    in
    tm_successively cohf next

(*
   Functorialisation a term once with respect to a list of variables.
   Returns a list containing the functorialise term followed by its
   target and its source.
 *)
and tm_one_step t l expl =
  match t with
  | Var v ->
      [ (Var (Var.Bridge v), expl); (Var (Var.Plus v), false); (Var v, false) ]
  | Coh (c, s) ->
      let t' = Unchecked.tm_rename t (tgt_renaming l) in
      let sf = sub_ps s l in
      let ps, _, _ = Coh.forget c in
      let psc = Unchecked.ps_to_ctx ps in
      let places = preimage psc s l in
      let cohf, _ = coh c places in
      let subf = Unchecked.list_to_sub (List.map fst sf) (Tm.ctx cohf) in
      let tm = App (cohf, subf) in
      [ (tm, expl); (t', false); (t, false) ]
  | App (t, s) ->
      let total_t = Unchecked.tm_apply_sub (Tm.develop t) s in
      tm_one_step total_t l expl
  | Meta_tm _ -> raise FunctorialiseMeta

and tm_one_step_tm t l = fst (List.hd (tm_one_step t l true))

and sub_ps s l =
  match s with
  | [] -> []
  | (t, expl) :: s ->
      if not (Unchecked.tm_contains_vars t l) then (t, expl) :: sub_ps s l
      else List.append (tm_one_step t l expl) (sub_ps s l)

and tm_successively t s =
  let l, next = next_round s in
  if l <> [] then
    let t, names =
      Tm.apply
        (fun c -> ctx c l)
        (fun t -> tm_one_step_tm t l)
        (fun pp -> pp_data l pp)
        t
    in
    tm_successively t
      (List.map (fun (x, i) -> (Display_maps.var_apply_sub x names, i)) next)
  else t

(* Public API *)
let report_errors f str =
  try f () with
  | FunctorialiseMeta ->
      Error.functorialisation (Lazy.force str)
        "cannot functorialise meta-variables"
  | NotClosed ->
      Error.functorialisation (Lazy.force str)
        "list of functorialised arguments is not closed"
  | Unsupported ->
      Error.functorialisation (Lazy.force str)
        "higher-dimensional transformations in depth >= 0 are not yet supported"

(* Functorialisation of a coherence: exposed function *)
let coh c l =
  report_errors
    (fun _ -> fst (coh c l))
    (lazy ("coherence: " ^ Coh.to_string c))

let coh_depth0 c l =
  report_errors
    (fun _ -> fst (coh_depth0 c l))
    (lazy ("coherence: " ^ Coh.to_string c))

let coh_successively c l =
  report_errors
    (fun _ -> coh_successively c l)
    (lazy ("coherence: " ^ Coh.to_string c))

let rec sub s l =
  match s with
  | [] -> []
  | (x, (t, e)) :: s when not (List.mem x l) -> (x, (t, e)) :: sub s l
  | (x, (t, e)) :: s -> (
      match tm_one_step t l true with
      | [ (tm_f, _); (tgt_t, _); (src_t, _) ] ->
          (Var.Bridge x, (tm_f, e))
          :: (Var.Plus x, (tgt_t, false))
          :: (x, (src_t, false))
          :: sub s l
      | [ (t, _) ] -> (x, (t, e)) :: sub s l
      | _ -> assert false)

(* Functorialisation once with respect to every maximal argument *)
let coh_all c =
  let ps, _, _ = Coh.forget c in
  let ct = Unchecked.ps_to_ctx ps in
  let d = Unchecked.dim_ps ps in
  let l =
    List.filter_map
      (fun (x, (ty, _)) -> if Unchecked.dim_ty ty = d then Some x else None)
      ct
  in
  coh_depth0 c l

(* Functorialisation a term: exposed function *)
let tm t l =
  report_errors (fun _ -> tm_successively t l) (lazy ("term: " ^ Tm.name t))

let ps p l =
  let c = ctx (Unchecked.ps_to_ctx p) l in
  let _, names, _ = Unchecked.db_levels c in
  (PS.(forget (mk (Ctx.check c))), names)

let sub_w_tgt p s l =
  let s_f = sub_ps s l in
  let l = preimage (Unchecked.ps_to_ctx p) s l in
  let p_f, names = ps p l in
  (s_f, p_f, names, l)
