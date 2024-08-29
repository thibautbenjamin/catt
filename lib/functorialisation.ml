open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh)

exception FunctorialiseMeta

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

(* Functorialised coherences with respect to locally maximal variables are
   coherences. This function updates the list of variables in the resulting
   coherence that come from a functorialisation *)
let compute_func_data l func =
  let incr_db v i =
    match v with Var.Db k -> Var.Db (k + i) | _ -> assert false
  in
  let rec add_in func v =
    match func with
    | [] -> [ (incr_db v 2, 1) ]
    | (w, n) :: func when v = w -> (incr_db v 2, n + 1) :: func
    | (w, n) :: func -> (incr_db w 2, n) :: add_in func v
  in
  let rec add_all func l =
    match l with [] -> func | v :: l -> add_all (add_in func v) l
  in
  add_all func l

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

let rec tgt_subst l =
  match l with [] -> [] | v :: tl -> (v, Var (Var.Plus v)) :: tgt_subst tl

(* returns the n-composite of a (n+j+1)-cell with a (n+k+1)-cell *)
let rec whisk n j k =
  let build_whisk t =
    let n, j, k = t in
    let comp = Builtin.comp_n 2 in
    let func_data = [ (Var.Db 4, k); (Var.Db 2, j) ] in
    let whisk =
      match coh_successively comp func_data with
      | Coh (c, _), _ -> c
      | _ -> assert false
    in
    Suspension.coh (Some n) whisk
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
  let sub_base = Unchecked.ty_to_sub_ps ty1 in
  let sub_ext = Common.take ((2 * k) + 1) (Unchecked.ty_to_sub_ps ty2) in
  ((t2, true) :: sub_ext) @ ((t1, true) :: sub_base)

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
  Unchecked.coh_ty whisk whisk_sub_ps

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
  let tgt_subst = tgt_subst l in
  let tm_incl = Unchecked.tm_apply_sub tm tgt_subst in
  let t_incl = Unchecked.ty_apply_sub t tgt_subst in
  let src, src_t = tgt_prod t l tm t d (d - 1) in
  let tgt, _tgt_t = src_prod t l tm_incl t_incl d (d - 1) in
  Arr (src_t, src, tgt)

and ctx c l =
  match c with
  | [] -> []
  | (x, (t, expl)) :: c when List.mem x l ->
      let ty_tgt = Unchecked.ty_apply_sub t (tgt_subst l) in
      let tf = ty t l (Var x) in
      (Var.Bridge x, (tf, expl))
      :: (Var.Plus x, (ty_tgt, false))
      :: (x, (t, false))
      :: ctx c l
  | (x, a) :: c -> (x, a) :: ctx c l

(* Functorialisation of a coherence once with respect to a list of
   variables *)
and coh_depth0 coh l =
  let ps, t, (name, susp, func) = Coh.forget coh in
  let ctxf = ctx (Unchecked.ps_to_ctx ps) l in
  let _, names, _ = Unchecked.db_levels ctxf in
  let psf = PS.forget (PS.mk (Ctx.check ctxf)) in
  let ty = ty t l (Coh (coh, Unchecked.identity_ps ps)) in
  let ty = Unchecked.rename_ty ty names in
  let func_data = compute_func_data l func in
  check_coh psf ty (name, susp, func_data)

and coh coh l =
  let ps, _, _ = Coh.forget coh in
  let c = Unchecked.ps_to_ctx ps in
  let depth0 = List.for_all (fun (x, (_, e)) -> e || not (List.mem x l)) c in
  let cohf =
    if depth0 then
      let id = Unchecked.identity_ps ps in
      let sf = sub_ps id l in
      let pscf = ctx (Unchecked.ps_to_ctx ps) l in
      let cohf = coh_depth0 coh l in
      (Coh (cohf, sf), pscf)
    else !coh_depth1 coh l
  in
  cohf

and coh_successively c l =
  let l, next = next_round l in
  if l = [] then
    let ps, _, _ = Coh.forget c in
    let id = Unchecked.identity_ps ps in
    (Coh (c, id), Unchecked.ps_to_ctx ps)
  else
    let cohf, ctxf = coh c l in
    tm ctxf cohf next

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
      let t' = Unchecked.tm_apply_sub t (tgt_subst l) in
      let sf = sub_ps s l in
      let ps, _, _ = Coh.forget c in
      let psc = Unchecked.ps_to_ctx ps in
      let places = preimage psc s l in
      let cohf, pscf = coh c places in
      let subf = Unchecked.list_to_sub (List.map fst sf) pscf in
      let tm = Unchecked.tm_apply_sub cohf subf in
      [ (tm, expl); (t', false); (t, false) ]
  | Meta_tm _ -> raise FunctorialiseMeta

and tm_one_step_tm t l = fst (List.hd (tm_one_step t l true))

and sub_ps s l =
  match s with
  | [] -> []
  | (t, expl) :: s ->
      if not (Unchecked.tm_contains_vars t l) then (t, expl) :: sub_ps s l
      else List.append (tm_one_step t l expl) (sub_ps s l)

and tm c t s =
  let l, next = next_round s in
  if l <> [] then
    let c = ctx c l in
    let t = tm_one_step_tm t l in
    tm c t next
  else (t, c)

(* Functorialisation of a coherence: exposed function *)
let coh c l =
  try coh c l
  with FunctorialiseMeta ->
    Error.functorialisation
      ("coherence: " ^ Coh.to_string c)
      (Printf.sprintf "cannot functorialise meta-variables")

let coh_depth0 c l =
  try coh_depth0 c l
  with FunctorialiseMeta ->
    Error.functorialisation
      ("coherence: " ^ Coh.to_string c)
      (Printf.sprintf "cannot functorialise meta-variables")

let coh_successively c l =
  try coh_successively c l
  with FunctorialiseMeta ->
    Error.functorialisation
      ("coherence: " ^ Coh.to_string c)
      (Printf.sprintf "cannot functorialise meta-variables")

let rec sub s l =
  match s with
  | [] -> []
  | (x, t) :: s when not (List.mem x l) -> (x, t) :: sub s l
  | (x, t) :: s -> (
      match tm_one_step t l true with
      | [ (tm_f, _); (tgt_t, _); (src_t, _) ] ->
          (Var.Bridge x, tm_f) :: (Var.Plus x, tgt_t) :: (x, src_t) :: sub s l
      | [ (t, _) ] ->
          Io.debug "no functorialisation needed for %s" (Var.to_string x);
          (x, t) :: sub s l
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
let tm c t s =
  try tm c t s
  with FunctorialiseMeta ->
    Error.functorialisation
      ("term: " ^ Unchecked.tm_to_string t)
      (Printf.sprintf "cannot functorialise meta-variables")

let ps p l =
  let c = ctx (Unchecked.ps_to_ctx p) l in
  let _, names, _ = Unchecked.db_levels c in
  (PS.(forget (mk (Ctx.check c))), names)

let sub_w_tgt p s l =
  let s_f = sub_ps s l in
  let l = preimage (Unchecked.ps_to_ctx p) s l in
  let p_f, names = ps p l in
  (s_f, p_f, names, l)
