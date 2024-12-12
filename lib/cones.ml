open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

let wcomp = Functorialisation.wcomp

let rename x names =
  match Unchecked.tm_apply_sub (Var x) names with
  | Var a -> a
  | _ -> assert false

(* Cone contexts *)
module Cone = struct
  let tbl = Hashtbl.create 97

  let rec ctx n =
    match Hashtbl.find_opt tbl n with
    | Some res -> res
    | None ->
        let res =
          match n with
          | n when n <= 0 ->
              ( Unchecked.ps_to_ctx (Br []),
                Var.Db 0,
                Var.Db 0,
                Var.Db 0,
                [ (Var.Db 0, (Var (Var.Db 0), true)) ],
                [ (Var.Db 0, (Var (Var.Db 0), true)) ] )
          | 1 ->
              ( Unchecked.ps_to_ctx (Br [ Br [] ]),
                Var.Db 0,
                Var.Db 1,
                Var.Db 2,
                [ (Var.Db 0, (Var (Var.Db 0), true)) ],
                [ (Var.Db 0, (Var (Var.Db 0), true)) ] )
          | n ->
              let ctx, b, a, f, _, _ = ctx (n - 1) in
              let id = Unchecked.identity ctx in
              let ctx = Functorialisation.ctx ctx [ b; f ] in
              let names = Unchecked.db_level_sub_inv ctx in
              let ctx, _, _ = Unchecked.db_levels ctx in
              let rename x = rename x names in
              let src = Unchecked.sub_apply_sub id names in
              let tgt_predb =
                List.map
                  (fun (x, (y, e)) ->
                    match y with
                    | Var a when a = b || a = f -> (x, (Var (Var.Plus a), e))
                    | _ -> (x, (y, e)))
                  id
              in
              let tgt = Unchecked.sub_apply_sub tgt_predb names in
              let b = Var.Bridge b in
              let f = Var.Bridge f in
              (ctx, rename b, rename a, rename f, src, tgt)
        in
        Hashtbl.add tbl n res;
        res

  let base n =
    let _, b, _, _, _, _ = ctx n in
    b

  let filler n =
    let _, _, _, f, _, _ = ctx n in
    f

  let apex n =
    let _, _, a, _, _, _ = ctx n in
    a

  let bdry_left_gen n =
    let _, _, _, _, bdry, _ = ctx n in
    bdry

  let bdry_right_gen n =
    let _, _, _, _, _, bdry = ctx n in
    bdry

  let ctx n =
    let ctx, _, _, _, _, _ = ctx n in
    ctx

  let rec bdry_left n k =
    if n = k + 1 then bdry_left_gen n
    else Unchecked.sub_apply_sub (bdry_left (n - 1) k) (bdry_left_gen n)

  let rec bdry_right n k =
    if n = k + 1 then bdry_right_gen n
    else Unchecked.sub_apply_sub (bdry_right (n - 1) k) (bdry_right_gen n)

  (* Cone types *)
  let ty n = fst (List.assoc (filler n) (ctx n))

  let ty_src n =
    match ty n with Arr (_, s, _) -> s | Obj | Meta_ty _ -> assert false

  let ty_tgt n =
    match ty n with Arr (_, _, t) -> t | Obj | Meta_ty _ -> assert false
end

(* Cone inductive relation : a (n+1)-cone is a suspended opposite of a n-cone *)
(* module Induct : sig *)
(*   val ctx : int -> ctx *)
(*   val sub : int -> sub *)
(* end = struct *)
(*   (\* The suspension opposite of a cone context *\) *)
(*   let ctx n = *)
(*     let op_data = List.init (n - 1) (fun i -> i + 1) in *)
(*     Suspension.ctx (Some 1) (Opposite.ctx (Cone.ctx (n - 1)) op_data) *)

(*   (\* substitution from the cone context to the suspension opposite of a cone. *)
(*      This function returns a horribly hardcoded list, even though the target *)
(*      context is not a pasting scheme *\) *)
(*   let fake_sub_ps_unsafe n = *)
(*     let ctx = Cone.ctx n in *)
(*     let with_type v = (Var v, fst (List.assoc v ctx)) in *)
(*     let b n = with_type (Cone.base n) in *)
(*     let fP1 = with_type (Var.Plus (Cone.filler 1)) in *)
(*     let bP n = with_type (Var.Plus (Cone.base n)) in *)
(*     List.concat *)
(*       [ *)
(*         [ (Var (Cone.filler n), true) ]; *)
(*         List.init *)
(*           (2 * (n - 2)) *)
(*           (fun i -> *)
(*             let i = i + 2 in *)
(*             let f = *)
(*               if i mod 2 = 0 then Cone.filler (n - (i / 2)) *)
(*               else Var.Plus (Cone.filler (n - ((i - 1) / 2))) *)
(*             in *)
(*             (Var f, false)); *)
(*         [ (Var (Cone.filler 1), false); (fst @@ wcomp (b n) 0 fP1, false) ]; *)
(*         List.init *)
(*           (2 * (n - 2)) *)
(*           (fun i -> *)
(*             let i = i + 2 in *)
(*             let b = *)
(*               if i mod 2 = 0 then b (n - (i / 2)) else bP (n - ((i - 1) / 2)) *)
(*             in *)
(*             (fst @@ wcomp b 0 fP1, false)); *)
(*         [ (Var (Cone.apex 1), false); (Var (Cone.base 1), false) ]; *)
(*       ] *)

(*   let sub n = *)
(*     let list = fake_sub_ps_unsafe n in *)
(*     List.map2 (fun (x, _) t -> (x, t)) (ctx n) list *)
(* end *)

(* Binary Composition of cones *)

module Codim1 = struct
  let tbl_comp_codim1 = Hashtbl.create 97

  let ctx n =
    match n with
    | n when n <= 1 -> assert false
    | n -> (
        match Hashtbl.find_opt tbl_comp_codim1 n with
        | Some res -> res
        | None ->
            let ctx, right_incl =
              Display_maps.pullback (Cone.ctx n)
                (Cone.bdry_right n (n - 1))
                (Cone.ctx n)
                (Cone.bdry_left n (n - 1))
            in
            let res = (ctx, right_incl) in

            Hashtbl.add tbl_comp_codim1 n res;
            res)

  let left_base n = Cone.base n

  let right_base n =
    let _, right_incl = ctx n in
    match Unchecked.tm_apply_sub (Var (Cone.base n)) right_incl with
    | Var x -> x
    | _ -> assert false

  let left_filler n = Cone.filler n

  let right_filler n =
    let _, right_incl = ctx n in
    match Unchecked.tm_apply_sub (Var (Cone.filler n)) right_incl with
    | Var x -> x
    | _ -> assert false

  let compose_dim2 () =
    let with_type ctx x = (Var x, fst (List.assoc x ctx)) in
    let ctx, right_incl = ctx 2 in
    let left_filler = with_type ctx (left_filler 2) in
    let right_filler = with_type ctx (right_filler 2) in
    let left_base = with_type ctx (left_base 2) in
    let right_base = with_type ctx (right_base 2) in
    let tm_1 =
      Functorialisation.wcomp left_filler 1
        (Functorialisation.wcomp left_base 0 right_filler)
    in
    let leftmost_pt, midpoint =
      match snd left_base with Arr (_, s, t) -> (s, t) | _ -> assert false
    in
    let rightmost_pt =
      match snd right_base with Arr (_, _, t) -> t | _ -> assert false
    in
    let sub_ps =
      [
        (Unchecked.tm_apply_sub (Var (Var.Db 5)) right_incl, true);
        (Var (Cone.apex 2), false);
        (fst right_base, true);
        (rightmost_pt, false);
        (fst left_base, true);
        (midpoint, false);
        (leftmost_pt, false);
      ]
    in
    let assoc = Builtin.assoc in
    let _, assoc_ty, _ = Coh.forget assoc in
    let tm_2 =
      ( Coh (Builtin.assoc, sub_ps),
        Unchecked.ty_apply_sub assoc_ty (Unchecked.sub_ps_to_sub sub_ps) )
    in
    let tm, _ = Functorialisation.wcomp tm_1 1 tm_2 in
    let names = Unchecked.db_level_sub_inv ctx in
    let ctx, _, _ = Unchecked.db_levels ctx in
    let tm = Unchecked.tm_apply_sub tm names in
    check_term (Ctx.check ctx) ("builtin_conecomp", 0, []) tm

  let intch n =
    let with_type ctx x = (Var x, fst (List.assoc x ctx)) in
    let ctx_comp = fst @@ ctx n in
    let lb = left_base n in
    let rb = right_base n in
    let rec wrap n =
      if n = 0 then
        Builtin.intch_comp_nm (with_type ctx_comp lb) (with_type ctx_comp rb)
          (with_type ctx_comp (Var.Plus (Cone.filler 1)))
      else if n mod 2 <> 0 then
        let f = with_type ctx_comp (Cone.filler (n + 1)) in
        wcomp f n (wrap (n - 1))
      else
        let f = with_type ctx_comp (Var.Plus (Cone.filler (n + 1))) in
        wcomp (wrap (n - 1)) n f
    in
    wrap (n - 2)

  let compose n =
    match n with
    | n when n <= 1 -> assert false
    | 2 -> compose_dim2 ()
    | _ -> assert false
  (* let ctx_comp, right_incl = ctx n in *)
  (* let suspopcomp = *)
  (*   let op_data = List.init (n - 1) (fun i -> i + 1) in *)
  (*   let comp = *)
  (*     Suspension.checked_tm (Some 1) *)
  (*       (Opposite.checked_tm (compose (n - 1)) op_data) *)
  (*   in *)
  (*   let _, right_incl_prev = ctx (n - 1) in *)
  (*   let ind_sub = Induct.sub n in *)
  (*   let sub = *)
  (*     if n mod 2 = 0 then *)
  (*       Display_maps.glue ind_sub *)
  (*         (Unchecked.sub_apply_sub ind_sub right_incl) *)
  (*         (Suspension.sub (Some 1) (Opposite.sub right_incl_prev op_data)) *)
  (*         (Induct.ctx n) *)
  (*         (Suspension.sub (Some 1) *)
  (*            (Opposite.sub (Cone.bdry_left (n - 2)) op_data)) *)
  (*     else *)
  (*       Display_maps.glue *)
  (*         (Unchecked.sub_apply_sub ind_sub right_incl) *)
  (*         ind_sub *)
  (*         (Suspension.sub (Some 1) (Opposite.sub right_incl_prev op_data)) *)
  (*         (Induct.ctx n) *)
  (*         (Suspension.sub (Some 1) *)
  (*            (Opposite.sub (Cone.bdry_left (n - 2)) op_data)) *)
  (*   in *)
  (*   Io.debug "target context is %s" *)
  (*     (Unchecked.ctx_to_string (Tm.ctx comp)); *)
  (*   Io.debug "generated substitution: %s" *)
  (*     (Unchecked.sub_to_string_debug sub); *)
  (*   Io.debug "bictx: %s" (Unchecked.ctx_to_string ctx_comp); *)
  (*   check_term (Ctx.check ctx_comp) *)
  (*     ("builtin_conecomp", 0, []) *)
  (*     (App (comp, sub)) *)
  (* in *)
  (* Io.debug "building intch"; *)
  (* let intch = intch n in *)
  (* let socomp = (Tm.develop suspopcomp, Tm.ty suspopcomp) in *)
  (* check_term (Ctx.check ctx_comp) *)
  (*   ("builtin_conecomp", 0, []) *)
  (*   (fst (wcomp intch (n - 1) socomp)) *)
end

module Composition = struct
  let rec ctx n m k =
    if n > m then
      let ctx, lb, lf, rb, rf = ctx (n - 1) m k in
      let ctx = Functorialisation.ctx ctx [ lb; lf ] in
      let names = Unchecked.db_level_sub_inv ctx in
      let ctx, _, _ = Unchecked.db_levels ctx in
      let rename x = rename x names in
      let lb = Var.Bridge lb in
      let lf = Var.Bridge lf in
      (ctx, rename lb, rename lf, rename rb, rename rf)
    else if m > n then
      let ctx, lb, lf, rb, rf = ctx n (m - 1) k in
      let ctx = Functorialisation.ctx ctx [ rb; rf ] in
      let names = Unchecked.db_level_sub_inv ctx in
      let ctx, _, _ = Unchecked.db_levels ctx in
      let rename x = rename x names in
      let rb = Var.Bridge rb in
      let rf = Var.Bridge rf in
      (ctx, rename lb, rename lf, rename rb, rename rf)
    else
      match n - k with
      | i when i <= 0 -> assert false
      | 1 -> (fst @@ Codim1.ctx n, Var.Db 2, Var.Db 6, Var.Db 8, Var.Db 10)
      | _ ->
          let ctx, lb, lf, rb, rf = ctx (n - 1) (m - 1) k in
          let ctx = Functorialisation.ctx ctx [ lb; lf; rb; rf ] in
          let names = Unchecked.db_level_sub_inv ctx in
          let ctx, _, _ = Unchecked.db_levels ctx in
          let rename x = rename x names in
          let lb = Var.Bridge lb in
          let lf = Var.Bridge lf in
          let rb = Var.Bridge rb in
          let rf = Var.Bridge rf in
          (ctx, rename lb, rename lf, rename rb, rename rf)

  let left_base n m k =
    let _, lb, _, _, _ = ctx n m k in
    lb

  let right_base n m k =
    let _, _, _, rb, _ = ctx n m k in
    rb

  let left_filler n m k =
    let _, _, lf, _, _ = ctx n m k in
    lf

  let right_filler n m k =
    let _, _, _, _, rf = ctx n m k in
    rf

  let tbl = Hashtbl.create 97

  let rec compose n m k =
    match Hashtbl.find_opt tbl (n, m, k) with
    | Some res -> res
    | None ->
        let res =
          if n > m then
            Functorialisation.tm
              (compose (n - 1) m k)
              [ (left_base (n - 1) m k, 1); (left_filler (n - 1) m k, 1) ]
          else if m > n then
            Functorialisation.tm
              (compose n (m - 1) k)
              [ (right_base n (m - 1) k, 1); (right_filler n (m - 1) k, 1) ]
          else
            match n - k with
            | i when i <= 0 -> assert false
            | 1 -> Codim1.compose n
            | _ ->
                Functorialisation.tm
                  (compose (n - 1) (m - 1) k)
                  [
                    (left_base (n - 1) (m - 1) k, 1);
                    (left_filler (n - 1) (m - 1) k, 1);
                    (right_base (n - 1) (m - 1) k, 1);
                    (right_filler (n - 1) (m - 1) k, 1);
                  ]
        in
        let ctx = Tm.ctx res in
        let names = Unchecked.db_level_sub_inv ctx in
        let ctx, _, _ = Unchecked.db_levels ctx in
        let res = Unchecked.tm_apply_sub (Tm.develop res) names in
        let res = check_term (Ctx.check ctx) ("builtin_conecomp", 0, []) res in
        Hashtbl.add tbl (n, m, k) res;
        res
end
