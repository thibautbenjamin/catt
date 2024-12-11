open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

let wcomp = Functorialisation.wcomp

(* Cone contexts *)
module Cone = struct
  let rec ctx n =
    match n with
    | n when n <= 0 -> Unchecked.ps_to_ctx (Br [])
    | 1 -> Unchecked.ps_to_ctx (Br [ Br [] ])
    | n -> Functorialisation.ctx (ctx (n - 1)) [ base (n - 1); filler (n - 1) ]

  and base n =
    match n with
    | n when n <= 0 -> assert false
    | 1 -> Var.Db 0
    | n -> Var.Bridge (base (n - 1))

  and filler n =
    match n with
    | n when n <= 0 -> Var.Db 0
    | 1 -> Var.Db 2
    | n -> Var.Bridge (filler (n - 1))

  let apex n = match n with n when n <= 0 -> Var.Db 0 | _ -> Var.Db 1

  let rec frame_base n =
    match n with
    | n when n <= 0 -> []
    | n ->
        (Var.Plus (base n), (Var (Var.Plus (base n)), false))
        :: (base n, (Var (base n), false))
        :: frame_base (n - 1)

  let rec frame_filler n =
    match n with
    | n when n <= 0 -> []
    | n ->
        (Var.Plus (filler n), (Var (Var.Plus (filler n)), false))
        :: (filler n, (Var (filler n), false))
        :: frame_filler (n - 1)

  let bdry_left n =
    List.concat
      [
        [ (filler n, (Var (filler n), true)) ];
        frame_filler (n - 1);
        [ (apex n, (Var (apex n), false)) ];
        [ (base n, (Var (base n), true)) ];
        frame_base (n - 1);
      ]

  let bdry_right n =
    List.concat
      [
        [ (filler n, (Var (Var.Plus (filler n)), true)) ];
        frame_filler (n - 1);
        [ (apex n, (Var (apex n), false)) ];
        [ (base n, (Var (Var.Plus (base n)), true)) ];
        frame_base (n - 1);
      ]

  (* Cone types *)
  let ty n = fst (List.assoc (filler n) (ctx n))

  let ty_src n =
    match ty n with Arr (_, s, _) -> s | Obj | Meta_ty _ -> assert false

  let ty_tgt n =
    match ty n with Arr (_, _, t) -> t | Obj | Meta_ty _ -> assert false
end

(* Cone inductive relation : a (n+1)-cone is a suspended opposite of a n-cone *)
module Induct : sig
  val ctx : int -> ctx
  val sub : int -> sub
end = struct
  (* The suspension opposite of a cone context *)
  let ctx n =
    let op_data = List.init (n - 1) (fun i -> i + 1) in
    Suspension.ctx (Some 1) (Opposite.ctx (Cone.ctx (n - 1)) op_data)

  (* substitution from the cone context to the suspension opposite of a cone.
     This function returns a horribly hardcoded list, even though the target
     context is not a pasting scheme *)
  let fake_sub_ps_unsafe n =
    let ctx = Cone.ctx n in
    let with_type v = (Var v, fst (List.assoc v ctx)) in
    let b n = with_type (Cone.base n) in
    let fP1 = with_type (Var.Plus (Cone.filler 1)) in
    let bP n = with_type (Var.Plus (Cone.base n)) in
    List.concat
      [
        [ (Var (Cone.filler n), true) ];
        List.init
          (2 * (n - 2))
          (fun i ->
            let i = i + 2 in
            let f =
              if i mod 2 = 0 then Cone.filler (n - (i / 2))
              else Var.Plus (Cone.filler (n - ((i - 1) / 2)))
            in
            (Var f, false));
        [ (Var (Cone.filler 1), false); (fst @@ wcomp (b n) 0 fP1, false) ];
        List.init
          (2 * (n - 2))
          (fun i ->
            let i = i + 2 in
            let b =
              if i mod 2 = 0 then b (n - (i / 2)) else bP (n - ((i - 1) / 2))
            in
            (fst @@ wcomp b 0 fP1, false));
        [ (Var (Cone.apex 1), false); (Var (Cone.base 1), false) ];
      ]

  let sub n =
    let list = fake_sub_ps_unsafe n in
    List.map2 (fun (x, _) t -> (x, t)) (ctx n) list
end

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
            Io.debug "pullback of cones of dim %d" n;
            Io.debug "left boundary: %s"
              (Unchecked.sub_to_string_debug (Cone.bdry_left (n - 1)));
            let ctx, right_incl =
              Display_maps.pullback (Cone.ctx n)
                (Cone.bdry_right (n - 1))
                (Cone.ctx n)
                (Cone.bdry_left (n - 1))
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
        ( Unchecked.tm_apply_sub (Var (Var.Plus (Cone.filler 1))) right_incl,
          true );
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
    let tm = Functorialisation.wcomp tm_1 1 tm_2 in
    check_term (Ctx.check ctx) ("builtin_conecomp", 0, []) (fst tm)

  let rec compose n =
    match n with
    | n when n <= 1 -> assert false
    | 2 -> compose_dim2 ()
    | n ->
        let op_data = List.init (n - 1) (fun i -> i + 1) in
        let comp =
          Suspension.checked_tm (Some 1)
            (Opposite.checked_tm (compose (n - 1)) op_data)
        in
        let bictx, right_incl = ctx n in
        let _, right_incl_prev = ctx (n - 1) in
        let ind_sub = Induct.sub n in
        Io.debug "substitution1 : %s" (Unchecked.sub_to_string_debug ind_sub);
        Io.debug "bictx: %s" (Unchecked.ctx_to_string bictx);
        Io.debug "right_incl: %s" (Unchecked.sub_to_string_debug right_incl);
        Io.debug "substitution2: %s"
          (Unchecked.sub_to_string_debug
             (Unchecked.sub_apply_sub ind_sub right_incl));
        let sub =
          Display_maps.glue
            (Unchecked.sub_apply_sub ind_sub right_incl)
            ind_sub
            (Suspension.sub (Some 1) (Opposite.sub right_incl_prev op_data))
            (Induct.ctx n)
            (Suspension.sub (Some 1)
               (Opposite.sub (Cone.bdry_left (n - 2)) op_data))
        in
        Io.debug "computed substitution: %s" (Unchecked.sub_to_string_debug sub);
        check_term
          (Ctx.check (fst (ctx n)))
          ("builtin_conecomp", 0, [])
          (App (comp, sub))

  (* let right_base_d2 = Var.fresh () *)
  (* let right_base_bdry_d2 = Var.fresh () *)
  (* let right_filler_d2 = Var.fresh () *)
  (* let right_filler_bdry_d2 = Var.fresh () *)

  (* let rec ctx n = *)
  (*   match Hashtbl.find_opt tbl_comp_codim1 n with *)
  (*   | Some res -> res *)
  (*   | None -> *)
  (*       let res = *)
  (*         match n with *)
  (*         | n when n <= 1 -> assert false *)
  (*         | 2 -> *)
  (*             let rb = right_base_d2 in *)
  (*             let rb_bdry = right_base_bdry_d2 in *)
  (*             let rf = right_filler_d2 in *)
  (*             let rf_bdry = right_filler_bdry_d2 in *)
  (*             let ty_rb = *)
  (*               Arr (Obj, Var (Var.Plus (Cone.base 1)), Var rb_bdry) *)
  (*             in *)
  (*             let ty_rf_bdry = Arr (Obj, Var rb_bdry, Var (Cone.apex 2)) in *)
  (*             let ty_rf = *)
  (*               Arr *)
  (*                 ( Arr (Obj, Var (Var.Plus (Cone.base 1)), Var (Cone.apex 2)), *)
  (*                   Var (Var.Plus (Cone.filler 1)), *)
  (*                   fst (wcomp (Var rb, ty_rb) 0 (Var rf_bdry, ty_rf_bdry)) ) *)
  (*             in *)
  (*             (rf, (ty_rf, true)) *)
  (*             :: (rf_bdry, (ty_rf_bdry, false)) *)
  (*             :: (rb, (ty_rb, false)) *)
  (*             :: (rb_bdry, (Obj, false)) *)
  (*             :: Cone.ctx 2 *)
  (*         | n -> *)
  (*             Functorialisation.ctx *)
  (*               (ctx (n - 1)) *)
  (*               [ *)
  (*                 left_base (n - 1); *)
  (*                 right_base (n - 1); *)
  (*                 left_filler (n - 1); *)
  (*                 right_filler (n - 1); *)
  (*               ] *)
  (*       in *)
  (*       Hashtbl.add tbl_comp_codim1 n res; *)
  (*       res *)

  (* and left_base n = Cone.base n *)

  (* and right_base n = *)
  (*   if n = 2 then right_base_d2 else Var.Bridge (right_base (n - 1)) *)

  (* and left_filler n = Cone.filler n *)

  (* and right_filler n = *)
  (*   if n = 2 then right_filler_d2 else Var.Bridge (right_filler (n - 1)) *)

  (* let compose_dim2 () = *)
  (*   let with_type ctx x = (Var x, fst (List.assoc x ctx)) in *)
  (*   let ctx = ctx 2 in *)
  (*   let left_filler = with_type ctx (left_filler 2) in *)
  (*   let right_filler = with_type ctx (right_filler 2) in *)
  (*   let left_base = with_type ctx (left_base 2) in *)
  (*   let right_base = with_type ctx (right_base 2) in *)
  (*   let tm_1 = wcomp left_filler 1 (wcomp left_base 0 right_filler) in *)
  (*   let leftmost_pt, midpoint = *)
  (*     match snd left_base with Arr (_, s, t) -> (s, t) | _ -> assert false *)
  (*   in *)
  (*   let rightmost_pt = *)
  (*     match snd right_base with Arr (_, _, t) -> t | _ -> assert false *)
  (*   in *)
  (*   let sub_ps = *)
  (*     [ *)
  (*       (Var right_filler_bdry_d2, true); *)
  (*       (Var (Cone.apex 2), false); *)
  (*       (fst right_base, true); *)
  (*       (rightmost_pt, false); *)
  (*       (fst left_base, true); *)
  (*       (midpoint, false); *)
  (*       (leftmost_pt, false); *)
  (*     ] *)
  (*   in *)
  (*   let assoc = Builtin.assoc in *)
  (*   let _, assoc_ty, _ = Coh.forget assoc in *)
  (*   let tm_2 = *)
  (*     ( Coh (Builtin.assoc, sub_ps), *)
  (*       Unchecked.ty_apply_sub assoc_ty (Unchecked.sub_ps_to_sub sub_ps) ) *)
  (*   in *)
  (*   let tm = Functorialisation.wcomp tm_1 1 tm_2 in *)
  (*   check_term (Ctx.check ctx) ("builtin_conecomp", 0, []) (fst tm) *)

  (* let compose n = *)
  (*   match n with *)
  (*   | n when n <= 1 -> assert false *)
  (*   | 2 -> compose_dim2 () *)
  (*   | _ -> assert false *)
end

let rec ctx_c n m k =
  if n > m then
    Functorialisation.ctx
      (ctx_c (n - 1) m k)
      [ left_base (n - 1); left_filler (n - 1) ]
  else if m > n then
    Functorialisation.ctx
      (ctx_c n (m - 1) k)
      [ right_base n (m - 1) k; right_filler n (m - 1) k ]
  else
    match n - k with
    | i when i <= 0 -> assert false
    | 1 -> fst @@ Codim1.ctx n
    | _ ->
        Functorialisation.ctx
          (ctx_c (n - 1) (m - 1) k)
          [
            left_base (n - 1);
            left_filler (n - 1);
            right_base (n - 1) (m - 1) k;
            right_filler (n - 1) (m - 1) k;
          ]

and left_base n = Cone.base n

and right_base n m k =
  if n > m then right_base (n - 1) m k
  else if m > n then Var.Bridge (right_base n (m - 1) k)
  else
    match n - k with
    | i when i <= 0 -> assert false
    | 1 -> Codim1.right_base m
    | _ -> Var.Bridge (right_base (n - 1) (m - 1) k)

and left_filler n = Cone.filler n

and right_filler n m k =
  if n > m then right_filler (n - 1) m k
  else if m > n then Var.Bridge (right_filler n (m - 1) k)
  else
    match n - k with
    | i when i <= 0 -> assert false
    | 1 -> Codim1.right_filler m
    | _ -> Var.Bridge (right_filler (n - 1) (m - 1) k)

let tbl = Hashtbl.create 97

let rec compose n m k =
  match Hashtbl.find_opt tbl (n, m, k) with
  | Some res -> res
  | None ->
      let res =
        if n > m then
          Functorialisation.tm
            (compose (n - 1) m k)
            [ (left_base (n - 1), 1); (left_filler (n - 1), 1) ]
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
                  (left_base (n - 1), 1);
                  (left_filler (n - 1), 1);
                  (right_base (n - 1) (m - 1) k, 1);
                  (right_filler (n - 1) (m - 1) k, 1);
                ]
      in
      Hashtbl.add tbl (n, m, k) res;
      res
