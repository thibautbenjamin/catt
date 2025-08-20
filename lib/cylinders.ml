open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

let wcomp = Construct.wcomp

(* Cylinder contexts *)
module Cylinder = struct
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
                [ (Var.Db 0, (Var (Var.Db 1), true)) ] )
          | n ->
              let ctx, lb, ub, f, _, _ = ctx (n - 1) in
              let id = Unchecked.identity ctx in
              let ctx = Functorialisation.ctx ctx [ lb; ub; f ] in
              let names = Unchecked.db_level_sub_inv ctx in
              let ctx, _, _ = Unchecked.db_levels ctx in
              let ctx = Opposite.ctx ctx [ n ] in
              let rename x = Display_maps.var_apply_sub x names in
              let src = Unchecked.sub_apply_sub id names in
              let tgt_predb =
                List.map
                  (fun (x, (y, e)) ->
                    match y with
                    | Var a when a = lb || a = ub || a = f ->
                        (x, (Var (Var.Plus a), e))
                    | _ -> (x, (y, e)))
                  id
              in
              let tgt = Unchecked.sub_apply_sub tgt_predb names in
              let lb = Var.Bridge lb in
              let ub = Var.Bridge ub in
              let f = Var.Bridge f in
              (ctx, rename lb, rename ub, rename f, src, tgt)
        in
        Hashtbl.add tbl n res;
        res

  let base_lower n =
    let _, b, _, _, _, _ = ctx n in
    b

  let filler n =
    let _, _, _, f, _, _ = ctx n in
    f

  let base_upper n =
    let _, _, b, _, _, _ = ctx n in
    b

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
    if n <= k then Unchecked.identity (ctx n)
    else if n = k + 1 then bdry_left_gen n
    else Unchecked.sub_apply_sub (bdry_left (n - 1) k) (bdry_left_gen n)

  let rec bdry_right n k =
    if n <= k then Unchecked.identity (ctx n)
    else if n = k + 1 then bdry_right_gen n
    else Unchecked.sub_apply_sub (bdry_right (n - 1) k) (bdry_right_gen n)
end

(* Cylinder inductive relation : a (n+1)-cylinder is a suspended n-cylinder up
   to an interchanger *)
module Induct : sig
  val ctx : int -> ctx
  val sub : int -> sub
end = struct
  (* The suspension opposite of a cone context *)
  let ctx n =
    let ctx = Suspension.ctx (Some 1) (Cylinder.ctx (n - 1)) in
    let ctx, _, _ = Unchecked.db_levels ctx in
    ctx

  (* substitution from the cylinder context to the suspension a cylinder.
     This function returns a horribly list, even though the target
     context is not a pasting scheme *)
  let fake_sub_ps_unsafe n =
    let ctx = Cylinder.ctx n in
    let with_type v = (Var v, fst (List.assoc v ctx)) in
    let lb k =
      Display_maps.var_apply_sub (Cylinder.base_lower k)
        (Cylinder.bdry_left n k)
    in
    let lbP k =
      Display_maps.var_apply_sub (Cylinder.base_lower k)
        (Cylinder.bdry_right n k)
    in
    let ub k =
      Display_maps.var_apply_sub (Cylinder.base_upper k)
        (Cylinder.bdry_left n k)
    in
    let ubP k =
      Display_maps.var_apply_sub (Cylinder.base_upper k)
        (Cylinder.bdry_right n k)
    in
    let f k =
      Display_maps.var_apply_sub (Cylinder.filler k) (Cylinder.bdry_left n k)
    in
    let fP k =
      Display_maps.var_apply_sub (Cylinder.filler k) (Cylinder.bdry_right n k)
    in
    let fP1 = with_type (fP 1) in
    let f1 = with_type (f 1) in
    let lb k = with_type (lb k) in
    let lbP k = with_type (lbP k) in
    let ub k = with_type (ub k) in
    let ubP k = with_type (ubP k) in
    List.concat
      [
        [ (Var (Cylinder.filler n), true) ];
        List.init
          (2 * (n - 2))
          (fun i ->
            let i = i + 2 in
            let v =
              if i mod 2 = 0 then fP (n - (i / 2)) else f (n - ((i - 1) / 2))
            in
            (Var v, false));
        [ (fst @@ wcomp f1 0 (ub n), false) ];
        List.init
          (2 * (n - 2))
          (fun i ->
            let i = i + 2 in
            let v =
              if i mod 2 = 0 then ubP (n - (i / 2)) else ub (n - ((i - 1) / 2))
            in
            (fst @@ wcomp f1 0 v, false));
        [ (fst @@ wcomp (lb n) 0 fP1, false) ];
        List.init
          (2 * (n - 2))
          (fun i ->
            let i = i + 2 in
            let v =
              if i mod 2 = 0 then lbP (n - (i / 2)) else lb (n - ((i - 1) / 2))
            in
            (fst @@ wcomp v 0 fP1, false));
        [ (fst @@ ubP 1, false); (fst @@ lb 1, false) ];
      ]

  let sub n = Unchecked.sub_ps_to_sub (fake_sub_ps_unsafe n)
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
            let ctx, right_incl =
              Display_maps.pullback (Cylinder.ctx n)
                (Cylinder.bdry_right n (n - 1))
                (Cylinder.ctx n)
                (Cylinder.bdry_left n (n - 1))
            in
            let names = Unchecked.db_level_sub_inv ctx in
            let ctx, _, _ = Unchecked.db_levels ctx in
            let right_incl = Unchecked.sub_apply_sub right_incl names in
            let res = (ctx, right_incl) in
            Hashtbl.add tbl_comp_codim1 n res;
            res)

  let right_incl n = snd @@ ctx n
  let ctx n = fst @@ ctx n
  let left_lbase n = Cylinder.base_lower n
  let left_ubase n = Cylinder.base_upper n
  let right_lbase n = Display_maps.var_apply_sub (left_lbase n) (right_incl n)
  let right_ubase n = Display_maps.var_apply_sub (left_ubase n) (right_incl n)
  let left_filler n = Cylinder.filler n
  let right_filler n = Display_maps.var_apply_sub (left_filler n) (right_incl n)

  let compose_dim2 () =
    let cubcomp =
      Functorialisation.coh (Builtin.comp_n 2)
        [ Var.Db 4; Var.Db 3; Var.Db 2; Var.Db 1; Var.Db 0 ]
    in
    let left_filler1 =
      Unchecked.tm_apply_sub (Var (Cylinder.filler 1)) (Cylinder.bdry_left 2 1)
    in
    let mid_filler1 =
      Unchecked.tm_apply_sub (Var (Cylinder.filler 1)) (Cylinder.bdry_right 2 1)
    in
    let right_filler1 = Unchecked.tm_apply_sub mid_filler1 (right_incl 2) in
    let left_lbase1 =
      Unchecked.tm_apply_sub (Var (Cylinder.filler 0)) (Cylinder.bdry_left 2 0)
    in
    let left_ubase1 =
      Unchecked.tm_apply_sub
        (Var (Cylinder.filler 0))
        (Unchecked.sub_apply_sub (Cylinder.bdry_right 1 0)
           (Cylinder.bdry_left 2 1))
    in
    let mid_lbase1 =
      Unchecked.tm_apply_sub
        (Var (Cylinder.filler 0))
        (Unchecked.sub_apply_sub (Cylinder.bdry_left 1 0)
           (Cylinder.bdry_right 2 1))
    in
    let mid_ubase1 =
      Unchecked.tm_apply_sub (Var (Cylinder.filler 0)) (Cylinder.bdry_right 2 0)
    in
    let right_lbase1 = Unchecked.tm_apply_sub mid_lbase1 (right_incl 2) in
    let right_ubase1 = Unchecked.tm_apply_sub mid_ubase1 (right_incl 2) in
    let sub_ps =
      [
        (Var (right_filler 2), true);
        (Var (right_ubase 2), false);
        (Var (right_lbase 2), false);
        (right_filler1, false);
        (right_ubase1, false);
        (right_lbase1, false);
        (Var (left_filler 2), true);
        (Var (left_ubase 2), false);
        (Var (left_lbase 2), false);
        (mid_filler1, false);
        (mid_ubase1, false);
        (mid_lbase1, false);
        (left_filler1, false);
        (left_ubase1, false);
        (left_lbase1, false);
      ]
    in
    let c = Tm.ctx cubcomp in
    let sub = List.map2 (fun (x, _) y -> (x, y)) c sub_ps in
    let tm = App (cubcomp, sub) in
    check_term (Ctx.check (ctx 2)) ~name:("cylcomp(2,1,2)", 0, []) tm

  let intch n =
    let with_type ctx x = (Var x, fst (List.assoc x ctx)) in
    let ctx_comp = ctx n in
    let f k =
      Display_maps.var_apply_sub (Cylinder.filler k) (Cylinder.bdry_left n k)
    in
    let fP k =
      Display_maps.var_apply_sub (Cylinder.filler k) (Cylinder.bdry_right n k)
    in
    let fP k = Display_maps.var_apply_sub (fP k) (right_incl n) in
    let llb = left_lbase n in
    let rlb = right_lbase n in
    let lub = left_ubase n in
    let rub = right_ubase n in
    let inner_intch_lower =
      Construct.(
        intch_comp_nm (with_type ctx_comp llb) (with_type ctx_comp rlb)
          (with_type ctx_comp (fP 1)))
    in
    let inner_intch_upper =
      Construct.(
        intch_comp_mn
          (with_type ctx_comp (f 1))
          (with_type ctx_comp lub) (with_type ctx_comp rub))
    in
    let inner_intch_upper = Construct.(inv inner_intch_upper) in
    let rec wrap_lower k =
      if k = 0 then inner_intch_lower
      else
        let f = with_type ctx_comp (fP (k + 1)) in
        wcomp (wrap_lower (k - 1)) k f
    in
    let rec wrap_upper k =
      if k = 0 then inner_intch_upper
      else
        let f = with_type ctx_comp (f (k + 1)) in
        wcomp f k (wrap_upper (k - 1))
    in
    (wrap_lower (n - 2), wrap_upper (n - 2))

  let rec compose n =
    match n with
    | n when n <= 1 -> assert false
    | 2 -> compose_dim2 ()
    | _ ->
        let right_incl_prev = right_incl (n - 1) in
        let ctx_comp = ctx n in
        let right_incl = right_incl n in
        let name = Printf.sprintf "builtin_cylcomp(%d,%d,%d)" n 1 n in
        let suspcomp =
          let comp = Suspension.checked_tm (Some 1) (compose (n - 1)) in
          let ind_sub = Induct.sub n in
          let sub =
            Display_maps.glue ind_sub
              (Unchecked.sub_apply_sub ind_sub right_incl)
              (Suspension.sub (Some 1) right_incl_prev)
              (Induct.ctx n)
              (Suspension.sub (Some 1) (Cylinder.bdry_left (n - 1) (n - 2)))
          in
          Io.debug "substitution:%s" (Unchecked.sub_to_string_debug sub);
          check_term (Ctx.check ctx_comp) ~name:(name, 0, []) (App (comp, sub))
        in
        let intch_lower, intch_upper = intch n in
        let scomp = (Tm.develop suspcomp, Tm.ty suspcomp) in
        let tm, _ =
          Construct.wcomp3 intch_lower (n - 1) scomp (n - 1) intch_upper
        in
        check_term (Ctx.check ctx_comp) ~name:(name, 0, []) tm
end

module Composition = struct
  let rec ctx n m k =
    if n > m then
      let ctx, llb, lub, lf, rlb, rub, rf = ctx (n - 1) m k in
      let ctx = Functorialisation.ctx ctx [ llb; lub; lf ] in
      let names = Unchecked.db_level_sub_inv ctx in
      let ctx, _, _ = Unchecked.db_levels ctx in
      let ctx = Opposite.ctx ctx [ n ] in
      let rename x = Display_maps.var_apply_sub x names in
      let llb = Var.Bridge llb in
      let lub = Var.Bridge lub in
      let lf = Var.Bridge lf in
      (ctx, rename llb, rename lub, rename lf, rename rlb, rename rub, rename rf)
    else if m > n then
      let ctx, llb, lub, lf, rlb, rub, rf = ctx n (m - 1) k in
      let ctx = Functorialisation.ctx ctx [ rlb; rub; rf ] in
      let names = Unchecked.db_level_sub_inv ctx in
      let ctx, _, _ = Unchecked.db_levels ctx in
      let ctx = Opposite.ctx ctx [ m ] in
      let rename x = Display_maps.var_apply_sub x names in
      let rlb = Var.Bridge rlb in
      let rub = Var.Bridge rub in
      let rf = Var.Bridge rf in
      (ctx, rename llb, rename lub, rename lf, rename rlb, rename rub, rename rf)
    else
      match n - k with
      | i when i <= 0 -> assert false
      | 1 ->
          let llb = Cylinder.base_lower n in
          let lub = Cylinder.base_upper n in
          let lf = Cylinder.filler n in
          let rlb =
            Display_maps.var_apply_sub (Cylinder.base_lower n)
              (Codim1.right_incl n)
          in
          let rub =
            Display_maps.var_apply_sub (Cylinder.base_upper n)
              (Codim1.right_incl n)
          in
          let rf =
            Display_maps.var_apply_sub (Cylinder.filler n) (Codim1.right_incl n)
          in
          (Codim1.ctx n, llb, lub, lf, rlb, rub, rf)
      | _ ->
          let ctx, llb, lub, lf, rlb, rub, rf = ctx (n - 1) (m - 1) k in
          let ctx = Functorialisation.ctx ctx [ llb; lub; lf; rlb; rub; rf ] in
          let names = Unchecked.db_level_sub_inv ctx in
          let ctx, _, _ = Unchecked.db_levels ctx in
          let rename x = Display_maps.var_apply_sub x names in
          let llb = Var.Bridge llb in
          let lub = Var.Bridge lub in
          let lf = Var.Bridge lf in
          let rlb = Var.Bridge rlb in
          let rub = Var.Bridge rub in
          let rf = Var.Bridge rf in
          ( ctx,
            rename llb,
            rename lub,
            rename lf,
            rename rlb,
            rename rub,
            rename rf )

  let left_base_lower n m k =
    let _, llb, _, _, _, _, _ = ctx n m k in
    llb

  let left_base_upper n m k =
    let _, _, lub, _, _, _, _ = ctx n m k in
    lub

  let right_base_lower n m k =
    let _, _, _, _, rlb, _, _ = ctx n m k in
    rlb

  let right_base_upper n m k =
    let _, _, _, _, _, rub, _ = ctx n m k in
    rub

  let left_filler n m k =
    let _, _, _, lf, _, _, _ = ctx n m k in
    lf

  let right_filler n m k =
    let _, _, _, _, _, _, rf = ctx n m k in
    rf

  let tbl = Hashtbl.create 97

  let rec compose n m k =
    match Hashtbl.find_opt tbl (n, m, k) with
    | Some res -> res
    | None ->
        let tm =
          if n > m then
            Opposite.checked_tm
              (Functorialisation.tm
                 (compose (n - 1) m k)
                 [
                   (left_base_lower (n - 1) m k, 1);
                   (left_base_upper (n - 1) m k, 1);
                   (left_filler (n - 1) m k, 1);
                 ])
              [ n ]
          else if m > n then
            Opposite.checked_tm
              (Functorialisation.tm
                 (compose n (m - 1) k)
                 [
                   (right_base_lower n (m - 1) k, 1);
                   (right_base_upper n (m - 1) k, 1);
                   (right_filler n (m - 1) k, 1);
                 ])
              [ m ]
          else
            match n - k with
            | i when i <= 0 -> assert false
            | 1 -> Codim1.compose n
            | _ ->
                Opposite.checked_tm
                  (Functorialisation.tm
                     (compose (n - 1) (m - 1) k)
                     [
                       (left_base_lower (n - 1) (m - 1) k, 1);
                       (left_base_upper (n - 1) (m - 1) k, 1);
                       (left_filler (n - 1) (m - 1) k, 1);
                       (right_base_lower (n - 1) (m - 1) k, 1);
                       (right_base_upper (n - 1) (m - 1) k, 1);
                       (right_filler (n - 1) (m - 1) k, 1);
                     ])
                  [ n ]
        in
        let ctx = Tm.ctx tm in
        let names = Unchecked.db_level_sub_inv ctx in
        let ctx, _, _ = Unchecked.db_levels ctx in
        let tm = Unchecked.tm_apply_sub (Tm.develop tm) names in
        let name = Printf.sprintf "builtin_conecomp(%d,%d,%d)" n k m in
        let res = check_term (Ctx.check ctx) ~name:(name, 0, []) tm in
        Hashtbl.add tbl (n, m, k) res;
        res
end

let compose = Composition.compose

module Stacking = struct
  let tbl_stacking_ctx = Hashtbl.create 97
  let tbl_stacking_tm = Hashtbl.create 97

  let rec ctx n =
    let res =
      match n with
      | n when n <= 1 -> assert false
      | n when n = 2 ->
          let ctx = Cylinder.ctx 2 in
          let base_lower = Cylinder.base_lower 2 in
          let base_upper = Cylinder.base_upper 2 in
          let char v =
            Unchecked.sub_ps_to_sub
              ((Var v, true) :: Unchecked.ty_to_sub_ps (fst (List.assoc v ctx)))
          in
          let ctx, upper_incl =
            Display_maps.pullback (Cylinder.ctx 2) (char base_upper)
              (Cylinder.ctx 2) (char base_lower)
          in
          let names = Unchecked.db_level_sub_inv ctx in
          let ctx, _, _ = Unchecked.db_levels ctx in
          let upper_incl = Unchecked.sub_apply_sub upper_incl names in
          (ctx, upper_incl)
      | n ->
          let ctx, upper_incl = ctx (n - 1) in
          let lb = Cylinder.base_lower (n - 1) in
          let mb = Cylinder.base_upper (n - 1) in
          let ub = Display_maps.var_apply_sub mb upper_incl in
          let lf = Cylinder.filler (n - 1) in
          let uf = Display_maps.var_apply_sub lf upper_incl in
          let var_fun = [ lb; mb; lf; ub; uf ] in
          let ctx = Functorialisation.ctx ctx var_fun in
          let ctx = Opposite.ctx ctx [ n ] in
          let upper_incl = Functorialisation.sub upper_incl var_fun in
          let upper_incl = Opposite.sub upper_incl [ n ] in
          let names = Unchecked.db_level_sub_inv ctx in
          let ctx, _, _ = Unchecked.db_levels ctx in
          let upper_incl = Unchecked.sub_apply_sub upper_incl names in
          let upper_incl =
            Unchecked.(sub_ps_to_sub (sub_to_sub_ps upper_incl))
          in
          (ctx, upper_incl)
    in
    Hashtbl.add tbl_stacking_ctx n res;
    res

  let rec stacking n =
    let res =
      match n with
      | n when n <= 1 -> assert false
      | n when n = 2 ->
          let ctx, upper_incl = ctx 2 in
          let tm =
            Functorialisation.coh (Builtin.comp_n 2)
              [ Var.Db 4; Var.Db 3; Var.Db 2; Var.Db 1; Var.Db 0 ]
          in
          let tm = Opposite.checked_tm tm [ 2 ] in
          let left_filler1_down =
            Unchecked.tm_apply_sub
              (Var (Cylinder.filler 1))
              (Cylinder.bdry_left 2 1)
          in
          let right_filler1_down =
            Unchecked.tm_apply_sub
              (Var (Cylinder.filler 1))
              (Cylinder.bdry_right 2 1)
          in
          let left_filler1_up =
            Unchecked.tm_apply_sub left_filler1_down upper_incl
          in
          let right_filler1_up =
            Unchecked.tm_apply_sub right_filler1_down upper_incl
          in
          let lower_base1_down =
            Unchecked.tm_apply_sub
              (Var (Cylinder.filler 0))
              (Cylinder.bdry_left 2 0)
          in
          let lower_base1_mid =
            Unchecked.tm_apply_sub
              (Var (Cylinder.filler 0))
              (Unchecked.sub_apply_sub (Cylinder.bdry_right 1 0)
                 (Cylinder.bdry_left 2 1))
          in
          let upper_base1_down =
            Unchecked.tm_apply_sub
              (Var (Cylinder.filler 0))
              (Unchecked.sub_apply_sub (Cylinder.bdry_left 1 0)
                 (Cylinder.bdry_right 2 1))
          in
          let upper_base1_mid =
            Unchecked.tm_apply_sub
              (Var (Cylinder.filler 0))
              (Cylinder.bdry_right 2 0)
          in
          let lower_base1_up =
            Unchecked.tm_apply_sub lower_base1_mid upper_incl
          in
          let upper_base1_up =
            Unchecked.tm_apply_sub upper_base1_mid upper_incl
          in
          let base2_down = Var (Cylinder.base_lower 2) in
          let base2_mid = Var (Cylinder.base_upper 2) in
          let base2_up = Unchecked.tm_apply_sub base2_mid upper_incl in
          let filler2_down = Var (Cylinder.filler 2) in
          let filler2_up = Unchecked.tm_apply_sub filler2_down upper_incl in
          let sub_ps =
            [
              (filler2_up, true);
              (right_filler1_up, false);
              (left_filler1_up, false);
              (base2_up, false);
              (upper_base1_up, false);
              (lower_base1_up, false);
              (filler2_down, true);
              (right_filler1_down, false);
              (left_filler1_down, false);
              (base2_mid, false);
              (upper_base1_mid, false);
              (lower_base1_mid, false);
              (base2_down, false);
              (upper_base1_down, false);
              (lower_base1_down, false);
            ]
          in
          let c = Tm.ctx tm in
          let sub = List.map2 (fun (x, _) y -> (x, y)) c sub_ps in
          check_term (Ctx.check ctx)
            ~name:("builtin_cylstack", 0, [])
            (App (tm, sub))
      | n ->
          let _, upper_incl = ctx (n - 1) in
          let lb = Cylinder.base_lower (n - 1) in
          let mb = Cylinder.base_upper (n - 1) in
          let ub = Display_maps.var_apply_sub mb upper_incl in
          let lf = Cylinder.filler (n - 1) in
          let uf = Display_maps.var_apply_sub lf upper_incl in
          let tm = stacking (n - 1) in
          let var_fun = [ (lb, 1); (mb, 1); (lf, 1); (ub, 1); (uf, 1) ] in
          let tm = Functorialisation.tm tm var_fun in
          let tm = Opposite.checked_tm tm [ n ] in
          tm
    in
    Hashtbl.add tbl_stacking_tm n res;
    res
end

let stacking = Stacking.stacking
