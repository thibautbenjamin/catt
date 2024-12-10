open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

(* Cone contexts *)
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
let bdry_left n = filler (n - 1)
let bdry_right n = Var.Plus (filler (n - 1))

(* Cone types *)
let ty n = fst (List.assoc (filler n) (ctx n))

let ty_src n =
  match ty n with Arr (_, s, _) -> s | Obj | Meta_ty _ -> assert false

let ty_tgt n =
  match ty n with Arr (_, _, t) -> t | Obj | Meta_ty _ -> assert false

(* Cone represented as a substitution from the cone context *)
let src n csub = Unchecked.tm_apply_sub (ty_src n) csub
let tgt n csub = Unchecked.tm_apply_sub (ty_tgt n) csub

(* Binary Composition of cones *)

module Codim1 = struct
  let tbl_comp_codim1 = Hashtbl.create 97

  let ctx n =
    let pick x ctx =
      let ty = fst (List.assoc x ctx) in
      let s = (Var x, true) :: Unchecked.ty_to_sub_ps ty in
      Unchecked.sub_ps_to_sub s
    in
    match n with
    | n when n <= 1 -> assert false
    | n -> (
        match Hashtbl.find_opt tbl_comp_codim1 n with
        | Some res -> res
        | None ->
            let ctx, right_incl =
              Display_maps.pullback (ctx n)
                (pick (bdry_right n) (ctx n))
                (ctx n)
                (pick (bdry_left n) (ctx n))
            in
            let res = (ctx, right_incl) in

            Hashtbl.add tbl_comp_codim1 n res;
            res)

  let left_base n = base n

  let right_base n =
    let _, right_incl = ctx n in
    match Unchecked.tm_apply_sub (Var (base n)) right_incl with
    | Var x -> x
    | _ -> assert false

  let left_filler n = filler n

  let right_filler n =
    let _, right_incl = ctx n in
    match Unchecked.tm_apply_sub (Var (filler n)) right_incl with
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
        (Unchecked.tm_apply_sub (Var (bdry_right 2)) right_incl, true);
        (Var (apex 2), false);
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

  let compose n =
    match n with
    | n when n <= 1 -> assert false
    | 2 -> compose_dim2 ()
    | _ -> assert false
end

let rec ctx_c n m k =
  match (n - k, m - k) with
  | i, j when i <= 0 || j <= 0 -> assert false
  | 1, 1 -> fst (Codim1.ctx n)
  | _, 1 ->
      Functorialisation.ctx
        (ctx_c (n - 1) m k)
        [ left_base (n - 1); left_filler (n - 1) ]
  | 1, _ ->
      Functorialisation.ctx
        (ctx_c n (m - 1) k)
        [ right_base 1 (m - 1) k; right_filler 1 (m - 1) k ]
  | _, _ ->
      Functorialisation.ctx
        (ctx_c (n - 1) (m - 1) k)
        [
          left_base (n - 1);
          left_filler (n - 1);
          right_base (n - 1) (m - 1) k;
          right_filler (n - 1) (m - 1) k;
        ]

and left_base n = base n

and right_base n m k =
  match (n - k, m - k) with
  | _, i when i <= 0 -> assert false
  | _, 1 -> Codim1.right_base m
  | _, _ -> Var.Bridge (right_base (n - 1) (m - 1) k)

and left_filler n =
  match n with
  | n when n <= 1 -> assert false
  | 2 -> filler 2
  | n -> Var.Bridge (left_filler (n - 1))

and right_filler n m k =
  match (n - k, m - k) with
  | _, i when i <= 0 -> assert false
  | _, 1 -> Codim1.right_filler m
  | _, _ -> Var.Bridge (right_filler (n - 1) (m - 1) k)

let tbl = Hashtbl.create 97

let rec compose n m k =
  match Hashtbl.find_opt tbl (n, m, k) with
  | Some res -> res
  | None ->
      let res =
        match (n - k, m - k) with
        | i, j when i <= 0 || j <= 0 -> assert false
        | 1, 1 -> Codim1.compose n
        | _, 1 ->
            Functorialisation.tm
              (compose (n - 1) m k)
              [ (left_base (n - 1), 1); (left_filler (n - 1), 1) ]
        | 1, _ ->
            Functorialisation.tm
              (compose n (m - 1) k)
              [ (right_base n (m - 1) k, 1); (right_filler n (m - 1) k, 1) ]
        | _, _ ->
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
