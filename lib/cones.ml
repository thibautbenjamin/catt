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

(* Composition of two cones *)
let ctx_c, right_incl =
  Display_maps.pullback (ctx 2)
    [
      (Var.Db 2, (Var (Var.Plus (Var.Db 2)), false));
      (Var.Db 1, (Var (Var.Db 1), false));
      (Var.Db 0, (Var (Var.Plus (Var.Db 0)), false));
    ]
    (ctx 2)
    [ (Var.Db 2, Var.Db 2); (Var.Db 1, Var.Db 1); (Var.Db 0, Var.Db 0) ]

let left_base = Var (base 2)
let right_base = Unchecked.tm_apply_sub left_base right_incl
let left_filler = Var (filler 2)
let right_filler = Unchecked.tm_apply_sub left_filler right_incl

let compose =
  let with_type ctx t =
    match t with Var x -> (t, fst (List.assoc x ctx)) | _ -> assert false
  in
  let left_filler = with_type ctx_c left_filler in
  let right_filler = with_type ctx_c right_filler in
  let left_base = with_type ctx_c left_base in
  let right_base = with_type ctx_c right_base in
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
  check_term (Ctx.check ctx_c) ("builtin_conecomp(1,0)", 0, []) (fst tm)
