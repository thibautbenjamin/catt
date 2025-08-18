open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

type constr = tm * ty

let to_tm (tm, _) = tm
let to_ty (_, ty) = ty
let characteristic_sub_ps (tm, ty) = (tm, true) :: Unchecked.ty_to_sub_ps ty
let dim (_, ty) = Unchecked.dim_ty ty
let arr (tm1, ty1) (tm2, _) = Arr (ty1, tm1, tm2)

let rec bdry n (t, ty) =
  match (n, ty) with
  | 0, _ -> ((t, ty), (t, ty))
  | 1, Arr (b, s, t) -> ((s, b), (t, b))
  | _, Arr (b, s, _) -> bdry (n - 1) (s, b)
  | _, _ -> assert false

let coh_app coh sub =
  let _, ty, _ = Coh.forget coh in
  (Coh (coh, sub), Unchecked.ty_apply_sub_ps ty sub)

let of_coh coh =
  let ps, _, _ = Coh.forget coh in
  coh_app coh (Unchecked.identity_ps ps)

let tm_app tm sub =
  let ty = Tm.ty tm in
  (App (tm, sub), Unchecked.ty_apply_sub ty sub)

let src n t = fst (bdry n t)
let tgt n t = snd (bdry n t)
let wcomp = Functorialisation.wcomp
let () = Builtin.wcomp := wcomp

(* returns the n-composite of a (n+j)-cell with a (n+k)-cell *)
let whisk3 n j k l =
  let comp = Builtin.comp_n 3 in
  let func_data = [ (Var.Db 6, l); (Var.Db 4, k); (Var.Db 2, j) ] in
  let whisk = Functorialisation.coh_successively comp func_data in
  Suspension.checked_tm (Some n) whisk

let whisk3_sub_ps k t1 ty1 t2 ty2 l t3 ty3 =
  let rec take n l =
    match l with h :: t when n > 0 -> h :: take (n - 1) t | _ -> []
  in
  let sub_base = Unchecked.ty_to_sub_ps ty1 in
  let sub_ext1 = take ((2 * k) + 1) (Unchecked.ty_to_sub_ps ty2) in
  let sub_ext2 = take ((2 * l) + 1) (Unchecked.ty_to_sub_ps ty3) in
  List.concat
    [
      [ (t3, true) ];
      sub_ext2;
      [ (t2, true) ];
      sub_ext1;
      [ (t1, true) ];
      sub_base;
    ]

let wcomp3 (f, fty) n (g, gty) m (h, hty) =
  let j = Unchecked.dim_ty fty - n - 1 in
  let k = Unchecked.dim_ty gty - n - 1 in
  let l = Unchecked.dim_ty hty - m - 1 in
  let whisk = whisk3 n j k l in
  let whisk_sub_ps = whisk3_sub_ps k f fty g gty l h hty in
  let whisk_sub = Unchecked.sub_ps_to_sub whisk_sub_ps in
  (App (whisk, whisk_sub), Unchecked.ty_apply_sub_ps (Tm.ty whisk) whisk_sub_ps)

let intch_comp_nm a b c =
  let n = Unchecked.dim_ty (snd a) in
  let m = Unchecked.dim_ty (snd c) in
  let sub_left =
    (fst b, true)
    :: (fst (tgt 1 b), false)
    :: (fst a, true)
    :: Unchecked.ty_to_sub_ps (snd a)
  in
  let sub_right =
    (fst c, true) :: Common.take m (Unchecked.ty_to_sub_ps (snd c))
  in
  let coh = Builtin.intch_comp_nm_coh n m in
  let sub = sub_right @ sub_left in
  let _, ty, _ = Coh.forget coh in
  (Coh (coh, sub), Unchecked.ty_apply_sub_ps ty sub)

let intch_comp_mn a b c =
  let m = Unchecked.dim_ty (snd a) in
  let n = Unchecked.dim_ty (snd b) in
  let sub_left = (fst a, true) :: Unchecked.ty_to_sub_ps (snd a) in
  let sub_right =
    (fst c, true)
    :: (fst (tgt 1 c), false)
    :: (fst b, true)
    :: Common.take ((2 * n) - (2 * m) + 1) (Unchecked.ty_to_sub_ps (snd b))
  in
  let coh = Builtin.intch_comp_nm_coh n m in
  let coh = Opposite.coh coh [ 1 ] in
  let sub = sub_right @ sub_left in
  let _, ty, _ = Coh.forget coh in
  (Coh (coh, sub), Unchecked.ty_apply_sub_ps ty sub)

let opposite (t, ty) op_data = (Opposite.tm t op_data, Opposite.ty ty op_data)
let inv (t, ty) = (Inverse.compute_inverse t, Inverse.ty ty)

let id constr =
  let d = dim constr in
  ( Coh (Suspension.coh (Some d) (Builtin.id ()), characteristic_sub_ps constr),
    arr constr constr )

let rec id_n n constr =
  match n with 0 -> constr | n -> id (id_n (n - 1) constr)

let apply_sub (tm, ty) sigma =
  (Unchecked.tm_apply_sub tm sigma, Unchecked.ty_apply_sub ty sigma)

let apply_sub_ps (tm, ty) sigma =
  (Unchecked.tm_apply_sub_ps tm sigma, Unchecked.ty_apply_sub_ps ty sigma)

let rename (tm, ty) sigma =
  (Unchecked.tm_rename tm sigma, Unchecked.ty_rename ty sigma)

let inverse (tm, ty) = (Inverse.compute_inverse tm, Inverse.ty ty)
let suspend i (tm, ty) = (Suspension.tm (Some i) tm, Suspension.ty (Some i) ty)

let functorialise (tm, ty) vars =
  (Functorialisation.tm_one_step_tm tm vars, Functorialisation.ty ty vars tm)

let comp_n constrs =
  let rec last = function
    | [] -> assert false
    | [ x ] -> x
    | _ :: tl -> last tl
  in
  let first = function [] -> assert false | h :: _ -> h in
  let rec glue_subs = function
    | [ c ] -> characteristic_sub_ps c
    | c :: constrs ->
        (to_tm c, true) :: (to_tm (tgt 1 c), false) :: glue_subs constrs
    | [] -> assert false
  in
  let l = List.length constrs in
  let c = first constrs in
  let d = dim c in
  ( Coh
      ( Suspension.coh (Some (d - 1)) (Builtin.comp_n l),
        glue_subs (List.rev constrs) ),
    arr (src 1 c) (tgt 1 (last constrs)) )

let comp3 c1 c2 c3 = comp_n [ c1; c2; c3 ]
let op dims (tm, ty) = (Opposite.tm tm dims, Opposite.ty ty dims)

let drop n xs =
  let rec aux xs counter =
    match xs with
    | [] -> []
    | h :: tl -> if counter > 0 then h :: aux tl (counter - 1) else []
  in
  aux xs (List.length xs - n)

let characteristic_sub_ps_composite constrs =
  let rec aux = function
    | [] -> assert false
    | [ constr ] -> characteristic_sub_ps constr
    | constr :: tail ->
        [ (to_tm constr, true); (to_tm @@ tgt 1 constr, false) ] @ aux tail
  in
  aux @@ List.rev constrs

let glue_subs_along k subs =
  let rec aux = function
    | [] -> assert false
    | [ sub ] -> sub
    | sub :: subs -> drop ((2 * k) + 1) sub @ aux subs
  in
  aux @@ List.rev subs

let rec whisk_n n dims =
  let l = List.length dims in
  let comp = Builtin.comp_n l in
  let func_data =
    List.rev
    @@ List.mapi (fun idx dim -> (Var.Db (2 * (idx + 1)), dim - 1)) dims
  in
  let whisk = Functorialisation.coh_successively comp func_data in
  Suspension.checked_tm (Some n) whisk

and wcomp_n k constrs =
  let dims_adjusted = List.map (fun c -> dim c - k) constrs in
  let whisk = whisk_n k dims_adjusted in
  let whisk_sub_ps =
    glue_subs_along k (List.map characteristic_sub_ps constrs)
  in
  let whisk_sub = Unchecked.sub_ps_to_sub whisk_sub_ps in
  (App (whisk, whisk_sub), Unchecked.ty_apply_sub_ps (Tm.ty whisk) whisk_sub_ps)

let witness constr =
  let tm = to_tm constr in
  let d = dim constr in
  let ty =
    arr (wcomp constr (d - 1) (inverse constr)) (id_n 1 (src 1 constr))
  in
  (Inverse.compute_witness tm, ty)
