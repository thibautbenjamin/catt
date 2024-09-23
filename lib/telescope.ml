open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh)

(* returns the associator pairing up the middle two cells of a composite of
    (2*k) 1-cells. The argument is the integer k *)
let middle_associator k =
  let ps = Builtin.ps_comp (2 * k) in
  let src = Coh (Builtin.comp_n (2 * k), Unchecked.(identity_ps ps)) in
  let tgt =
    let sub_assoc_middle =
      let rec compute_sub i =
        match i with
        | i when i <= 0 -> [ (Var (Db 0), false) ]
        | i when i < k ->
            (Var (Db (2 * i)), true)
            :: (Var (Db ((2 * i) - 1)), false)
            :: compute_sub (i - 1)
        | i when i = k ->
            let sub_comp =
              [
                (Var (Db ((2 * k) + 2)), true);
                (Var (Db ((2 * k) + 1)), false);
                (Var (Db (2 * k)), true);
                (Var (Db ((2 * k) - 1)), false);
                (Var (Db ((2 * k) - 3)), false);
              ]
            in
            let comp = Coh (Builtin.comp_n 2, sub_comp) in
            (comp, true)
            :: (Var (Db ((2 * k) + 1)), false)
            :: compute_sub (k - 1)
        | i ->
            (Var (Db ((2 * i) + 2)), true)
            :: (Var (Db ((2 * i) + 1)), false)
            :: compute_sub (i - 1)
      in
      compute_sub ((2 * k) - 1)
    in
    Coh (Builtin.comp_n ((2 * k) - 1), sub_assoc_middle)
  in
  Coh.check_inv ps src tgt ("focus", 0, [])

(* returns the unitor cancelling the identity in the middle of a composite of
   (2*k+1) 1-cells. The argument is the integer k *)
let middle_unitor k =
  let ps = Builtin.ps_comp (2 * k) in
  let src =
    let sub_id_middle =
      let rec compute_sub i =
        match i with
        | i when i <= 0 -> [ (Var (Db 0), false) ]
        | i when i <= k ->
            (Var (Db (2 * i)), true)
            :: (Var (Db ((2 * i) - 1)), false)
            :: compute_sub (i - 1)
        | i when i = k + 1 ->
            let id = Coh (Builtin.id, [ (Var (Db ((2 * k) - 1)), false) ]) in
            (id, true) :: (Var (Db ((2 * k) - 1)), false) :: compute_sub k
        | i ->
            (Var (Db ((2 * i) - 2)), true)
            :: (Var (Db ((2 * i) - 3)), false)
            :: compute_sub (i - 1)
      in
      compute_sub ((2 * k) + 1)
    in
    Coh (Builtin.comp_n ((2 * k) + 1), sub_id_middle)
  in
  let tgt = Coh (Builtin.comp_n (2 * k), Unchecked.(identity_ps ps)) in
  Coh.check_inv ps src tgt ("unit", 0, [])

(* returns the whiskering rewriting the middle term of a composite of (2*k+1)
    1-cells. The argument is the integer k *)
let middle_rewrite k =
  let comp = Builtin.comp_n ((2 * k) + 1) in
  let func_data = [ Var.Db ((2 * k) + 2) ] in
  Functorialisation.coh_depth0 comp func_data

let tdb i = Var (Db i)
let cell_max k = Var.Db (4 * k)
let cell_forward k = Var.Db ((4 * k) - 2)
let cell_backward k = Var.Db ((4 * k) - 1)
let obj k = if k <= 0 then Var.Db 0 else Var.Db ((4 * k) - 3)
let type_cell_forward k = Arr (Obj, Var (obj (k - 1)), Var (obj k))
let type_cell_backward k = Arr (Obj, Var (obj k), Var (obj (k - 1)))

let type_cell_max k =
  Arr
    ( Arr (Obj, Var (obj (k - 1)), Var (obj (k - 1))),
      Coh
        ( Builtin.comp_n 2,
          [
            (Var (cell_backward k), true);
            (Var (obj (k - 1)), false);
            (Var (cell_forward k), true);
            (Var (obj k), false);
            (Var (obj (k - 1)), false);
          ] ),
      Coh (Builtin.id, [ (Var (obj (k - 1)), true) ]) )

let rec ctx k =
  match k with
  | k when k < 0 -> Error.fatal "cannot build context for the telescope"
  | k when k = 0 -> [ (Var.Db 0, (Obj, false)) ]
  | k ->
      (cell_max k, (type_cell_max k, true))
      :: (cell_backward k, (type_cell_backward k, false))
      :: (cell_forward k, (type_cell_forward k, false))
      :: (obj k, (Obj, false))
      :: ctx (k - 1)

let rec subs_telescope_bdry ?(whisk = false) k =
  match k with
  | k when k <= 0 -> Error.fatal "telescopes must have positive length"
  | k when k = 1 ->
      ( [ (tdb 2, true); (tdb 1, false); (tdb 0, false) ],
        [ (tdb 3, true); (tdb 0, false) ] )
  | k ->
      let right, left = subs_telescope_bdry ~whisk:false (k - 1) in
      if whisk then
        let src_max_var =
          Coh
            ( Builtin.comp_n 2,
              [
                (Var (cell_backward k), true);
                (Var (obj (k - 1)), false);
                (Var (cell_forward k), true);
                (Var (obj k), false);
                (Var (obj (k - 1)), false);
              ] )
        in
        ( right,
          List.append left
            [
              (Var (cell_max k), true);
              (Coh (Builtin.id, [ (Var (obj (k - 1)), true) ]), false);
              (src_max_var, false);
              (Var (obj (k - 1)), false);
            ] )
      else
        ( (Var (cell_forward k), true) :: (Var (obj k), false) :: right,
          List.append left
            [ (Var (cell_backward k), true); (Var (obj (k - 1)), false) ] )

let sub_ps_telescope_bdry ?(whisk = false) k =
  let right, left = subs_telescope_bdry ~whisk k in
  List.append left right

let rec telescope k =
  match k with
  | k when k <= 0 -> Error.fatal "telescopes must have positive length"
  | k when k = 1 -> tdb 4
  | k ->
      let comp = Suspension.coh (Some 1) (Builtin.comp_n 4) in
      let tm_src_tgt coh sub_ps =
        match Coh.forget coh with
        | _, Arr (_, t, u), _ ->
            let sub = Unchecked.sub_ps_to_sub sub_ps in
            ( Coh (coh, sub_ps),
              Unchecked.tm_apply_sub t sub,
              Unchecked.tm_apply_sub u sub )
        | _ -> Error.fatal "coherence must be of an arrow type"
      in
      let m3, src_m3, tgt_m3 =
        tm_src_tgt (middle_unitor (k - 1)) (sub_ps_telescope_bdry (k - 1))
      in
      let m2 =
        Coh (middle_rewrite (k - 1), sub_ps_telescope_bdry ~whisk:true k)
      in
      let m1, src_m1, tgt_m1 =
        tm_src_tgt (middle_associator k) (sub_ps_telescope_bdry k)
      in
      let sub_telescope =
        [
          (telescope (k - 1), true);
          (Coh (Builtin.id, [ (tdb 0, true) ]), false);
          (m3, true);
          (tgt_m3, false);
          (m2, true);
          (src_m3, false);
          (m1, true);
          (tgt_m1, false);
          (src_m1, false);
          (tdb 0, false);
          (tdb 0, false);
        ]
      in
      Coh (comp, sub_telescope)

let checked k = check_term (Ctx.check (ctx k)) (telescope k)
