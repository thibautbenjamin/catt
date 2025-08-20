open Std
open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

module UnbiasedPadding = struct
  let x = Var.Db 0
  let v = Var.Db 1
  let v_plus = Var.Db 2
  let v_bridge = Var.Db 3

  let id2 n k =
    let id = Construct.id_n n (Var x, Obj) in
    if k < n then Construct.wcomp id k id else id

  let ty i l =
    let t = id2 i l in
    Construct.arr t t

  let ctx i l = [ (v, (ty (i - 1) l, true)); (x, (Obj, false)) ]
  let v_constr i l = (Var v, ty (i - 1) l)
  let in_minus = [ (v, (Var v, true)); (x, (Var x, false)) ]
  let in_plus = [ (v, (Var v_plus, true)); (x, (Var x, false)) ]

  let sub i l =
    [
      (v_bridge, (Var v, true));
      (v_plus, (Construct.to_tm (id2 (i - 1) l), false));
      (v, (Construct.to_tm (id2 (i - 1) l), false));
      (x, (Var x, false));
    ]

  let rec padded n k l =
    let name = Printf.sprintf "UPadded(%d,%d,%d)" n k l in
    let padded_constr =
      let m = Int.min k l + 1 in
      if n = m then (Var v, ty (m - 1) l)
      else
        let n = n - 1 in
        let p, q = u n k l in
        Padding.pad p q (padded n k l) v (sub (n + 1) l)
    in
    check_constr (ctx n l) ~name:(name, 0, []) padded_constr

  and u n k l =
    let pp_indices =
      string_of_int n ^ "_(" ^ string_of_int k ^ "," ^ string_of_int l ^ ")"
    in
    let padded_subbed =
      Construct.tm_app (padded n k l)
        [ (v, (Construct.to_tm (id2 n l), true)); (x, (Var x, false)) ]
    in
    let p =
      let ty = Construct.arr (id2 n k) padded_subbed in
      check_coh (Br []) ty ("p^" ^ pp_indices, 0, [])
    in
    let q =
      let ty = Construct.arr padded_subbed (id2 n k) in
      check_coh (Br []) ty ("q^" ^ pp_indices, 0, [])
    in
    (Construct.of_coh p, Construct.of_coh q)

  let rec padded_func n k l = function
    | 1 -> Construct.of_tm (Functorialisation.tm (padded n k l) [ (v, 1) ])
    | r ->
        Construct.functorialise
          (Construct.apply_sub (padded_func n k l (r - 1)) (sub (n + r - 1) l))
          [ v ]
end

module ForwardBiasedPadding = struct
  let ctx i = Unchecked.ps_to_ctx (Unchecked.disc i)
  let v i = Var.Db (2 * i)
  let v_constr i = (Var (v i), Unchecked.disc_type i)
  let d_plus = Var.Db 1
  let d_plus_constr = (Var d_plus, Obj)

  let sub n =
    (Var.Bridge (v (n - 1)), (Var (v n), true))
    :: (Var.Plus (v (n - 1)), (Var (Var.Db ((2 * n) - 1)), false))
    :: Unchecked.(identity (disc_ctx (n - 1)))

  let rec padded n =
    let name = Printf.sprintf "FPadded(%d)" n in
    let padded_constr =
      if n = 1 then v_constr 1
      else
        let n = n - 1 in
        let p, q = u n in
        Padding.pad p q (padded n) (v n) (sub (n + 1))
    in
    check_constr (ctx n) ~name:(name, 0, []) padded_constr

  and u n =
    let p =
      let ty =
        Construct.(
          arr (wcomp (v_constr n) 0 (id_n n d_plus_constr)) (of_tm (padded n)))
      in
      check_coh (Unchecked.disc n) ty ("p^" ^ string_of_int n ^ "_<", 0, [])
    in
    let q =
      let q_type =
        Construct.(
          arr (of_tm (padded n)) (wcomp (v_constr n) 0 (id_n n d_plus_constr)))
      in
      check_coh (Unchecked.disc n) q_type ("q^" ^ string_of_int n ^ "_<", 0, [])
    in
    ( Construct.coh_app p (Unchecked.disc_src n),
      Construct.coh_app q (Unchecked.disc_tgt n) )
end

module BackwardBiasedPadding = struct
  let d_src i = (Var (Var.Db (2 * i)), Unchecked.disc_type i)
  let d_tgt i = (Var (Var.Db ((2 * i) + 1)), Unchecked.disc_type i)

  let src i =
    if i = 0 then d_src i else Construct.(wcomp (d_src i) 0 (id_n i (d_tgt 0)))

  let tgt i =
    if i = 0 then d_tgt i else Construct.(wcomp (d_tgt i) 0 (id_n i (d_tgt 0)))

  let ty i = Construct.arr (src i) (tgt i)
  let v i = Var.Db (2 * i)
  let v_plus i = Var.Db ((2 * i) + 1)
  let v_bridge i = Var.Db ((2 * i) + 2)
  let ctx i = (v i, (ty (i - 1), true)) :: Unchecked.sphere (i - 1)

  let gamma_i_gt_to_db n =
    (v n, (Construct.to_tm (src n), true))
    :: Unchecked.(identity (sphere (n - 1)))

  let sub n =
    (v_bridge (n - 1), (Var (v n), true))
    :: (v_plus (n - 1), (Construct.to_tm (tgt (n - 1)), false))
    :: (v (n - 1), (Construct.to_tm (src (n - 1)), false))
    :: Unchecked.(identity (sphere (n - 2)))

  let rec padded n =
    let name = Printf.sprintf "BPadding(%d)" n in
    let padded_constr =
      if n = 1 then d_src 1
      else
        let n = n - 1 in
        let p, q = u n in
        Padding.pad p q (padded n) (v n) (sub (n + 1))
    in
    check_constr (ctx n) ~name:(name, 0, []) padded_constr

  and u n =
    let p =
      let ty =
        Construct.(arr (d_src n) (tm_app (padded n) (gamma_i_gt_to_db n)))
      in
      check_coh (Unchecked.disc n) ty ("p^" ^ string_of_int n ^ "_>", 0, [])
    in
    let q =
      let ty =
        Construct.(arr (tm_app (padded n) (gamma_i_gt_to_db n)) (d_src n))
      in
      check_coh (Unchecked.disc n) ty ("q^" ^ string_of_int n ^ "_>", 0, [])
    in
    ( Construct.coh_app p (Unchecked.disc_src n),
      Construct.coh_app q (Unchecked.disc_tgt n) )
end

module UP = UnbiasedPadding
module FP = ForwardBiasedPadding
module BP = BackwardBiasedPadding

let sphere_to_point n =
  let id_pt n = Construct.(to_tm (id_n n (Var (Var.Db 0), Obj))) in
  let rec aux = function
    | -1 -> []
    | n ->
        (Var.Db ((2 * n) + 1), (id_pt n, false))
        :: (Var.Db (2 * n), (id_pt n, false))
        :: aux (n - 1)
  in
  aux n

module ForwardToUnbiasedRepadding = struct
  let filtration_morphism n =
    (FP.v n, (Var UP.v, true)) :: sphere_to_point (n - 1)

  let rec repad n i =
    let repadding_constr =
      if i = 1 then Construct.id_n 1 (UP.v_constr 1 (n - 1))
      else
        let i = i - 1 in
        let p_lt, q_lt = FP.u i in
        let p_lt = Construct.apply_sub p_lt (filtration_morphism (i + 1)) in
        let q_lt = Construct.apply_sub q_lt (filtration_morphism (i + 1)) in
        let p_u, q_u = UP.u i 0 (n - 1) in
        let previous = repad n i in
        let in_m = UP.in_minus in
        let in_p = UP.in_plus in
        let sigma = UP.sub (i + 1) (n - 1) in
        let pp_indices = string_of_int i ^ "_(" ^ string_of_int n ^ ",<)" in
        let f =
          let ty =
            Construct.(
              arr (wcomp p_lt i (apply_sub (tm_app previous in_m) sigma)) p_u)
          in
          check_coh (Br []) ty ("f^" ^ pp_indices, 0, [])
        in
        let g =
          let ty =
            Construct.(
              arr q_lt (wcomp (apply_sub (tm_app previous in_p) sigma) i q_u))
          in
          check_coh (Br []) ty ("g^" ^ pp_indices, 0, [])
        in
        let f, g = Construct.(of_coh f, of_coh g) in
        Padding.repad p_lt p_u f q_lt q_u g previous in_m in_p UP.v sigma
    in
    check_constr (UP.ctx n i) ~name:("RepaddingUToF", 0, []) repadding_constr
end

module BackwardToUnbiasedRepadding = struct
  let filtration_morphism n =
    (BP.v n, (Var UP.v, true)) :: sphere_to_point (n - 1)

  let rec repad n i =
    Io.debug "computing repadding B to U";
    let repadding_constr =
      if i = 1 then Construct.id_n 1 (UP.v_constr i 0)
      else
        let p_gt, q_gt = BP.u (i - 1) in
        let p_gt = Construct.apply_sub p_gt (filtration_morphism i) in
        let q_gt = Construct.apply_sub q_gt (filtration_morphism i) in
        let p_u, q_u = UP.u (i - 1) (n - 1) 0 in
        let previous = repad n (i - 1) in
        let sub_f = Unchecked.sub_apply_sub UP.in_minus (UP.sub i 0) in
        let sub_g = Unchecked.sub_apply_sub UP.in_plus (UP.sub i 0) in
        let sigma = UP.sub i 0 in
        let pp_indices =
          string_of_int (i - 1) ^ "_(" ^ string_of_int n ^ ",>)"
        in
        let f =
          let ty =
            Construct.(arr (wcomp p_gt (i - 1) (tm_app previous sub_f)) p_u)
          in
          check_coh (Br []) ty ("f^" ^ pp_indices, 0, [])
        in
        let g =
          let ty =
            Construct.(arr q_gt (wcomp (tm_app previous sub_g) (i - 1) q_u))
          in
          check_coh (Br []) ty ("g^" ^ pp_indices, 0, [])
        in
        let f, g = Construct.(of_coh f, of_coh g) in
        Padding.repad p_gt p_u f q_gt q_u g previous UP.in_minus UP.in_plus UP.v
          sigma
    in
    Io.debug "computed the constr";
    Io.debug "context %d %d : %s" n i (Unchecked.ctx_to_string (UP.ctx i 0));
    Io.debug "term: %s" (Unchecked.tm_to_string (fst repadding_constr));
    Io.debug "type: %s" (Unchecked.ty_to_string (snd repadding_constr));
    check_constr (UP.ctx i 0) ~name:("RepaddingBToU", 0, []) repadding_constr
end

module FToU = ForwardToUnbiasedRepadding
module BToU = BackwardToUnbiasedRepadding

(* ****************************************************************** *)

(* TODO: replace all instances of drop by a Construct.sub_ps_builder *)
let drop n xs =
  let rec aux xs counter =
    match xs with
    | [] -> []
    | h :: tl -> if counter > 0 then h :: aux tl (counter - 1) else []
  in
  aux xs (List.length xs - n)

module PseudoFunctorialityUnbiasedPadding = struct
  let w = Var.Db 2
  let ctx n l = (w, (UP.ty n l, true)) :: UP.ctx n l
  let w_constr n l = (Var w, UP.ty n l)
  let v = UP.v
  let v_constr = UP.v_constr

  (* TODO: cleanup these two coherences *)

  let assoc n =
    let tree = Br [ Br []; Br []; Br []; Br []; Br []; Br [] ] in
    let f1 = (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) in
    let f2 = (Var (Var.Db 4), Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))) in
    let f3 = (Var (Var.Db 6), Arr (Obj, Var (Var.Db 3), Var (Var.Db 5))) in
    let f4 = (Var (Var.Db 8), Arr (Obj, Var (Var.Db 5), Var (Var.Db 7))) in
    let f5 = (Var (Var.Db 10), Arr (Obj, Var (Var.Db 7), Var (Var.Db 9))) in
    let f6 = (Var (Var.Db 12), Arr (Obj, Var (Var.Db 9), Var (Var.Db 11))) in
    let cohty =
      Construct.arr
        (Construct.wcomp (Construct.comp3 f1 f2 f3) 0 (Construct.comp3 f4 f5 f6))
        (Construct.comp3 f1
           (Construct.comp3 f2 (Construct.wcomp f3 0 f4) f5)
           f6)
    in
    Suspension.coh (Some n)
      (check_coh tree cohty ("assoc_(---)(---)_to_-(-(--)-)-", 0, []))

  let unitor n =
    let tree = Br [ Br []; Br [] ] in
    let f1 = (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) in
    let f2 = (Var (Var.Db 4), Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))) in
    let x1 = (Var (Var.Db 1), Obj) in
    let cohty =
      Construct.arr
        (Construct.comp3 f1 (Construct.id_n 1 x1) f2)
        (Construct.wcomp f1 0 f2)
    in
    Suspension.coh (Some n) (check_coh tree cohty ("unitor_-id-_to_--", 0, []))

  let intch n i =
    let ps =
      Br [ Br []; Suspension.ps (Some (n - 2)) (Br [ Br []; Br [] ]); Br [] ]
    in
    let tdb i = Var (Var.Db i) in
    let d_L = (tdb 2, Arr (Obj, tdb 0, tdb 1)) in
    let d_R = (tdb ((2 * n) + 8), Arr (Obj, tdb 3, tdb ((2 * n) + 7))) in
    let d_max i =
      let rec ty k =
        if k = 0 then Arr (Obj, tdb 1, tdb 3)
        else Arr (ty (k - 1), tdb ((2 * k) + 2), tdb ((2 * k) + 3))
      in
      let d i =
        let lvl = if i = 0 then (2 * n) + 2 else (2 * n) + (2 * i) + 1 in
        (tdb lvl, ty (n - 1))
      in
      (tdb (2 + (2 * n) + (2 * i)), Construct.arr (d (i - 1)) (d i))
    in
    let ty =
      Construct.(
        arr
          (comp
             (wcomp_n 0 [ d_L; d_max 1; d_R ])
             (wcomp_n 0 [ d_L; d_max 2; d_R ]))
          (wcomp_n 0 [ d_L; comp_n [ d_max 1; d_max 2 ]; d_R ]))
    in
    Suspension.coh (Some i) (check_coh ps ty ("chi^" ^ string_of_int n, 0, []))

  (* TODO: Merge witness_aux and witness_aux_gt *)

  let rec witness_aux n i =
    let v = v_constr (i - 1) (n - 1) in
    let w = w_constr (i - 1) (n - 1) in
    match i with
    | 1 -> Construct.id_n 1 (Construct.wcomp v (n - 1) w)
    | i when 1 < i -> (
        let p, q = UP.u (i - 1) 0 (n - 1) in
        let t = UP.padded_func (i - 1) 0 (n - 1) (n - i + 1) in
        let v_sub = Construct.characteristic_sub_ps v in
        let w_sub = Construct.characteristic_sub_ps w in
        let tv = Construct.apply_sub t (Unchecked.sub_ps_to_sub v_sub) in
        let tw = Construct.apply_sub t (Unchecked.sub_ps_to_sub w_sub) in
        match i with
        | i when i < n ->
            let sub =
              drop ((2 * i) - 1) (Construct.characteristic_sub_ps q)
              @ drop ((2 * n) - 1) (Construct.characteristic_sub_ps tw)
              @ drop ((2 * i) - 1) (Construct.characteristic_sub_ps tv)
              @ Construct.characteristic_sub_ps p
            in
            let intch = Construct.coh_app (intch (n - i) (i - 1)) sub in
            Construct.wcomp intch n
              (Construct.wcomp_n (i - 1) [ p; witness_aux n (i - 1); q ])
        | i when i == n ->
            (* TODO: replace this by a builder *)
            let sub6 =
              let open Construct in
              (to_tm q, true)
              :: (to_tm @@ tgt 1 q, false)
              :: (to_tm tv, true)
              :: (to_tm @@ tgt 1 tw, false)
              :: (to_tm p, true)
              :: (to_tm @@ tgt 1 p, false)
              :: (to_tm q, true)
              :: (to_tm @@ tgt 1 q, false)
              :: (to_tm tv, true)
              :: (to_tm @@ tgt 1 tw, false)
              :: Construct.characteristic_sub_ps p
            in
            let assoc = Construct.coh_app (assoc (n - 1)) sub6 in
            let w = Construct.witness q in
            (* TODO: replace this by a builder *)
            let sub2 =
              let open Construct in
              (to_tm tw, true)
              :: (to_tm @@ tgt 1 tw, false)
              :: characteristic_sub_ps tv
            in
            let unitor = Construct.coh_app (unitor (n - 1)) sub2 in
            Construct.comp_n
              [
                assoc;
                Construct.wcomp_n (n - 1)
                  [ p; Construct.wcomp_n (n - 1) [ tv; w; tw ]; q ];
                Construct.wcomp_n (n - 1) [ p; unitor; q ];
                Construct.wcomp_n (n - 1) [ p; witness_aux n (n - 1); q ];
              ]
        | _ ->
            Error.fatal "[EH] Wrong arguments in pseudofunctoriality of padding"
        )
    | _ -> Error.fatal "[EH] Wrong arguments in pseudofunctoriality of padding"

  let witness n = witness_aux n n

  let rec witness_aux_gt n i =
    let v = v_constr (i - 1) 0 in
    let w = w_constr (i - 1) 0 in
    match i with
    | 1 -> Construct.id_n 1 (Construct.wcomp v (n - 1) w)
    | i when 1 < i -> (
        let p, q = UP.u (i - 1) (n - 1) 0 in
        let t = UP.padded_func (i - 1) (n - 1) 0 (n - i + 1) in
        let v_sub = Construct.characteristic_sub_ps v in
        let w_sub = Construct.characteristic_sub_ps w in
        let tv = Construct.apply_sub t (Unchecked.sub_ps_to_sub v_sub) in
        let tw = Construct.apply_sub t (Unchecked.sub_ps_to_sub w_sub) in
        match i with
        | i when i < n ->
            let sub =
              drop ((2 * i) - 1) (Construct.characteristic_sub_ps q)
              @ drop ((2 * n) - 1) (Construct.characteristic_sub_ps tw)
              @ drop ((2 * i) - 1) (Construct.characteristic_sub_ps tv)
              @ Construct.characteristic_sub_ps p
            in
            let intch = Construct.coh_app (intch (n - i) (i - 1)) sub in
            Construct.wcomp intch n
              (Construct.wcomp_n (i - 1) [ p; witness_aux_gt n (i - 1); q ])
        | i when i == n ->
            let sub6 =
              (Construct.to_tm q, true)
              :: (Construct.to_tm @@ Construct.tgt 1 q, false)
              :: (Construct.to_tm tw, true)
              :: (Construct.to_tm @@ Construct.tgt 1 tw, false)
              :: (Construct.to_tm p, true)
              :: (Construct.to_tm @@ Construct.tgt 1 p, false)
              :: (Construct.to_tm q, true)
              :: (Construct.to_tm @@ Construct.tgt 1 q, false)
              :: (Construct.to_tm tv, true)
              :: (Construct.to_tm @@ Construct.tgt 1 tv, false)
              :: Construct.characteristic_sub_ps p
            in
            let assoc = Construct.coh_app (assoc (n - 1)) sub6 in
            let w = Construct.witness q in
            let sub2 =
              (Construct.to_tm tw, true)
              :: (Construct.to_tm @@ Construct.tgt 1 tw, false)
              :: Construct.characteristic_sub_ps tv
            in
            let unitor = Construct.coh_app (unitor (n - 1)) sub2 in
            Construct.comp_n
              [
                assoc;
                Construct.wcomp_n (n - 1)
                  [ p; Construct.wcomp_n (n - 1) [ tv; w; tw ]; q ];
                Construct.wcomp_n (n - 1) [ p; unitor; q ];
                Construct.wcomp_n (n - 1) [ p; witness_aux_gt n (n - 1); q ];
              ]
        | _ ->
            Error.fatal "[EH] Wrong arguments in pseudofunctoriality of padding"
        )
    | _ -> Error.fatal "[EH] Wrong arguments in pseudofunctoriality of padding"

  let witness_gt n = witness_aux_gt n n
end

module EHBaseCases = struct
  let x = Var.Db 0
  let a _ = Var.Db 1
  let b _ = Var.Db 2
  let id n = Construct.id_n n (Var x, Obj)

  let ty n =
    let id = id n in
    Construct.arr id id

  let ctx n =
    [ (b n, (ty (n - 1), true)); (a n, (ty (n - 1), true)); (x, (Obj, false)) ]

  let x_constr = (Var x, Obj)
  let a_constr n = (Var (a n), ty (n - 1))
  let b_constr n = (Var (b n), ty (n - 1))

  let a_comp_id i l =
    if l = i - 1 then a_constr i
    else Construct.wcomp (a_constr i) l (Construct.id_n i x_constr)

  let id_comp_b i l =
    if l = i - 1 then b_constr i
    else Construct.wcomp (Construct.id_n i x_constr) l (b_constr i)

  (* Step3 = PseudoFunctoriality(a_comp_id, id_comp_b) *)

  let step1_gt n =
    let p, _ = BP.u (n + 1) in
    (* TODO: Use builders here *)
    let a_padded =
      Construct.(apply_sub_ps p (characteristic_sub_ps (a_constr n)))
    in
    let b_padded =
      Construct.apply_sub_ps (Construct.op [ 1 ] p)
        (Construct.characteristic_sub_ps (b_constr n))
    in
    Construct.wcomp a_padded (n - 1) b_padded

  let gamma_i_l_to_eh_a i l =
    [ (UP.v, (Construct.to_tm @@ a_comp_id i l, true)); (x, (Var x, false)) ]

  let gamma_i_l_to_eh_b i l =
    [ (UP.v, (Construct.to_tm @@ id_comp_b i l, true)); (x, (Var x, false)) ]

  let step2_gt n =
    let r = BToU.repad n n in
    let repad_a = Construct.tm_app r (gamma_i_l_to_eh_a n 0) in
    let repad_b =
      Construct.tm_app (Opposite.checked_tm r [ 1 ]) (gamma_i_l_to_eh_b n 0)
    in
    Construct.wcomp repad_a (n - 1) repad_b

  (* let eh_gt n = *)
  (*   Construct.comp_n [ step1_gt n; step2_gt n; step3_gt n; step4_gt n ] *)
end

module V = EHBaseCases

let x = V.x

let rec sphere_type_db = function
  | -1 -> Obj
  | n ->
      Arr
        ( sphere_type_db @@ (n - 1),
          Var (Var.Db (2 * n)),
          Var (Var.Db ((2 * n) + 1)) )

let d_n_constr n = (Var (Var.Db (2 * n)), sphere_type_db (n - 1))
let whisker left middle right = Construct.wcomp_n 0 [ left; middle; right ]

let intch_n_h n h =
  let d_1_L_constr =
    (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1)))
  in
  let d_1_R_constr =
    ( Var (Var.Db ((2 * n) + (2 * h) + 4)),
      Arr (Obj, Var (Var.Db 3), Var (Var.Db ((2 * n) + (2 * h) + 3))) )
  in
  let rec adj_sphere_type k =
    if k = 0 then Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))
    else
      Arr
        ( adj_sphere_type (k - 1),
          Var (Var.Db ((2 * k) + 2)),
          Var (Var.Db ((2 * k) + 3)) )
  in
  let d_n_constr i =
    if i = 0 then (Var (Var.Db (2 + (2 * n))), adj_sphere_type (n - 1))
    else (Var (Var.Db (1 + (2 * n) + (2 * i))), adj_sphere_type (n - 1))
  in
  let d_nplus1_i_constr i =
    ( Var (Var.Db (2 + (2 * n) + (2 * i))),
      Construct.arr (d_n_constr (i - 1)) (d_n_constr i) )
  in
  let rec middle_constrs r =
    if r = h + 1 then [] else d_nplus1_i_constr r :: middle_constrs (r + 1)
  in
  let rec middle_whiskered r =
    if r = h + 1 then []
    else
      whisker d_1_L_constr (d_nplus1_i_constr r) d_1_R_constr
      :: middle_whiskered (r + 1)
  in
  let rec chain = function 0 -> [] | h -> Br [] :: chain (h - 1) in
  let rec tower xs = function 0 -> Br xs | n -> Br [ tower xs (n - 1) ] in
  let intch_ctx_db = Br [ Br []; tower (chain h) (n - 1); Br [] ] in
  let coh_type =
    Construct.arr
      (Construct.comp_n @@ middle_whiskered 1)
      (whisker d_1_L_constr (Construct.comp_n @@ middle_constrs 1) d_1_R_constr)
  in
  ( check_coh intch_ctx_db coh_type
      ("chi^" ^ string_of_int n ^ "_" ^ string_of_int h, 0, []),
    coh_type )

(* TODO: Fix this function *)
let rec padded_n_k_l_func_r n k l = function
  | 1 -> Construct.of_tm (Functorialisation.tm (UP.padded n k l) [ (UP.v, 1) ])
  | r ->
      Construct.functorialise
        (Construct.apply_sub
           (padded_n_k_l_func_r n k l (r - 1))
           (UP.sub (n + r - 1) l))
        [ UP.v ]

let a_comp_id i l =
  if l = i - 1 then V.a_constr i
  else Construct.wcomp (V.a_constr i) l (Construct.id_n i V.x_constr)

let id_comp_b i l =
  if l = i - 1 then V.b_constr i
  else Construct.wcomp (Construct.id_n i V.x_constr) l (V.b_constr i)

let gamma_i_l_to_eh_a i l =
  [ (UP.v, (Construct.to_tm @@ a_comp_id i l, true)); (x, (Var x, false)) ]

let gamma_i_l_to_eh_b i l =
  [ (UP.v, (Construct.to_tm @@ id_comp_b i l, true)); (x, (Var x, false)) ]

let gamma_iminus1_l_func_to_eh_a i l =
  [
    (UP.v_bridge, (Construct.to_tm @@ a_comp_id i l, true));
    (UP.v_plus, (Construct.to_tm @@ UP.id2 (i - 1) l, false));
    (UP.v, (Construct.to_tm @@ UP.id2 (i - 1) l, false));
    (x, (Var x, false));
  ]

let gamma_iminus1_l_func_to_eh_b i l =
  [
    (UP.v_bridge, (Construct.to_tm @@ id_comp_b i l, true));
    (UP.v_plus, (Construct.to_tm @@ UP.id2 (i - 1) l, false));
    (UP.v, (Construct.to_tm @@ UP.id2 (i - 1) l, false));
    (x, (Var x, false));
  ]

module PseudoFunctoriality = struct
  let w = Var.Db 2
  let ctx n l = (w, (UP.ty n l, true)) :: UP.ctx n l
  let w_constr n l = (Var w, UP.ty n l)

  let rec xi_n_i_lt n i =
    match i with
    | 1 ->
        Construct.id_n 1
          (Construct.wcomp (a_comp_id n (n - 1)) (n - 1) (id_comp_b n (n - 1)))
    | i ->
        let p, q = UP.u (i - 1) 0 (n - 1) in
        let sub =
          drop ((2 * i) - 1) (Construct.characteristic_sub_ps q)
          @ drop
              ((2 * n) - 1)
              (Construct.characteristic_sub_ps
                 (Construct.apply_sub
                    (padded_n_k_l_func_r (i - 1) 0 (n - 1) (n - i + 1))
                    (gamma_iminus1_l_func_to_eh_b n (n - 1))))
          @ drop
              ((2 * i) - 1)
              (Construct.characteristic_sub_ps
                 (Construct.apply_sub
                    (padded_n_k_l_func_r (i - 1) 0 (n - 1) (n - i + 1))
                    (gamma_iminus1_l_func_to_eh_a n (n - 1))))
          @ Construct.characteristic_sub_ps p
        in
        let chi, chi_ty = intch_n_h (n - i) 2 in
        let chi_applied =
          ( Coh (Suspension.coh (Some (i - 1)) chi, sub),
            Unchecked.ty_apply_sub_ps (Suspension.ty (Some (i - 1)) chi_ty) sub
          )
        in
        Construct.wcomp chi_applied n
          (Construct.wcomp_n (i - 1) [ p; xi_n_i_lt n (i - 1); q ])

  let rec xi_n_i_gt n i =
    match i with
    | 1 ->
        Construct.id_n 1
          (Construct.wcomp (a_comp_id n 0) (n - 1) (id_comp_b n 0))
    | i ->
        let p, q = UP.u (i - 1) (n - 1) 0 in
        let sub =
          drop ((2 * i) - 1) (Construct.characteristic_sub_ps q)
          @ drop
              ((2 * n) - 1)
              (Construct.characteristic_sub_ps
                 (Construct.apply_sub
                    (padded_n_k_l_func_r (i - 1) (n - 1) 0 (n - i + 1))
                    (gamma_iminus1_l_func_to_eh_b n 0)))
          @ drop
              ((2 * i) - 1)
              (Construct.characteristic_sub_ps
                 (Construct.apply_sub
                    (padded_n_k_l_func_r (i - 1) (n - 1) 0 (n - i + 1))
                    (gamma_iminus1_l_func_to_eh_a n 0)))
          @ Construct.characteristic_sub_ps p
        in
        let chi, chi_ty = intch_n_h (n - i) 2 in
        let chi_applied =
          ( Coh (Suspension.coh (Some (i - 1)) chi, sub),
            Unchecked.ty_apply_sub_ps (Suspension.ty (Some (i - 1)) chi_ty) sub
          )
        in
        Construct.wcomp chi_applied n
          (Construct.wcomp_n (i - 1) [ p; xi_n_i_gt n (i - 1); q ])

  let assoc_33_to_middle2 () =
    let tree = Br [ Br []; Br []; Br []; Br []; Br []; Br [] ] in
    let f1 = (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) in
    let f2 = (Var (Var.Db 4), Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))) in
    let f3 = (Var (Var.Db 6), Arr (Obj, Var (Var.Db 3), Var (Var.Db 5))) in
    let f4 = (Var (Var.Db 8), Arr (Obj, Var (Var.Db 5), Var (Var.Db 7))) in
    let f5 = (Var (Var.Db 10), Arr (Obj, Var (Var.Db 7), Var (Var.Db 9))) in
    let f6 = (Var (Var.Db 12), Arr (Obj, Var (Var.Db 9), Var (Var.Db 11))) in
    let cohty =
      Construct.arr
        (Construct.wcomp (Construct.comp3 f1 f2 f3) 0 (Construct.comp3 f4 f5 f6))
        (Construct.comp3 f1
           (Construct.comp3 f2 (Construct.wcomp f3 0 f4) f5)
           f6)
    in
    ( Coh
        ( check_coh tree cohty ("assoc_(---)(---)_to_-(-(--)-)-", 0, []),
          Unchecked.identity_ps tree ),
      cohty )

  let middle_unitor () =
    let tree = Br [ Br []; Br [] ] in
    let f1 = (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) in
    let f2 = (Var (Var.Db 4), Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))) in
    let x1 = (Var (Var.Db 1), Obj) in
    let cohty =
      Construct.arr
        (Construct.comp3 f1 (Construct.id_n 1 x1) f2)
        (Construct.wcomp f1 0 f2)
    in
    ( Coh
        ( check_coh tree cohty ("unitor_-id-_to_--", 0, []),
          Unchecked.identity_ps tree ),
      cohty )

  let xi_lt n =
    let p, q = UP.u (n - 1) 0 (n - 1) in
    let padded_a =
      Construct.apply_sub
        (padded_n_k_l_func_r (n - 1) 0 (n - 1) 1)
        (gamma_iminus1_l_func_to_eh_a n (n - 1))
    in
    let padded_b =
      Construct.apply_sub
        (padded_n_k_l_func_r (n - 1) 0 (n - 1) 1)
        (gamma_iminus1_l_func_to_eh_b n (n - 1))
    in
    let sub6 =
      (Construct.to_tm q, true)
      :: (Construct.to_tm @@ Construct.tgt 1 q, false)
      :: (Construct.to_tm padded_b, true)
      :: (Construct.to_tm @@ Construct.tgt 1 padded_b, false)
      :: (Construct.to_tm p, true)
      :: (Construct.to_tm @@ Construct.tgt 1 p, false)
      :: (Construct.to_tm q, true)
      :: (Construct.to_tm @@ Construct.tgt 1 q, false)
      :: (Construct.to_tm padded_a, true)
      :: (Construct.to_tm @@ Construct.tgt 1 padded_a, false)
      :: Construct.characteristic_sub_ps p
    in
    let assoc =
      Construct.apply_sub_ps
        (Construct.suspend (n - 1) (assoc_33_to_middle2 ()))
        sub6
    in
    let w = Construct.witness q in
    let sub2 =
      (Construct.to_tm padded_b, true)
      :: (Construct.to_tm @@ Construct.tgt 1 padded_b, false)
      :: Construct.characteristic_sub_ps padded_a
    in
    let unitor =
      Construct.apply_sub_ps (Construct.suspend (n - 1) (middle_unitor ())) sub2
    in
    Construct.comp_n
      [
        assoc;
        Construct.wcomp_n (n - 1)
          [ p; Construct.wcomp_n (n - 1) [ padded_a; w; padded_b ]; q ];
        Construct.wcomp_n (n - 1) [ p; unitor; q ];
        Construct.wcomp_n (n - 1) [ p; xi_n_i_lt n (n - 1); q ];
      ]

  let xi_gt n =
    let p, q = UP.u (n - 1) (n - 1) 0 in
    let padded_a =
      Construct.apply_sub
        (padded_n_k_l_func_r (n - 1) (n - 1) 0 1)
        (gamma_iminus1_l_func_to_eh_a n 0)
    in
    let padded_b =
      Construct.apply_sub
        (padded_n_k_l_func_r (n - 1) (n - 1) 0 1)
        (gamma_iminus1_l_func_to_eh_b n 0)
    in
    let sub6 =
      (Construct.to_tm q, true)
      :: (Construct.to_tm @@ Construct.tgt 1 q, false)
      :: (Construct.to_tm padded_b, true)
      :: (Construct.to_tm @@ Construct.tgt 1 padded_b, false)
      :: (Construct.to_tm p, true)
      :: (Construct.to_tm @@ Construct.tgt 1 p, false)
      :: (Construct.to_tm q, true)
      :: (Construct.to_tm @@ Construct.tgt 1 q, false)
      :: (Construct.to_tm padded_a, true)
      :: (Construct.to_tm @@ Construct.tgt 1 padded_a, false)
      :: Construct.characteristic_sub_ps p
    in
    let assoc =
      Construct.apply_sub_ps
        (Construct.suspend (n - 1) (assoc_33_to_middle2 ()))
        sub6
    in
    let w = Construct.witness q in
    let sub2 =
      (Construct.to_tm padded_b, true)
      :: (Construct.to_tm @@ Construct.tgt 1 padded_b, false)
      :: Construct.characteristic_sub_ps padded_a
    in
    let unitor =
      Construct.apply_sub_ps (Construct.suspend (n - 1) (middle_unitor ())) sub2
    in
    Construct.comp_n
      [
        assoc;
        Construct.wcomp_n (n - 1)
          [ p; Construct.wcomp_n (n - 1) [ padded_a; w; padded_b ]; q ];
        Construct.wcomp_n (n - 1) [ p; unitor; q ];
        Construct.wcomp_n (n - 1) [ p; xi_n_i_gt n (n - 1); q ];
      ]
end

module PSU = PseudoFunctoriality

let zeta n =
  let tree = Br [ Unchecked.disc (n - 1); Unchecked.disc (n - 1) ] in
  let rec sphere_type_L = function
    | -1 -> Obj
    | k ->
        Arr
          ( sphere_type_L (k - 1),
            Var (Var.Db (2 * k)),
            Var (Var.Db ((2 * k) + 1)) )
  in
  let rec sphere_type_R = function
    | -1 -> Obj
    | 0 -> Arr (Obj, Var (Var.Db 1), Var (Var.Db ((2 * n) + 1)))
    | k ->
        Arr
          ( sphere_type_R (k - 1),
            Var (Var.Db ((2 * n) + (2 * k))),
            Var (Var.Db ((2 * n) + (2 * k) + 1)) )
  in
  let d_l = (Var (Var.Db (2 * n)), sphere_type_L (n - 1)) in
  let d_r = (Var (Var.Db (4 * n)), sphere_type_R (n - 1)) in
  let cohty =
    Construct.arr
      (Construct.wcomp
         (Construct.wcomp d_l 0 (Construct.id_n 1 (Construct.src 1 d_r)))
         (n - 1)
         (Construct.wcomp (Construct.id_n 1 (Construct.tgt 1 d_l)) 0 d_r))
      (Construct.wcomp d_l 0 d_r)
  in
  let sub =
    drop 1 (Construct.characteristic_sub_ps (V.b_constr n))
    @ Construct.characteristic_sub_ps (V.a_constr n)
  in
  ( Coh (check_coh tree cohty ("zeta^" ^ string_of_int n, 0, []), sub),
    Unchecked.ty_apply_sub_ps cohty sub )

let zeta_inv n =
  let tree = Br [ Unchecked.disc (n - 1); Unchecked.disc (n - 1) ] in
  let rec sphere_type_L = function
    | -1 -> Obj
    | k ->
        Arr
          ( sphere_type_L (k - 1),
            Var (Var.Db (2 * k)),
            Var (Var.Db ((2 * k) + 1)) )
  in
  let rec sphere_type_R = function
    | -1 -> Obj
    | 0 -> Arr (Obj, Var (Var.Db 1), Var (Var.Db ((2 * n) + 1)))
    | k ->
        Arr
          ( sphere_type_R (k - 1),
            Var (Var.Db ((2 * n) + (2 * k))),
            Var (Var.Db ((2 * n) + (2 * k) + 1)) )
  in
  let d_l = (Var (Var.Db (2 * n)), sphere_type_L (n - 1)) in
  let d_r = (Var (Var.Db (4 * n)), sphere_type_R (n - 1)) in
  let cohty =
    Construct.arr
      (Construct.wcomp d_l 0 d_r)
      (Construct.wcomp
         (Construct.wcomp d_l 0 (Construct.id_n 1 (Construct.src 1 d_r)))
         (n - 1)
         (Construct.wcomp (Construct.id_n 1 (Construct.tgt 1 d_l)) 0 d_r))
  in
  let sub =
    drop 1 (Construct.characteristic_sub_ps (V.b_constr n))
    @ Construct.characteristic_sub_ps (V.a_constr n)
  in
  ( Coh (check_coh tree cohty ("(zeta^" ^ string_of_int n ^ ")^-1", 0, []), sub),
    Unchecked.ty_apply_sub_ps cohty sub )

let first_step_gt n =
  let p_type =
    Construct.arr (d_n_constr n)
      (Construct.tm_app (BP.padded n) (BP.gamma_i_gt_to_db n))
  in
  let pad =
    ( Coh
        ( check_coh (Unchecked.disc n) p_type
            ("p^" ^ string_of_int n ^ "_>", 0, []),
          Unchecked.identity_ps @@ Unchecked.disc n ),
      p_type )
  in
  let phi =
    Construct.apply_sub_ps pad (Construct.characteristic_sub_ps (V.a_constr n))
  in
  let phi_op =
    Construct.apply_sub_ps (Construct.op [ 1 ] pad)
      (Construct.characteristic_sub_ps (V.b_constr n))
  in
  Construct.wcomp phi (n - 1) phi_op

let second_step_lt n =
  let p_type =
    Construct.arr
      (Construct.wcomp (d_n_constr n) 0
         (Construct.id_n n (Var (Var.Db 1), Obj)))
      (Construct.of_tm (FP.padded n))
  in
  let pad =
    ( Coh
        ( check_coh (Unchecked.disc n) p_type
            ("p^" ^ string_of_int n ^ "_<", 0, []),
          Unchecked.identity_ps @@ Unchecked.disc n ),
      p_type )
  in
  let phi =
    Construct.apply_sub_ps pad (Construct.characteristic_sub_ps (V.a_constr n))
  in
  let phi_op =
    Construct.apply_sub_ps (Construct.op [ 1 ] pad)
      (Construct.characteristic_sub_ps (V.b_constr n))
  in
  Construct.wcomp phi (n - 1) phi_op

let second_step_gt n =
  let r = BToU.repad n n in
  let repad_a = Construct.tm_app r (gamma_i_l_to_eh_a n 0) in
  let repad_b =
    Construct.tm_app (Opposite.checked_tm r [ 1 ]) (gamma_i_l_to_eh_b n 0)
  in
  Construct.wcomp repad_a (n - 1) repad_b

let third_step_lt n =
  let r = FToU.repad n n in
  let repad_a = Construct.tm_app r (gamma_i_l_to_eh_a n (n - 1)) in
  let repad_b =
    Construct.tm_app (Opposite.checked_tm r [ 1 ]) (gamma_i_l_to_eh_b n (n - 1))
  in
  Construct.wcomp repad_a (n - 1) repad_b

let func_v_to_zeta n =
  [
    (UP.v_bridge, (Construct.to_tm @@ zeta n, true));
    ( UP.v_plus,
      (Construct.to_tm @@ Construct.wcomp (V.a_constr n) 0 (V.b_constr n), false)
    );
    ( UP.v,
      ( Construct.to_tm
        @@ Construct.wcomp (a_comp_id n 0) (n - 1) (id_comp_b n 0),
        false ) );
    (x, (Var x, false));
  ]

let fourth_step_gt n =
  Construct.tm_app
    (Functorialisation.tm (UP.padded n (n - 1) 0) [ (UP.v, 1) ])
    (func_v_to_zeta n)

let eh_gt n =
  Construct.comp_n
    [ first_step_gt n; second_step_gt n; PSU.xi_gt n; fourth_step_gt n ]

let eh_lt n =
  Construct.comp_n
    [ zeta_inv n; second_step_lt n; third_step_lt n; PSU.xi_lt n ]

let swap_a_and_b n =
  [
    (V.b n, (Var (V.a n), true));
    (V.a n, (Var (V.b n), true));
    (x, (Var x, false));
  ]

let suspended_point_to_point () =
  [
    (x, (Construct.to_tm @@ Construct.id_n 1 V.x_constr, true));
    (Var.Db 1, (Var x, false));
    (Var.Db 0, (Var x, false));
  ]

let rec repad_suspended n k l i =
  let m = min k l + 1 in
  if i = m then Construct.id_n 1 (UP.v_constr i l)
  else
    let i = i - 1 in
    let p_u_minus, q_u_minus = UP.u (i - 1) (k - 1) (l - 1) in
    let p_s =
      Construct.apply_sub
        (Construct.suspend 1 p_u_minus)
        (suspended_point_to_point ())
    in
    let q_s =
      Construct.apply_sub
        (Construct.suspend 1 q_u_minus)
        (suspended_point_to_point ())
    in
    let p_u, q_u = UP.u i k l in
    let previous_repadding = repad_suspended n k l i in
    let iota_m = UP.in_minus in
    let iota_p = UP.in_plus in
    let sigma = UP.sub (i + 1) l in
    let f_type =
      Construct.arr
        (Construct.wcomp p_s i
           (Construct.apply_sub
              (Construct.apply_sub previous_repadding iota_m)
              sigma))
        p_u
    in
    let g_type =
      Construct.arr q_s
        (Construct.wcomp
           (Construct.apply_sub
              (Construct.apply_sub previous_repadding iota_p)
              sigma)
           i q_u)
    in
    let f =
      ( Coh
          ( check_coh (Br [])
              (Unchecked.ty_rename f_type [ (x, Var (Var.Db 0)) ])
              ( "f^" ^ string_of_int i ^ "_(" ^ string_of_int n ^ ","
                ^ string_of_int k ^ "," ^ string_of_int l ^ ")",
                0,
                [] ),
            [ (Var x, true) ] ),
        f_type )
    in
    let g =
      ( Coh
          ( check_coh (Br [])
              (Unchecked.ty_rename g_type [ (x, Var (Var.Db 0)) ])
              ( "g^" ^ string_of_int i ^ "_(" ^ string_of_int n ^ ","
                ^ string_of_int k ^ "," ^ string_of_int l ^ ")",
                0,
                [] ),
            [ (Var x, true) ] ),
        g_type )
    in
    Padding.repad_old p_s p_u f q_s q_u g previous_repadding iota_m iota_p UP.v
      sigma

let gamma_i_l_to_a_comp_b n l =
  [
    ( UP.v,
      (Construct.to_tm @@ Construct.wcomp (V.a_constr n) l (V.b_constr n), true)
    );
    (x, (Var x, false));
  ]

let eh_suspended_to_eh n =
  [
    (V.b n, (Var (V.b (n + 1)), true));
    (V.a n, (Var (V.a (n + 1)), true));
    (x, (Construct.to_tm @@ Construct.id_n 1 V.x_constr, false));
    (Var.Db 1, (Var x, false));
    (Var.Db 0, (Var x, false));
  ]

let suspension_move eh_minus n k l =
  let suspended_eh =
    Construct.apply_sub
      (Construct.suspend 1 eh_minus)
      (eh_suspended_to_eh (n - 1))
  in
  Construct.comp_n
    [
      suspended_eh;
      Construct.apply_sub (repad_suspended n k l n) (gamma_i_l_to_a_comp_b n l);
    ]

let nat_unitor constr =
  let x_constr = (Var (Var.Db 0), Obj) in
  let y_constr = (Var (Var.Db 1), Obj) in
  let f_constr = (Var (Var.Db 2), Construct.arr x_constr y_constr) in
  let cohty =
    Construct.arr f_constr
      (Construct.comp_n [ f_constr; Construct.id_n 1 y_constr ])
  in
  let runit = check_coh (Unchecked.disc 1) cohty ("unitor_-_to_-id", 0, []) in
  let d = Construct.dim constr in
  let sub = Construct.characteristic_sub_ps constr in
  ( Coh (Suspension.coh (Some (d - 1)) runit, sub),
    Unchecked.ty_apply_sub_ps (Suspension.ty (Some (d - 1)) cohty) sub )

let nat_factor prev_eh n k l =
  let db0 = (Var (Var.Db 0), Obj) in
  let idnx = Construct.id_n n db0 in
  let lhs = Construct.id_n 1 (Construct.wcomp idnx k idnx) in
  let eh_to_id =
    [
      (V.b n, (Construct.to_tm idnx, true));
      (V.a n, (Construct.to_tm idnx, true));
      (x, (Var (Var.Db 0), false));
    ]
  in
  let _, q_n = UP.u n k l in
  let rhs =
    Construct.comp_n
      [
        Construct.apply_sub prev_eh eh_to_id;
        Construct.rename q_n [ (x, Var (Var.Db 0)) ];
      ]
  in
  let cohty = Construct.arr lhs rhs in
  let coherence =
    check_coh (Unchecked.disc 0) cohty
      ( "factor_identity^" ^ string_of_int n ^ "_(" ^ string_of_int k ^ ","
        ^ string_of_int l ^ ")",
        0,
        [] )
  in
  Construct.of_coh coherence

let nat_associator1 constr1 constr2 constr3 =
  let f1 = (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) in
  let f2 = (Var (Var.Db 4), Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))) in
  let f3 = (Var (Var.Db 6), Arr (Obj, Var (Var.Db 3), Var (Var.Db 5))) in
  let cohty =
    Construct.arr
      (Construct.comp_n [ f1; Construct.comp_n [ f2; f3 ] ])
      (Construct.comp_n [ Construct.comp_n [ f1; f2 ]; f3 ])
  in
  let coherence =
    check_coh (Br [ Br []; Br []; Br [] ]) cohty ("assoc_-(--)_to_(--)-", 0, [])
  in
  let d = Construct.dim constr1 in
  let sub =
    Construct.characteristic_sub_ps_composite [ constr1; constr2; constr3 ]
  in
  ( Coh (Suspension.coh (Some (d - 1)) coherence, sub),
    Unchecked.ty_apply_sub_ps (Suspension.ty (Some (d - 1)) cohty) sub )

let nat_associator2 constr1 constr2 constr3 =
  let f1 = (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) in
  let f2 = (Var (Var.Db 4), Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))) in
  let f3 = (Var (Var.Db 6), Arr (Obj, Var (Var.Db 3), Var (Var.Db 5))) in
  let cohty =
    Construct.arr
      (Construct.comp_n [ Construct.comp_n [ f1; f2 ]; f3 ])
      (Construct.comp_n [ f1; f2; f3 ])
  in
  let coherence =
    check_coh (Br [ Br []; Br []; Br [] ]) cohty ("assoc_(--)-_to_---", 0, [])
  in
  let d = Construct.dim constr1 in
  let sub =
    Construct.characteristic_sub_ps_composite [ constr1; constr2; constr3 ]
  in
  ( Coh (Suspension.coh (Some (d - 1)) coherence, sub),
    Unchecked.ty_apply_sub_ps (Suspension.ty (Some (d - 1)) cohty) sub )

let nat_finalcoh prev_eh n k l =
  let db0 = (Var (Var.Db 0), Obj) in
  let idnx = Construct.id_n n db0 in
  let eh_to_id =
    [
      (V.b n, (Construct.to_tm idnx, true));
      (V.a n, (Construct.to_tm idnx, true));
      (x, (Var (Var.Db 0), false));
    ]
  in
  let p_n, _ = UP.u n k l in
  let lhs = Construct.apply_sub prev_eh eh_to_id in
  let rhs = Construct.rename p_n [ (x, Var (Var.Db 0)) ] in
  let cohty = Construct.arr lhs rhs in
  let coherence =
    check_coh (Unchecked.disc 0) cohty
      ( "eh_to_p^" ^ string_of_int n ^ "_(" ^ string_of_int k ^ ","
        ^ string_of_int l ^ ")",
        0,
        [] )
  in
  Construct.of_coh coherence

let eh_func_to_eh n =
  [
    (Var.Bridge (V.b n), (Var (V.b (n + 1)), true));
    (Var.Plus (V.b n), (Construct.to_tm @@ V.id n, false));
    (V.b n, (Construct.to_tm @@ V.id n, false));
    (Var.Bridge (V.a n), (Var (V.a (n + 1)), true));
    (Var.Plus (V.a n), (Construct.to_tm @@ V.id n, false));
    (V.a n, (Construct.to_tm @@ V.id n, false));
    (x, (Var x, false));
  ]

let gamma_i_l_func_to_a_comp_b n l =
  [
    ( UP.v_bridge,
      ( Construct.to_tm
        @@ Construct.wcomp (V.a_constr (n + 1)) l (V.b_constr (n + 1)),
        true ) );
    (UP.v_plus, (Construct.to_tm @@ UP.id2 n l, false));
    (UP.v, (Construct.to_tm @@ UP.id2 n l, false));
    (x, (Var x, false));
  ]

let naturality_move prev_eh n k l =
  let a_k_b = Construct.wcomp (V.a_constr (n + 1)) k (V.b_constr (n + 1)) in
  let _, q_n = UP.u n k l in
  let idnx = V.id n in
  let eh_to_id =
    [
      (V.b n, (Construct.to_tm idnx, true));
      (V.a n, (Construct.to_tm idnx, true));
      (x, (Var x, false));
    ]
  in
  let nat =
    Construct.inverse
      (Construct.apply_sub
         (Construct.functorialise prev_eh [ V.b n; V.a n ])
         (eh_func_to_eh n))
  in
  let paddedfunc =
    Construct.tm_app
      (Functorialisation.tm (UP.padded n k l) [ (UP.v, 1) ])
      (gamma_i_l_func_to_a_comp_b n l)
  in
  let eh_id_id = Construct.apply_sub prev_eh eh_to_id in
  Construct.comp_n
    [
      nat_unitor a_k_b;
      Construct.wcomp a_k_b n (nat_factor prev_eh n k l);
      nat_associator1 a_k_b eh_id_id q_n;
      Construct.wcomp nat n q_n;
      nat_associator2 eh_id_id paddedfunc q_n;
      Construct.wcomp_n n [ nat_finalcoh prev_eh n k l; paddedfunc; q_n ];
    ]

let rec eh n k l =
  if k = 0 && l = n - 1 then eh_lt n
  else if k = n - 1 && l = 0 then eh_gt n
  else if max k l = n - 1 then
    suspension_move (eh (n - 1) (k - 1) (l - 1)) n k l
  else naturality_move (eh (n - 1) k l) (n - 1) k l

let full_eh n k l =
  let ehnkl = eh n k l in
  Construct.comp_n
    [
      ehnkl;
      Construct.inverse
        (Construct.apply_sub (Construct.op [ l + 1 ] ehnkl) (swap_a_and_b n));
    ]

let eh_Tm n k l =
  let tm = Construct.to_tm @@ eh n k l in
  let checked_ctx = Ctx.check @@ V.ctx n in
  check_term checked_ctx ~name:(Printf.sprintf "eh^%d_(%d,%d)" n k l, 0, []) tm

let full_eh_Tm n k l =
  let tm = Construct.to_tm @@ full_eh n k l in
  let checked_ctx = Ctx.check @@ V.ctx n in
  check_term checked_ctx
    ~name:(Printf.sprintf "EH^%d_(%d,%d)" n k l, 0, [])
    ~ty:
      (Construct.arr
         (Construct.wcomp (V.a_constr n) k (V.b_constr n))
         (Construct.wcomp (V.b_constr n) k (V.a_constr n)))
    tm
