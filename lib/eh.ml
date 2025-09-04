open Std
open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

module type EHArgsS = sig
  val n : int
  val k : int
  val l : int
end

module type BiasedPaddingArgsS = sig
  val n : int
end

module UnbiasedPadding (Args : EHArgsS) = Padding.Padding.MakeCanonical (struct
  let x = Var.Db 0
  let x_constr = (Var x, Obj)

  let id2 i j =
    let id = Construct.id_n i (Var x, Obj) in
    if j < i then Construct.wcomp id j id else id

  let id_l_id i = id2 i Args.l

  module F = Padding.Filtration.Make (struct
    let min = Int.min Args.k Args.l + 1
    let max = Args.n
    let v _ = Var.Db 1
    let ty i = Construct.arr (id_l_id i) (id_l_id i)
    let ctx i = [ (v i, (ty (i - 1), true)); (x, (Obj, false)) ]
  end)

  module D = struct
    let ps _ = Unchecked.disc 0
    let p_src i = id2 i Args.k
    let q_tgt i = id2 i Args.k
    let p_inc _ = [ x_constr ]
    let q_inc _ = [ x_constr ]

    let pad_in_ps i =
      [ (F.v i, (Construct.to_tm (id_l_id i), true)); (x, (Var x, false)) ]
  end
end)

(* Find a good place for these *)
let d_src i = (Var (Var.Db (2 * i)), Unchecked.disc_type i)
let d_tgt i = (Var (Var.Db ((2 * i) + 1)), Unchecked.disc_type i)

let t_comp_id d t =
  if d = 0 then t else Construct.(wcomp t 0 (id_n d (d_tgt 0)))

module ForwardBiasedPadding (Args : BiasedPaddingArgsS) =
Padding.Padding.MakeCanonical (struct
  module F = Padding.Filtration.Make (struct
    let min = 1
    let max = Args.n
    let ctx i = Unchecked.ps_to_ctx (Unchecked.disc i)
    let v i = Var.Db (2 * i)
  end)

  module D = struct
    let ps _ = Unchecked.disc 0
    let p_src i = t_comp_id i (F.src_v i)
    let q_tgt i = t_comp_id i (F.src_v i)
    let p_inc i = [ (Var (Var.Db (2 * i)), Unchecked.disc_type i) ]
    let q_inc i = [ (Var (Var.Db ((2 * i) + 1)), Unchecked.disc_type i) ]
    let pad_in_ps i = Unchecked.(identity (ps_to_ctx (ps i)))
  end
end)

module BackwardBiasedPadding (Args : BiasedPaddingArgsS) =
Padding.Padding.MakeCanonical (struct
  module F = Padding.Filtration.Make (struct
    let min = 1
    let max = Args.n
    let ty_v i = Construct.arr (t_comp_id i (d_src i)) (t_comp_id i (d_tgt i))
    let v i = Var.Db (2 * i)
    let ctx i = (v i, (ty_v (i - 1), true)) :: Unchecked.sphere (i - 1)
  end)

  module D = struct
    let ps i = Unchecked.disc i
    let p_src i = d_src i
    let q_tgt i = d_src i
    let p_inc i = [ d_src i ]
    let q_inc i = [ d_tgt i ]

    let pad_in_ps i =
      (F.v i, (Construct.to_tm (F.src_v (i + 1)), true))
      :: Unchecked.(identity (sphere (i - 1)))
  end
end)

let sphere_to_point i =
  let id_pt i = Construct.(to_tm (id_n i (Var (Var.Db 0), Obj))) in
  let rec aux = function
    | -1 -> []
    | i ->
        (Var.Db ((2 * i) + 1), (id_pt i, false))
        :: (Var.Db (2 * i), (id_pt i, false))
        :: aux (i - 1)
  in
  aux i

module ForwardToUnbiasedRepadding (Args : BiasedPaddingArgsS) =
Padding.Repadding.MakeCanonical (struct
  module EHArgs = struct
    let n = Args.n
    let k = 0
    let l = n - 1
  end

  module P2 = UnbiasedPadding (EHArgs)
  module FP = ForwardBiasedPadding (Args)

  module M : Padding.FiltrationMorphismS = struct
    let sub i = (FP.F.v i, (Var (P2.F.v i), true)) :: sphere_to_point (i - 1)
  end

  module P1 = Padding.PaddingApp (P2.F) (M) (FP)

  module D = struct
    let ps _ = Br []
    let incl _ = [ (Var (Var.Db 0), Obj) ]
  end
end)

module BackwardToUnbiasedRepadding (Args : BiasedPaddingArgsS) =
Padding.Repadding.MakeCanonical (struct
  module EHArgs = struct
    let n = Args.n
    let k = n - 1
    let l = 0
  end

  module P2 = UnbiasedPadding (EHArgs)
  module BP = BackwardBiasedPadding (Args)

  module M : Padding.FiltrationMorphismS = struct
    let sub i = (BP.F.v i, (Var (P2.F.v i), true)) :: sphere_to_point (i - 1)
  end

  module P1 = Padding.PaddingApp (P2.F) (M) (BP)

  module D = struct
    let ps _ = Br []
    let incl _ = [ (Var (Var.Db 0), Obj) ]
  end
end)

module PseudoFunctorialityUnbiasedPadding (Args : EHArgsS) = struct
  module UP = UnbiasedPadding (Args)

  let x = Var.Db 0
  let w = Var.Db 2
  let ty = snd UP.v_constr
  let ctx = (w, (ty, true)) :: UP.ctx
  let w_constr = (Var w, ty)
  let v = UP.v
  let v_plus = UP.v_plus
  let v_bridge = UP.v_bridge
  let v_constr = UP.v_constr

  module LTree = struct
    (* TODO: move this module somewhere else *)
    let tdb i = Var (Var.Db i)
    let tree i = Br (List.init i (fun _ -> Br []))
    let x i = if i = 0 then (tdb 0, Obj) else (tdb ((2 * i) - 1), Obj)
    let f i = (tdb (2 * i), Arr (Obj, fst @@ x (i - 1), fst @@ x i))
  end

  let assoc n =
    let tree = LTree.tree 6 in
    let f i = LTree.f i in
    let ty =
      Construct.(
        arr
          (wcomp (comp3 (f 1) (f 2) (f 3)) 0 (comp3 (f 4) (f 5) (f 6)))
          (comp3 (f 1) (comp3 (f 2) (wcomp (f 3) 0 (f 4)) (f 5)) (f 6)))
    in
    Suspension.coh (Some n) (check_coh tree ty ("_builtin_assoc", 0, []))

  let unitor n =
    let tree = LTree.tree 2 in
    let f i = LTree.f i in
    let x i = LTree.x i in
    let ty =
      Construct.(arr (comp3 (f 1) (id_n 1 (x 1)) (f 2)) (wcomp (f 1) 0 (f 2)))
    in
    Suspension.coh (Some n) (check_coh tree ty ("_builtin_unitor", 0, []))

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

  let rec witness_aux_gt i =
    let m = UP.F.min in
    let n = UP.F.max in
    let v_c = v_constr in
    let w_c = w_constr in
    let witness_constr =
      match i with
      | i when i = m -> Construct.id_n 1 (Construct.wcomp v_c (n - 1) w_c)
      | i when 1 < i -> (
          let p, q = (UP.D.p (i - 1), UP.D.q (i - 1)) in
          let p, q = (Tm.constr p, Tm.constr q) in
          let t = UP.padded_func (i - 1) (n - i + 1) in
          let tv = Tm.constr t in
          let w_sub = [ (v, (Var w, true)); (x, (Var x, false)) ] in
          let tw = Construct.tm_app t w_sub in
          match i with
          | i when i < n ->
              let intch =
                Construct.coh_app (intch (n - i) (i - 1)) [ p; tv; tw; q ]
              in
              Construct.wcomp intch n
                (Construct.wcomp_n (i - 1)
                   [ p; Tm.constr (witness_aux_gt (i - 1)); q ])
          | i when i == n ->
              let assoc =
                Construct.coh_app (assoc (n - 1)) [ p; tv; q; p; tw; q ]
              in
              let w = Construct.witness q in
              let unitor = Construct.coh_app (unitor (n - 1)) [ tv; tw ] in
              Construct.comp_n
                [
                  assoc;
                  Construct.wcomp_n (n - 1)
                    [ p; Construct.wcomp_n (n - 1) [ tv; w; tw ]; q ];
                  Construct.wcomp_n (n - 1) [ p; unitor; q ];
                  Construct.wcomp_n (n - 1)
                    [ p; Tm.constr (witness_aux_gt (n - 1)); q ];
                ]
          | _ ->
              Error.fatal
                "[EH] Wrong arguments in pseudofunctoriality of padding")
      | _ ->
          Error.fatal "[EH] Wrong arguments in pseudofunctoriality of padding"
    in
    check_constr ctx witness_constr

  let witness_gt = witness_aux_gt Args.n
end

module EHCtx (Args : EHArgsS) = struct
  let x = Var.Db 0
  let a = Var.Db 1
  let b = Var.Db 2
  let id = Construct.id_n (Args.n - 1) (Var x, Obj)
  let ty = Construct.arr id id
  let ctx = [ (b, (ty, true)); (a, (ty, true)); (x, (Obj, false)) ]
  let x_constr = (Var x, Obj)
  let a_constr = (Var a, ty)
  let b_constr = (Var b, ty)

  let a_comp_id =
    if Args.l = Args.n - 1 then a_constr
    else Construct.wcomp a_constr Args.l (Construct.id_n 1 id)

  let id_comp_b =
    if Args.l = Args.n - 1 then b_constr
    else Construct.wcomp (Construct.id_n 1 id) Args.l b_constr
end

module type EHBaseCaseGTArgsS = sig
  val n : int
end

module EHBaseCaseGT (Args : EHBaseCaseGTArgsS) = struct
  module EHArgs = struct
    let n = Args.n
    let k = n - 1
    let l = 0
  end

  module C = EHCtx (EHArgs)
  module UP = UnbiasedPadding (EHArgs)
  module BP = BackwardBiasedPadding (Args)
  module BToU = BackwardToUnbiasedRepadding (Args)
  module PSU = PseudoFunctorialityUnbiasedPadding (EHArgs)

  (* TODO: inline the steps here *)
  let step1 =
    let p = BP.p in
    let a_padded =
      Construct.(
        tm_app p (Unchecked.sub_ps_to_sub (characteristic_sub_ps C.a_constr)))
    in
    let b_padded =
      Construct.(
        tm_app
          (Opposite.checked_tm p [ 1 ])
          (Unchecked.sub_ps_to_sub (characteristic_sub_ps C.b_constr)))
    in
    (* TODO: there should be a fix here so that there is no need for the develop *)
    Construct.(develop (wcomp a_padded (Args.n - 1) b_padded))

  let a_comp_id_sub =
    [ (UP.v, (Construct.to_tm C.a_comp_id, true)); (C.x, (Var C.x, false)) ]

  let id_comp_b_sub =
    [ (UP.v, (Construct.to_tm C.id_comp_b, true)); (C.x, (Var C.x, false)) ]

  let step2 =
    let r = BToU.repadded in
    let r_op = Opposite.checked_tm r [ 1 ] in
    let repad_a = Construct.tm_app r a_comp_id_sub in
    let repad_b = Construct.tm_app r_op id_comp_b_sub in
    Construct.wcomp repad_a (Args.n - 1) repad_b

  let step3 =
    let sub =
      [
        (PSU.w, (Construct.to_tm C.id_comp_b, false));
        (PSU.v, (Construct.to_tm C.a_comp_id, false));
        (PSU.x, (Var C.x, false));
      ]
    in
    Construct.tm_app PSU.witness_gt sub

  let step4 =
    let n = Args.n in
    let intch =
      let tree = Br [ Unchecked.disc (n - 1); Unchecked.disc (n - 1) ] in
      let rec sphere_l = function
        | -1 -> Obj
        | k ->
            Arr
              ( sphere_l (k - 1),
                Var (Var.Db (2 * k)),
                Var (Var.Db ((2 * k) + 1)) )
      in
      let rec sphere_r = function
        | -1 -> Obj
        | 0 -> Arr (Obj, Var (Var.Db 1), Var (Var.Db ((2 * n) + 1)))
        | k ->
            Arr
              ( sphere_r (k - 1),
                Var (Var.Db ((2 * n) + (2 * k))),
                Var (Var.Db ((2 * n) + (2 * k) + 1)) )
      in
      let d_l = (Var (Var.Db (2 * n)), sphere_l (n - 1)) in
      let d_r = (Var (Var.Db (4 * n)), sphere_r (n - 1)) in
      let cohty =
        Construct.arr
          (Construct.wcomp
             (Construct.wcomp d_l 0 (Construct.id_n 1 (Construct.src 1 d_r)))
             (n - 1)
             (Construct.wcomp (Construct.id_n 1 (Construct.tgt 1 d_l)) 0 d_r))
          (Construct.wcomp d_l 0 d_r)
      in
      check_coh tree cohty ("zeta^" ^ string_of_int n, 0, [])
    in
    let zeta = Construct.coh_app intch [ C.a_constr; C.b_constr ] in
    let sub =
      [
        (UP.v_bridge, (Construct.to_tm zeta, true));
        ( UP.v_plus,
          (Construct.to_tm @@ Construct.wcomp C.a_constr 0 C.b_constr, false) );
        ( UP.v,
          ( Construct.to_tm
            @@ Construct.wcomp C.a_comp_id (Args.n - 1) C.id_comp_b,
            false ) );
        (C.x, (Var C.x, false));
      ]
    in
    Construct.tm_app (Functorialisation.tm UP.padded [ (UP.v, 1) ]) sub

  let eh_gt = Construct.comp_n [ step1; step2; step3; step4 ]
end

(* TODO: replace all instances of drop by a Construct.sub_ps_builder *)
(* let drop n xs = *)
(*   let rec aux xs counter = *)
(*     match xs with *)
(*     | [] -> [] *)
(*     | h :: tl -> if counter > 0 then h :: aux tl (counter - 1) else [] *)
(*   in *)
(*   aux xs (List.length xs - n) *)

(* module V = EHBaseCases *)

(* let x = V.x *)

(* let rec sphere_type_db = function *)
(*   | -1 -> Obj *)
(*   | n -> *)
(*       Arr *)
(*         ( sphere_type_db @@ (n - 1), *)
(*           Var (Var.Db (2 * n)), *)
(*           Var (Var.Db ((2 * n) + 1)) ) *)

(* let d_n_constr n = (Var (Var.Db (2 * n)), sphere_type_db (n - 1)) *)
(* let whisker left middle right = Construct.wcomp_n 0 [ left; middle; right ] *)

(* let intch_n_h n h = *)
(*   let d_1_L_constr = *)
(*     (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) *)
(*   in *)
(*   let d_1_R_constr = *)
(*     ( Var (Var.Db ((2 * n) + (2 * h) + 4)), *)
(*       Arr (Obj, Var (Var.Db 3), Var (Var.Db ((2 * n) + (2 * h) + 3))) ) *)
(*   in *)
(*   let rec adj_sphere_type k = *)
(*     if k = 0 then Arr (Obj, Var (Var.Db 1), Var (Var.Db 3)) *)
(*     else *)
(*       Arr *)
(*         ( adj_sphere_type (k - 1), *)
(*           Var (Var.Db ((2 * k) + 2)), *)
(*           Var (Var.Db ((2 * k) + 3)) ) *)
(*   in *)
(*   let d_n_constr i = *)
(*     if i = 0 then (Var (Var.Db (2 + (2 * n))), adj_sphere_type (n - 1)) *)
(*     else (Var (Var.Db (1 + (2 * n) + (2 * i))), adj_sphere_type (n - 1)) *)
(*   in *)
(*   let d_nplus1_i_constr i = *)
(*     ( Var (Var.Db (2 + (2 * n) + (2 * i))), *)
(*       Construct.arr (d_n_constr (i - 1)) (d_n_constr i) ) *)
(*   in *)
(*   let rec middle_constrs r = *)
(*     if r = h + 1 then [] else d_nplus1_i_constr r :: middle_constrs (r + 1) *)
(*   in *)
(*   let rec middle_whiskered r = *)
(*     if r = h + 1 then [] *)
(*     else *)
(*       whisker d_1_L_constr (d_nplus1_i_constr r) d_1_R_constr *)
(*       :: middle_whiskered (r + 1) *)
(*   in *)
(*   let rec chain = function 0 -> [] | h -> Br [] :: chain (h - 1) in *)
(*   let rec tower xs = function 0 -> Br xs | n -> Br [ tower xs (n - 1) ] in *)
(*   let intch_ctx_db = Br [ Br []; tower (chain h) (n - 1); Br [] ] in *)
(*   let coh_type = *)
(*     Construct.arr *)
(*       (Construct.comp_n @@ middle_whiskered 1) *)
(*       (whisker d_1_L_constr (Construct.comp_n @@ middle_constrs 1) d_1_R_constr) *)
(*   in *)
(*   ( check_coh intch_ctx_db coh_type *)
(*       ("chi^" ^ string_of_int n ^ "_" ^ string_of_int h, 0, []), *)
(*     coh_type ) *)

(* (\* TODO: Fix this function *\) *)
(* let rec padded_n_k_l_func_r n k l = function *)
(*   | 1 -> Construct.of_tm (Functorialisation.tm (UP.padded n k l) [ (UP.v, 1) ]) *)
(*   | r -> *)
(*       Construct.functorialise *)
(*         (Construct.apply_sub *)
(*            (padded_n_k_l_func_r n k l (r - 1)) *)
(*            (UP.sub (n + r - 1) l)) *)
(*         [ UP.v ] *)

(* let a_comp_id i l = *)
(*   if l = i - 1 then V.a_constr i *)
(*   else Construct.wcomp (V.a_constr i) l (Construct.id_n i V.x_constr) *)

(* let id_comp_b i l = *)
(*   if l = i - 1 then V.b_constr i *)
(*   else Construct.wcomp (Construct.id_n i V.x_constr) l (V.b_constr i) *)

(* let gamma_i_l_to_eh_a i l = *)
(*   [ (UP.v, (Construct.to_tm @@ a_comp_id i l, true)); (x, (Var x, false)) ] *)

(* let gamma_i_l_to_eh_b i l = *)
(*   [ (UP.v, (Construct.to_tm @@ id_comp_b i l, true)); (x, (Var x, false)) ] *)

(* let gamma_iminus1_l_func_to_eh_a i l = *)
(*   [ *)
(*     (UP.v_bridge, (Construct.to_tm @@ a_comp_id i l, true)); *)
(*     (UP.v_plus, (Construct.to_tm @@ UP.id2 (i - 1) l, false)); *)
(*     (UP.v, (Construct.to_tm @@ UP.id2 (i - 1) l, false)); *)
(*     (x, (Var x, false)); *)
(*   ] *)

(* let gamma_iminus1_l_func_to_eh_b i l = *)
(*   [ *)
(*     (UP.v_bridge, (Construct.to_tm @@ id_comp_b i l, true)); *)
(*     (UP.v_plus, (Construct.to_tm @@ UP.id2 (i - 1) l, false)); *)
(*     (UP.v, (Construct.to_tm @@ UP.id2 (i - 1) l, false)); *)
(*     (x, (Var x, false)); *)
(*   ] *)

(* module PseudoFunctoriality = struct *)
(*   let w = Var.Db 2 *)
(*   let ctx n l = (w, (UP.ty n l, true)) :: UP.ctx n l *)
(*   let w_constr n l = (Var w, UP.ty n l) *)

(*   let rec xi_n_i_lt n i = *)
(*     match i with *)
(*     | 1 -> *)
(*         Construct.id_n 1 *)
(*           (Construct.wcomp (a_comp_id n (n - 1)) (n - 1) (id_comp_b n (n - 1))) *)
(*     | i -> *)
(*         let p, q = UP.u (i - 1) 0 (n - 1) in *)
(*         let sub = *)
(*           drop ((2 * i) - 1) (Construct.characteristic_sub_ps q) *)
(*           @ drop *)
(*               ((2 * n) - 1) *)
(*               (Construct.characteristic_sub_ps *)
(*                  (Construct.apply_sub *)
(*                     (padded_n_k_l_func_r (i - 1) 0 (n - 1) (n - i + 1)) *)
(*                     (gamma_iminus1_l_func_to_eh_b n (n - 1)))) *)
(*           @ drop *)
(*               ((2 * i) - 1) *)
(*               (Construct.characteristic_sub_ps *)
(*                  (Construct.apply_sub *)
(*                     (padded_n_k_l_func_r (i - 1) 0 (n - 1) (n - i + 1)) *)
(*                     (gamma_iminus1_l_func_to_eh_a n (n - 1)))) *)
(*           @ Construct.characteristic_sub_ps p *)
(*         in *)
(*         let chi, chi_ty = intch_n_h (n - i) 2 in *)
(*         let chi_applied = *)
(*           ( Coh (Suspension.coh (Some (i - 1)) chi, sub), *)
(*             Unchecked.ty_apply_sub_ps (Suspension.ty (Some (i - 1)) chi_ty) sub *)
(*           ) *)
(*         in *)
(*         Construct.wcomp chi_applied n *)
(*           (Construct.wcomp_n (i - 1) [ p; xi_n_i_lt n (i - 1); q ]) *)

(*   let rec xi_n_i_gt n i = *)
(*     match i with *)
(*     | 1 -> *)
(*         Construct.id_n 1 *)
(*           (Construct.wcomp (a_comp_id n 0) (n - 1) (id_comp_b n 0)) *)
(*     | i -> *)
(*         let p, q = UP.u (i - 1) (n - 1) 0 in *)
(*         let sub = *)
(*           drop ((2 * i) - 1) (Construct.characteristic_sub_ps q) *)
(*           @ drop *)
(*               ((2 * n) - 1) *)
(*               (Construct.characteristic_sub_ps *)
(*                  (Construct.apply_sub *)
(*                     (padded_n_k_l_func_r (i - 1) (n - 1) 0 (n - i + 1)) *)
(*                     (gamma_iminus1_l_func_to_eh_b n 0))) *)
(*           @ drop *)
(*               ((2 * i) - 1) *)
(*               (Construct.characteristic_sub_ps *)
(*                  (Construct.apply_sub *)
(*                     (padded_n_k_l_func_r (i - 1) (n - 1) 0 (n - i + 1)) *)
(*                     (gamma_iminus1_l_func_to_eh_a n 0))) *)
(*           @ Construct.characteristic_sub_ps p *)
(*         in *)
(*         let chi, chi_ty = intch_n_h (n - i) 2 in *)
(*         let chi_applied = *)
(*           ( Coh (Suspension.coh (Some (i - 1)) chi, sub), *)
(*             Unchecked.ty_apply_sub_ps (Suspension.ty (Some (i - 1)) chi_ty) sub *)
(*           ) *)
(*         in *)
(*         Construct.wcomp chi_applied n *)
(*           (Construct.wcomp_n (i - 1) [ p; xi_n_i_gt n (i - 1); q ]) *)

(*   let assoc_33_to_middle2 () = *)
(*     let tree = Br [ Br []; Br []; Br []; Br []; Br []; Br [] ] in *)
(*     let f1 = (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) in *)
(*     let f2 = (Var (Var.Db 4), Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))) in *)
(*     let f3 = (Var (Var.Db 6), Arr (Obj, Var (Var.Db 3), Var (Var.Db 5))) in *)
(*     let f4 = (Var (Var.Db 8), Arr (Obj, Var (Var.Db 5), Var (Var.Db 7))) in *)
(*     let f5 = (Var (Var.Db 10), Arr (Obj, Var (Var.Db 7), Var (Var.Db 9))) in *)
(*     let f6 = (Var (Var.Db 12), Arr (Obj, Var (Var.Db 9), Var (Var.Db 11))) in *)
(*     let cohty = *)
(*       Construct.arr *)
(*         (Construct.wcomp (Construct.comp3 f1 f2 f3) 0 (Construct.comp3 f4 f5 f6)) *)
(*         (Construct.comp3 f1 *)
(*            (Construct.comp3 f2 (Construct.wcomp f3 0 f4) f5) *)
(*            f6) *)
(*     in *)
(*     ( Coh *)
(*         ( check_coh tree cohty ("assoc_(---)(---)_to_-(-(--)-)-", 0, []), *)
(*           Unchecked.identity_ps tree ), *)
(*       cohty ) *)

(*   let middle_unitor () = *)
(*     let tree = Br [ Br []; Br [] ] in *)
(*     let f1 = (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) in *)
(*     let f2 = (Var (Var.Db 4), Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))) in *)
(*     let x1 = (Var (Var.Db 1), Obj) in *)
(*     let cohty = *)
(*       Construct.arr *)
(*         (Construct.comp3 f1 (Construct.id_n 1 x1) f2) *)
(*         (Construct.wcomp f1 0 f2) *)
(*     in *)
(*     ( Coh *)
(*         ( check_coh tree cohty ("unitor_-id-_to_--", 0, []), *)
(*           Unchecked.identity_ps tree ), *)
(*       cohty ) *)

(*   let xi_lt n = *)
(*     let p, q = UP.u (n - 1) 0 (n - 1) in *)
(*     let padded_a = *)
(*       Construct.apply_sub *)
(*         (padded_n_k_l_func_r (n - 1) 0 (n - 1) 1) *)
(*         (gamma_iminus1_l_func_to_eh_a n (n - 1)) *)
(*     in *)
(*     let padded_b = *)
(*       Construct.apply_sub *)
(*         (padded_n_k_l_func_r (n - 1) 0 (n - 1) 1) *)
(*         (gamma_iminus1_l_func_to_eh_b n (n - 1)) *)
(*     in *)
(*     let sub6 = *)
(*       (Construct.to_tm q, true) *)
(*       :: (Construct.to_tm @@ Construct.tgt 1 q, false) *)
(*       :: (Construct.to_tm padded_b, true) *)
(*       :: (Construct.to_tm @@ Construct.tgt 1 padded_b, false) *)
(*       :: (Construct.to_tm p, true) *)
(*       :: (Construct.to_tm @@ Construct.tgt 1 p, false) *)
(*       :: (Construct.to_tm q, true) *)
(*       :: (Construct.to_tm @@ Construct.tgt 1 q, false) *)
(*       :: (Construct.to_tm padded_a, true) *)
(*       :: (Construct.to_tm @@ Construct.tgt 1 padded_a, false) *)
(*       :: Construct.characteristic_sub_ps p *)
(*     in *)
(*     let assoc = *)
(*       Construct.apply_sub_ps *)
(*         (Construct.suspend (n - 1) (assoc_33_to_middle2 ())) *)
(*         sub6 *)
(*     in *)
(*     let w = Construct.witness q in *)
(*     let sub2 = *)
(*       (Construct.to_tm padded_b, true) *)
(*       :: (Construct.to_tm @@ Construct.tgt 1 padded_b, false) *)
(*       :: Construct.characteristic_sub_ps padded_a *)
(*     in *)
(*     let unitor = *)
(*       Construct.apply_sub_ps (Construct.suspend (n - 1) (middle_unitor ())) sub2 *)
(*     in *)
(*     Construct.comp_n *)
(*       [ *)
(*         assoc; *)
(*         Construct.wcomp_n (n - 1) *)
(*           [ p; Construct.wcomp_n (n - 1) [ padded_a; w; padded_b ]; q ]; *)
(*         Construct.wcomp_n (n - 1) [ p; unitor; q ]; *)
(*         Construct.wcomp_n (n - 1) [ p; xi_n_i_lt n (n - 1); q ]; *)
(*       ] *)

(*   let xi_gt n = *)
(*     let p, q = UP.u (n - 1) (n - 1) 0 in *)
(*     let padded_a = *)
(*       Construct.apply_sub *)
(*         (padded_n_k_l_func_r (n - 1) (n - 1) 0 1) *)
(*         (gamma_iminus1_l_func_to_eh_a n 0) *)
(*     in *)
(*     let padded_b = *)
(*       Construct.apply_sub *)
(*         (padded_n_k_l_func_r (n - 1) (n - 1) 0 1) *)
(*         (gamma_iminus1_l_func_to_eh_b n 0) *)
(*     in *)
(*     let sub6 = *)
(*       (Construct.to_tm q, true) *)
(*       :: (Construct.to_tm @@ Construct.tgt 1 q, false) *)
(*       :: (Construct.to_tm padded_b, true) *)
(*       :: (Construct.to_tm @@ Construct.tgt 1 padded_b, false) *)
(*       :: (Construct.to_tm p, true) *)
(*       :: (Construct.to_tm @@ Construct.tgt 1 p, false) *)
(*       :: (Construct.to_tm q, true) *)
(*       :: (Construct.to_tm @@ Construct.tgt 1 q, false) *)
(*       :: (Construct.to_tm padded_a, true) *)
(*       :: (Construct.to_tm @@ Construct.tgt 1 padded_a, false) *)
(*       :: Construct.characteristic_sub_ps p *)
(*     in *)
(*     let assoc = *)
(*       Construct.apply_sub_ps *)
(*         (Construct.suspend (n - 1) (assoc_33_to_middle2 ())) *)
(*         sub6 *)
(*     in *)
(*     let w = Construct.witness q in *)
(*     let sub2 = *)
(*       (Construct.to_tm padded_b, true) *)
(*       :: (Construct.to_tm @@ Construct.tgt 1 padded_b, false) *)
(*       :: Construct.characteristic_sub_ps padded_a *)
(*     in *)
(*     let unitor = *)
(*       Construct.apply_sub_ps (Construct.suspend (n - 1) (middle_unitor ())) sub2 *)
(*     in *)
(*     Construct.comp_n *)
(*       [ *)
(*         assoc; *)
(*         Construct.wcomp_n (n - 1) *)
(*           [ p; Construct.wcomp_n (n - 1) [ padded_a; w; padded_b ]; q ]; *)
(*         Construct.wcomp_n (n - 1) [ p; unitor; q ]; *)
(*         Construct.wcomp_n (n - 1) [ p; xi_n_i_gt n (n - 1); q ]; *)
(*       ] *)
(* end *)

(* module PSU = PseudoFunctoriality *)

(* let zeta n = *)
(*   let tree = Br [ Unchecked.disc (n - 1); Unchecked.disc (n - 1) ] in *)
(*   let rec sphere_type_L = function *)
(*     | -1 -> Obj *)
(*     | k -> *)
(*         Arr *)
(*           ( sphere_type_L (k - 1), *)
(*             Var (Var.Db (2 * k)), *)
(*             Var (Var.Db ((2 * k) + 1)) ) *)
(*   in *)
(*   let rec sphere_type_R = function *)
(*     | -1 -> Obj *)
(*     | 0 -> Arr (Obj, Var (Var.Db 1), Var (Var.Db ((2 * n) + 1))) *)
(*     | k -> *)
(*         Arr *)
(*           ( sphere_type_R (k - 1), *)
(*             Var (Var.Db ((2 * n) + (2 * k))), *)
(*             Var (Var.Db ((2 * n) + (2 * k) + 1)) ) *)
(*   in *)
(*   let d_l = (Var (Var.Db (2 * n)), sphere_type_L (n - 1)) in *)
(*   let d_r = (Var (Var.Db (4 * n)), sphere_type_R (n - 1)) in *)
(*   let cohty = *)
(*     Construct.arr *)
(*       (Construct.wcomp *)
(*          (Construct.wcomp d_l 0 (Construct.id_n 1 (Construct.src 1 d_r))) *)
(*          (n - 1) *)
(*          (Construct.wcomp (Construct.id_n 1 (Construct.tgt 1 d_l)) 0 d_r)) *)
(*       (Construct.wcomp d_l 0 d_r) *)
(*   in *)
(*   let sub = *)
(*     drop 1 (Construct.characteristic_sub_ps (V.b_constr n)) *)
(*     @ Construct.characteristic_sub_ps (V.a_constr n) *)
(*   in *)
(*   ( Coh (check_coh tree cohty ("zeta^" ^ string_of_int n, 0, []), sub), *)
(*     Unchecked.ty_apply_sub_ps cohty sub ) *)

(* let zeta_inv n = *)
(*   let tree = Br [ Unchecked.disc (n - 1); Unchecked.disc (n - 1) ] in *)
(*   let rec sphere_type_L = function *)
(*     | -1 -> Obj *)
(*     | k -> *)
(*         Arr *)
(*           ( sphere_type_L (k - 1), *)
(*             Var (Var.Db (2 * k)), *)
(*             Var (Var.Db ((2 * k) + 1)) ) *)
(*   in *)
(*   let rec sphere_type_R = function *)
(*     | -1 -> Obj *)
(*     | 0 -> Arr (Obj, Var (Var.Db 1), Var (Var.Db ((2 * n) + 1))) *)
(*     | k -> *)
(*         Arr *)
(*           ( sphere_type_R (k - 1), *)
(*             Var (Var.Db ((2 * n) + (2 * k))), *)
(*             Var (Var.Db ((2 * n) + (2 * k) + 1)) ) *)
(*   in *)
(*   let d_l = (Var (Var.Db (2 * n)), sphere_type_L (n - 1)) in *)
(*   let d_r = (Var (Var.Db (4 * n)), sphere_type_R (n - 1)) in *)
(*   let cohty = *)
(*     Construct.arr *)
(*       (Construct.wcomp d_l 0 d_r) *)
(*       (Construct.wcomp *)
(*          (Construct.wcomp d_l 0 (Construct.id_n 1 (Construct.src 1 d_r))) *)
(*          (n - 1) *)
(*          (Construct.wcomp (Construct.id_n 1 (Construct.tgt 1 d_l)) 0 d_r)) *)
(*   in *)
(*   let sub = *)
(*     drop 1 (Construct.characteristic_sub_ps (V.b_constr n)) *)
(*     @ Construct.characteristic_sub_ps (V.a_constr n) *)
(*   in *)
(*   ( Coh (check_coh tree cohty ("(zeta^" ^ string_of_int n ^ ")^-1", 0, []), sub), *)
(*     Unchecked.ty_apply_sub_ps cohty sub ) *)

(* let first_step_gt n = *)
(*   let p_type = *)
(*     Construct.arr (d_n_constr n) *)
(*       (Construct.tm_app (BP.padded n) (BP.gamma_i_gt_to_db n)) *)
(*   in *)
(*   let pad = *)
(*     ( Coh *)
(*         ( check_coh (Unchecked.disc n) p_type *)
(*             ("p^" ^ string_of_int n ^ "_>", 0, []), *)
(*           Unchecked.identity_ps @@ Unchecked.disc n ), *)
(*       p_type ) *)
(*   in *)
(*   let phi = *)
(*     Construct.apply_sub_ps pad (Construct.characteristic_sub_ps (V.a_constr n)) *)
(*   in *)
(*   let phi_op = *)
(*     Construct.apply_sub_ps (Construct.op [ 1 ] pad) *)
(*       (Construct.characteristic_sub_ps (V.b_constr n)) *)
(*   in *)
(*   Construct.wcomp phi (n - 1) phi_op *)

(* let second_step_lt n = *)
(*   let p_type = *)
(*     Construct.arr *)
(*       (Construct.wcomp (d_n_constr n) 0 *)
(*          (Construct.id_n n (Var (Var.Db 1), Obj))) *)
(*       (Construct.of_tm (FP.padded n)) *)
(*   in *)
(*   let pad = *)
(*     ( Coh *)
(*         ( check_coh (Unchecked.disc n) p_type *)
(*             ("p^" ^ string_of_int n ^ "_<", 0, []), *)
(*           Unchecked.identity_ps @@ Unchecked.disc n ), *)
(*       p_type ) *)
(*   in *)
(*   let phi = *)
(*     Construct.apply_sub_ps pad (Construct.characteristic_sub_ps (V.a_constr n)) *)
(*   in *)
(*   let phi_op = *)
(*     Construct.apply_sub_ps (Construct.op [ 1 ] pad) *)
(*       (Construct.characteristic_sub_ps (V.b_constr n)) *)
(*   in *)
(*   Construct.wcomp phi (n - 1) phi_op *)

(* let second_step_gt n = *)
(*   let r = BToU.repad n n in *)
(*   let repad_a = Construct.tm_app r (gamma_i_l_to_eh_a n 0) in *)
(*   let repad_b = *)
(*     Construct.tm_app (Opposite.checked_tm r [ 1 ]) (gamma_i_l_to_eh_b n 0) *)
(*   in *)
(*   Construct.wcomp repad_a (n - 1) repad_b *)

(* let third_step_lt n = *)
(*   let r = FToU.repad n n in *)
(*   let repad_a = Construct.tm_app r (gamma_i_l_to_eh_a n (n - 1)) in *)
(*   let repad_b = *)
(*     Construct.tm_app (Opposite.checked_tm r [ 1 ]) (gamma_i_l_to_eh_b n (n - 1)) *)
(*   in *)
(*   Construct.wcomp repad_a (n - 1) repad_b *)

(* let func_v_to_zeta n = *)
(*   [ *)
(*     (UP.v_bridge, (Construct.to_tm @@ zeta n, true)); *)
(*     ( UP.v_plus, *)
(*       (Construct.to_tm @@ Construct.wcomp (V.a_constr n) 0 (V.b_constr n), false) *)
(*     ); *)
(*     ( UP.v, *)
(*       ( Construct.to_tm *)
(*         @@ Construct.wcomp (a_comp_id n 0) (n - 1) (id_comp_b n 0), *)
(*         false ) ); *)
(*     (x, (Var x, false)); *)
(*   ] *)

(* let fourth_step_gt n = *)
(*   Construct.tm_app *)
(*     (Functorialisation.tm (UP.padded n (n - 1) 0) [ (UP.v, 1) ]) *)
(*     (func_v_to_zeta n) *)

let eh_gt n =
  let module EH = EHBaseCaseGT (struct
    let n = n
  end) in
  EH.eh_gt
(* Construct.comp_n *)
(*   [ first_step_gt n; second_step_gt n; PSU.xi_gt n; fourth_step_gt n ] *)

(* let eh_lt n = *)
(*   Construct.comp_n *)
(*     [ zeta_inv n; second_step_lt n; third_step_lt n; PSU.xi_lt n ] *)

(* let swap_a_and_b n = *)
(*   [ (V.b, (Var V.a, true)); (V.a, (Var V.b, true)); (x, (Var x, false)) ] *)

(* let suspended_point_to_point () = *)
(*   [ *)
(*     (x, (Construct.to_tm @@ Construct.id_n 1 V.x_constr, true)); *)
(*     (Var.Db 1, (Var x, false)); *)
(*     (Var.Db 0, (Var x, false)); *)
(*   ] *)

(* let rec repad_suspended n k l i = *)
(*   let m = min k l + 1 in *)
(*   if i = m then Construct.id_n 1 (UP.v_constr i l) *)
(*   else *)
(*     let i = i - 1 in *)
(*     let p_u_minus, q_u_minus = UP.u (i - 1) (k - 1) (l - 1) in *)
(*     let p_s = *)
(*       Construct.apply_sub *)
(*         (Construct.suspend 1 p_u_minus) *)
(*         (suspended_point_to_point ()) *)
(*     in *)
(*     let q_s = *)
(*       Construct.apply_sub *)
(*         (Construct.suspend 1 q_u_minus) *)
(*         (suspended_point_to_point ()) *)
(*     in *)
(*     let p_u, q_u = UP.u i k l in *)
(*     let previous_repadding = repad_suspended n k l i in *)
(*     let iota_m = UP.in_minus in *)
(*     let iota_p = UP.in_plus in *)
(*     let sigma = UP.sub (i + 1) l in *)
(*     let f_type = *)
(*       Construct.arr *)
(*         (Construct.wcomp p_s i *)
(*            (Construct.apply_sub *)
(*               (Construct.apply_sub previous_repadding iota_m) *)
(*               sigma)) *)
(*         p_u *)
(*     in *)
(*     let g_type = *)
(*       Construct.arr q_s *)
(*         (Construct.wcomp *)
(*            (Construct.apply_sub *)
(*               (Construct.apply_sub previous_repadding iota_p) *)
(*               sigma) *)
(*            i q_u) *)
(*     in *)
(*     let f = *)
(*       ( Coh *)
(*           ( check_coh (Br []) *)
(*               (Unchecked.ty_rename f_type [ (x, Var (Var.Db 0)) ]) *)
(*               ( "f^" ^ string_of_int i ^ "_(" ^ string_of_int n ^ "," *)
(*                 ^ string_of_int k ^ "," ^ string_of_int l ^ ")", *)
(*                 0, *)
(*                 [] ), *)
(*             [ (Var x, true) ] ), *)
(*         f_type ) *)
(*     in *)
(*     let g = *)
(*       ( Coh *)
(*           ( check_coh (Br []) *)
(*               (Unchecked.ty_rename g_type [ (x, Var (Var.Db 0)) ]) *)
(*               ( "g^" ^ string_of_int i ^ "_(" ^ string_of_int n ^ "," *)
(*                 ^ string_of_int k ^ "," ^ string_of_int l ^ ")", *)
(*                 0, *)
(*                 [] ), *)
(*             [ (Var x, true) ] ), *)
(*         g_type ) *)
(*     in *)
(*     Padding.repad_old p_s p_u f q_s q_u g previous_repadding iota_m iota_p UP.v *)
(*       sigma *)

(* let gamma_i_l_to_a_comp_b n l = *)
(*   [ *)
(*     ( UP.v, *)
(*       (Construct.to_tm @@ Construct.wcomp (V.a_constr n) l (V.b_constr n), true) *)
(*     ); *)
(*     (x, (Var x, false)); *)
(*   ] *)

(* let eh_suspended_to_eh n = *)
(*   [ *)
(*     (V.b, (Var V.b, true)); *)
(*     (V.a, (Var V.a, true)); *)
(*     (x, (Construct.to_tm @@ Construct.id_n 1 V.x_constr, false)); *)
(*     (Var.Db 1, (Var x, false)); *)
(*     (Var.Db 0, (Var x, false)); *)
(*   ] *)

(* let suspension_move eh_minus n k l = *)
(*   let suspended_eh = *)
(*     Construct.apply_sub *)
(*       (Construct.suspend 1 eh_minus) *)
(*       (eh_suspended_to_eh (n - 1)) *)
(*   in *)
(*   Construct.comp_n *)
(*     [ *)
(*       suspended_eh; *)
(*       Construct.apply_sub (repad_suspended n k l n) (gamma_i_l_to_a_comp_b n l); *)
(*     ] *)

(* let nat_unitor constr = *)
(*   let x_constr = (Var (Var.Db 0), Obj) in *)
(*   let y_constr = (Var (Var.Db 1), Obj) in *)
(*   let f_constr = (Var (Var.Db 2), Construct.arr x_constr y_constr) in *)
(*   let cohty = *)
(*     Construct.arr f_constr *)
(*       (Construct.comp_n [ f_constr; Construct.id_n 1 y_constr ]) *)
(*   in *)
(*   let runit = check_coh (Unchecked.disc 1) cohty ("unitor_-_to_-id", 0, []) in *)
(*   let d = Construct.dim constr in *)
(*   let sub = Construct.characteristic_sub_ps constr in *)
(*   ( Coh (Suspension.coh (Some (d - 1)) runit, sub), *)
(*     Unchecked.ty_apply_sub_ps (Suspension.ty (Some (d - 1)) cohty) sub ) *)

(* let nat_factor prev_eh n k l = *)
(*   let db0 = (Var (Var.Db 0), Obj) in *)
(*   let idnx = Construct.id_n n db0 in *)
(*   let lhs = Construct.id_n 1 (Construct.wcomp idnx k idnx) in *)
(*   let eh_to_id = *)
(*     [ *)
(*       (V.b, (Construct.to_tm idnx, true)); *)
(*       (V.a, (Construct.to_tm idnx, true)); *)
(*       (x, (Var (Var.Db 0), false)); *)
(*     ] *)
(*   in *)
(*   let _, q_n = UP.u n k l in *)
(*   let rhs = *)
(*     Construct.comp_n *)
(*       [ *)
(*         Construct.apply_sub prev_eh eh_to_id; *)
(*         Construct.rename q_n [ (x, Var (Var.Db 0)) ]; *)
(*       ] *)
(*   in *)
(*   let cohty = Construct.arr lhs rhs in *)
(*   let coherence = *)
(*     check_coh (Unchecked.disc 0) cohty *)
(*       ( "factor_identity^" ^ string_of_int n ^ "_(" ^ string_of_int k ^ "," *)
(*         ^ string_of_int l ^ ")", *)
(*         0, *)
(*         [] ) *)
(*   in *)
(*   Construct.of_coh coherence *)

(* let nat_associator1 constr1 constr2 constr3 = *)
(*   let f1 = (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) in *)
(*   let f2 = (Var (Var.Db 4), Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))) in *)
(*   let f3 = (Var (Var.Db 6), Arr (Obj, Var (Var.Db 3), Var (Var.Db 5))) in *)
(*   let cohty = *)
(*     Construct.arr *)
(*       (Construct.comp_n [ f1; Construct.comp_n [ f2; f3 ] ]) *)
(*       (Construct.comp_n [ Construct.comp_n [ f1; f2 ]; f3 ]) *)
(*   in *)
(*   let coherence = *)
(*     check_coh (Br [ Br []; Br []; Br [] ]) cohty ("assoc_-(--)_to_(--)-", 0, []) *)
(*   in *)
(*   let d = Construct.dim constr1 in *)
(*   let sub = *)
(*     Construct.characteristic_sub_ps_composite [ constr1; constr2; constr3 ] *)
(*   in *)
(*   ( Coh (Suspension.coh (Some (d - 1)) coherence, sub), *)
(*     Unchecked.ty_apply_sub_ps (Suspension.ty (Some (d - 1)) cohty) sub ) *)

(* let nat_associator2 constr1 constr2 constr3 = *)
(*   let f1 = (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) in *)
(*   let f2 = (Var (Var.Db 4), Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))) in *)
(*   let f3 = (Var (Var.Db 6), Arr (Obj, Var (Var.Db 3), Var (Var.Db 5))) in *)
(*   let cohty = *)
(*     Construct.arr *)
(*       (Construct.comp_n [ Construct.comp_n [ f1; f2 ]; f3 ]) *)
(*       (Construct.comp_n [ f1; f2; f3 ]) *)
(*   in *)
(*   let coherence = *)
(*     check_coh (Br [ Br []; Br []; Br [] ]) cohty ("assoc_(--)-_to_---", 0, []) *)
(*   in *)
(*   let d = Construct.dim constr1 in *)
(*   let sub = *)
(*     Construct.characteristic_sub_ps_composite [ constr1; constr2; constr3 ] *)
(*   in *)
(*   ( Coh (Suspension.coh (Some (d - 1)) coherence, sub), *)
(*     Unchecked.ty_apply_sub_ps (Suspension.ty (Some (d - 1)) cohty) sub ) *)

(* let nat_finalcoh prev_eh n k l = *)
(*   let db0 = (Var (Var.Db 0), Obj) in *)
(*   let idnx = Construct.id_n n db0 in *)
(*   let eh_to_id = *)
(*     [ *)
(*       (V.b, (Construct.to_tm idnx, true)); *)
(*       (V.a, (Construct.to_tm idnx, true)); *)
(*       (x, (Var (Var.Db 0), false)); *)
(*     ] *)
(*   in *)
(*   let p_n, _ = UP.u n k l in *)
(*   let lhs = Construct.apply_sub prev_eh eh_to_id in *)
(*   let rhs = Construct.rename p_n [ (x, Var (Var.Db 0)) ] in *)
(*   let cohty = Construct.arr lhs rhs in *)
(*   let coherence = *)
(*     check_coh (Unchecked.disc 0) cohty *)
(*       ( "eh_to_p^" ^ string_of_int n ^ "_(" ^ string_of_int k ^ "," *)
(*         ^ string_of_int l ^ ")", *)
(*         0, *)
(*         [] ) *)
(*   in *)
(*   Construct.of_coh coherence *)

(* let eh_func_to_eh n = *)
(*   [ *)
(*     (Var.Bridge V.b, (Var V.b, true)); *)
(*     (Var.Plus V.b, (Construct.to_tm @@ V.id n, false)); *)
(*     (V.b, (Construct.to_tm @@ V.id n, false)); *)
(*     (Var.Bridge V.a, (Var V.a, true)); *)
(*     (Var.Plus V.a, (Construct.to_tm @@ V.id n, false)); *)
(*     (V.a, (Construct.to_tm @@ V.id n, false)); *)
(*     (x, (Var x, false)); *)
(*   ] *)

(* let gamma_i_l_func_to_a_comp_b n l = *)
(*   [ *)
(*     ( UP.v_bridge, *)
(*       ( Construct.to_tm *)
(*         @@ Construct.wcomp (V.a_constr (n + 1)) l (V.b_constr (n + 1)), *)
(*         true ) ); *)
(*     (UP.v_plus, (Construct.to_tm @@ UP.id2 n l, false)); *)
(*     (UP.v, (Construct.to_tm @@ UP.id2 n l, false)); *)
(*     (x, (Var x, false)); *)
(*   ] *)

(* let naturality_move prev_eh n k l = *)
(*   let a_k_b = Construct.wcomp (V.a_constr (n + 1)) k (V.b_constr (n + 1)) in *)
(*   let _, q_n = UP.u n k l in *)
(*   let idnx = V.id n in *)
(*   let eh_to_id = *)
(*     [ *)
(*       (V.b, (Construct.to_tm idnx, true)); *)
(*       (V.a, (Construct.to_tm idnx, true)); *)
(*       (x, (Var x, false)); *)
(*     ] *)
(*   in *)
(*   let nat = *)
(*     Construct.inverse *)
(*       (Construct.apply_sub *)
(*          (Construct.functorialise prev_eh [ V.b; V.a ]) *)
(*          (eh_func_to_eh n)) *)
(*   in *)
(*   let paddedfunc = *)
(*     Construct.tm_app *)
(*       (Functorialisation.tm (UP.padded n k l) [ (UP.v, 1) ]) *)
(*       (gamma_i_l_func_to_a_comp_b n l) *)
(*   in *)
(*   let eh_id_id = Construct.apply_sub prev_eh eh_to_id in *)
(*   Construct.comp_n *)
(*     [ *)
(*       nat_unitor a_k_b; *)
(*       Construct.wcomp a_k_b n (nat_factor prev_eh n k l); *)
(*       nat_associator1 a_k_b eh_id_id q_n; *)
(*       Construct.wcomp nat n q_n; *)
(*       nat_associator2 eh_id_id paddedfunc q_n; *)
(*       Construct.wcomp_n n [ nat_finalcoh prev_eh n k l; paddedfunc; q_n ]; *)
(*     ] *)

let rec eh n k l =
  if k = 0 && l = n - 1 then assert false (* eh_lt n *)
  else if k = n - 1 && l = 0 then eh_gt n
  else assert false
(* if max k l = n - 1 then *)
(*   suspension_move (eh (n - 1) (k - 1) (l - 1)) n k l *)
(* else naturality_move (eh (n - 1) k l) (n - 1) k l *)

let full_eh n k l = assert false
(* let ehnkl = eh n k l in *)
(* Construct.comp_n *)
(*   [ *)
(*     ehnkl; *)
(*     Construct.inverse *)
(*       (Construct.apply_sub (Construct.op [ l + 1 ] ehnkl) (swap_a_and_b n)); *)
(*   ] *)

let eh_Tm n k l =
  let module C = EHCtx (struct
    let n = n
    let k = k
    let l = l
  end) in
  let tm = Construct.to_tm @@ eh n k l in
  let checked_ctx = Ctx.check @@ C.ctx in
  check_term checked_ctx ~name:(Printf.sprintf "eh^%d_(%d,%d)" n k l, 0, []) tm

let full_eh_Tm n k l =
  let module C = EHCtx (struct
    let n = n
    let k = k
    let l = l
  end) in
  let tm = Construct.to_tm @@ full_eh n k l in
  let checked_ctx = Ctx.check @@ C.ctx in
  check_term checked_ctx
    ~name:(Printf.sprintf "EH^%d_(%d,%d)" n k l, 0, [])
    ~ty:
      (Construct.arr
         (Construct.wcomp C.a_constr k C.b_constr)
         (Construct.wcomp C.b_constr k C.a_constr))
    tm
