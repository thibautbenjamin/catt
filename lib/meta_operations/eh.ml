open Common

module Make (Theory : Theory.S) = struct
  open Kernel.Make (Theory)
  module Construct = Construct.Make (Theory)
  module Padding = Padding.Make (Theory)
  module Builtin = Builtin.Make (Theory)
  module Comp = Comp.Make (Theory)
  module Suspension = Suspension.Make (Theory)
  module Opposite = Opposite.Make (Theory)
  module Functorialisation = Functorialisation.Make (Theory)
  module Inverse = Inverse.Make (Theory)

  module type EHArgsS = sig
    val n : int
    val k : int
    val l : int
  end

  module type BiasedPaddingArgsS = sig
    val n : int
  end

  let memo_args = Hashtbl.create 97
  let memo_args_biased = Hashtbl.create 97

  let args n k l =
    match Hashtbl.find_opt memo_args (n, k, l) with
    | Some m -> m
    | None ->
        let res =
          (module struct
            let n = n
            let k = k
            let l = l
          end : EHArgsS)
        in
        Hashtbl.add memo_args (n, k, l) res;
        res

  let args_biased n =
    match Hashtbl.find_opt memo_args_biased n with
    | Some m -> m
    | None ->
        let res =
          (module struct
            let n = n
          end : BiasedPaddingArgsS)
        in
        Hashtbl.add memo_args_biased n res;
        res

  module UnbiasedPadding (Args : EHArgsS) =
  Padding.Padding.MakeCanonical (struct
    let name = "UBPad"
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
    let name = "FPad"

    module F = Padding.Filtration.Make (struct
      let min = 1
      let max = Args.n
      let ctx i = Unchecked.ps_to_ctx (Unchecked.disc i)
      let v i = Var.Db (2 * i)
    end)

    module D = struct
      let ps i = Unchecked.disc i
      let p_src i = t_comp_id i (F.src_v (i + 1))
      let q_tgt i = p_src i
      let p_inc i = [ (Var (Var.Db (2 * i)), Unchecked.disc_type i) ]
      let q_inc i = [ (Var (Var.Db ((2 * i) + 1)), Unchecked.disc_type i) ]
      let pad_in_ps i = Unchecked.(identity (ps_to_ctx (ps i)))
    end
  end)

  module BackwardBiasedPadding (Args : BiasedPaddingArgsS) =
  Padding.Padding.MakeCanonical (struct
    let name = "BPad"

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

  module ForwardToUnbiasedRepadding (Args : BiasedPaddingArgsS) =
  Padding.Repadding.MakeCanonical (struct
    let name = "FToURepad"

    module EHArgs = (val args Args.n 0 (Args.n - 1) : EHArgsS)
    module P2 = UnbiasedPadding (EHArgs)
    module FP = ForwardBiasedPadding (Args)

    module M : Padding.FiltrationMorphismS = struct
      let name = "id"

      let sub i =
        Unchecked.sub_ps_to_sub
          (Construct.characteristic_sub_ps (P2.F.v_constr i))
    end

    module P1 = Padding.PaddingApp (P2.F) (M) (FP)

    module D = struct
      let ps _ = Br []
      let incl _ = [ (Var (Var.Db 0), Obj) ]
    end
  end)

  module BackwardToUnbiasedRepadding (Args : BiasedPaddingArgsS) =
  Padding.Repadding.MakeCanonical (struct
    let name = "BToURepad"

    module EHArgs = (val args Args.n (Args.n - 1) 0)
    module P2 = UnbiasedPadding (EHArgs)
    module BP = BackwardBiasedPadding (Args)

    module M : Padding.FiltrationMorphismS = struct
      let name = "id"

      let sub i =
        let id_pt i = Construct.(to_tm (id_n i (Var (Var.Db 0), Obj))) in
        let rec sphere_to_point i =
          match i with
          | -1 -> []
          | i ->
              (Var.Db ((2 * i) + 1), (id_pt i, false))
              :: (Var.Db (2 * i), (id_pt i, false))
              :: sphere_to_point (i - 1)
        in
        (BP.F.v i, (Var (P2.F.v i), true)) :: sphere_to_point (i - 1)
    end

    module P1 = Padding.PaddingApp (P2.F) (M) (BP)

    module D = struct
      let ps _ = Br []
      let incl _ = [ (Var (Var.Db 0), Obj) ]
    end
  end)

  module SuspUnbiasedToUnbiasedRepadding (Args : EHArgsS) =
  Padding.Repadding.MakeCanonical (struct
    let name = "ΣUToURepad"

    module PrevArgs = (val args (Args.n - 1) (Args.k - 1) (Args.l - 1))

    let x = Var.Db 0
    let x_constr = (Var x, Obj)

    module P2 = UnbiasedPadding (Args)
    module PrevA = UnbiasedPadding (PrevArgs)
    module Prev = Padding.Suspend (UnbiasedPadding (PrevArgs))

    module M : Padding.FiltrationMorphismS = struct
      let name = "Susp"

      let sub _ =
        let list = [ P2.v_constr; Construct.id x_constr; x_constr; x_constr ] in
        Construct.make_sub Prev.ctx list
    end

    module P1 = Padding.PaddingApp (P2.F) (M) (Prev)

    module D = struct
      let ps _ = Br []
      let incl _ = [ x_constr ]
    end
  end)

  module PseudoFunctorialityUnbiasedPadding (Args : EHArgsS) = struct
    module UP = UnbiasedPadding (Args)

    let x = Var.Db 0
    let w = Var.Db 2
    let ty = snd UP.v_constr
    let ctx = (w, (ty, true)) :: UP.ctx
    let w_constr = (Var w, ty)
    let x_constr = (Var x, Obj)
    let v_constr = UP.v_constr

    let assoc n =
      let tree = Comp.tree 6 in
      let f i = Comp.f i in
      let ty =
        Construct.(
          arr
            (wcomp (comp3 (f 1) (f 2) (f 3)) 0 (comp3 (f 4) (f 5) (f 6)))
            (comp3 (f 1) (comp3 (f 2) (wcomp (f 3) 0 (f 4)) (f 5)) (f 6)))
      in
      Suspension.coh (Some n) (check_coh tree ty ("_builtin_assoc", 0, []))

    let unitor n =
      let tree = Comp.tree 2 in
      let f i = Comp.f i in
      let x i = Comp.x i in
      let ty =
        Construct.(arr (comp3 (f 1) (id_n 1 (x 1)) (f 2)) (wcomp (f 1) 0 (f 2)))
      in
      Suspension.coh (Some n) (check_coh tree ty ("_builtin_unitor", 0, []))

    let intch n i =
      assert (n >= 2);
      let ps =
        Br [ Br []; Suspension.ps (Some (n - 2)) (Br [ Br []; Br [] ]); Br [] ]
      in
      let tdb i = Var (Var.Db i) in
      let d_L = (tdb 2, Arr (Obj, tdb 0, tdb 1)) in
      let d_R = (tdb ((2 * n) + 6), Arr (Obj, tdb 3, tdb ((2 * n) + 5))) in
      let d_max i =
        let rec ty k =
          if k = 1 then Arr (Obj, tdb 1, tdb 3)
          else Arr (ty (k - 1), tdb (2 * k), tdb ((2 * k) + 1))
        in
        let d i =
          let lvl = if i = 0 then 2 * n else (2 * n) + (2 * i) - 1 in
          (tdb lvl, ty (n - 1))
        in
        (tdb ((2 * n) + (2 * i)), Construct.arr (d (i - 1)) (d i))
      in
      let ty =
        Construct.(
          arr
            (comp
               (wcomp_n 0 [ d_L; d_max 1; d_R ])
               (wcomp_n 0 [ d_L; d_max 2; d_R ]))
            (wcomp_n 0 [ d_L; comp_n [ d_max 1; d_max 2 ]; d_R ]))
      in
      Suspension.coh (Some i)
        (check_coh ps ty ("_builtin_intch_chi" ^ string_of_int n, 0, []))

    let rec psfpad_aux i =
      let m = UP.F.min in
      let n = UP.F.max in
      let v_c = v_constr in
      let w_c = w_constr in
      let w_sub = [ w_constr; x_constr ] in
      let witness_constr =
        match i with
        | i when i = m -> Construct.id_n 1 (Construct.wcomp v_c (n - 1) w_c)
        | i when m < i -> (
            let p, q = (UP.D.p (i - 1), UP.D.q (i - 1)) in
            let p, q = (Tm.constr p, Tm.constr q) in
            let t = UP.padded_func (i - 1) (n - i + 1) in
            let tv = Tm.constr t in
            let tw = Construct.tm_app t w_sub in
            match i with
            | i when i < n ->
                let intch =
                  Construct.coh_app (intch (n - i + 1) (i - 1)) [ p; tv; tw; q ]
                in
                Construct.wcomp intch n
                  (Construct.wcomp_n (i - 1)
                     [ p; Tm.constr (psfpad_aux (i - 1)); q ])
            | i when i = n ->
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
                      [ p; Tm.constr (psfpad_aux (n - 1)); q ];
                  ]
            | _ ->
                Error.fatal
                  "[EH] Wrong arguments in pseudofunctoriality of padding")
        | _ ->
            Error.fatal "[EH] Wrong arguments in pseudofunctoriality of padding"
      in
      check_constr ctx witness_constr

    let psfpad = psfpad_aux Args.n
  end

  module EHCtx (EHArgs : EHArgsS) = struct
    let x = Var.Db 0
    let a = Var.Db 1
    let b = Var.Db 2
    let id = Construct.id_n (EHArgs.n - 1) (Var x, Obj)
    let ty = Construct.arr id id
    let ctx = [ (b, (ty, true)); (a, (ty, true)); (x, (Obj, false)) ]
    let x_constr = (Var x, Obj)
    let a_constr = (Var a, ty)
    let b_constr = (Var b, ty)

    let a_comp_id =
      if EHArgs.l = EHArgs.n - 1 then a_constr
      else Construct.wcomp a_constr EHArgs.l (Construct.id_n 1 id)

    let id_comp_b =
      if EHArgs.l = EHArgs.n - 1 then b_constr
      else Construct.wcomp (Construct.id_n 1 id) EHArgs.l b_constr

    module UP = UnbiasedPadding (EHArgs)

    let a_comp_id_sub = [ a_comp_id; x_constr ]
    let id_comp_b_sub = [ id_comp_b; x_constr ]
  end

  module BaseCases (EHArgs : EHArgsS) = struct
    let intch n =
      let ps = Br [ Unchecked.disc (n - 1); Unchecked.disc (n - 1) ] in
      let rec disc_type_r = function
        | 0 -> Obj
        | 1 -> Arr (Obj, Var (Var.Db 1), Var (Var.Db ((2 * n) + 1)))
        | k ->
            Arr
              ( disc_type_r (k - 1),
                Var (Var.Db ((2 * n) + (2 * k) - 2)),
                Var (Var.Db ((2 * n) + (2 * k) - 1)) )
      in
      let d_l = (Var (Var.Db (2 * n)), Unchecked.disc_type n) in
      let d_r = (Var (Var.Db (4 * n)), disc_type_r n) in
      let ty =
        Construct.arr
          (Construct.wcomp
             (Construct.wcomp d_l 0 (Construct.id_n 1 (Construct.src 1 d_r)))
             (n - 1)
             (Construct.wcomp (Construct.id_n 1 (Construct.tgt 1 d_l)) 0 d_r))
          (Construct.wcomp d_l 0 d_r)
      in
      let name = (Printf.sprintf "intch(%d,%d)" n 0, 0, []) in
      check_coh ps ty name

    module GT (Args : BiasedPaddingArgsS) = struct
      module BP = BackwardBiasedPadding (Args)
      module BToU = BackwardToUnbiasedRepadding (Args)
      module PSU = PseudoFunctorialityUnbiasedPadding (EHArgs)

      let eh =
        let open EHCtx (EHArgs) in
        let step1 =
          let p = BP.p in
          let a_padded =
            Construct.(
              tm_app_sub p
                (Unchecked.sub_ps_to_sub (characteristic_sub_ps a_constr)))
          in
          let b_padded =
            Construct.(
              tm_app_sub
                (Opposite.checked_tm p [ 1 ])
                (Unchecked.sub_ps_to_sub (characteristic_sub_ps b_constr)))
          in
          (* TODO: there should be a fix here so that there is no need for the develop *)
          Construct.(develop (wcomp a_padded (Args.n - 1) b_padded))
        in
        let step2 =
          let r = BToU.repadded in
          let r_op = Opposite.checked_tm r [ 1 ] in
          let repad_a = Construct.tm_app r a_comp_id_sub in
          let repad_b = Construct.tm_app r_op id_comp_b_sub in
          Construct.wcomp repad_a (Args.n - 1) repad_b
        in
        let step3 =
          Construct.tm_app PSU.psfpad [ id_comp_b; a_comp_id; x_constr ]
        in
        let step4 =
          let intch = Construct.coh_app (intch Args.n) [ a_constr; b_constr ] in
          Construct.tm_app
            (Functorialisation.tm UP.padded [ (UP.v, 1) ])
            [ intch; Construct.tgt 1 intch; Construct.src 1 intch; x_constr ]
        in
        Construct.comp_n [ step1; step2; step3; step4 ]
    end

    module LT (Args : BiasedPaddingArgsS) = struct
      module FP = ForwardBiasedPadding (Args)
      module FToU = ForwardToUnbiasedRepadding (Args)
      module PSU = PseudoFunctorialityUnbiasedPadding (EHArgs)

      let eh =
        let open EHCtx (EHArgs) in
        let a_sub =
          Unchecked.sub_ps_to_sub (Construct.characteristic_sub_ps a_constr)
        in
        let b_sub =
          Unchecked.sub_ps_to_sub (Construct.characteristic_sub_ps b_constr)
        in
        let step1 =
          Construct.inverse
            (Construct.coh_app (intch Args.n) [ a_constr; b_constr ])
        in
        let step2 =
          let p = FP.p in
          let a_padded = Construct.tm_app_sub p a_sub in
          let b_padded =
            Construct.(tm_app_sub (Opposite.checked_tm p [ 1 ]) b_sub)
          in
          Construct.(develop (wcomp a_padded (Args.n - 1) b_padded))
        in
        let step3 =
          let r = FToU.repadded in
          let r_op = Opposite.checked_tm r [ 1 ] in
          let repad_a = Construct.tm_app r [ a_constr; x_constr ] in
          let repad_b = Construct.tm_app r_op [ b_constr; x_constr ] in
          Construct.wcomp repad_a (Args.n - 1) repad_b
        in
        let step4 =
          Construct.tm_app PSU.psfpad [ b_constr; a_constr; x_constr ]
        in
        Construct.comp_n [ step1; step2; step3; step4 ]
    end
  end

  let suspend eh_prev curargs =
    let module EHArgs = (val curargs : EHArgsS) in
    let open EHCtx (EHArgs) in
    let module R = SuspUnbiasedToUnbiasedRepadding (EHArgs) in
    let suspended_eh = Suspension.checked_tm (Some 1) eh_prev in
    Construct.comp_n
      [
        Construct.tm_app suspended_eh
          [ b_constr; a_constr; Construct.id x_constr; x_constr; x_constr ];
        Construct.tm_app R.repadded
          [ Construct.wcomp a_constr EHArgs.l b_constr; x_constr ];
      ]

  module Naturality = struct
    let nat_unitor constr =
      let x_constr = (Var (Var.Db 0), Obj) in
      let y_constr = (Var (Var.Db 1), Obj) in
      let f_constr = (Var (Var.Db 2), Construct.arr x_constr y_constr) in
      let cohty =
        Construct.arr f_constr
          (Construct.comp_n [ f_constr; Construct.id_n 1 y_constr ])
      in
      let runit = check_coh (Unchecked.disc 1) cohty ("_ehnat_step1", 0, []) in
      let d = Construct.dim constr in
      let sub = Construct.characteristic_sub_ps constr in
      ( Coh (Suspension.coh (Some (d - 1)) runit, sub),
        Unchecked.ty_apply_sub_ps (Suspension.ty (Some (d - 1)) cohty) sub )

    let nat_factor eh_id_id ehargs =
      let module EHArgs = (val ehargs : EHArgsS) in
      let open EHCtx (EHArgs) in
      let idn = Construct.id id in
      let ty =
        Construct.arr
          (Construct.id (Construct.wcomp idn EHArgs.k idn))
          (Construct.comp_n [ eh_id_id; Tm.constr UP.q ])
      in

      let name =
        (Printf.sprintf "_factor_id(%d,%d,%d)" EHArgs.n EHArgs.k EHArgs.l, 0, [])
      in
      let coh = check_coh (Unchecked.disc 0) ty name in
      Construct.of_coh coh

    let nat_associator1 c1 c2 c3 =
      let open Comp in
      let ty =
        Construct.arr
          (Construct.comp_n [ f 1; Construct.comp_n [ f 2; f 3 ] ])
          (Construct.comp_n [ Construct.comp_n [ f 1; f 2 ]; f 3 ])
      in
      let coh = check_coh (tree 3) ty ("_assoc_left", 0, []) in
      let d = Construct.dim c1 in
      Construct.coh_app (Suspension.coh (Some (d - 1)) coh) [ c1; c2; c3 ]

    let nat_associator2 c1 c2 c3 =
      let open Comp in
      let ty =
        Construct.arr
          (Construct.comp_n [ Construct.comp_n [ f 1; f 2 ]; f 3 ])
          (Construct.comp_n [ f 1; f 2; f 3 ])
      in
      let coh = check_coh (tree 3) ty ("_unbiasor_left", 0, []) in
      let d = Construct.dim c1 in
      Construct.coh_app (Suspension.coh (Some (d - 1)) coh) [ c1; c2; c3 ]

    let nat_finalcoh eh_id_id ehargs =
      let module EHArgs = (val ehargs : EHArgsS) in
      let open EHCtx (EHArgs) in
      let module UP = UnbiasedPadding (EHArgs) in
      let p = Tm.constr UP.p in
      let ty = Construct.arr eh_id_id p in
      let name =
        (Printf.sprintf "_eh_to_p(%d,%d,%d)" EHArgs.n EHArgs.k EHArgs.l, 0, [])
      in
      let coh = check_coh (Unchecked.disc 0) ty name in
      Construct.of_coh coh

    let compute eh_prev prev_args args =
      let module PrevArgs = (val prev_args : EHArgsS) in
      let open PrevArgs in
      let module NextArgs = (val args : EHArgsS) in
      let open EHCtx (NextArgs) in
      let module Prev = EHCtx (PrevArgs) in
      let module UP = UnbiasedPadding (PrevArgs) in
      let q = Tm.constr UP.q in
      let a_k_b = Construct.wcomp a_constr k b_constr in
      let nat =
        Construct.inverse
          (Construct.tm_app
             (Functorialisation.tm eh_prev [ (Prev.b, 1); (Prev.a, 1) ])
             [ b_constr; id; id; a_constr; id; id; x_constr ])
      in
      let paddedfunc =
        Construct.tm_app
          (Functorialisation.tm UP.padded [ (UP.v, 1) ])
          [
            Construct.wcomp a_constr l b_constr;
            UP.F.tgt_v (n + 1);
            UP.F.src_v (n + 1);
            x_constr;
          ]
      in
      let eh_id_id = Construct.tm_app eh_prev [ id; id; x_constr ] in
      Construct.comp_n
        [
          nat_unitor a_k_b;
          Construct.wcomp a_k_b n (nat_factor eh_id_id prev_args);
          nat_associator1 a_k_b eh_id_id q;
          Construct.wcomp nat n q;
          nat_associator2 eh_id_id paddedfunc q;
          Construct.wcomp3 (nat_finalcoh eh_id_id prev_args) n paddedfunc n q;
        ]
  end

  let rec eh nkl =
    let module EHArgs = (val nkl : EHArgsS) in
    let open EHArgs in
    let module BArgs = (val args_biased n) in
    let eh_constr =
      if k = 0 && l = n - 1 then
        let module BaseCases = BaseCases (EHArgs) in
        let module BaseCase = BaseCases.LT (BArgs) in
        BaseCase.eh
      else if k = n - 1 && l = 0 then
        let module BaseCases = BaseCases (EHArgs) in
        let module BaseCase = BaseCases.GT (BArgs) in
        BaseCase.eh
      else if max k l = n - 1 then
        let prevargs = args (n - 1) (k - 1) (l - 1) in
        suspend (eh prevargs) nkl
      else
        let prevargs = args (n - 1) k l in
        Naturality.compute (eh prevargs) prevargs nkl
    in
    let module C = EHCtx (EHArgs) in
    check_constr C.ctx
      ~name:(Printf.sprintf "eh^%d_(%d,%d)" n k l, 0, [])
      eh_constr

  let full_eh nkl =
    let eh = eh nkl in
    let open (val nkl) in
    let open EHCtx ((val nkl)) in
    let constr =
      Construct.comp_n
        [
          Construct.of_tm eh;
          Construct.tm_app
            (Inverse.inverse (Opposite.checked_tm eh [ l + 1 ]))
            [ a_constr; b_constr; x_constr ];
        ]
    in
    check_constr ctx constr

  let eh n k l = eh (args n k l)
  let full_eh n k l = full_eh (args n k l)
end
