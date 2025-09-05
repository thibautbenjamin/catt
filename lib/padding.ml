open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)

let pad_new p q previous v sigma ctx =
  let prev =
    Construct.tm_app (Functorialisation.tm previous [ (v, 1) ]) sigma
  in
  Construct.comp3 (Tm.constr p) prev (Tm.constr q)

let pad p q previous v sigma =
  Construct.comp3 p
    (Construct.tm_app (Functorialisation.tm previous [ (v, 1) ]) sigma)
    q

module Filtration = struct
  (* Data defining a filtration *)
  module type DataS = sig
    val min : int
    val max : int
    val ctx : int -> ctx
    val v : int -> Var.t
  end

  (* Functions relative to a filtration *)
  module type S = sig
    include DataS

    val sub : int -> sub
    val v_constr : int -> constr
    val src_v : int -> constr
    val tgt_v : int -> constr
    val v_plus : int -> Var.t
    val v_bridge : int -> Var.t
    val in_plus : int -> sub
    val in_minus : int -> sub
  end

  module Make (F : DataS) : S = struct
    include F

    let v_constr i = (Var (F.v i), fst (List.assoc (F.v i) (F.ctx i)))
    let src_v i = Construct.src 1 (v_constr i)
    let tgt_v i = Construct.tgt 1 (v_constr i)

    let to_db i =
      let c = Functorialisation.ctx (F.ctx i) [ F.v i ] in
      Unchecked.db_level_sub_inv c

    let v_plus i = Display_maps.var_apply_sub (Var.Plus (F.v i)) (to_db i)
    let v_bridge i = Display_maps.var_apply_sub (Var.Bridge (F.v i)) (to_db i)

    let in_plus i =
      let rec aux ctx =
        match ctx with
        | [] -> []
        | (x, (ty, b)) :: ctx when x == F.v i ->
            (v i, (Var (v_plus i), false)) :: aux ctx
        | (x, (ty, b)) :: ctx ->
            (x, (Unchecked.tm_apply_sub (Var x) (to_db i), b)) :: aux ctx
      in
      aux (F.ctx i)

    let in_minus i =
      let rec aux ctx =
        match ctx with
        | [] -> []
        | (x, (ty, b)) :: ctx when x == F.v i ->
            (v i, (Var (v i), false)) :: aux ctx
        | (x, (ty, b)) :: ctx ->
            (x, (Unchecked.tm_apply_sub (Var x) (to_db i), b)) :: aux ctx
      in
      aux (F.ctx i)

    let sub i =
      let w = v_constr (i + 1) in
      let rec aux ctx =
        match ctx with
        | [] -> []
        | (x, (ty, b)) :: ctx when x = v i ->
            (v_bridge i, (Construct.to_tm w, true))
            :: (v_plus i, (Construct.(to_tm (tgt 1 w)), false))
            :: (v i, (Construct.(to_tm (src 1 w)), false))
            :: aux ctx
        | (x, (ty, b)) :: ctx -> (x, (Var x, b)) :: aux ctx
      in
      aux (ctx i)
  end
end

module Padding = struct
  module type PaddingDataS = sig
    val p : int -> Tm.t
    val q : int -> Tm.t
  end

  module type PaddedS = sig
    val padded : int -> Tm.t
  end

  module Padded (F : Filtration.S) (D : PaddingDataS) : PaddedS = struct
    let memo_padded : (int, Tm.t) Hashtbl.t = Hashtbl.create 77

    let rec padded i =
      let compute_padded i =
        let name = Printf.sprintf "Padding(%d)" i in
        let padded_constr =
          if i = F.min then F.v_constr i
          else
            pad_new
              (D.p (i - 1))
              (D.q (i - 1))
              (padded (i - 1))
              (F.v (i - 1))
              (F.sub (i - 1))
              (F.ctx i)
        in
        check_constr (F.ctx i) ~name:(name, 0, []) padded_constr
      in
      match Hashtbl.find_opt memo_padded i with
      | Some padded -> padded
      | None ->
          let padded = compute_padded i in
          Hashtbl.add memo_padded i padded;
          padded
  end

  (* Several padding data we consider are canonical -- they are given by a single
     coherence in a well-chosen pasting scheme. The following aims at streamlining
     the construction of such padding data *)
  module type CanonicalPaddingDataArgsS = sig
    val ps : int -> ps
    val p_src : int -> constr
    val q_tgt : int -> constr
    val p_inc : int -> constr list
    val q_inc : int -> constr list
    val pad_in_ps : int -> sub
  end

  module CanonicalPaddingData
      (F : Filtration.S)
      (Args : CanonicalPaddingDataArgsS)
      (P : PaddedS) =
  struct
    let p i =
      let padded_subbed = Construct.tm_app (P.padded i) (Args.pad_in_ps i) in
      let ty = Construct.arr (Args.p_src i) padded_subbed in
      let coh = check_coh (Args.ps i) ty ("p", 0, []) in
      check_constr (F.ctx (i + 1)) (Construct.coh_app coh (Args.p_inc i))

    let q i =
      let padded_subbed = Construct.tm_app (P.padded i) (Args.pad_in_ps i) in
      let ty = Construct.arr padded_subbed (Args.q_tgt i) in
      let coh = check_coh (Args.ps i) ty ("q", 0, []) in
      check_constr (F.ctx (i + 1)) (Construct.coh_app coh (Args.q_inc i))
  end

  module type DataS = sig
    module F : Filtration.S
    module D : PaddingDataS
    module P : PaddedS
  end

  module type S = sig
    include DataS

    val ctx : ctx
    val v : Var.t
    val v_constr : constr
    val v_plus : Var.t
    val v_bridge : Var.t
    val p : Tm.t
    val q : Tm.t
    val padded : Tm.t
    val padded_func : int -> int -> Tm.t
  end

  module Make (A : DataS) : S = struct
    module F = A.F
    module D = A.D
    module P = A.P

    let ctx = F.ctx F.max
    let v = F.v F.max
    let v_constr = F.v_constr F.max
    let v_plus = F.v_plus F.max
    let v_bridge = F.v_bridge F.max
    let p = D.p F.max
    let q = D.q F.max
    let padded = P.padded F.max

    (* Assumption: t is in the i-th context of the filtration *)
    let rec iterated_func t i r =
      match r with
      | 0 -> t
      | r ->
          check_constr
            (F.ctx (i + r))
            (Construct.tm_app
               (Functorialisation.tm
                  (iterated_func t i (r - 1))
                  [ (F.v (i + r), 1) ])
               (F.sub (i + r - 1)))

    let padded_func i r = iterated_func (P.padded i) i r
  end

  module type CanonicalDataS = sig
    module F : Filtration.S
    module D : CanonicalPaddingDataArgsS
  end

  module MakeCanonical (A : CanonicalDataS) = Make (struct
    module F = A.F

    module rec D : PaddingDataS = CanonicalPaddingData (F) (A.D) (P)
    and P : PaddedS = Padded (F) (D)
  end)
end

module type FiltrationMorphismS = sig
  val sub : int -> sub
end

module PaddingApp
    (Tgt : Filtration.S)
    (M : FiltrationMorphismS)
    (P : Padding.S) : Padding.S = Padding.Make (struct
  module F = Tgt

  module D = struct
    let p i =
      check_constr
        (Tgt.ctx (i + 1))
        (Construct.tm_app (P.D.p i) (M.sub (i + 1)))

    let q i =
      check_constr
        (Tgt.ctx (i + 1))
        (Construct.tm_app (P.D.q i) (M.sub (i + 1)))
  end

  module P = struct
    let padded i =
      check_constr (Tgt.ctx i) (Construct.tm_app (P.P.padded i) (M.sub i))
  end
end)

let hexcomp fminus fplus ybridge fbridge gminus gplus gbridge zbridge hminus
    hplus hbridge =
  let d = Construct.dim fminus - 1 in
  let db n = Var.Db n in
  let hex =
    Functorialisation.coh (Builtin.comp_n 3) [ db 6; db 4; db 3; db 2; db 1 ]
  in
  let hex = Suspension.checked_tm (Some d) hex in
  let x = Construct.src 1 fminus in
  let yminus = Construct.tgt 1 fminus in
  let yplus = Construct.tgt 1 fplus in
  let zminus = Construct.src 1 hminus in
  let zplus = Construct.src 1 hplus in
  let w = Construct.tgt 1 hminus in
  let sub =
    let tm = Construct.to_tm in
    (tm hbridge, true)
    :: (tm hplus, false)
    :: (tm hminus, false)
    :: (tm w, false)
    :: (tm gbridge, true)
    :: (tm gplus, false)
    :: (tm gminus, false)
    :: (tm zbridge, false)
    :: (tm zplus, false)
    :: (tm zminus, false)
    :: (tm fbridge, true)
    :: (tm fplus, false)
    :: (tm fminus, false)
    :: (tm ybridge, false)
    :: (tm yplus, false)
    :: (tm yminus, false)
    :: (tm x, false)
    :: Unchecked.ty_to_sub_ps (Construct.to_ty w)
  in
  (* The call to sub_ps_to_sub is a bit of a hack, relying on the fact that all
     checked terms use deBruijn. Further refactoring to be done in the kernel to
     enforce this more statically *)
  Construct.tm_app hex (Unchecked.sub_ps_to_sub sub)

let repad p_0 p_1 f q_0 q_1 g previous iota_minus iota_plus v sub =
  let padding_0, padding_1 = Tm.bdry previous in
  hexcomp p_0 p_1
    Construct.(apply_sub (tm_app previous iota_minus) sub)
    f
    Construct.(tm_app (Functorialisation.tm padding_0 [ (v, 1) ]) sub)
    Construct.(tm_app (Functorialisation.tm padding_1 [ (v, 1) ]) sub)
    Construct.(inverse (tm_app (Functorialisation.tm previous [ (v, 1) ]) sub))
    Construct.(apply_sub (tm_app previous iota_plus) sub)
    q_0 q_1 g

let repad_old p_0 p_1 f q_0 q_1 g previous iota_minus iota_plus v sub =
  let padding_0 = Construct.src 1 previous in
  let padding_1 = Construct.tgt 1 previous in
  hexcomp p_0 p_1
    Construct.(apply_sub (apply_sub previous iota_minus) sub)
    f
    Construct.(apply_sub (functorialise padding_0 [ v ]) sub)
    Construct.(apply_sub (functorialise padding_1 [ v ]) sub)
    Construct.(inverse (apply_sub (functorialise previous [ v ]) sub))
    Construct.(apply_sub (apply_sub previous iota_plus) sub)
    q_0 q_1 g

let repad_one_step p_0 p_1 f q_0 q_1 g previous iota_minus iota_plus v sub =
  let padding_0, padding_1 = Tm.bdry previous in
  hexcomp (Tm.constr p_0) (Tm.constr p_1)
    Construct.(apply_sub (tm_app previous iota_minus) sub)
    (Tm.constr f)
    Construct.(tm_app (Functorialisation.tm padding_0 [ (v, 1) ]) sub)
    Construct.(tm_app (Functorialisation.tm padding_1 [ (v, 1) ]) sub)
    Construct.(inverse (tm_app (Functorialisation.tm previous [ (v, 1) ]) sub))
    Construct.(apply_sub (tm_app previous iota_plus) sub)
    (Tm.constr q_0) (Tm.constr q_1) (Tm.constr g)

module Repadding = struct
  module type RepaddingDataS = sig
    val f : int -> Tm.t
    val g : int -> Tm.t
  end

  module type RepaddedS = sig
    val repad : int -> Tm.t
  end

  module Repadded (P1 : Padding.S) (P2 : Padding.S) (D : RepaddingDataS) =
  struct
    let rec repad i =
      let repadding_constr =
        if i = P1.F.min then Construct.id_n 1 (P1.F.v_constr i)
        else
          let previous = repad (i - 1) in
          let sigma = P1.F.sub (i - 1) in
          let f, g = (D.f (i - 1), D.g (i - 1)) in
          repad_one_step
            (P1.D.p (i - 1))
            (P2.D.p (i - 1))
            f
            (P1.D.q (i - 1))
            (P2.D.q (i - 1))
            g previous
            (P1.F.in_minus (i - 1))
            (P1.F.in_plus (i - 1))
            (P1.F.v (i - 1))
            sigma
      in
      let name = (Printf.sprintf "Repadding(%d)" i, 0, []) in
      check_constr (P1.F.ctx i) ~name repadding_constr
  end

  module type CanonicalRepaddingDataArgsS = sig
    val ps : int -> ps
    val incl : int -> constr list
  end

  module CanonicalRepaddingData
      (Args : CanonicalRepaddingDataArgsS)
      (P1 : Padding.S)
      (P2 : Padding.S)
      (R : RepaddedS) : RepaddingDataS = struct
    let f i =
      let ty =
        Construct.(
          arr
            (wcomp
               (Construct.develop (Tm.constr (P1.D.p i)))
               i
               (tm_app (R.repad i)
                  (Unchecked.sub_apply_sub (P1.F.in_minus i) (P1.F.sub i))))
            (Construct.develop (Tm.constr (P2.D.p i))))
      in
      let coh = check_coh (Args.ps i) ty ("f^", 0, []) in
      check_constr (P1.F.ctx i) (Construct.coh_app coh (Args.incl i))

    let g i =
      let ty =
        Construct.(
          arr
            (Construct.develop (Tm.constr (P1.D.q i)))
            (wcomp
               (tm_app (R.repad i)
                  (Unchecked.sub_apply_sub (P1.F.in_plus i) (P1.F.sub i)))
               i
               (Construct.develop (Tm.constr (P2.D.q i)))))
      in
      let coh = check_coh (Args.ps i) ty ("g^", 0, []) in
      check_constr (P1.F.ctx i) (Construct.coh_app coh (Args.incl i))
  end

  module type DataS = sig
    module P1 : Padding.S
    module P2 : Padding.S
    module D : RepaddingDataS
    module R : RepaddedS
  end

  module type S = sig
    include DataS

    val repadded : Tm.t
    val f : Tm.t
    val g : Tm.t
  end

  module Make (A : DataS) : S = struct
    module P1 = A.P1
    module P2 = A.P2
    module D = A.D
    module R = A.R

    let repadded = R.repad P1.F.max
    let f = D.f (P1.F.max - 1)
    let g = D.g (P1.F.max - 1)
  end

  module type CanonicalDataS = sig
    module P1 : Padding.S
    module P2 : Padding.S
    module D : CanonicalRepaddingDataArgsS
  end

  module MakeCanonical (A : CanonicalDataS) : S = Make (struct
    module P1 = A.P1
    module P2 = A.P2

    module rec D : RepaddingDataS = CanonicalRepaddingData (A.D) (P1) (P2) (R)
    and R : RepaddedS = Repadded (P1) (P2) (D)
  end)
end
