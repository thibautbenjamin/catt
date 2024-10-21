open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)
open Std

exception NotInvertible of string
exception CohNonInv

let coh c =
  if not (Coh.is_inv c) then raise CohNonInv;
  let ps, ty, (name, susp, func) = Coh.forget c in
  let ty_inv =
    match ty with
    | Obj | Meta_ty _ -> assert false
    | Arr (a, u, v) -> Arr (a, v, u)
  in
  check_coh ps ty_inv (name ^ "^-1", susp, func)

let rec compute_inverse t =
  match t with
  | Var x -> raise (NotInvertible (Var.to_string x))
  | Meta_tm _ -> t
  | Coh (c, sub) -> (
      try Coh (coh c, sub)
      with CohNonInv ->
        let ps, _, _ = Coh.forget c in
        let d = Unchecked.dim_ps ps in
        let pctx = Unchecked.ps_to_ctx ps in
        let sub = Unchecked.sub_ps_to_sub sub in
        let sub_inv = sub_inv sub pctx d in
        let equiv = Opposite.equiv_op_ps ps [ d ] in
        let coh = Opposite.coh c [ d ] in
        Coh (coh, Unchecked.sub_ps_apply_sub equiv sub_inv))
  | App (t,s) ->
    let t = Tm.develop t in
    let total_t = Unchecked.tm_apply_sub t s in
    compute_inverse total_t

and sub_inv s ps i =
  match (s, ps) with
  | [], [] -> []
  | (x, (t, e)) :: sub, (_, (ty, _)) :: ctx when Unchecked.dim_ty ty = i ->
      (x, (compute_inverse t, e)) :: sub_inv sub ctx i
  | (x, t) :: sub, _ :: ctx -> (x, t) :: sub_inv sub ctx i
  | _, _ -> assert false

let compute_inverse t =
  try compute_inverse t
  with NotInvertible s ->
    Error.inversion
      ("term: " ^ Unchecked.tm_to_string t)
      (Printf.sprintf "term %s is not invertible" s)

let group_vertically ps t src_t tgt_t =
  let coh_unbiased = Coh.check_noninv ps src_t tgt_t ("unbiased_comp", 0, []) in
  let coh_vertically_grouped = Ps_reduction.coh coh_unbiased in
  let reduce = Ps_reduction.reduction_sub ps in
  let t_vertically_grouped = Coh (coh_vertically_grouped, reduce) in
  Coh.check_inv ps t t_vertically_grouped ("vertical_grouping", 0, [])

type lin_comp = { arity : int; dim : int; sub_ps : sub_ps }

let tm_to_lin_comp t =
  let ps, sub_ps =
    match t with
    | Coh (c, s) ->
        let ps, _, _ = Coh.forget c in
        (ps, s)
    | _ -> Error.fatal "term must be a linear composite"
  in
  let dim = Unchecked.dim_ps ps in
  let rec arity i ps =
    match (i, ps) with
    | 0, Br l -> List.length l
    | _, Br [ Br l ] -> arity (i - 1) (Br l)
    | _ -> Error.fatal "term must be a linear composite"
  in
  { arity = arity (dim - 1) ps; dim; sub_ps }

let rec cancel_linear_comp lc =
  let k = lc.arity / 2 in
  let rec sub_to_telescope i sub invs =
    match (i, sub, invs) with
    | 0, s, _ -> List.map fst s
    | i, (t, _) :: _ :: s, invs when i > k ->
        sub_to_telescope (i - 1) s (t :: invs)
    | i, (t, _) :: (x, _) :: s, t_inv :: invs ->
        compute_witness t :: t_inv :: t :: x :: sub_to_telescope (i - 1) s invs
    | _, _, _ -> Error.fatal "term must be a linear composite"
  in
  let tel = Telescope.checked k in
  let ctel = Telescope.ctx k in
  let stel =
    Unchecked.list_to_sub
      (sub_to_telescope (2 * k) lc.sub_ps [])
      (Suspension.ctx (Some (lc.dim - 1)) ctel)
  in
  App((Suspension.checked_tm (Some (lc.dim - 1)) tel), stel)

and cancel_all_linear_comp t =
  let c, sub = match t with Coh (c, sub) -> (c, sub) | _ -> Error.fatal "" in
  let ps, _, _ = Coh.forget c in
  let d = Unchecked.dim_ps ps in
  let rec compute_sub i ps sub ty_base =
    match (ps, sub) with
    | Br [], [ t ] -> [ t ]
    | Br [ Br [] ], (t, _) :: (_, _) :: (src_t, _) :: sub when i = d - 1 ->
        let t_wit = cancel_linear_comp (tm_to_lin_comp t) in
        let id_src_t =
          let sub_base = Unchecked.ty_to_sub_ps ty_base in
          let id =
            Suspension.coh (Some (Unchecked.dim_ty ty_base)) (Builtin.id ())
          in
          Coh (id, (src_t, true) :: sub_base)
        in
        (t_wit, true) :: (id_src_t, false) :: (t, false) :: (src_t, false)
        :: (src_t, false) :: sub
    | Br l, sub ->
        let incls = Unchecked.canonical_inclusions l in
        let sub = Unchecked.sub_ps_to_sub sub in
        let lsubs =
          List.map2
            (fun p incl ->
              let s =
                Unchecked.(sub_ps_to_sub_ps_bp (sub_ps_apply_sub incl sub))
              in
              {
                Unchecked.sub_ps =
                  compute_sub (i + 1) p s.sub_ps (Arr (ty_base, s.l, s.r));
                l = s.l;
                r = s.r;
              })
            l incls
        in
        Unchecked.wedge_sub_ps_bp lsubs
  in
  Coh (Functorialisation.coh_all c, compute_sub 0 ps sub Obj)

and compute_witness t =
  match t with
  | Var x -> raise (NotInvertible (Var.to_string x))
  | Meta_tm _ ->
      raise (NotInvertible "Meta_variable not allowed in witness generation")
  | Coh (c, s) ->
      let ps, ty, pp_data = Coh.forget c in
      let d = Coh.dim c in
      let sub_base, u, v =
        match ty with
        | Arr (ty, u, v) -> (Unchecked.ty_to_sub_ps ty, u, v)
        | _ -> Error.fatal "invertible coherence has to be an arrow type"
      in
      if Coh.is_inv c then
        compute_witness_coh_inv c s ~ps ~d ~pp_data ~sub_base ~u ~v
      else compute_witness_comp c s ~ps ~d ~sub_base ~u ~v
  | App (t,s) ->
    let t = Tm.develop t in
    let total_t = Unchecked.tm_apply_sub t s in
    compute_witness total_t


and compute_witness_coh_inv c s ~ps ~pp_data ~d ~sub_base ~u ~v =
  let name, susp, func = pp_data in
  let src_wit =
    let id_ps = Unchecked.identity_ps ps in
    let c_inv = coh c in
    let comp = Suspension.coh (Some (d - 1)) (Builtin.comp_n 2) in
    let c_c_inv =
      (Coh (c_inv, id_ps), true)
      :: (u, false)
      :: (Coh (c, id_ps), true)
      :: (v, true) :: (u, true) :: sub_base
    in
    Coh (comp, c_c_inv)
  in
  let tgt_wit =
    let id = Suspension.coh (Some (d - 1)) (Builtin.id ()) in
    let sub_id_u = (u, true) :: sub_base in
    Coh (id, sub_id_u)
  in
  let c_wit = Coh.check_inv ps src_wit tgt_wit (name ^ "_Unit", susp, func) in
  Coh (c_wit, s)

and compute_witness_comp c s ~ps ~d ~sub_base ~u ~v =
  let ps_doubled, inl, inr = Unchecked.ps_compose (d - 1) ps ps in
  let t =
    let tm1 = Coh (c, inl) in
    let c_op = Opposite.coh c [ d ] in
    let tm2 = Coh (c_op, inr) in
    let sub_inr = Unchecked.sub_ps_to_sub inr in
    let sub_inl = Unchecked.sub_ps_to_sub inl in
    let w = Unchecked.tm_apply_sub (Coh.tgt c_op) sub_inr in
    let comp = Suspension.coh (Some (d - 1)) (Builtin.comp_n 2) in
    Coh
      ( comp,
        (tm2, true) :: (w, false) :: (tm1, true)
        :: Unchecked.sub_ps_apply_sub
             ((v, false) :: (u, false) :: sub_base)
             sub_inl )
  in
  let ps_reduced =
    Ps_reduction.reduce (Unchecked.dim_ps ps_doubled - 1) ps_doubled
  in
  let src_c, _, _ = Coh.noninv_srctgt c in
  let cps = Unchecked.ps_to_ctx ps in
  let sub = Unchecked.sub_ps_to_sub s in
  let m1, src_m1, tgt_m1 =
    let coh = group_vertically ps_doubled t src_c src_c in
    let src, tgt = Coh.src coh, Coh.tgt coh in
    let sinv =
      Unchecked.sub_ps_apply_sub
        (Opposite.equiv_op_ps ps [ d ])
        (sub_inv sub cps d)
    in
    let ssinv = Unchecked.pullback_up (d - 1) ps ps s sinv in
    let subsinv = Unchecked.sub_ps_to_sub ssinv in
    ( Coh (coh, ssinv),
      Unchecked.tm_apply_sub src subsinv,
      Unchecked.tm_apply_sub tgt subsinv)
  in
  let m2 = cancel_all_linear_comp tgt_m1 in
  let m3, src_m3, tgt_m3 =
    let coh = Builtin.unbiased_unitor ps_reduced src_c in
    let src, tgt = Coh.src coh, Coh.tgt coh in
    let s = Unchecked.sub_ps_apply_sub (Unchecked.ps_src ps) sub in
    let sub = Unchecked.sub_ps_to_sub s in
    ( Coh (coh, s),
      Unchecked.tm_apply_sub src sub,
      Unchecked.tm_apply_sub tgt sub )
  in
  let sub_total =
    (m3, true) :: (tgt_m3, false) :: (m2, true) :: (src_m3, false) :: (m1, true)
    :: (tgt_m1, false) :: (src_m1, false)
    :: Unchecked.sub_ps_apply_sub ((u, false) :: (u, false) :: sub_base) sub
  in
  Coh (Suspension.coh (Some d) (Builtin.comp_n 3), sub_total)

let compute_witness t =
  try
    let r = compute_witness t in
    Io.info ~v:3
      (lazy (Printf.sprintf "inverse term: %s" (Unchecked.tm_to_string r)));
    r
  with NotInvertible s ->
    Error.inversion
      ("term: " ^ Unchecked.tm_to_string t)
      (Printf.sprintf "term %s is not invertible" s)
