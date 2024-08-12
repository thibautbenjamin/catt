open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh)
module F = Functorialisation

module LinearComp = struct
  module Memo = struct
    let tbl = Hashtbl.create 24

    let find arity list f =
      try Hashtbl.find tbl (arity, list)
      with Not_found ->
        let res = f arity list in
        Hashtbl.add tbl (arity, list) res;
        res
  end

  let arity ps =
    let d = Unchecked.dim_ps ps in
    let rec aux ps i =
      match (i, ps) with
      | 0, Br l -> List.length l
      | i, Br [ ps ] -> aux ps (i - 1)
      | _, _ ->
          Error.fatal "cubical composite must be on suspended linear composite"
    in
    aux ps (d - 1)

  let tdb i = Var (Db i)
  let tpl i = Var (Plus (Db i))
  let tbr i = Var (Bridge (Db i))
  let idx_src i = if i = 2 then 0 else i - 3
  let plus i l = if List.mem (Var.Db i) l then tpl i else tdb i

  let src_i_f i active =
    if active then
      Builtin.bcomp
        (tdb (idx_src i))
        (tdb (i - 1))
        (tdb i)
        (tpl (i - 1))
        (tbr (i - 1))
    else tdb i

  let tgt_i_f i active l =
    if active then
      let isrc = idx_src i in
      Builtin.bcomp (tdb isrc) (tpl isrc) (tbr isrc) (plus (i - 1) l) (tpl i)
    else Var (Plus (Db i))

  let comp_biased_start arity =
    let lin_incl =
      let rec sub k =
        match k with
        | 0 -> [ (tdb 1, false) ]
        | k -> (tdb (k + 2), k mod 2 == 0) :: sub (k - 1)
      in
      sub (2 * arity)
    in
    let lin_comp = Coh (Builtin.comp_n arity, lin_incl) in
    Builtin.bcomp (tdb 0) (tdb 1) (tdb 2) (tdb ((2 * arity) + 1)) lin_comp

  let comp_biased_end arity =
    let lin_incl = Unchecked.identity_ps (Builtin.ps_comp arity) in
    let lin_comp = Coh (Builtin.comp_n arity, lin_incl) in
    Builtin.bcomp (tdb 0)
      (tdb ((2 * arity) - 1))
      lin_comp
      (tdb ((2 * arity) + 1))
      (tdb ((2 * arity) + 2))

  let comp_biased_middle arity pos =
    let comp = Builtin.comp_n arity in
    let rec sub k =
      match k with
      | _ when k = 0 -> [ (tdb 0, false) ]
      | _ when k < pos -> (tdb k, true) :: (tdb (k - 1), false) :: sub (k - 2)
      | _ when k = pos + 1 ->
          let bcomp =
            Builtin.bcomp
              (tdb (idx_src k))
              (tdb (k - 1))
              (tdb k)
              (tdb (k + 1))
              (tdb (k + 2))
          in
          (bcomp, true) :: (tdb (k + 1), false) :: sub (k - 2)
      | _ when k > pos + 1 ->
          (tdb (k + 2), true) :: (tdb (k + 1), false) :: sub (k - 2)
      | _ -> assert false
    in
    Coh (comp, sub (2 * arity))

  let comp_biased arity pos =
    match pos with
    | _ when pos = 0 -> comp_biased_start arity
    | _ when pos = (2 * arity) + 1 -> comp_biased_end arity
    | _ -> comp_biased_middle arity pos

  let sub_whisk_i i arity l src tgt =
    let rec sub k =
      match k with
      | k when k = 0 -> [ (tdb 0, false) ]
      | k when k < i -> (tdb k, true) :: (tdb (k - 1), false) :: sub (k - 2)
      | k when k = i ->
          List.append
            [
              (tbr i, true); (tgt, false); (src, false); (plus (i - 1) l, false);
            ]
            (sub (i - 2))
      | k when k > i ->
          (plus k l, true) :: (plus (k - 1) l, false) :: sub (k - 2)
      | _ -> assert false
    in
    sub (2 * arity)

  let sub_assc_i i arity l =
    let rec sub k =
      match k with
      | k when k = 0 && i = 0 ->
          [ (tbr 0, true); (tpl 0, false); (tdb 0, false) ]
      | k when k = 0 -> [ (tdb 0, false) ]
      | k when k < i + 1 -> (tdb k, true) :: (tdb (k - 1), false) :: sub (k - 2)
      | k when k = i + 1 ->
          List.append
            [ (tbr i, true); (tpl i, false); (tdb k, true); (tdb i, false) ]
            (sub (k - 2))
      | k when k > i + 1 ->
          (plus k l, true) :: (plus (k - 1) l, false) :: sub (k - 2)
      | _ -> assert false
    in
    sub (2 * arity)

  let assc i arity l =
    let src = comp_biased arity (if i = 0 then 1 else i + 2) in
    let tgt = comp_biased arity i in
    let ps = Builtin.ps_comp (arity + 1) in
    let assc = Coh.check_inv ps src tgt ("builtin_assc", 0, []) in
    let sub = sub_assc_i i arity l in
    Unchecked.coh_ty assc sub

  let whsk i arity l =
    let src = src_i_f i (List.mem (Var.Db (i - 1)) l) in
    let tgt = tgt_i_f i (List.mem (Var.Db (idx_src i)) l) l in
    let sub = sub_whisk_i i arity l src tgt in
    let comp = Builtin.comp_n arity in
    let whsk = F.coh_depth0 comp [ Db i ] in
    Unchecked.coh_ty whsk sub

  let move_at v l arity =
    let mv, ty =
      match v with
      | Var.Db i when i = 0 -> assc 0 arity l
      | Var.Db i when i mod 2 = 0 -> whsk i arity l
      | Var.Db i -> assc i arity l
      | _ ->
          Error.fatal
            "cubical composite can only compute on De Bruijn variables"
    in
    match ty with Arr (_, s, t) -> (mv, s, t) | _ -> assert false

  let build_cubical_long arity list =
    let append_onto_if cond l1 l2 = if cond then List.append l1 l2 else l2 in
    let rec sub ctx ?(add_src = false) onto =
      match ctx with
      | [] -> onto
      | [ (v, _) ] ->
          if List.mem v list then
            let mv, _, tgtv = move_at v list arity in
            (mv, true) :: (tgtv, false) :: onto
          else onto
      | (v, _) :: (tv, _) :: ctx ->
          let mv, srcv, tgtv = move_at v list arity in
          let mtv, srctv, tgttv = move_at tv list arity in
          let src = if List.mem tv list then srctv else srcv in
          let onto =
            append_onto_if (List.mem v list)
              [ (mv, true); (tgtv, false) ]
              (append_onto_if (List.mem tv list)
                 [ (mtv, true); (tgttv, false) ]
                 (append_onto_if add_src [ (src, false) ] onto))
          in
          sub ctx onto
    in
    let comp = Suspension.coh (Some 1) (Builtin.comp_n (List.length list)) in
    let base = [ (plus ((2 * arity) - 1) list, false); (tdb 0, false) ] in
    let ctx_comp = Unchecked.ps_to_ctx (Builtin.ps_comp arity) in
    let s = sub ctx_comp ~add_src:true base in
    Unchecked.coh_ty comp s

  let build_cubical arity list =
    match arity with
    | 1 ->
        let src_on = List.mem (Var.Db 1) list in
        let tgt_on = List.mem (Var.Db 0) list in
        (tbr 2, Arr (Obj, src_i_f 2 src_on, tgt_i_f 2 tgt_on list))
    | arity -> build_cubical_long arity list

  let cubical arity list = Memo.find arity list build_cubical
end

let desuspend_db v d =
  match v with
  | Var.Db i -> Var.Db (i - (2 * d))
  | _ -> Error.fatal "only de Bruijn levels expected in coherences"

(* source and source inclusion of a functorialised ps *)
let ctx_src ps l =
  let d = Unchecked.dim_ps ps in
  let bdry = Unchecked.ps_bdry ps in
  let tgt_incl_ps = Unchecked.ps_tgt ps in
  let tgt_f, bdry_f, names, l = F.sub_w_tgt bdry tgt_incl_ps l in
  let src_ctx, i1, i2 = Unchecked.ps_compose (d - 1) ps bdry_f in
  let in_minus = Unchecked.identity_ps ps in
  let src_incl = Unchecked.pullback_up (d - 1) ps bdry_f in_minus tgt_f in
  (src_ctx, src_incl, i1, i2, bdry_f, l, names)

(* target and target inclusion of a functorialised ps *)
let ctx_tgt ps l =
  let d = Unchecked.dim_ps ps in
  let bdry = Unchecked.ps_bdry ps in
  let src_incl_ps = Unchecked.ps_src ps in
  let src_f, bdry_f, names, l_bdry = F.sub_w_tgt bdry src_incl_ps l in
  let tgt_ctx, i1, i2 = Unchecked.ps_compose (d - 1) bdry_f ps in
  let in_plus = Unchecked.sub_to_sub_ps ps (F.tgt_subst l) in
  let tgt_incl = Unchecked.pullback_up (d - 1) bdry_f ps src_f in_plus in
  (tgt_ctx, tgt_incl, i1, i2, bdry_f, l_bdry, names)

(* Construct source (t[i1]) * (tgt_f[i2]) *)
let naturality_src coh ty tgt ty_base dim l i1 i2 names =
  let t = Coh (coh, i1) in
  if l = [] then t
  else
    let tgt_f_ty = Unchecked.rename_ty (F.ty ty_base l tgt) names in
    let tgt_f_ty = Unchecked.ty_apply_sub_ps tgt_f_ty i2 in
    let tgt_f = Unchecked.rename_tm (F.tm_one_step_tm tgt l) names in
    let tgt_f = Unchecked.tm_apply_sub_ps tgt_f i2 in
    let ty = Unchecked.ty_apply_sub_ps ty i1 in
    let coh_src_sub_ps = F.whisk_sub_ps 0 t ty tgt_f tgt_f_ty in
    let comp = Suspension.coh (Some (dim - 1)) (Builtin.comp_n 2) in
    Coh (comp, coh_src_sub_ps)

(* Construct target (src_f[i1]) * (t[i2]) *)
let naturality_tgt coh ty src ty_base dim l i1 i2 names =
  let t = Coh (coh, i2) in
  if l = [] then t
  else
    let src_f_ty = Unchecked.rename_ty (F.ty ty_base l src) names in
    let src_f_ty = Unchecked.ty_apply_sub_ps src_f_ty i1 in
    let src_f = Unchecked.rename_tm (F.tm_one_step_tm src l) names in
    let src_f = Unchecked.tm_apply_sub_ps src_f i1 in
    let ty = Unchecked.ty_apply_sub_ps ty i2 in
    let coh_tgt_sub_ps = F.whisk_sub_ps 0 src_f src_f_ty t ty in
    let comp = Suspension.coh (Some (dim - 1)) (Builtin.comp_n 2) in
    Coh (comp, coh_tgt_sub_ps)

let biasor_sub_intch_src ps bdry_f i1 i2 d =
  let ps_red = Ps_reduction.reduce (d - 1) ps in
  let prod, _, _ = Unchecked.ps_compose (d - 1) ps_red bdry_f in
  let red_sub_prod = Ps_reduction.reduction_sub prod in
  let red_sub_ps = Ps_reduction.reduction_sub ps in
  let left_leg = Unchecked.sub_ps_apply_sub_ps red_sub_ps i1 in
  let prod_to_src = Unchecked.pullback_up (d - 1) ps_red bdry_f left_leg i2 in
  Unchecked.sub_ps_apply_sub_ps red_sub_prod prod_to_src

let biasor_sub_intch_tgt ps bdry_f i1 i2 d =
  let ps_red = Ps_reduction.reduce (d - 1) ps in
  let prod, _, _ = Unchecked.ps_compose (d - 1) bdry_f ps_red in
  let red_sub_prod = Ps_reduction.reduction_sub prod in
  let red_sub_ps = Ps_reduction.reduction_sub ps in
  let right_leg = Unchecked.sub_ps_apply_sub_ps red_sub_ps i2 in
  let prod_to_src = Unchecked.pullback_up (d - 1) bdry_f ps_red i1 right_leg in
  Unchecked.sub_ps_apply_sub_ps red_sub_prod prod_to_src

(* Interchange needed for source of depth-1 non-inv coh *)
(*
https://q.uiver.app/#q=WzAsOCxbMSwwLCJcXHBhcnRpYWxcXEdhbW1hIl0sWzIsMSwiXFxvdmVycmlnaHRhcnJvd3tcXHBhcnRpYWxcXEdhbW1hfV57WF9cXHRhdX0iXSxbMCwzLCJcXEdhbW1hIl0sWzAsMSwiXFxHYW1tYV57cmVkfSJdLFsxLDIsIlxcRGVsdGEiXSxbMSwzLCJcXFBoaSJdLFszLDIsIlxcRGVsdGFee3JlZH0iXSxbMSw0LCJcXG92ZXJyaWdodGFycm93e1xcR2FtbWF9XlgiXSxbMCwxLCJcXHNpZ21hIl0sWzAsMiwiXFx0YXUiLDEseyJsYWJlbF9wb3NpdGlvbiI6NzAsImN1cnZlIjo1fV0sWzMsMiwiXFxyaG9fXFxHYW1tYSIsMl0sWzAsMywiXFx0YXVfciIsMV0sWzEsNCwial8yIiwxXSxbMyw0LCJqXzEiLDFdLFs0LDAsIiIsMCx7InN0eWxlIjp7Im5hbWUiOiJjb3JuZXIifX1dLFs0LDUsIiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsyLDUsImlfMSIsMV0sWzEsNSwiaV8yIiwxXSxbNSwwLCIiLDEseyJzdHlsZSI6eyJuYW1lIjoiY29ybmVyIn19XSxbNiw0LCJcXHJob19cXERlbHRhIiwxLHsiY3VydmUiOjF9XSxbMiw3XSxbMSw3LCJcXG92ZXJyaWdodGFycm93e1xcdGF1fV5YIiwxLHsiY3VydmUiOi0zfV0sWzUsNywiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d
 *)
let depth1_interchanger_src coh coh_bridge l =
  let gamma, coh_ty, _ = Coh.forget coh in
  let _, tgt, ty_base = Coh.noninv_srctgt coh in
  let d = Unchecked.dim_ps gamma in
  let src_ctx, src_incl, i1, i2, bdry_f, l_tgt, names = ctx_src gamma l in
  let coh_src = naturality_src coh coh_ty tgt ty_base d l_tgt i1 i2 names in
  let coh_tgt = Coh (coh_bridge, biasor_sub_intch_src gamma bdry_f i1 i2 d) in
  let intch_coh = Coh.check_inv src_ctx coh_src coh_tgt ("intch_src", 0, []) in
  Unchecked.coh_ty intch_coh src_incl

let depth1_interchanger_tgt coh coh_bridge l =
  let gamma, coh_ty, _ = Coh.forget coh in
  let src, _, ty_base = Coh.noninv_srctgt coh in
  let d = Unchecked.dim_ps gamma in
  let tgt_ctx, tgt_incl, i1, i2, bdry_f, l_src, names = ctx_tgt gamma l in
  let coh_tgt = naturality_tgt coh coh_ty src ty_base d l_src i1 i2 names in
  let coh_src = Coh (coh_bridge, biasor_sub_intch_tgt gamma bdry_f i1 i2 d) in
  let intch_coh = Coh.check_inv tgt_ctx coh_src coh_tgt ("intch_tgt", 0, []) in
  Unchecked.coh_ty intch_coh tgt_incl

(*
  Compare substitutions out of the same ps-context
  and fill gaps between matching but different terms with
  the correct cubical composite
 *)
let depth1_bridge_sub ps_inter l_inter d =
  let rec aux red =
    match red with
    | [] -> []
    | (t, true) :: (w, false) :: red ->
        let ps_comp, s =
          match t with
          | Coh (comp, s) ->
              let ps_comp, _, _ = Coh.forget comp in
              (ps_comp, s)
          | Var v ->
              let ty, _ = List.assoc v (Unchecked.ps_to_ctx ps_inter) in
              let s = (Var v, true) :: Unchecked.ty_to_sub_ps ty in
              let ps_comp =
                Suspension.ps (Some (Unchecked.dim_ty ty)) (Br [])
              in
              (ps_comp, s)
          | Meta_tm _ -> Error.fatal "meta_variables must have been resolved"
        in
        let l = F.preimage (Unchecked.ps_to_ctx ps_comp) s l_inter in
        if l <> [] then
          let arity = LinearComp.arity ps_comp in
          let s = F.sub (Unchecked.sub_ps_to_sub s) l in
          let w_plus = Unchecked.tm_apply_sub w (F.tgt_subst l_inter) in
          let list = List.map (fun v -> desuspend_db v (d - 1)) l in
          let ccomp, ty = LinearComp.cubical arity list in
          let ccomp = Suspension.tm (Some (d - 1)) ccomp in
          let ccomp = Unchecked.tm_apply_sub ccomp s in
          let ty = Suspension.ty (Some (d - 1)) ty in
          let ty = Unchecked.ty_apply_sub ty s in
          let src, tgt =
            match ty with Arr (_, s, t) -> (s, t) | _ -> assert false
          in
          (ccomp, true) :: (tgt, false) :: (src, false) :: (w_plus, false)
          :: aux red
        else (t, true) :: (w, false) :: aux red
    | (t, e) :: red -> (t, e) :: aux red
  in
  aux (Ps_reduction.reduction_sub ps_inter)

let loc_max_dim d ps x =
  let ctx = Unchecked.ps_to_ctx ps in
  let ty, expl = List.assoc x ctx in
  expl && Unchecked.dim_ty ty = d

let intermediate_ps ps l d =
  let l_d0, l_d1 = List.partition (loc_max_dim (d - 1) ps) l in
  if l_d0 = [] then (ps, l, Unchecked.(sub_ps_to_sub (identity_ps ps)))
  else
    let ps_f_c = F.ctx (Unchecked.ps_to_ctx ps) l_d0 in
    let _, names, _ = Unchecked.db_levels ps_f_c in
    let ps_f = PS.(forget (mk (Ctx.check ps_f_c))) in
    let l_psf = List.map (fun x -> Var.Db (List.assoc x names)) l_d1 in
    let names = List.map (fun (x, n) -> (Var.Db n, Var x)) names in
    (ps_f, l_psf, names)

let bridge_ps ps_inter l_inter d =
  let red_sub = Ps_reduction.reduction_sub ps_inter in
  let ps_red = Ps_reduction.reduce (d - 1) ps_inter in
  let ps_red_c = Unchecked.ps_to_ctx ps_red in
  let coh_l = F.preimage ps_red_c red_sub l_inter in
  let coh_l = List.filter (loc_max_dim d ps_red) coh_l in
  (ps_red, coh_l)

let bridge_coh coh ps_bridge =
  let _, _, name = Coh.forget coh in
  let src, tgt, _ = Coh.noninv_srctgt coh in
  let name_red = (Unchecked.full_name name ^ "_red", 0, []) in
  let coh_bridge = Coh.check_noninv ps_bridge src tgt name_red in
  coh_bridge

let coh_depth1 coh l =
  let ps, _, _ = Coh.forget coh in
  let d = Unchecked.dim_ps ps in
  let ps_inter, l_inter, names = intermediate_ps ps l d in
  let ps_bridge, l_bridge = bridge_ps ps_inter l_inter d in
  let coh_bridge = bridge_coh coh ps_bridge in
  let intch_src, intch_src_ty = depth1_interchanger_src coh coh_bridge l in
  let intch_tgt, intch_tgt_ty = depth1_interchanger_tgt coh coh_bridge l in
  let bridge = depth1_bridge_sub ps_inter l_inter d in
  let bridge = Unchecked.sub_ps_apply_sub bridge (F.sub names l_inter) in
  let coh_bridge_f = F.coh_depth0 coh_bridge l_bridge in
  let middle = Coh (coh_bridge_f, bridge) in
  let inner_tgt, final_tgt =
    match intch_tgt_ty with Arr (_, t, t') -> (t, t') | _ -> assert false
  in
  let comp_sub_ps =
    List.append
      [
        (intch_tgt, true);
        (final_tgt, false);
        (middle, true);
        (inner_tgt, false);
        (intch_src, true);
      ]
      (Unchecked.ty_to_sub_ps intch_src_ty)
  in
  let comp = Suspension.coh (Some d) (Builtin.comp_n 3) in
  (Coh (comp, comp_sub_ps), F.ctx (Unchecked.ps_to_ctx ps) l)

let init () = F.coh_depth1 := coh_depth1
