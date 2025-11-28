open Common

module Make (Theory : Theory.S) = struct
  open Kernel.Make (Theory)
  module Comp = Comp.Make (Theory)
  module Suspension = Suspension.Make (Theory)
  module Functorialisation = Functorialisation.Make (Theory)

  let mod_coh = assert false

  let id _ =
    check_coh (Br []) (Arr (Obj, Var (Db 0), Var (Db 0))) ("builtin_id", 0, [])

  let ps_comp = Comp.tree
  let comp_n = Comp.comp_n
  let arity_comp = Comp.arity_comp
  let comp = Comp.comp
  let bcomp = Comp.bcomp

  let id_all_max ps =
    let d = Unchecked.dim_ps ps in
    let rec id_map l =
      let t = Var (Db 0) in
      match l with
      | [] -> [ (t, false) ]
      | Br [] :: l ->
          (Coh (mod_coh, id (), [ (t, true) ]), true) :: (t, false) :: id_map l
      | _ -> Error.fatal "identity must be inserted on maximal argument"
    in
    let rec aux i ps =
      match (i, ps) with
      | _, Br [] -> [ (Var (Db 0), true) ]
      | 0, Br l -> id_map l
      | i, Br l ->
          Unchecked.suspwedge_subs_ps
            (List.map (aux (i - 1)) l)
            (List.map Unchecked.ps_bdry l)
    in
    aux (d - 1) ps

  let assoc =
    let tdb i = Var (Db i) in
    let src =
      bcomp (tdb 0) (tdb 1) (tdb 2) (tdb 5)
        (bcomp (tdb 1) (tdb 3) (tdb 4) (tdb 5) (tdb 6))
    in
    let tgt =
      bcomp (tdb 0) (tdb 3)
        (bcomp (tdb 0) (tdb 1) (tdb 2) (tdb 3) (tdb 4))
        (tdb 5) (tdb 6)
    in
    Coh.check_inv (ps_comp 3) src tgt ("assoc", 0, [])

  let unbiased_unitor ps t =
    let bdry = Unchecked.ps_bdry ps in
    let src =
      let coh = Coh.check_noninv ps t t ("endo", 0, []) in
      Coh (mod_coh, coh, id_all_max ps)
    in
    let a = Tm.ty (check_term (Ctx.check (Unchecked.ps_to_ctx bdry)) t) in
    let da = Unchecked.dim_ty a in
    let sub_base = Unchecked.ty_to_sub_ps a in
    let tgt =
      Coh (mod_coh, Suspension.coh (Some da) (id ()), (t, true) :: sub_base)
    in
    Coh.check_inv bdry src tgt ("unbiased_unitor", 0, [])

  let tdb i = Var (Var.Db i)
  let wcomp = Functorialisation.wcomp

  (*
  (a *_n b) *_0 g -> (a *_0 g) *_n (b *_0 g)
    https://q.uiver.app/#q=WzAsMyxbMCwwLCIwIl0sWzIsMCwiMSJdLFs0LDAsIjciXSxbMCwxLCIyIiwwLHsiY3VydmUiOi01fV0sWzAsMSwiNSIsMix7ImN1cnZlIjo1fV0sWzAsMSwiMyIsMV0sWzEsMiwiOCIsMV0sWzMsNSwiNCIsMix7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbNSw0LCI2IiwyLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dXQ==
*)
  let intch_comp_n0_coh n =
    let rec ty n =
      match n with
      | 0 -> Obj
      | _ -> Arr (ty (n - 1), tdb ((2 * n) - 2), tdb ((2 * n) - 1))
    in
    let fty = ty n in
    let a = (tdb ((2 * n) + 2), Arr (fty, tdb (2 * n), tdb ((2 * n) + 1))) in
    let b =
      (tdb ((2 * n) + 4), Arr (fty, tdb ((2 * n) + 1), tdb ((2 * n) + 3)))
    in
    let g = (tdb ((2 * n) + 6), Arr (Obj, tdb 1, tdb ((2 * n) + 5))) in
    let s, _ = wcomp (wcomp a n b) 0 g in
    let t, _ = wcomp (wcomp a 0 g) n (wcomp b 0 g) in
    let ps = Br [ Br []; Suspension.ps (Some (n - 1)) (Br [ Br []; Br [] ]) ] in
    Coh.check_inv ps s t (Printf.sprintf "builtin_comp_%d_0_intch" n, 0, [])

  (*
  For n>m
  (a *_n b) *_m c -> (a *_m c) *_n (b *_m c)
*)
  let intch_comp_nm_coh n m =
    Suspension.coh (Some (m - 1)) (intch_comp_n0_coh (n - m))
end
