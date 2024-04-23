open Common
module Telescope (Strictness : StrictnessLv)
= struct
  module Kernel = Kernel.Kernel(Strictness)
  module Ctx = Kernel.Ctx
  module Unchecked = Kernel.Unchecked
  open Kernel.Unchecked_types
  module Suspension = Suspension.Suspension(Strictness)
  module Builtin = Builtin.Builtin(Strictness)

  let tdb i = Var (Db i)

  let cell_max k = Var.Db (4*k)
  let cell_forward k = Var.Db (4*k-2)
  let cell_backward k = Var.Db (4*k-1)
  let obj k = if k <= 0 then Var.Db 0 else Var.Db (4*k-3)
  let type_cell_forward k = Arr(Obj, Var (obj(k-1)), Var (obj k))
  let type_cell_backward k = Arr(Obj, (Var (obj k)), Var (obj(k-1)))
  let type_cell_max k = Arr
      (Arr(Obj, Var (obj(k-1)), Var (obj(k-1))),
       Coh(Builtin.comp_n 2,
           [Var (cell_backward k),true;
            Var (obj(k-1)), false;
            Var (cell_forward k),true;
            Var (obj k), false;
            Var (obj(k-1)), false]),
       Coh(Builtin.id, [Var (obj(k-1)), true])
      )


  let rec ctx k =
    match k with
    | k when k < 0 -> Error.fatal "cannot build context for the telescope"
    | k when k = 0 ->
      [Var.Db 0, (Obj, false)]
    | k ->
      (cell_max k, (type_cell_max k, true))::
      (cell_backward k, (type_cell_backward k, false))::
      (cell_forward k, (type_cell_forward k, false))::
      (obj k, (Obj, false))::
      (ctx (k-1))

  let rec subs_telescope_bdry ?(whisk=false) k =
    match k with
    | k when k <= 0 -> Error.fatal "telescopes must have positive length"
    | k when k = 1 ->
      [tdb 2, true; tdb 1, false; tdb 0, false],
      [tdb 3, true; tdb 0, false]
    | k ->
      let right,left = subs_telescope_bdry ~whisk:false (k-1) in
      if whisk then
        let src_max_var =
          Coh (Builtin.comp_n 2,
               [Var (cell_backward k), true;
                Var (obj (k-1)), false;
                Var (cell_forward k), true;
                Var (obj k), false ;
                Var (obj (k-1)), false])
        in
        right,
        List.append left [Var (cell_max k), true;
                          Coh(Builtin.id, [Var (obj (k-1)), true]), false;
                          src_max_var, false;
                          Var (obj(k-1)), false]
      else
        (Var (cell_forward k), true)::(Var (obj k), false)::right,
        List.append left [Var (cell_backward k), true; Var (obj(k-1)), false]

  let sub_ps_telescope_bdry ?(whisk=false) k =
    let right,left = subs_telescope_bdry ~whisk k in
    List.append left right

  let rec telescope k =
    match k with
    | k when k <= 0 -> Error.fatal "telescopes must have positive length"
    | k when k = 1 -> tdb 4
    | k ->
      let comp = Suspension.coh (Some 1) (Builtin.comp_n 4) in
      let tm_src_tgt coh sub_ps =
        match Kernel.forget_coh coh with
        | ps,Arr(_,t,u),_ ->
          let sub = fst (Unchecked.sub_ps_to_sub sub_ps ps) in
          Coh(coh,sub_ps),
          Unchecked.tm_apply_sub t sub,
          Unchecked.tm_apply_sub u sub
        | _ -> Error.fatal "coherence must be of an arrow type"
      in
      let
        m3,src_m3, tgt_m3 =
        tm_src_tgt (Builtin.middle_unitor (k-1)) (sub_ps_telescope_bdry (k-1))
      in
      let
        m2 = Coh(Builtin.middle_rewrite (k-1), sub_ps_telescope_bdry ~whisk:true k)
      in
      let
        m1,src_m1, tgt_m1 =
        tm_src_tgt (Builtin.middle_associator k) (sub_ps_telescope_bdry k)
      in
      let sub_telescope =
        [telescope (k-1), true;
         Coh(Builtin.id, [tdb 0, true]), false;
         m3, true;
         tgt_m3, false;
         m2, true;
         src_m3, false;
         m1, true;
         tgt_m1, false;
         src_m1, false;
         tdb 0, false;
         tdb 0, false]
      in Coh (comp, sub_telescope)

  let checked k = Kernel.check_term (Ctx.check (ctx k)) (telescope k)
end
