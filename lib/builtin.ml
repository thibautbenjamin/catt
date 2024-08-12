open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh)

module Memo = struct
  let tbl = Hashtbl.create 97

  let find i f =
    try Hashtbl.find tbl i
    with Not_found ->
      let res = f i in
      Hashtbl.add tbl i res;
      res

  let id =
    check_coh (Br []) (Arr (Obj, Var (Db 0), Var (Db 0))) ("builtin_id", 0, [])
end

let rec ps_comp i =
  match i with
  | i when i <= 0 -> Error.fatal "builtin composition with less than 0 argument"
  | i when i = 1 -> Br [ Br [] ]
  | i -> ( match ps_comp (i - 1) with Br l -> Br (Br [] :: l))

let comp_n arity =
  let build_comp i =
    let ps = ps_comp i in
    let pp_data = (Printf.sprintf "builtin_comp%i" arity, 0, []) in
    Coh.check_noninv ps (Var (Db 0)) (Var (Db 0)) pp_data
  in
  Memo.find arity build_comp

let arity_comp s expl =
  let n = List.length s in
  if expl || !Settings.explicit_substitutions then (n - 1) / 2 else n

let comp s expl =
  let arity = arity_comp s expl in
  comp_n arity

let bcomp x y f z g =
  let comp = comp_n 2 in
  let sub = [ (g, true); (z, false); (f, true); (y, false); (x, false) ] in
  Coh (comp, sub)

let id = Memo.id

let id_all_max ps =
  let d = Unchecked.dim_ps ps in
  let rec id_map l =
    let t = Var (Db 0) in
    match l with
    | [] -> [ (t, false) ]
    | Br [] :: l -> (Coh (id, [ (t, true) ]), true) :: (t, false) :: id_map l
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
    bcomp (tdb 0) (tdb 3)
      (bcomp (tdb 0) (tdb 1) (tdb 2) (tdb 3) (tdb 4))
      (tdb 5) (tdb 6)
  in
  let tgt =
    bcomp (tdb 0) (tdb 1) (tdb 2) (tdb 5)
      (bcomp (tdb 1) (tdb 3) (tdb 4) (tdb 5) (tdb 6))
  in
  Coh.check_inv (ps_comp 3) src tgt ("assoc", 0, [])

let unbiased_unitor ps t =
  let bdry = Unchecked.ps_bdry ps in
  let src =
    let coh = Coh.check_noninv ps t t ("endo", 0, []) in
    Coh (coh, id_all_max ps)
  in
  let a =
    Ty.forget (Tm.typ (check_term (Ctx.check (Unchecked.ps_to_ctx bdry)) t))
  in
  let da = Unchecked.dim_ty a in
  let sub_base = Unchecked.ty_to_sub_ps a in
  let tgt = Coh (Suspension.coh (Some da) id, (t, true) :: sub_base) in
  Coh.check_inv bdry src tgt ("unbiased_unitor", 0, [])
