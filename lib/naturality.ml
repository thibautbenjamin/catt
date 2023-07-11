open Common

let elaborate_ctx : ((Var.t * Syntax.ty) list -> ctx) ref
    = ref (fun _ -> failwith "uninitialised forward reference")

let resolve_constraints_ty : (ctx -> meta_ctx -> ty -> ty) ref
  = ref (fun _ _ -> failwith "uninitialised forward reference")

let elaborate_tm : ((Var.t * Syntax.ty) list -> Syntax.tm -> tm) ref
  = ref (fun _ _ -> failwith "uninitialised forward reference")

let boundary_maps c =
  let c = Kernel.(PS.mk (Ctx.check c)) in
  let src = Kernel.(PS.(source c)) in
  let tgt = Kernel.(PS.(target c)) in
  (Kernel.PS.forget c),
  List.map (fun v -> Var v) src,
  List.map (fun v -> Var v) tgt

let build_substitution s = List.map (fun (x,_) -> Var x) s

let rec ps_composition i = match i with
  | i when i <= 0 -> assert false
  | i when i = 1 -> Br [Br[]; Br[]]
  | i -> Br [ps_composition (i-1)]

let ty_composition i =
  let rec base_ty i = match i with
    | i when i<= 0 -> assert false
    | i when i = 1 -> Obj
    | i -> Arr(base_ty (i-1), Var(Db (0+2*(i-2))), Var (Db(1+2*(i-2))))
  in
  Arr (base_ty i, Var (Db (0+2*(i-1))), Var (Db (3+2*(i-1))))

let substitution_composition i u v =
  let rec aux k  =
    match k with
    | 0 -> let t,meta_t = new_meta_tm () in [t],[meta_t]
    | k ->
      let s,meta_s = aux (k-1) in
      match k with
      | k when k = (4+2*(i-1)) -> v::s, meta_s
      | k when k = (2+2*(i-1)) -> u::s, meta_s
      | _ -> let t, meta_t =  new_meta_tm() in
        t::s, meta_t::meta_s
  in
  aux (4+2*(i-1))

let composition i u v =
  let ps = ps_composition i in
  let ty = ty_composition i in
  let sub, meta = substitution_composition i u v in
  Coh(ps,ty,sub), meta

let build c ps ty t t' =
  let ctx = !elaborate_ctx c in
  let ps_out,src,tgt = boundary_maps ctx in
  let t = !elaborate_tm c t in
  let t' = !elaborate_tm c t' in

  let i = Unchecked.dim_ty ty in
  let sr, meta_sr = composition i (Coh(ps,ty,src)) t' in
  let tg, meta_tg = composition i t (Coh(ps,ty,tgt)) in
  let nat_ty = Arr (new_meta_ty(), sr, tg) in
  let meta = List.append meta_sr meta_tg in
  let nat_ty = !resolve_constraints_ty ctx meta nat_ty in
  let _, names,_ = Unchecked.db_levels ctx in
  let nat_ty = Unchecked.rename_ty nat_ty names in
  let names = build_substitution names in
  Coh (ps_out, nat_ty, names)
