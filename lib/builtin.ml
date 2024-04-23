open Common

module Builtin (Strictness : StrictnessLv)
= struct
  module Kernel = Kernel.Kernel(Strictness)
  module Unchecked = Kernel.Unchecked
  open Kernel.Unchecked_types
  module Suspension = Suspension.Suspension(Strictness)
  module Functorialisation = Functorialisation.Functorialisation(Strictness)

  module Memo = struct
    let tbl = Hashtbl.create 97

    let find i f =
      try Hashtbl.find tbl i with
      | Not_found ->
        let res = f i in
        Hashtbl.add tbl i res;
        res

    let id =
      Kernel.check_coh (Br[]) (Arr(Obj,Var(Db 0),Var(Db 0))) ("builtin_id", 0, None)
  end

  let arity_comp s =
    let n = List.length s in
    if !Settings.explicit_substitutions then
      (n-1)/2
    else n

  let rec ps_comp i =
    match i with
    | i when i <= 0 -> Error.fatal "builtin composition with less than 0 argument"
    | i when i = 1 -> Br [Br[]]
    | i ->
      match ps_comp (i-1) with
      | Br l -> Br (Br[] :: l)

  let comp_n arity =
    let build_comp i =
      let ps = ps_comp i in
      Kernel.check_noninv_coh ps (Var (Db 0)) (Var(Db 0)) ("builtin_comp", 0, None)
    in
    Memo.find arity build_comp

  let comp s =
    let arity = arity_comp s in
    comp_n arity

  let id = Memo.id

  let id_all_max ps =
    let d = Unchecked.dim_ps ps in
    let rec id_map l =
      let t = Var (Db 0) in
      match l with
      | [] -> [t, false]
      | Br[]::l -> (Coh(id, [t,true]), true)::(t,false)::(id_map l)
      | _ -> Error.fatal "identity must be inserted on maximal argument"
    in
    let rec aux i ps =
      match i,ps with
      | _, Br [] -> [Var (Db 0), true]
      | 0, Br l -> id_map l
      | i, Br l -> Unchecked.suspwedge_subs_ps
                     (List.map (aux (i-1)) l)
                     (List.map (Unchecked.ps_bdry) l)
    in
    aux (d-1) ps

  let unbiased_unitor ps t =
    let bdry =  Unchecked.ps_bdry ps in
    let src =
      let coh = Kernel.check_noninv_coh ps t t ("endo",0,None) in
      Coh(coh, id_all_max ps)
    in
    let a = Kernel.check_term (Unchecked.ps_to_ctx bdry) t in
    let da = Unchecked.dim_ty a in
    let sub_base = Unchecked.ty_to_sub_ps a in
    let tgt = Coh (Suspension.coh (Some da) id, (t,true)::sub_base) in
    Kernel.check_inv_coh bdry src tgt ("unbiased_unitor",0,None)

  (* returns the associator pairing up the middle two cells of a composite of
      (2*k) 1-cells. The argument is the integer k *)
  let middle_associator k =
    let ps = ps_comp (2*k) in
    let src = Coh(comp_n (2*k), Unchecked.(identity_ps ps)) in
    let tgt =
      let sub_assoc_middle =
        let rec compute_sub i =
          match i with
          | i when i <= 0 -> [Var(Db 0), false]
          | i when i < k ->
            (Var (Db (2*i)), true)::
            (Var (Db (2*i-1)), false)::
            (compute_sub (i-1))
          | i when i = k ->
            let sub_comp =
              [ Var (Db (2*k+2)),true;
                Var (Db (2*k+1)), false;
                Var (Db (2*k)), true;
                Var (Db (2*k-1)), false;
                Var (Db (2*k-3)), false]
            in
            let comp = (Coh(comp_n 2, sub_comp)) in
            (comp, true)::(Var (Db (2*k+1)), false)::(compute_sub (k-1))
          | i -> (Var (Db (2*i+2)), true)::
                 (Var (Db (2*i+1)), false)::
                 (compute_sub (i-1))
        in
        compute_sub (2*k-1)
      in
      Coh(comp_n (2*k-1), sub_assoc_middle)
    in
    Kernel.check_inv_coh ps src tgt ("focus", 0, None)

  (* returns the unitor cancelling the identity in the middle of a composite of
     (2*k+1) 1-cells. The argument is the integer k *)
  let middle_unitor k =
    let ps = ps_comp (2*k) in
    let src =
      let sub_id_middle =
        let rec compute_sub i =
          match i with
          | i when i <= 0 -> [Var (Db  0), false]
          | i when i <= k ->
            (Var (Db (2*i)), true)::
            (Var (Db (2*i-1)), false)::
            (compute_sub (i-1))
          | i when i = k+1 ->
            let id = (Coh(id, [Var (Db (2*k-1)), false])) in
            (id, true)::(Var (Db (2*k-1)), false)::(compute_sub (k))
          | i -> (Var (Db (2*i-2)), true)::
                 (Var (Db (2*i-3)), false)::
                 (compute_sub (i-1))
        in
        compute_sub (2*k+1)
      in
      Coh(comp_n (2*k+1), sub_id_middle) in
    let tgt = Coh(comp_n (2*k), Unchecked.(identity_ps ps)) in
    Kernel.check_inv_coh ps src tgt ("unit", 0, None)

  (* returns the whiskering rewriting the middle term of a composite of (2*k+1)
      1-cells. The argument is the integer k *)
  let middle_rewrite k =
    let comp = comp_n (2*k+1) in
    let func_data =
      List.concat [(List.init k (fun _ -> 0)); [1]; (List.init k (fun _ -> 0))]
    in
    Functorialisation.coh comp func_data
end
