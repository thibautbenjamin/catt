open Common
open Kernel
open Unchecked_types.Unchecked_types(Coh)

module Memo = struct
  let tbl = Hashtbl.create 97
  let tbl_whisk = Hashtbl.create 97

  let find i f =
    try Hashtbl.find tbl i with
    | Not_found ->
      let res = f i in
      Hashtbl.add tbl i res;
      res

  let find_whisk i f =
    try Hashtbl.find tbl_whisk i with
    | Not_found ->
      let res = f i in
      Hashtbl.add tbl_whisk i res;
      res

  let id =
    check_coh (Br[]) (Arr(Obj,Var(Db 0),Var(Db 0))) ("builtin_id", 0, None)
end

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
    Coh.check_noninv ps (Var (Db 0)) (Var(Db 0)) ("builtin_comp", 0, None)
  in
  Memo.find arity build_comp

let arity_comp s =
  let n = List.length s in
  if !Settings.explicit_substitutions then
    (n-1)/2
  else n

let comp s =
  let arity = arity_comp s in
  comp_n arity

(* returns the n-composite of a (n+j)-cell with a (n+k)-cell *)
let whisk n j k =
  let build_whisk t =
    let n,j,k = t in
    let comp = comp_n 2 in
    let func_data = [k;j] in
    Suspension.coh (Some(n)) (Functorialisation.coh comp func_data)
  in
  Memo.find_whisk (n,j,k) build_whisk

(*
  How long should substitutions for whisk be?
  (whisk 0 0 0) requires ps-context (x(f)y(g)z) so 2+1+1+1
  (whisk n 0 0) requires 2*(n+1)+1+1+1
  (whisk n j 0) requires (2*(n+1))+((2*j)+1)+1+1
  (whisk n 0 k) requires (2*(n+1))+1+(2*k+1)+1

  Assuming ty1 has right dimension, we just need to know k
*)
let whisk_sub_ps k t1 ty1 t2 ty2 =
    let rec take n l =
        match l with
        | h::t when n > 0 -> h::(take (n-1) t)
        | _ -> [] in
    let sub_base = Unchecked.ty_to_sub_ps ty1 in
    let sub_ext = take (2*k+1) (Unchecked.ty_to_sub_ps ty2) in
    List.concat [[(t2,true)];sub_ext;[(t1,true)];sub_base]

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
    let coh = Coh.check_noninv ps t t ("endo",0,None) in
    Coh(coh, id_all_max ps)
  in
  let
    a = Ty.forget (Tm.typ (check_term (Ctx.check (Unchecked.ps_to_ctx bdry)) t))
  in
  let da = Unchecked.dim_ty a in
  let sub_base = Unchecked.ty_to_sub_ps a in
  let tgt = Coh (Suspension.coh (Some da) id, (t,true)::sub_base) in
  Coh.check_inv bdry src tgt ("unbiased_unitor",0,None)

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
  Coh.check_inv ps src tgt ("focus", 0, None)

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
  Coh.check_inv ps src tgt ("unit", 0, None)

(* returns the whiskering rewriting the middle term of a composite of (2*k+1)
    1-cells. The argument is the integer k *)
let middle_rewrite k =
  let comp = comp_n (2*k+1) in
  let func_data =
    List.concat [(List.init k (fun _ -> 0)); [1]; (List.init k (fun _ -> 0))] in
  Functorialisation.coh comp func_data

let () = Functorialisation.builtin_comp := comp_n
let () = Functorialisation.builtin_whisk := whisk
let () = Functorialisation.builtin_whisk_sub_ps := whisk_sub_ps

