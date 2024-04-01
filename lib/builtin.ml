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

(*
% https://q.uiver.app/#q=WzAsMTgsWzEsMiwiMCJdLFszLDIsIjMiXSxbMyw0LCI0Il0sWzEsNCwiMSJdLFsxLDAsIjAiXSxbMywwLCIxIl0sWzMsMSwiMCJdLFswLDQsIlxcYnVsbGV0Il0sWzAsNSwiXFxidWxsZXQiXSxbMSw1LCJcXGJ1bGxldCJdLFs1LDEsIjEiXSxbNywxLCI1Il0sWzAsNiwiMCJdLFsyLDYsIjEiXSxbNCw2LCIzIl0sWzUsMCwiMyJdLFs1LDMsIjAiXSxbNywzLCIxIl0sWzAsMSwiNiIsMCx7ImN1cnZlIjotM31dLFsxLDIsIjUiLDFdLFswLDMsIjIiLDFdLFszLDIsIjciLDIseyJjdXJ2ZSI6M31dLFsxLDMsIjgiLDEseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9LCJsZXZlbCI6Mn1dLFswLDEsIjYiLDFdLFszLDIsIjciLDFdLFs0LDUsIjIiLDFdLFs3LDhdLFs4LDldLFs2LDEwLCIyIiwxLHsiY3VydmUiOi0yfV0sWzYsMTAsIjMiLDEseyJjdXJ2ZSI6Mn1dLFsxMCwxMSwiNiIsMV0sWzEyLDEzLCIyIiwxXSxbMTMsMTQsIjQiLDEseyJjdXJ2ZSI6LTJ9XSxbMTMsMTQsIjUiLDEseyJjdXJ2ZSI6Mn1dLFs1LDE1LCI0IiwxXSxbMTYsMTcsIjIiLDEseyJjdXJ2ZSI6LTV9XSxbMTYsMTcsIjUiLDEseyJjdXJ2ZSI6Mn1dLFsxNiwxNywiMyIsMSx7ImN1cnZlIjotMn1dLFsxNiwxNywiNyIsMSx7ImN1cnZlIjo1fV0sWzI0LDIxLCIiLDIseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9fV0sWzE4LDIzLCIiLDAseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9fV0sWzI4LDI5LCI0IiwxLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dLFszMiwzMywiNiIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XSxbMzUsMzcsIjQiLDEseyJzaG9ydGVuIjp7InNvdXJjZSI6MjAsInRhcmdldCI6MjB9fV0sWzM3LDM2LCI2IiwxLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfX1dLFszNiwzOCwiOCIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH19XV0=
*)

let tdb i = Var (Db i)
let comp_unary x y f = Coh(comp_n 1, [(f,true);(y,false);(x,false)])
let comp_binary x y f z g = Coh(comp_n 2, [(g,true);(z,false);(f,true);(y,false);(x,false)])

let ccomp_unary =
    let phase1_sub_ps = [(tdb 5,true);(tdb 4,false);(tdb 6,true);(tdb 3,false);(tdb 0,false)] in
    let phase1_sub = Unchecked.list_to_db_level_sub (List.map fst phase1_sub_ps) in
    let phase1_src = (comp_binary (tdb 0) (tdb 1) (tdb 2) (tdb 3) (comp_unary (tdb 1) (tdb 3) (tdb 4))) in
    let phase1_tgt = (comp_binary (tdb 0) (tdb 1) (tdb 2) (tdb 3) (tdb 4)) in
    let phase1 = Coh(Coh.check_inv (ps_comp 2) phase1_src phase1_tgt ("builtin_unbiasor",0,None),phase1_sub_ps) in
    let phase3_sub_ps = [(tdb 7,true);(tdb 4,false);(tdb 2,true);(tdb 1,false);(tdb 0,false)] in
    let phase3_sub = Unchecked.list_to_db_level_sub (List.map fst phase3_sub_ps) in
    let phase3_src = (comp_binary (tdb 0) (tdb 1) (tdb 2) (tdb 3) (tdb 4)) in
    let phase3_tgt = (comp_binary (tdb 0) (tdb 1) (comp_unary (tdb 0) (tdb 1) (tdb 2)) (tdb 3) (tdb 4)) in
    let phase3 = Coh(Coh.check_inv (ps_comp 2) phase3_src phase3_tgt ("builtin_biasor",0,None),phase3_sub_ps) in
    let phase1_sub_contr = [(phase1,true);(Unchecked.tm_apply_sub phase1_tgt phase1_sub,false);(Unchecked.tm_apply_sub phase1_src phase1_sub,false);(tdb 4,false);(tdb 0,false)] in
    let phase2_sub_contr = [(tdb 8,true);(Unchecked.tm_apply_sub phase3_src phase3_sub,false)] in
    let phase3_sub_contr = [(phase3,true);(Unchecked.tm_apply_sub phase3_tgt phase3_sub,false)] in
    let comp_sub = List.concat [phase3_sub_contr;phase2_sub_contr;phase1_sub_contr] in
    let comp = Suspension.coh (Some(1)) (comp_n 3) in
    Coh(comp,comp_sub)

let ccomp_n _arity =
    ccomp_unary

let ccomp s =
  let arity = arity_comp s in
  ccomp_n arity

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

