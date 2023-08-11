open Kernel
open Unchecked_types.Unchecked_types(Coh)

let tdb i = Var (Db i)

(* returns the associator pairing up the middle two cells of a composite of
    (2*k) 1-cells. The argument is the integer k *)
let middle_associator k =
  let ps = Builtin.ps_comp (2*k) in
  let src = Coh(Builtin.comp_n (2*k), Unchecked.(identity_ps ps)) in
  let tgt =
    let sub_assoc_middle =
      let rec compute_sub i =
        match i with
        | i when i <= 0 -> [Var(Db 0), false]
        | i when i < k ->
            (tdb (2*i), true)::(tdb (2*i-1), false)::(compute_sub (i-1))
        | i when i = k ->
            let sub_comp =
              [ tdb (2*k+2),true;
                tdb (2*k+1), false;
                tdb (2*k), true;
                tdb (2*k-1), false;
                tdb (2*k-3), false]
            in
            let comp = (Coh(Builtin.comp_n 2, sub_comp)) in
            (comp, true)::(tdb (2*k+1), false)::(compute_sub (k-1))
        | i -> (tdb (2*i+2), true)::(tdb (2*i+1), false)::(compute_sub (i-1))
      in
      compute_sub (2*k-1)
    in
    Coh(Builtin.comp_n (2*k-1), sub_assoc_middle)
  in
  Coh.check_inv ps src tgt ("focus", 0, None)

(* returns the unitor cancelling the identity in the middle of a composite of
(2*k+1) 1-cells. The argument is the integer k *)
let middle_unitor k =
  let ps = Builtin.ps_comp (2*k) in
  let src =
    let sub_id_middle =
      let rec compute_sub i =
        match i with
        | i when i <= 0 -> [tdb 0, false]
        | i when i <= k ->
            (tdb (2*i), true)::(tdb (2*i-1), false)::(compute_sub (i-1))
        | i when i = k+1 ->
          let id = (Coh(Builtin.id, [tdb (2*k-1), false])) in
            (id, true)::(tdb (2*k-1), false)::(compute_sub (k))
        | i -> (tdb (2*i-2), true)::(tdb (2*i-3), false)::(compute_sub (i-1))
      in
      compute_sub (2*k+1)
    in
    Coh(Builtin.comp_n (2*k+1), sub_id_middle) in
  let tgt = Coh(Builtin.comp_n (2*k), Unchecked.(identity_ps ps)) in
  Coh.check_inv ps src tgt ("unit", 0, None)

(** returns the whiskering rewriting the middle term of a composite of (2*k+1)
    1-cells. The argument is the integer k *)
let middle_rewrite k =
  let comp = Builtin.comp_n (2*k+1) in
  let func_data =
    List.concat [(List.init k (fun _ -> 0)); [1]; (List.init k (fun _ -> 0))] in
  Functorialisation.coh comp func_data
