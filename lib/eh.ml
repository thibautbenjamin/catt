open Common
open Kernel
open Unchecked_types.Unchecked_types (Coh) (Tm)





let func (tm,ty) vars =
  (Functorialisation.tm_one_step_tm tm vars,Functorialisation.ty ty vars tm)


let rec disc = function
  | 0 -> Br []
  | n -> Br [(disc (n-1))]


let ternary_comp constr1 constr2 constr3 =
  Construct.comp_n [constr1;constr2;constr3]



(* [Gamma_n, Gamma_n-1, ... Gamma_m], [sigma_n, dots, sigma_m+1] *)
(* First variable of Gamma_i is v_i *)
(* type filtration = ctx list * sub list

(* [(p_n-1,q_n-1), ... (p_m, q_m)] *)
type padding_data = (Construct.constr * Construct.constr) list

let rec pad filtration padding_data = match padding_data, filtration with
  | [], ([(v_m,(ty,_)) :: _],[]) -> (Var v_m, ty)
  | (p_n,q_n)::padding_data_rest, ( _ :: ((v_n,(ty,b))::delta) :: ctx_rest ,sigma_nplus1 :: subs_rest) ->
  ternary_comp p_n (Construct.apply_sub (func (pad (((v_n,(ty,b))::delta) :: ctx_rest ,subs_rest) padding_data_rest) [v_n]) sigma_nplus1) q_n
  | _ -> assert false *)

let pad_one_step p_n q_n previous_padding v_n sigma 
= ternary_comp p_n (Construct.apply_sub (func previous_padding [v_n]) sigma) q_n

let x = Var.Name "x"
let x_constr = (Var x, Obj)
let id_n_x n = Construct.id_n n x_constr

let id_comp n k =
  let idnx = id_n_x n in
  if k < n then Construct.wcomp idnx k idnx
  else idnx

(* let id_comp_db n k =
    let id_n_x = Construct.id_n n (Var (Db 0),Obj) in 
    if k < n then Construct.wcomp id_n_x k id_n_x
    else id_n_x *)

let type_i_l i l = let t = id_comp i l in Construct.arr t t

let v_i_l i l = Var.Name ("v^" ^ (string_of_int i) ^ "_" ^ (string_of_int l))

let v_i_l_constr i l = (Var (v_i_l i l), type_i_l (i-1) l)

(* let gamma_i_l i l = [(v_i_l i l,(type_i_l (i-1) l, true));(x,(Obj,false))] *)
let sigma_i_l i l = [(Var.Bridge (v_i_l (i-1) l),(Var (v_i_l i l),true));(Var.Plus (v_i_l (i-1) l),(Construct.to_tm (id_comp (i-1) l),false));(v_i_l (i-1) l,(Construct.to_tm (id_comp (i-1) l),false));(x,(Var x, false))]
let gamma_i_l_to_point i l= [(v_i_l i l,(Construct.to_tm (id_comp i l),true));(x,(Var x,false))]
let x_to_db0 = [(x,(Var (Var.Db 0), true))]
let db0_to_x = [(Var x, true)]


let min k l = if k < l then k else l
(* 
let rec gamma_n_k_l n k l = let m = (min k l) + 1 in
  match n with
  | m -> ([gamma_i_l m l],[])
  | n ->  let (ctxs, subs) = gamma_n_k_l (n-1) k l in ((gamma_i_l n l)::ctxs, (sigma_i_l n l)::subs) *)



let rec padded_n_k_l n k l = let m = (min k l) + 1 in
  if n = m then (Var (v_i_l m l), type_i_l (m-1) l)
  else let n = n - 1 in let (p_n, q_n) = u_n_k_l n k l in pad_one_step p_n q_n (padded_n_k_l n k l) (v_i_l n l) (sigma_i_l (n+1) l)
  and u_n_k_l n k l = 
  let ty_pn = Construct.arr (id_comp n k) (Construct.apply_sub (padded_n_k_l n k l) (gamma_i_l_to_point n l)) in
  let ty_qn = Construct.arr (Construct.apply_sub (padded_n_k_l n k l) (gamma_i_l_to_point n l)) (id_comp n k) in
  ((Coh (check_coh (Br []) (Unchecked.ty_apply_sub ty_pn x_to_db0) ("p^"^(string_of_int n)^"_("^(string_of_int k)^","^(string_of_int l)^")",0,[]),[(Var x,true)])
    , ty_pn),
   (Coh (check_coh (Br []) (Unchecked.ty_apply_sub ty_qn x_to_db0) ("q^"^(string_of_int n)^"_("^(string_of_int k)^","^(string_of_int l)^")",0,[]),[(Var x,true)])
   , ty_qn))

let d_i_minus i = Var.Name ("d^"^(string_of_int i)^"_-")
let d_i_plus i = Var.Name ("d^"^(string_of_int i)^"_+")

let rec characteristic_sub_ty ty d = match (ty,d) with
  | Obj, _ -> []
  | Arr(ty2, tm1, tm2), d -> (d_i_plus d, (tm2, false)) :: (d_i_minus d, (tm1, false)) :: (characteristic_sub_ty ty2 (d-1)) 
  | _ -> assert false


let rec sphere_type = function
    | -1 -> Obj
    | n -> Arr(sphere_type @@ n-1,Var (d_i_minus n) ,Var (d_i_plus n))

let d_i_minus_constr i = (Var (d_i_minus i),sphere_type @@ i-1)
let d_i_plus_constr i = (Var (d_i_plus i),sphere_type @@ i-1)

let rec sphere_type_db = function 
| -1 -> Obj
| n -> Arr(sphere_type_db @@ n-1,Var (Var.Db (2*n)) ,Var (Var.Db (2*n+1)))

(* let rec sphere = function
    | -1 -> []
    | n -> (d_i_plus n, (sphere_type @@ n-1, false)) :: (d_i_minus n ,(sphere_type @@ n-1,false)) :: (sphere @@ n-1) *)

let v_i_lt i = Var.Name ("v^"^(string_of_int i)^"_<")
let v_i_gt i = Var.Name ("v^"^(string_of_int i)^"_>")

let v_i_lt_constr i = (Var (v_i_lt i), sphere_type (i-1))


let d_n_constr n = (Var (Var.Db (2*n)),sphere_type_db (n-1))

(* let gamma_i_lt i = (v_i_lt i,(sphere_type @@ i-1,true)) :: (sphere @@ i-1) *)

(* let gt_type_i i = if i = 0 then sphere_type 0 else Construct.arr (Construct.wcomp (d_i_minus_constr i) 0 (Construct.id_n i (d_i_plus_constr 0))) (Construct.wcomp (d_i_plus_constr i) 0 (Construct.id_n i (d_i_plus_constr 0))) *)
(* let v_i_gt_constr i = (Var (v_i_gt i), gt_type_i (i-1)) *)
(* let gamma_i_gt i = (v_i_gt i,(gt_type_i (i-1),true)) :: (sphere @@ i-1) *)

let include_sphere_source n = 
  let rec aux = function
  | (-1) -> []
  | n -> (Var (d_i_plus n), false) :: (Var (d_i_minus n), false) :: (aux @@ n-1)
in (Var (d_i_minus n), true) :: (aux @@ n-1)

let include_sphere_target n = 
  let rec aux = function
  | (-1) -> []
  | n -> (Var (d_i_plus n), false) :: (Var (d_i_minus n), false) :: (aux @@ n-1)
in (Var (d_i_plus n), true) :: (aux @@ n-1)


let rec sphere_to_db = function
  | (-1) -> []
  | n -> (d_i_plus n,(Var (Var.Db (2*n+1)),false)) :: (d_i_minus n,(Var (Var.Db (2*n)),false)) :: (sphere_to_db @@ n-1)

let gamma_i_gt_to_db n = (v_i_gt n, (Construct.to_tm @@ Construct.wcomp (d_n_constr n) 0 (Construct.id_n n (Var (Var.Db 1), Obj)),true))  :: (sphere_to_db (n-1))
let gamma_i_lt_to_db n = (v_i_lt n, (Var (Var.Db (2*n)),true)) :: (sphere_to_db (n-1))


let rec sphere_include_n = function
  | (-1) -> []
  | n -> (d_i_plus n , (Var (d_i_plus n),false)) :: (d_i_minus n, (Var (d_i_minus n),false)) :: (sphere_include_n (n-1))

let rec sphere_include_db = function
| (-1) -> []
| n -> (Var (d_i_plus n),false) :: (Var (d_i_minus n),false) :: (sphere_include_db (n-1))

let sigma_i_lt n = (Var.Bridge (v_i_lt (n-1)),(Var (v_i_lt n),true)) :: (Var.Plus (v_i_lt (n-1)),(Var (d_i_plus (n-1)),false)) :: (v_i_lt (n-1),(Var (d_i_minus (n-1)),false)) :: (sphere_include_n (n-2))
let sigma_i_gt n = (Var.Bridge (v_i_gt (n-1)),(Var (v_i_gt n),true)) :: (Var.Plus (v_i_gt (n-1)),(Construct.to_tm (Construct.wcomp (d_i_plus_constr (n-1)) 0 (Construct.id_n (n-1) (d_i_plus_constr 0))),false)) :: (v_i_gt (n-1),(Construct.to_tm (Construct.wcomp (d_i_minus_constr (n-1)) 0 (Construct.id_n (n-1) (d_i_plus_constr 0))),false)) :: (sphere_include_n (n-2))

let lt_n_to_source_nplus1 n = (v_i_lt n,(Var (d_i_minus n),true)) :: (sphere_include_n (n-1))
let lt_n_to_target_nplus1 n = (v_i_lt n,(Var (d_i_plus n),true)) :: (sphere_include_n (n-1))

let inlcude_source_db n = (Var (d_i_minus n),true) :: sphere_include_db (n-1)
let include_target_db n = (Var (d_i_plus n), true) :: sphere_include_db (n-1)

let rec bpadded_lt n  = 
  if n = 1 then (Var (v_i_lt 1), sphere_type 0)
  else let n = n - 1 in let (p_n,q_n) = (b_lt n) in pad_one_step p_n q_n (bpadded_lt n) (v_i_lt n) (sigma_i_lt (n+1))
  and b_lt n = 
    let p_type = Construct.arr (Construct.wcomp (v_i_lt_constr n) 0 (Construct.id_n n (d_i_plus_constr 0))) (bpadded_lt n) in
    let q_type = Construct.arr (bpadded_lt n) (Construct.wcomp (v_i_lt_constr n) 0 (Construct.id_n n (d_i_plus_constr 0))) in
    (
    (Coh (check_coh (disc n) (Unchecked.ty_apply_sub p_type (gamma_i_lt_to_db n)) ("p^"^(string_of_int n)^"_<",0,[]),include_sphere_source n),Unchecked.ty_apply_sub p_type (lt_n_to_source_nplus1 n))
    ,
    (Coh (check_coh (disc n) (Unchecked.ty_apply_sub q_type (gamma_i_lt_to_db n)) ("q^"^(string_of_int n)^"_<",0,[]),include_sphere_target n),Unchecked.ty_apply_sub q_type (lt_n_to_target_nplus1 n))
    )
    
let rec bpadded_gt n =
  if n = 1 then (Var (v_i_gt 1), sphere_type 0)
  else let n = n - 1 in let (p_n,q_n) = (b_gt n) in pad_one_step p_n q_n (bpadded_gt n) (v_i_gt n) (sigma_i_gt (n+1))
  and b_gt n = 
    let p_type = Construct.arr (d_n_constr n) (Construct.apply_sub  (bpadded_gt n) (gamma_i_gt_to_db n )) in
    let q_type = Construct.arr (Construct.apply_sub  (bpadded_gt n) (gamma_i_gt_to_db n)) (d_n_constr n) in
  (
  (Coh (check_coh (disc n) (p_type) ("p^"^(string_of_int n)^"_>",0,[]),include_sphere_source n),Unchecked.ty_apply_sub_ps p_type (inlcude_source_db n))
  ,
  (Coh (check_coh (disc n) (q_type) ("q^"^(string_of_int n)^"_>",0,[]),include_sphere_target n),Unchecked.ty_apply_sub_ps q_type (include_target_db n))
  )


let hexcomp fminus fplus ybridge fbridge gminus gplus gbridge zbridge hminus hplus hbridge  = 
  let d = (Construct.dim fminus) - 1 in
  let x,y,z,w = Var.Name "x", Var.Name "y", Var.Name "z", Var.Name "w" in
  let x_constr, y_constr, z_constr, w_constr = (Var x, sphere_type (d-1)), (Var y, sphere_type (d-1)), (Var z, sphere_type (d-1)), (Var w, sphere_type (d-1)) in
  let f,g,h = Var.Name "f" , Var.Name "g", Var.Name "h" in
  let f_constr,g_constr,h_constr = (Var f, Construct.arr x_constr y_constr), (Var g, Construct.arr y_constr z_constr), (Var h, Construct.arr z_constr w_constr) in
  let fgh = ternary_comp f_constr g_constr h_constr in
  let hexfgh = func fgh [y;f;z;g;h] in
  let x_im = Construct._src 1 fminus in
  let yminus = Construct.tgt 1 fminus in
  let yplus = Construct.tgt 1 fplus in
  let zminus = Construct._src 1 hminus in
  let zplus = Construct._src 1 hplus in
  let w_im = Construct.tgt 1 hminus in
  let subs = (Var.Bridge h, (Construct.to_tm hbridge, true)) :: (Var.Plus h, (Construct.to_tm hplus, false)) :: (h, (Construct.to_tm hminus, false)) ::
  (w, (Construct.to_tm w_im, false)) ::
  (Var.Bridge g, (Construct.to_tm gbridge, true)) :: (Var.Plus g, (Construct.to_tm gplus, false)) :: (g, (Construct.to_tm gminus, false)) ::
  (Var.Bridge z, (Construct.to_tm zbridge, false)) :: (Var.Plus z, (Construct.to_tm zplus, false)) :: (z, (Construct.to_tm zminus, false)) ::
  (Var.Bridge f, (Construct.to_tm fbridge, true)) :: (Var.Plus f, (Construct.to_tm fplus, false)) :: (f, (Construct.to_tm fminus, false)) ::
  (Var.Bridge y, (Construct.to_tm ybridge, false)) :: (Var.Plus y, (Construct.to_tm yplus, false)) :: (y, (Construct.to_tm yminus, false)) ::
  (x, (Construct.to_tm x_im, false)) :: (characteristic_sub_ty (Construct.to_ty w_im) (d-1)) in
  Construct.apply_sub hexfgh subs

let repad_one_step p_0 p_1 f_n q_0 q_1 g_n previous_repadding iota_minus iota_plus v_i sigma=
  let padding_0 = Construct._src 1 previous_repadding in
  let padding_1 = Construct.tgt 1 previous_repadding in
  hexcomp p_0 p_1 (Construct.apply_sub (Construct.apply_sub previous_repadding iota_minus) sigma) f_n (Construct.apply_sub (func padding_0 [v_i]) sigma) (Construct.apply_sub (func padding_1 [v_i]) sigma) (Construct.inverse (Construct.apply_sub (func previous_repadding [v_i]) sigma)) (Construct.apply_sub (Construct.apply_sub previous_repadding iota_plus) sigma) q_0 q_1 g_n

let iota_minus i l = [(v_i_l i l, (Var (v_i_l i l), true));(x, (Var x, false))]
let iota_plus i l = [(v_i_l i l, (Var (Var.Plus (v_i_l i l)), true));(x, (Var x, false))]

let rec sphere_to_point = function
  | (-1) -> []
  | n -> (d_i_plus n, (Construct.to_tm (Construct.id_n n x_constr), false)) :: (d_i_minus n, (Construct.to_tm (Construct.id_n n x_constr), false)) :: (sphere_to_point (n-1))

(* let gamma_lt_to_point n = (v_i_lt n , (Construct.to_tm (Construct.id_n n (Var x,Obj)), true)) :: (sphere_to_point (n-1)) *)
let gamma_lt_to_gamma_i_l n = (v_i_lt n , (Var (v_i_l n (n-1)), true)) :: (sphere_to_point (n-1))
let gamma_gt_to_gamma_i_l n = (v_i_gt n , (Var (v_i_l n 0), true)) :: (sphere_to_point (n-1))

let rec repad_lt n i =
  if i = 1 then Construct.id_n 1 (v_i_l_constr 1 (n-1)) else
  let i = i-1 in
  let p_lt, q_lt = b_lt i in
  let p_lt_subbed = Construct.apply_sub p_lt (gamma_lt_to_gamma_i_l (i+1)) in
  let q_lt_subbed = Construct.apply_sub q_lt (gamma_lt_to_gamma_i_l (i+1)) in
  let p_u, q_u = u_n_k_l i 0 (n-1) in
  (* let lt_padding = Construct.apply_sub (bpadded_lt i) (gamma_lt_to_point i) in
  let unbiased_padding = padded_n_k_l n 0 (i-1) in *)
  let previous_repadding = repad_lt n i in
  let iota_m = (iota_minus i (n-1)) in
  let iota_p = (iota_plus i (n-1)) in
  let sigma = sigma_i_l (i+1) (n-1) in
  let f_type = Construct.arr (Construct.wcomp p_lt_subbed i (Construct.apply_sub (Construct.apply_sub previous_repadding iota_m) sigma)) p_u in
  let g_type = Construct.arr q_lt_subbed (Construct.wcomp (Construct.apply_sub (Construct.apply_sub previous_repadding iota_p) sigma) i q_u) in
  let f = (Coh(check_coh (Br []) (Unchecked.ty_apply_sub f_type x_to_db0) ("f^"^(string_of_int i)^"_("^(string_of_int n)^",<)",0,[]),[(Var x, true)]),f_type) in
  let g = (Coh(check_coh (Br []) (Unchecked.ty_apply_sub g_type x_to_db0) ("g^"^(string_of_int i)^"_("^(string_of_int n)^",<)",0,[]),[(Var x, true)]),g_type) in
  repad_one_step p_lt_subbed p_u f q_lt_subbed q_u g previous_repadding iota_m iota_p (v_i_l i (n-1)) sigma

let rec repad_gt n i =
  if i = 1 then Construct.id_n 1 (v_i_l_constr 1 0) else
  let i = i-1 in
  let p_gt, q_gt = b_gt i in
  let p_gt_subbed = Construct.apply_sub p_gt (gamma_gt_to_gamma_i_l (i+1)) in
  let q_gt_subbed = Construct.apply_sub q_gt (gamma_gt_to_gamma_i_l (i+1)) in
  let p_u, q_u = u_n_k_l i (n-1) 0 in
  (* let lt_padding = Construct.apply_sub (bpadded_lt i) (gamma_lt_to_point i) in
  let unbiased_padding = padded_n_k_l n 0 (i-1) in *)
  let previous_repadding = repad_gt n i in
  let iota_m = (iota_minus i 0) in
  let iota_p = (iota_plus i 0) in
  let sigma = sigma_i_l (i+1) 0 in
  let f_type = Construct.arr (Construct.wcomp p_gt_subbed i (Construct.apply_sub (Construct.apply_sub previous_repadding iota_m) sigma)) p_u in
  let g_type = Construct.arr q_gt_subbed (Construct.wcomp (Construct.apply_sub (Construct.apply_sub previous_repadding iota_p) sigma) i q_u) in
  let f = (Coh(check_coh (Br []) (Unchecked.ty_apply_sub f_type x_to_db0) ("f^"^(string_of_int i)^"_("^(string_of_int n)^",>)",0,[]),[(Var x, true)]),f_type) in
  let g = (Coh(check_coh (Br []) (Unchecked.ty_apply_sub g_type x_to_db0) ("g^"^(string_of_int i)^"_("^(string_of_int n)^",>)",0,[]),[(Var x, true)]),g_type) in
  repad_one_step p_gt_subbed p_u f q_gt_subbed q_u g previous_repadding iota_m iota_p (v_i_l i 0) sigma


let drop n xs =
  let rec aux xs counter =
    match xs with
    | [] -> []
    | h :: tl -> if counter > 0 then h :: aux tl (counter - 1) else []
  in aux xs (List.length xs - n)


let whisker left middle right = Construct.wcomp_n 0 [left;middle;right] 
   
let intch_n_h n h =
  let d_1_L_constr = (Var (Var.Db 2), Arr(Obj, Var (Var.Db 0), Var (Var.Db 1))) in
  let d_1_R_constr = (Var (Var.Db (2*n+2*h+4)), Arr(Obj, Var (Var.Db 3), Var (Var.Db (2*n+2*h+3)))) in
  let rec adj_sphere_type k = if k = 0 then Arr(Obj, Var(Var.Db 1), Var(Var.Db 3)) else Arr (adj_sphere_type (k-1), Var (Var.Db (2*k + 2)), Var (Var.Db (2 * k + 3))) in
  let d_n_constr i = if i = 0 then (Var (Var.Db (2 + 2*n)), adj_sphere_type (n-1)) else (Var (Var.Db (1 + 2*n+2*i)), adj_sphere_type (n-1)) in
  let d_nplus1_i_constr i =  (Var (Var.Db (2+2*n+2*i)), Construct.arr (d_n_constr (i-1)) (d_n_constr i)) in
  let rec middle_constrs r = if r = h + 1 then [] else (d_nplus1_i_constr r) :: (middle_constrs (r+1))
  in
  let rec middle_whiskered r = if r = h + 1 then [] else (whisker d_1_L_constr (d_nplus1_i_constr r) d_1_R_constr) :: (middle_whiskered (r+1))
  in
  let rec chain = function
  | 0 -> []
  | h -> (Br []) :: (chain (h-1))
  in
  let rec tower xs = function
  | 0 -> Br xs
  | n -> Br [(tower xs (n-1))]
  in
  let intch_ctx_db = Br [Br [];tower (chain h) (n-1);Br []] in
  let coh_type = Construct.arr  (Construct.comp_n @@ middle_whiskered 1) (whisker d_1_L_constr (Construct.comp_n @@ middle_constrs 1) d_1_R_constr) in
  (check_coh intch_ctx_db coh_type ("chi^"^(string_of_int n)^"_"^(string_of_int h),0,[]), coh_type)

let b_n n = Var.Name ("b^"^(string_of_int n))
let a_n n = Var.Name ("a^"^(string_of_int n))

let a_n_constr n = (Var (a_n n), type_i_l (n-1) (n-1))
let b_n_constr n = (Var (b_n n), type_i_l (n-1) (n-1))

let rec padded_n_k_l_func_r n k l = function
  | 1 -> func (padded_n_k_l n k l) [v_i_l n l]
  | r -> func (Construct.apply_sub (padded_n_k_l_func_r n k l (r-1)) (sigma_i_l (n+r-1) l)) [v_i_l (n+r-1) l]


let eh_ctx n = [(b_n n ,(type_i_l (n-1) (n-1),true));(a_n n,(type_i_l (n-1) (n-1),true));(x,(Obj,false))]

let a_n_comp_id i l = if l = i-1 then (Var (a_n i), type_i_l (i-1) (i-1)) else Construct.wcomp (Var (a_n i),type_i_l (i-1) (i-1)) l (Construct.id_n i x_constr)
let id_comp_b_n i l = if l = i-1 then (Var (b_n i), type_i_l (i-1) (i-1)) else Construct.wcomp (Construct.id_n i x_constr) l (Var (b_n i),type_i_l (i-1) (i-1))

let gamma_i_l_to_eh_a i l = [(v_i_l i l,(Construct.to_tm @@ a_n_comp_id i l,true));(x,(Var x, false))] 
let gamma_i_l_to_eh_b i l = [(v_i_l i l,(Construct.to_tm @@ id_comp_b_n i l,true));(x,(Var x, false))] 

let gamma_iminus1_l_func_to_eh_a i l = [(Var.Bridge (v_i_l (i-1) l),(Construct.to_tm @@ a_n_comp_id i l,true));(Var.Plus (v_i_l (i-1) l),(Construct.to_tm @@ id_comp (i-1) l,false));(v_i_l (i-1) l,(Construct.to_tm @@ id_comp (i-1) l,false));(x,(Var x, false))] 
let gamma_iminus1_l_func_to_eh_b i l = [(Var.Bridge (v_i_l (i-1) l),(Construct.to_tm @@ id_comp_b_n i l,true));(Var.Plus (v_i_l (i-1) l),(Construct.to_tm @@ id_comp (i-1) l,false));(v_i_l (i-1) l,(Construct.to_tm @@ id_comp (i-1) l,false));(x,(Var x, false))] 

let rec xi_n_i_lt n i = match i with
  | 1 -> Construct.id_n 1 (Construct.wcomp (a_n_comp_id n (n-1)) (n-1) (id_comp_b_n n (n-1)))
  | i -> let (p,q) = u_n_k_l (i-1) 0 (n-1) in
    let sub =
    (drop (2*i-1) (Construct.characteristic_sub_ps q))  
    @ (drop (2*n-1) (Construct.characteristic_sub_ps (Construct.apply_sub (padded_n_k_l_func_r (i-1) 0 (n-1) (n-i+1)) (gamma_iminus1_l_func_to_eh_b n (n-1)) )))   
    @ (drop (2*i-1) (Construct.characteristic_sub_ps (Construct.apply_sub (padded_n_k_l_func_r (i-1) 0 (n-1) (n-i+1)) (gamma_iminus1_l_func_to_eh_a n (n-1)) ))) 
    @ Construct.characteristic_sub_ps p
  in 
  let (chi,chi_ty) = intch_n_h (n-i) 2 in
  let chi_applied = (Coh (Suspension.coh (Some (i-1)) chi, sub), Unchecked.ty_apply_sub_ps (Suspension.ty (Some (i-1)) chi_ty) sub) in
    Construct.wcomp chi_applied n (Construct.wcomp_n (i-1) [p ;(xi_n_i_lt n (i-1)); q])

let rec xi_n_i_gt n i = match i with
| 1 -> Construct.id_n 1 (Construct.wcomp (a_n_comp_id n 0) (n-1) (id_comp_b_n n 0))
| i -> let (p,q) = u_n_k_l (i-1) (n-1) 0 in
  let sub =
  (drop (2*i-1) (Construct.characteristic_sub_ps q))  
  @ (drop (2*n-1) (Construct.characteristic_sub_ps (Construct.apply_sub (padded_n_k_l_func_r (i-1) (n-1) 0 (n-i+1)) (gamma_iminus1_l_func_to_eh_b n 0) )))   
  @ (drop (2*i-1) (Construct.characteristic_sub_ps (Construct.apply_sub (padded_n_k_l_func_r (i-1) (n-1) 0 (n-i+1)) (gamma_iminus1_l_func_to_eh_a n 0) ))) 
  @ Construct.characteristic_sub_ps p
in 
let (chi,chi_ty) = intch_n_h (n-i) 2 in
let chi_applied = (Coh (Suspension.coh (Some (i-1)) chi, sub), Unchecked.ty_apply_sub_ps (Suspension.ty (Some (i-1)) chi_ty) sub) in
Construct.wcomp chi_applied n (Construct.wcomp_n (i-1) [p ;(xi_n_i_gt n (i-1)); q])

let assoc_33_to_middle2 =
  let tree = Br [Br[];Br[];Br[];Br[];Br[];Br[]] in
  let f1 = (Var (Var.Db 2), Arr(Obj,Var (Var.Db 0), Var (Var.Db 1))) in
  let f2 = (Var (Var.Db 4), Arr(Obj,Var (Var.Db 1), Var (Var.Db 3))) in
  let f3 = (Var (Var.Db 6), Arr(Obj,Var (Var.Db 3), Var (Var.Db 5))) in
  let f4 = (Var (Var.Db 8), Arr(Obj,Var (Var.Db 5), Var (Var.Db 7))) in
  let f5 = (Var (Var.Db 10), Arr(Obj,Var (Var.Db 7), Var (Var.Db 9))) in
  let f6 = (Var (Var.Db 12), Arr(Obj,Var (Var.Db 9), Var (Var.Db 11))) in
  let cohty = Construct.arr 
  (Construct.wcomp (ternary_comp f1 f2 f3) 0 (ternary_comp f4 f5 f6))
  (ternary_comp f1 (ternary_comp f2 (Construct.wcomp f3 0 f4) f5) f6)
  in
  (Coh (check_coh tree cohty ("assoc",0,[]),Unchecked.identity_ps tree), cohty)
  
let middle_unitor = 
  let tree = Br [Br []; Br []] in
  let f1 = (Var (Var.Db 2), Arr(Obj,Var (Var.Db 0), Var (Var.Db 1))) in
  let f2 = (Var (Var.Db 4), Arr(Obj,Var (Var.Db 1), Var (Var.Db 3))) in
  let x1 = (Var (Var.Db 1), Obj) in
  let cohty = Construct.arr
  (ternary_comp f1 (Construct.id_n 1 x1) f2)
  (Construct.wcomp f1 0 f2) in
  (Coh (check_coh tree cohty ("unitor",0,[]), Unchecked.identity_ps tree), cohty)

let xi_lt n = 
  let (p,q) = u_n_k_l (n-1) 0 (n-1) in
  let padded_a = Construct.apply_sub (padded_n_k_l_func_r (n-1) 0 (n-1) (1)) (gamma_iminus1_l_func_to_eh_a n (n-1)) in
  let padded_b = Construct.apply_sub (padded_n_k_l_func_r (n-1) 0 (n-1) (1)) (gamma_iminus1_l_func_to_eh_b n (n-1)) in
  let sub6 = 
    (Construct.to_tm q,true) ::
    ((Construct.to_tm @@ Construct.tgt 1 q),false) ::
    (Construct.to_tm padded_b,true) ::
    ((Construct.to_tm @@ Construct.tgt 1 padded_b),false) ::
    (Construct.to_tm p,true) ::
    ((Construct.to_tm @@ Construct.tgt 1 p),false) ::
    (Construct.to_tm q,true) ::
    ((Construct.to_tm @@ Construct.tgt 1 q),false) ::
    (Construct.to_tm padded_a,true) ::
    ((Construct.to_tm @@ Construct.tgt 1 padded_a),false) ::
     Construct.characteristic_sub_ps p
  in
  let assoc = Construct.apply_sub_ps (Construct.suspend (n-1) assoc_33_to_middle2) sub6 in
  let w = Construct.witness q in
  let sub2 =  
  (Construct.to_tm padded_b,true) ::
  ((Construct.to_tm @@ Construct.tgt 1 padded_b),false) ::
  (Construct.characteristic_sub_ps padded_a)
  in
  let unitor = Construct.apply_sub_ps (Construct.suspend (n-1) middle_unitor) sub2 in
  Construct.comp_n [
    assoc ; 
    Construct.wcomp_n (n-1) [p ;(Construct.wcomp_n (n-1) [padded_a ;w ;padded_b]) ;q ];
    Construct.wcomp_n (n-1) [p; unitor; q] ;
    Construct.wcomp_n (n-1) [p ;(xi_n_i_lt n (n-1)); q]
  ]

let xi_gt n = 
  let (p,q) = u_n_k_l (n-1) (n-1) 0 in
  let padded_a = Construct.apply_sub (padded_n_k_l_func_r (n-1) (n-1) 0 (1)) (gamma_iminus1_l_func_to_eh_a n (0)) in
  let padded_b = Construct.apply_sub (padded_n_k_l_func_r (n-1) (n-1) 0 (1)) (gamma_iminus1_l_func_to_eh_b n (0)) in
  let sub6 = 
    (Construct.to_tm q,true) ::
    ((Construct.to_tm @@ Construct.tgt 1 q),false) ::
    (Construct.to_tm padded_b,true) ::
    ((Construct.to_tm @@ Construct.tgt 1 padded_b),false) ::
    (Construct.to_tm p,true) ::
    ((Construct.to_tm @@ Construct.tgt 1 p),false) ::
    (Construct.to_tm q,true) ::
    ((Construct.to_tm @@ Construct.tgt 1 q),false) ::
    (Construct.to_tm padded_a,true) ::
    ((Construct.to_tm @@ Construct.tgt 1 padded_a),false) ::
      Construct.characteristic_sub_ps p
  in
  let assoc = Construct.apply_sub_ps (Construct.suspend (n-1) assoc_33_to_middle2) sub6 in
  let w = Construct.witness q in
  let sub2 =  
  (Construct.to_tm padded_b,true) ::
  ((Construct.to_tm @@ Construct.tgt 1 padded_b),false) ::
  (Construct.characteristic_sub_ps padded_a)
  in
  let unitor = Construct.apply_sub_ps (Construct.suspend (n-1) middle_unitor) sub2 in
  Construct.comp_n [
    assoc ; 
    Construct.wcomp_n (n-1) [p ;(Construct.wcomp_n (n-1) [padded_a ;w ;padded_b]); q] ;
    Construct.wcomp_n (n-1) [p ;unitor ;q] ;
    Construct.wcomp_n (n-1) [p ;(xi_n_i_gt n (n-1)) ;q]
  ]

let zeta n = 
  let tree = Br[disc (n-1); disc (n-1)] in
  let rec sphere_type_L = function
  | (-1) -> Obj
  | k -> Arr(sphere_type_L (k-1),Var (Var.Db (2*k)), Var (Var.Db (2*k + 1)))
  in
  let rec sphere_type_R = function
  | (-1) -> Obj
  | 0 -> Arr (Obj, Var (Var.Db 1), Var (Var.Db (2*n + 1)))
  | k -> Arr (sphere_type_R (k-1),Var (Var.Db (2*n + 2*k)),Var (Var.Db (2*n + 2*k + 1)))
  in
  let d_l = (Var (Var.Db (2*n)),sphere_type_L (n-1)) in
  let d_r = (Var (Var.Db (4*n)),sphere_type_R (n-1)) in
  let cohty = Construct.arr
  (Construct.wcomp (Construct.wcomp d_l 0 (Construct.id_n 1 (Construct._src 1 d_r))) (n-1) (Construct.wcomp (Construct.id_n 1 (Construct.tgt 1 d_l)) 0 d_r))
  (Construct.wcomp d_l 0 d_r)
  in
  let sub = (drop 1 (Construct.characteristic_sub_ps (Var (b_n n),type_i_l (n-1) (n-1)))) @ (Construct.characteristic_sub_ps (Var (a_n n), type_i_l (n-1) (n-1))) in
  (Coh (check_coh tree cohty ("zeta^"^(string_of_int n), 0, []), sub), Unchecked.ty_apply_sub_ps cohty sub)
  
let zeta_inv n = 
  let tree = Br[disc (n-1); disc (n-1)] in
  let rec sphere_type_L = function
  | (-1) -> Obj
  | k -> Arr(sphere_type_L (k-1),Var (Var.Db (2*k)), Var (Var.Db (2*k + 1)))
  in
  let rec sphere_type_R = function
  | (-1) -> Obj
  | 0 -> Arr (Obj, Var (Var.Db 1), Var (Var.Db (2*n + 1)))
  | k -> Arr (sphere_type_R (k-1),Var (Var.Db (2*n + 2*k)),Var (Var.Db (2*n + 2*k + 1)))
  in
  let d_l = (Var (Var.Db (2*n)),sphere_type_L (n-1)) in
  let d_r = (Var (Var.Db (4*n)),sphere_type_R (n-1)) in
  let cohty = Construct.arr
  (Construct.wcomp d_l 0 d_r)
  (Construct.wcomp (Construct.wcomp d_l 0 (Construct.id_n 1 (Construct._src 1 d_r))) (n-1) (Construct.wcomp (Construct.id_n 1 (Construct.tgt 1 d_l)) 0 d_r))
  in
  let sub = (drop 1 (Construct.characteristic_sub_ps (Var (b_n n),type_i_l (n-1) (n-1)))) @ (Construct.characteristic_sub_ps (Var (a_n n), type_i_l (n-1) (n-1))) in
  (Coh (check_coh tree cohty ("zeta^"^(string_of_int n), 0, []), sub), Unchecked.ty_apply_sub_ps cohty sub)
    

let first_step_gt n = 
  let p_type = Construct.arr (d_n_constr n) (Construct.apply_sub  (bpadded_gt n) (gamma_i_gt_to_db n )) in
  let pad = (Coh (check_coh (disc n) p_type ("p^"^(string_of_int n)^"_>",0,[]),Unchecked.identity_ps @@ disc n),p_type) in
let phi = Construct.apply_sub_ps pad (Construct.characteristic_sub_ps (a_n_constr n)) in
let phi_op = Construct.apply_sub_ps (Construct.op [1] pad) (Construct.characteristic_sub_ps (b_n_constr n)) in
Construct.wcomp phi (n-1) phi_op

let second_step_lt n = 
  let p_type = Construct.arr (Construct.wcomp (d_n_constr n) 0 (Construct.id_n n (Var (Var.Db 1),Obj))) (Construct.apply_sub (bpadded_lt n) (gamma_i_lt_to_db n)) in
  let pad = (Coh (check_coh (disc n) p_type ("p^"^(string_of_int n)^"_<",0,[]),Unchecked.identity_ps @@ disc n),p_type) in
let phi = Construct.apply_sub_ps pad (Construct.characteristic_sub_ps (a_n_constr n)) in
let phi_op = Construct.apply_sub_ps (Construct.op [1] pad) (Construct.characteristic_sub_ps (b_n_constr n)) in
Construct.wcomp phi (n-1) phi_op

let second_step_gt n = 
  let r = repad_gt n n in
  let repad_a = Construct.apply_sub r (gamma_i_l_to_eh_a n 0) in
  let repad_b =  Construct.apply_sub (Construct.op [1] r) (gamma_i_l_to_eh_b n 0) in
  Construct.wcomp repad_a (n-1) repad_b

let third_step_lt n = 
  let r = repad_lt n n in
  let repad_a = Construct.apply_sub r (gamma_i_l_to_eh_a n (n-1)) in
  let repad_b =  Construct.apply_sub (Construct.op [1] r) (gamma_i_l_to_eh_b n (n-1)) in
  Construct.wcomp repad_a (n-1) repad_b  

let func_v_to_zeta n = [(Var.Bridge (v_i_l n 0),(Construct.to_tm @@ zeta n,true));(Var.Plus (v_i_l n 0),(Construct.to_tm @@ Construct.wcomp (a_n_constr n) 0 (b_n_constr n),false));(v_i_l n 0,(Construct.to_tm @@ Construct.wcomp (a_n_comp_id n 0) (n-1) (id_comp_b_n n 0),false));(x,(Var x, false))]

let fourth_step_gt n = Construct.apply_sub (func (padded_n_k_l n (n-1) 0) [v_i_l n 0]) (func_v_to_zeta n)


let eh_gt n =
  Construct.comp_n [first_step_gt n; second_step_gt n; xi_gt n; fourth_step_gt n]

let eh_lt n = Construct.comp_n [zeta_inv n ; second_step_lt n; third_step_lt n ; xi_lt n]

let swap_a_and_b n = [(b_n n, (Var (a_n n), true)); (a_n n, (Var (b_n n), true)); (x, (Var x, false))]

let suspended_point_to_point = [(x,(Construct.to_tm @@ Construct.id_n 1 x_constr, true)); (Var.Db 1, (Var x, false)); (Var.Db 0, (Var x, false))]

let rec repad_suspended n k l i =
  let m = (min k l) + 1 in
  if i = m then Construct.id_n 1 (v_i_l_constr i l) else
    let i = i-1 in
    let p_u_minus, q_u_minus = u_n_k_l (i-1) (k-1) (l-1) in
    let p_s = Construct.apply_sub (Construct.suspend 1 p_u_minus) suspended_point_to_point in
    let q_s = Construct.apply_sub (Construct.suspend 1 q_u_minus) suspended_point_to_point in
    let p_u, q_u = u_n_k_l i k l in
    (* let lt_padding = Construct.apply_sub (bpadded_lt i) (gamma_lt_to_point i) in
    let unbiased_padding = padded_n_k_l n 0 (i-1) in *)
    let previous_repadding = repad_suspended n k l i in
    let iota_m = (iota_minus i l) in
    let iota_p = (iota_plus i l) in
    let sigma = sigma_i_l (i+1) l in
    let f_type = Construct.arr (Construct.wcomp p_s i (Construct.apply_sub (Construct.apply_sub previous_repadding iota_m) sigma)) p_u in
    let g_type = Construct.arr q_s (Construct.wcomp (Construct.apply_sub (Construct.apply_sub previous_repadding iota_p) sigma) i q_u) in
    let f = (Coh(check_coh (Br []) (Unchecked.ty_apply_sub f_type x_to_db0) ("f^"^(string_of_int i)^"_("^(string_of_int n)^","^(string_of_int k)^","^(string_of_int l)^")",0,[]),[(Var x, true)]),f_type) in
    let g = (Coh(check_coh (Br []) (Unchecked.ty_apply_sub g_type x_to_db0) ("g^"^(string_of_int i)^"_("^(string_of_int n)^","^(string_of_int k)^","^(string_of_int l)^")",0,[]),[(Var x, true)]),g_type) in
    repad_one_step p_s p_u f q_s q_u g previous_repadding iota_m iota_p (v_i_l i l) sigma

let gamma_i_l_to_a_comp_b n l = [(v_i_l n l, (Construct.to_tm @@ Construct.wcomp (a_n_constr n) l (b_n_constr n), true)); (x, (Var x, false))]

let eh_suspended_to_eh n = [(b_n n,(Var (b_n (n+1)),true)); (a_n n,(Var (a_n (n+1)),true)) ; (x, (Construct.to_tm @@ Construct.id_n 1 x_constr,false));(Var.Db 1, (Var x,false)); (Var.Db 0, (Var x, false))]

let suspension_move eh_minus n k l = 
  let suspended_eh = Construct.apply_sub (Construct.suspend 1 eh_minus) (eh_suspended_to_eh (n-1)) in
  Construct.comp_n [suspended_eh; (Construct.apply_sub (repad_suspended n k l n) (gamma_i_l_to_a_comp_b n l))]    

let nat_unitor constr = 
  let x_constr = (Var (Var.Db 0), Obj) in
  let y_constr = (Var (Var.Db 1), Obj) in
  let f_constr = (Var (Var.Db 2), Construct.arr x_constr y_constr) in
  let cohty = Construct.arr f_constr (Construct.comp_n [f_constr;Construct.id_n 1 y_constr]) in
  let runit = check_coh (disc 1) cohty ("unit_r^-1",0,[]) in
  let d = Construct.dim constr in
  let sub = Construct.characteristic_sub_ps constr in
  (Coh(Suspension.coh (Some (d-1)) runit,sub),Unchecked.ty_apply_sub_ps (Suspension.ty (Some (d-1)) cohty) sub)


let nat_factor prev_eh n k l = 
  let db0 = (Var (Var.Db 0), Obj) in
  let idnx = Construct.id_n n db0 in
  let lhs = Construct.id_n 1 (Construct.wcomp idnx k idnx) in
  let eh_to_id = [(b_n n, (Construct.to_tm idnx,true)) ; (a_n n, (Construct.to_tm idnx,true)) ; (x, (Var (Var.Db 0),false))] in
  let (_,q_n) = u_n_k_l n k l in
  let rhs = Construct.comp_n [Construct.apply_sub prev_eh eh_to_id;Construct.apply_sub q_n x_to_db0] in
  let cohty = Construct.arr lhs rhs in
  let coherence = check_coh (disc 0) cohty ("factor_identity^"^(string_of_int n)^"_("^(string_of_int k)^","^(string_of_int l)^")", 0, []) in
  (Coh(coherence,db0_to_x), Unchecked.ty_apply_sub_ps cohty db0_to_x)

let nat_associator1 constr1 constr2 constr3 =
  let f1 = (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) in
  let f2 = (Var (Var.Db 4), Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))) in
  let f3 = (Var (Var.Db 6), Arr (Obj, Var (Var.Db 3), Var (Var.Db 5))) in
  let cohty = Construct.arr (Construct.comp_n [f1 ; Construct.comp_n [f2; f3]]) (Construct.comp_n [Construct.comp_n [f1 ; f2] ; f3]) in
  let coherence = check_coh (Br[Br[];Br[];Br[]]) cohty ("assoc^-1",0,[]) in
  let d = Construct.dim constr1 in
  let sub = Construct.characteristic_sub_ps_composite [constr1;constr2;constr3] in
  (Coh(Suspension.coh (Some (d-1)) coherence,sub),Unchecked.ty_apply_sub_ps (Suspension.ty (Some (d-1)) cohty) sub)

let nat_associator2 constr1 constr2 constr3 =
  let f1 = (Var (Var.Db 2), Arr (Obj, Var (Var.Db 0), Var (Var.Db 1))) in
  let f2 = (Var (Var.Db 4), Arr (Obj, Var (Var.Db 1), Var (Var.Db 3))) in
  let f3 = (Var (Var.Db 6), Arr (Obj, Var (Var.Db 3), Var (Var.Db 5))) in
  let cohty = Construct.arr  (Construct.comp_n [Construct.comp_n [f1 ; f2] ; f3]) (Construct.comp_n [f1 ; f2 ; f3]) in
  let coherence = check_coh (Br[Br[];Br[];Br[]]) cohty ("assoc_ternary",0,[]) in
  let d = Construct.dim constr1 in
  let sub = Construct.characteristic_sub_ps_composite [constr1;constr2;constr3] in
  (Coh(Suspension.coh (Some (d-1)) coherence,sub),Unchecked.ty_apply_sub_ps (Suspension.ty (Some (d-1)) cohty) sub)

let nat_finalcoh prev_eh n k l = 
  let db0 = (Var (Var.Db 0), Obj) in
  let idnx = Construct.id_n n db0 in
  let eh_to_id = [(b_n n, (Construct.to_tm idnx,true)) ; (a_n n, (Construct.to_tm idnx,true)) ; (x, (Var (Var.Db 0),false))] in
  let (p_n,_) = u_n_k_l n k l in
  let lhs = Construct.apply_sub prev_eh eh_to_id in
  let rhs = Construct.apply_sub p_n (x_to_db0) in 
  let cohty = Construct.arr lhs rhs in
  let coherence = check_coh (disc 0) cohty ("eh_to_p^"^(string_of_int n)^"_("^(string_of_int k)^","^(string_of_int l)^")", 0, []) in
  (Coh(coherence,db0_to_x), Unchecked.ty_apply_sub_ps cohty db0_to_x)

let eh_func_to_eh n = [(Var.Bridge (b_n n),(Var (b_n (n+1)),true));(Var.Plus (b_n n),(Construct.to_tm @@ id_n_x n,false));(b_n n,(Construct.to_tm @@ id_n_x n,false));(Var.Bridge (a_n n),(Var (a_n (n+1)),true));(Var.Plus (a_n n),(Construct.to_tm @@ id_n_x n,false));(a_n n,(Construct.to_tm @@ id_n_x n,false));(x,(Var x, false))]

let gamma_i_l_func_to_a_comp_b n l = [(Var.Bridge (v_i_l n l),(Construct.to_tm @@ Construct.wcomp (a_n_constr (n+1)) l (b_n_constr (n+1)),true)); (Var.Plus (v_i_l n l),(Construct.to_tm @@ id_comp n l,false)); (v_i_l n l,(Construct.to_tm @@ id_comp n l,false));(x,(Var x, false))]

let naturality_move prev_eh n k l =
  let a_k_b = Construct.wcomp (a_n_constr (n+1)) k (b_n_constr (n+1)) in
  let (_,q_n) = u_n_k_l n k l in
  let idnx = id_n_x n in
  let eh_to_id = [(b_n n, (Construct.to_tm idnx,true)) ; (a_n n, (Construct.to_tm idnx,true)) ; (x, (Var x,false))] in
  let nat = Construct.inverse (Construct.apply_sub (func prev_eh [b_n n;a_n n]) (eh_func_to_eh n)) in
  let paddedfunc = Construct.apply_sub (func (padded_n_k_l n k l) [v_i_l n l]) (gamma_i_l_func_to_a_comp_b n l) in
  let eh_id_id = Construct.apply_sub prev_eh eh_to_id in
  Construct.comp_n [
    nat_unitor a_k_b ;
    Construct.wcomp a_k_b n (nat_factor prev_eh n k l) ;
    nat_associator1 a_k_b eh_id_id q_n ; 
    Construct.wcomp nat n q_n ;
    nat_associator2 eh_id_id paddedfunc q_n ;
    Construct.wcomp_n n [nat_finalcoh prev_eh n k l ; paddedfunc ; q_n]
  ]



(* let rec eh_alt n k l = 
  if k = 0 && l = (n-1) then eh_lt n
  else if k = (n-1) && l = 0 then eh_gt n
  (*Pathway 1 : all suspensions then all naturalities*)
  else if (min k l) = 0 then naturality_move (eh_alt (n-1) k l) (n-1) k l
  else suspension_move (eh_alt (n-1) (k-1) (l-1)) n k l  *)

let max k l = if k > l then k else l

let rec eh n k l = 
  if k = 0 && l = (n-1) then eh_lt n
  else if k = (n-1) && l = 0 then eh_gt n
 
  (* Pathway 2 : all naturalities then all suspensions *) 
  else if (max k l) = (n-1) then suspension_move (eh (n-1) (k-1) (l-1)) n k l
  else naturality_move (eh (n-1) k l) (n-1) k l
  
let full_eh n k l = 
  let ehnkl = eh n k l in
  Construct.comp_n [ehnkl; Construct.inverse (Construct.apply_sub (Construct.op [l+1] (ehnkl)) (swap_a_and_b n))]
(* 
let full_eh_alt n k l = 
  let ehnkl = eh_alt n k l in
  Construct.comp_n [ehnkl; Construct.inverse (Construct.apply_sub (Construct.op [l+1] (ehnkl)) (swap_a_and_b n))] *)


  
 