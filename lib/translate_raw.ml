open Common

exception WrongNumberOfArguments

let elaborate : ((Var.t * Syntax.ty) list -> Syntax.ty ->
                 ps * ty * (Var.t * int) list) ref
    = ref (fun _ _ -> failwith "uninitialised forward reference")

let meta_namer_ty = ref 0
let meta_namer_tm = ref 0

let new_meta_ty () =
  let meta = Meta_ty !meta_namer_ty in
  meta_namer_ty := !meta_namer_ty + 1; meta
let new_meta_tm () =
  let i = !meta_namer_tm in
  let meta = Meta_tm i in
  meta_namer_tm := !meta_namer_tm + 1;
  meta, (i, new_meta_ty())

let list_functorialised s c =
  if not !Settings.explicit_substitutions then
    let rec list s c =
      match s,c with
      | [],[] -> [],[]
      | (t,true)::s, (x,(_, true))::tgt ->
        let s,func = list s tgt in
        t::s, x::func
      | (t,false)::s, (_,(_, true))::tgt ->
        let s,func = list s tgt in
        t::s, func
      | s , (_,(_, false))::tgt ->
        list s tgt
      | _::_, [] |[],_::_ -> raise WrongNumberOfArguments
    in list s c
  else
    let rec ensure_no_func = function
      | [] -> []
      | (_,true)::_ -> raise Error.FunctorialiseWithExplicit
      | (t,false)::s -> t::(ensure_no_func s)
    in ensure_no_func s,[]

(* inductive translation on terms and types without let_in *)
let rec tm c t =
  match t with
  | Syntax.Var v -> Var v, []
  | Syntax.Sub(Var v, s, susp) ->
     begin
       match Environment.val_var v with
       | Coh(ps, ty) ->
         let ps = Suspension.ps susp ps in
         let ty = Suspension.ty susp ty in
         let ctx = Unchecked.ps_to_ctx ps in
         let s,l = list_functorialised s ctx in
         let
           ps,ty =
           if l <> [] then Functorialisation.coh ps ty l else ps,ty
         in
         let s, meta_types = sub_ps c s ps in
         Coh(ps,ty,s), meta_types
       | Tm(tgt,t) ->
         let tgt = Suspension.ctx susp tgt in
         let t = Suspension.tm susp t in
         let s,l = list_functorialised s tgt in
         let tgt,t =
           if l <> [] then Functorialisation.tm tgt t l else tgt,t
         in
         let s, meta_types = sub c s tgt in
         Unchecked.tm_apply_sub t s, meta_types
     end;
  | Meta -> let m,meta_type = new_meta_tm() in (m,[meta_type])
  | Nat(x,t,t') ->
    begin
      match Environment.val_var x with
      | Coh(ps, _) ->
        let src,tgt = Naturality.identify_boundary c ps in
        let nat_ty =
          Syntax.Arr
            (Naturality.composition (Syntax.Sub(Var x,src,None)) t',
             Naturality.composition t (Syntax.Sub(Var x,tgt,None))) in
        let p,t,names = !elaborate c nat_ty in
        let names = Naturality.build_substitution names in
        Coh (p, t, names),[]
      | Tm(_,_) -> raise Error.NaturalityOnTerm
    end
  | Syntax.Sub (Letin_tm _,_,_)
  | Sub(Sub _,_,_)
  | Sub(Meta,_,_)
  | Sub (Nat _,_,_)
  | Letin_tm _ -> assert false
and sub_ps c s ps =
  let sub,meta_types = sub c s (Unchecked.ps_to_ctx ps) in
  List.map snd sub, meta_types
and sub c s tgt  =
  match s,tgt with
  | [],[] -> [],[]
  | t::s, (x,(_, true))::tgt ->
    let t, meta_types_t = tm c t in
    let s,meta_types_s = sub c s tgt in
    (x,t)::s,  List.append meta_types_t meta_types_s
  | t::s, (x,(_, false))::tgt when !Settings.explicit_substitutions ->
    let t, meta_types_t = tm c t in
    let s,meta_types_s = sub c s tgt in
    (x, t)::s, List.append meta_types_t meta_types_s
  | s , (x,(_, false))::tgt ->
    let t, meta_type = new_meta_tm() in
    let s,meta_types_s = sub c s tgt in
    (x, t)::s, meta_type::meta_types_s
  | _::_, [] |[],_::_ -> raise WrongNumberOfArguments

let ty c ty =
  match ty with
  | Syntax.Obj -> Obj,[]
  | Syntax.Arr(u,v) ->
     let (tu, meta_types_tu), (tv, meta_types_tv) = tm c u, tm c v in
     Arr(new_meta_ty(),tu, tv), List.append meta_types_tu meta_types_tv
  | Syntax.Letin_ty _ -> assert false

let ctx c =
  let rec aux c after =
    match c with
    | [] -> [],[]
    | (v,t) :: c ->
      let
        expl = not (List.exists (fun (_,ty) -> Syntax.var_in_ty v ty) after)
      in
      let ct, meta_c = aux c ((v,t)::after) in
      let t, meta_ty = ty c t in
      (v,(t,expl)) :: ct , List.append meta_ty meta_c
  in
  aux c []

let rec sub_to_suspended = function
  | [] ->
    let (m1,mc1),(m0,mc0) = new_meta_tm(), new_meta_tm() in
    [ m1; m0], [mc1; mc0]
  | t::s -> let s,m = sub_to_suspended s in t::s, m
