open Stdlib
open Common
open Syntax
open Ps
open Env
       
let rec normalize e env =
  (*debug "normalizing %s in environnement : \n %s" (to_string e) (Env.to_string env);*)
  match e.desc with
  | Var x -> let value = (try Env.val_var x env with Not_found -> None) in
             begin match value with
             | None -> e
             | Some e -> normalize e env
             end
  | Type | Cat -> e
  | HomType c -> mk ~pos:e.pos ~show:e.show (HomType (normalize c env))
  | Obj c -> mk ~pos:e.pos ~show:e.show (Obj (normalize c env))
  | Arr (c,t,u,v) -> mk ~pos:e.pos ~show:e.show (Arr (normalize c env, normalize t env, normalize u env, normalize v env))
  | Pi (x,t,u) ->
     let t = normalize t env in
     mk ~pos:e.pos ~show:e.show (Pi (x, t, normalize u (Env.ext x t env)))
  | Lambda (x,t,u) ->
     let t = normalize t env in
     mk ~pos:e.pos ~show:e.show (Lambda (x, t, normalize u (Env.ext x t env)))
  | App (f,x) ->
     let x = normalize x env in
     begin match (normalize f env).desc with
     |Lambda (a,_,u) -> normalize (subst [(a,x)] u) env
     |f -> mk ~pos:e.pos ~show:e.show (App (mk f,x))
     end
  | Coh (str,c,ps,u) ->
     let env = Env.ext c (mk Cat) env in
     let (ps, env) = normalize_ps ps env in
     mk ~pos:e.pos ~show:e.show (Coh (str,c,ps,normalize u env))
  | Functor (e1,e2) -> mk ~pos:e.pos ~show:e.show (Functor (normalize e1 env, normalize e2 env))
  | Aptor (f,x) -> mk ~pos:e.pos ~show:e.show (Aptor (normalize f env, normalize x env))
  | Fcoh (str,f,(c,d),ps,t) ->
     let env = Env.ext c (mk Cat) env in
     let env = Env.ext d (mk Cat) env in
     let env = Env.ext f (mk (Functor (mk (Var c),mk (Var d)))) env in
     let (ps,env) = normalize_ps ps env in
     mk ~pos:e.pos ~show:e.show (Fcoh (str,f,(c,d),ps,normalize t env))
     
and normalize_ps ps env =
  match ps with
  | PStart (x,tx) -> let tx = normalize tx env in (PStart (x,tx), Env.ext x tx env)
  | PExt (ps,(x1,tx1),(x2,tx2)) -> let (ps, env) = normalize_ps ps env in
                                   let tx1 = normalize tx1 env in
                                   let env = Env.ext x1 tx1 env in
                                   let tx2 = normalize tx2 env in
                                   let env = Env.ext x2 tx2 env in
                                   (PExt (ps,(x1, tx1),(x2,tx2)), env)
  |PDrop ps -> let (ps,env) = normalize_ps ps env in (PDrop ps, env)

let rec string_of_sub s =
  match s with
  | [] -> ""
  | (x,y)::t -> "("^(string_of_var x)^", "^(to_string y)^") "^(string_of_sub s)
                                                              
                                                       
let isEqual e1 e2 env =
  let rec equal e1 e2 = 
  match e1.desc, e2.desc with
  | Var x1, Var x2 -> x1 = x2
  | Type, Type -> true
  | HomType c1, HomType c2 -> equal c1 c2
  | Cat, Cat -> true
  | Obj c1, Obj c2 -> equal c1 c2
  | Arr (c1,t1,u1,v1), Arr (c2,t2,u2,v2) -> equal c1 c2 && equal t1 t2 && equal u1 u2 && equal v1 v2
  | Pi (x1,t1,u1), Pi (x2,t2,u2) -> equal t1 t2 && (equal u1 (subst [(x2, (mk (Var x1)))] u2)) 
  | Lambda (x1,t1,u1), Lambda (x2,t2,u2) -> equal t1 t2 && (equal u1 (subst [(x2, (mk (Var x1)))] u2))
  | App (f1,x1), App (f2,x2) -> equal f1 f2 && equal x1 x2
  | Coh (_,c1,ps1,u1), Coh (_,c2,ps2,u2) ->
     (*debug "checking equality of coherences %s and %s" (to_string e1) (to_string e2);*)
     let s = [c2,mk (Var c1)] in
     let eq,sub = equal_ps ps1 ps2 s in
     eq && equal u1 (subst sub u2) 
  | Functor (e1,e2), Functor (g1,g2) -> equal e1 g1 && equal e2 g2
  | Aptor (f1,e1), Aptor (f2,e2) -> equal f1 f2 && equal e1 e2
  | Fcoh (_,f1,(c1,d1),ps1,u1), Fcoh (_,f2,(c2,d2),ps2,u2) ->
     let s = (c2,mk (Var c1)) :: (d2,mk (Var d1)) :: [f2,mk (Var f1)] in
     let eq,sub = equal_ps ps1 ps2 s in
     eq && equal u1 (subst sub u2)
  | (Var _ | Type | HomType _ | Cat | Obj _ | Arr _ | Pi _ | Lambda _ | App _ | Coh _ | Functor _ | Aptor _ | Fcoh _) , _ -> false
and equal_ps ps1 ps2 s =
  match ps1, ps2 with
  | PStart(x1,t1), PStart(x2,t2) ->  (equal t1 (subst s t2), (x2, (mk (Var x1)))::s)                                 
  | PExt (ps1,(x1,t1),(x2,t2)), PExt (ps2,(y1,u1),(y2,u2)) -> let (eq,sub) = equal_ps ps1 ps2 s in
                                                              let sub1 = ((y1, (mk (Var x1)))::sub) in
                                                              let sub2 = ((y2, (mk (Var x2)))::sub1) in
                                                              (eq && equal t1 (subst sub u1) && equal t2 (subst sub1 u2), sub2)
                                                               
  | PDrop ps1, PDrop ps2 -> equal_ps ps1 ps2 s
  | _ -> (false, [])
  in equal (normalize e1 env) (normalize e2 env)
           
let checkEqual e1 e2 env =
  if (isEqual e1 e2 env) then () else error ~pos:e1.pos "got %s but %s is expected"
                                            (to_string e1) (to_string e2)
                                                 
let rec infer e env =
  (* debug "infering type of %s" (to_string e);*)
  let res = match e.desc with
  | Var x -> Env.ty_var x env
  | Type -> mk Type
  | HomType c -> checkType c (mk Cat) env; mk Type 
  | Cat -> mk Type
  | Obj c -> checkType c (mk Cat) env; mk (HomType c)
  | Arr (c,t,u,v) ->
     checkType c (mk Cat) env;
     checkType t (mk (HomType c)) env;
     checkType u t env;
     checkType v t env;
     (mk (HomType c))
  | Pi (x,t,u) ->
     isType t env;
     isType u (Env.ext x t env);
     mk Type 
  | Lambda (x,t,u) ->
     isType t env;
     let te = infer t (Env.ext x t env) in
     mk (Pi (x,t,te)) 
  | App (f,x) -> begin
     let tf = infer f env in
     let tx = infer x env in
     match tf.desc with
     | Pi (a,t,u) -> checkEqual tx t env; subst [(a,x)] u
     | _ -> error ~pos:f.pos "got %s : %s but a function in expected" (to_string f) (to_string tf) end
  | (Coh (str,c,ps,t)) ->
     let homC = (mk (HomType (mk (Var c)))) in
     let env = ref (Env.add env c (mk Cat)) in
     let env' = ref (Env.add [] c (mk Cat)) in
     let ps =
       PS.map
         (fun (x,t) ->
           let t = normalize t !env in
           checkType t (homC) !env';
           env := Env.add !env x t;
           env':= Env.add !env' x t;
           x,t
         ) ps
     in 
     let env = !env in
     let env' = !env' in
     let t = normalize t env in
     checkType t homC env';
     let fv = PS.free_vars ps in
     let fvt = free_vars t in
     if not (List.included fv fvt) then
       begin
         (* debug "target is %s" (to_string t); *)
         let a,f,g =
           match t.desc with
           (** TODO : check if the checkEqual is necessary *)
           | Arr (c',a,f,g) -> checkEqual (mk (Var c)) c' env; a,f,g
           | _ -> assert false
         in
         let fva = free_vars a in
         let fvf = List.union (free_vars f) fva in
         let fvg = List.union (free_vars g) fva in
         begin
           let i = PS.dim ps in
           let pss = PS.source (i-1) ps in
           let pst = PS.target (i-1) ps in
           let fvs = PS.free_vars pss in
           let fvt = PS.free_vars pst in
           if i < 1
              || not (List.included fvs fvf)
              || not (List.included fvt fvg)
           then
             let bad = List.union (List.diff fvs fvf) (List.diff fvt fvg) in
             let bad = String.concat ", " (List.map string_of_var bad) in
             error ~pos:t.pos "not algebraic: %s not used in %s" bad (to_string (mk (Coh (str,c,ps,t))));
         end;
       end;
     mk (Pi (c, mk Cat, PS.fold_right (fun (x,t) u -> mk (Pi (x,t,u))) ps t))
  | Functor (e1,e2) -> checkType e1 (mk Cat) env; checkType e2 (mk Cat) env; mk Type
  | Aptor (f,x) ->
     let c,d = isFunct f env in
     checkType x (mk (Obj c)) env;
     mk (Obj d)
  |Fcoh (str,f,(c,d),ps,u) ->
     let homC = (mk (HomType (mk (Var c)))) in
     let homD = (mk (HomType (mk (Var d)))) in
     let funCD = mk (Functor (mk (Var c),mk (Var d))) in
     let env = ref (Env.add (Env.add (Env.add env f funCD) d (mk Cat)) c (mk Cat)) in
     let env' = ref (Env.add (Env.add (Env.add [] f funCD) d (mk Cat)) c (mk Cat)) in
     let ps =
       PS.map
         (fun (x,t) ->
           let t = normalize t !env in
           checkType t (homC) !env';
           env := Env.add !env x t;
           env':= Env.add !env' x t;
           x,t
         ) ps
     in 
     let env = !env in
     let env' = !env' in
     let u = normalize u env in
     checkType u homD env';
     let fv = PS.free_vars ps in
     let fvu = free_vars u in
     if not (List.included (c::d::[f]@fv) fvu)
     then
       begin     
         (*debug "target is %s" (to_string u);*)
         let a,g1,g2 =
           match u.desc with
           (** TODO : check if the checkEqual is necessary *)
           | Arr (d',a,g1,g2) -> checkEqual (mk (Var d)) d' env; a,g1,g2
           | _ -> assert false
         in
         let fva = free_vars a in
         let fvg1 = List.union (free_vars g1) fva in
         let fvg2 = List.union (free_vars g2) fva in
         begin
           let i = PS.dim ps in
           let pss = PS.source (i-1) ps in
           let pst = PS.target (i-1) ps in
           let fvs = (d::[f])@(PS.free_vars pss) in
           let fvt = (d::[f])@(PS.free_vars pst) in
           if i < 1
              || not (List.included fvs fvg1)
              || not (List.included fvt fvg2)
           then
             let bad = List.union (List.diff fvs fvg1) (List.diff fvt fvg2) in
             let bad = String.concat ", " (List.map string_of_var bad) in
             error ~pos:u.pos "not algebraic: %s not used in %s" bad (to_string (mk (Fcoh (str,f,(c,d),ps,u))));
         end;
       end;
     mk (Pi (c, mk Cat,
             mk (Pi (d, mk Cat,
                     mk (Pi (f, funCD,
                             PS.fold_right (fun (x,t) u -> mk (Pi (x,t,u))) ps u))))))
       
  in (*debug "type of %s infered to be %s" (to_string e) (to_string res);*) res
               
and checkType e1 e2 env =
  (*debug "checking that term %s is of type %s" (to_string e1) (to_string e2);*)
  checkEqual (infer e1 env) e2 env
and isType e env =
  let te = infer e env in
  match (normalize te env).desc with
  | Type -> () 
  | HomType c -> checkType c (mk Cat) env     
  | _ -> error ~pos:e.pos "got %s : %s but a type is expected" (to_string e) (to_string te)
and isFunct f env =
  let tf = infer f env in
  match (normalize tf env).desc with
  | Functor (c,d) -> c,d                
  | _ -> error ~pos:f.pos "got %s  : %s but a functor is expected" (to_string f) (to_string tf)   
