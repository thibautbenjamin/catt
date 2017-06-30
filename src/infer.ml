open Stdlib
open Common
open Syntax
open Env
open PS

                                         
(** Normalization of a term, performs the substitutions when possible *)
let rec normalize e env =
  match e.desc with
  |Var x -> let value = (try Env.val_var x env with Error _ -> None) in
            begin match value with
            |None -> e 
            |Some e -> normalize e env
            end
  |Obj -> e
  |Arr (t,u,v) ->
    mk ~pos:e.pos ~show:e.show (Arr (normalize t env, normalize u env, normalize v env))
  |Coh (c,t) ->
    mk ~pos:e.pos ~show:e.show (Coh (normalize_ps c env, normalize t env))
  |Sub (t,s) -> let s = normalize_sub s env in
                let t = normalize t env in
                substitute ~pos:e.pos ~show:e.show t s
  |Badsub (t,l) -> assert false
and normalize_ps c env =
  PS.map (fun (x,t) -> (x,normalize t env)) c
and normalize_sub s env =
  match s with
  |[] -> []
  |(x,t)::s -> (x, normalize t env) :: (normalize_sub s env)



(** Elimination of ill-formed substitutions (syntaxic trick to avoid writing all variables) *)
let rec elim_badsub e env =
  match e.desc with
  |(Var _ | Obj)-> e
  |Arr (t,u,v) -> mk ~pos:e.pos ~show:e.show (Arr(elim_badsub t env, elim_badsub u env, elim_badsub v env))
  |Coh (ps,t) -> let ps = elim_badsub_ps ps env
                 and t = elim_badsub t env in
                 mk ~pos:e.pos ~show:e.show (Coh (ps,t))
  |Sub (t,s) -> let s = elim_badsub_sub s env
                and t = elim_badsub t env in
                mk ~pos:e.pos ~show:e.show (Sub (t,s))
  |Badsub (t,l) -> mk ~pos:e.pos ~show:e.show (Sub (t,PS.create_sub (PS.extract (normalize t env)) l))
and elim_badsub_ps ps env =
  PS.map (fun (x,t) -> (x,elim_badsub t env)) ps
and elim_badsub_sub s env =
  match s with
  |[] -> []
  |(x,e)::s -> (x,elim_badsub e env) :: (elim_badsub_sub s env)


                                         
let isEqual e1 e2 env =
  let rec equal e1 e2 =
    match e1.desc, e2.desc with
    |Var x,Var y -> x = y
    |Obj,Obj -> true
    |Arr(t1,u1,v1),Arr(t2,u2,v2) -> equal t1 t2 && equal u1 u2 && equal v1 v2
    |Coh(c1,t1),Coh(c2,t2) -> equal_ps c1 c2 && equal t1 t2
    |Sub(t1,s1),Sub(t2,s2) -> equal t1 t2 && equal_sub s1 s2
    |(Var _|Obj |Arr _|Coh _|Sub _ | Badsub _),_ -> false
  and equal_ps c1 c2 =
    match c1,c2 with
    |PNil (x1,t1), PNil (x2,t2) -> x1 = x2 && equal t1 t2
    |PCons (ps1,(x1,t1),(y1,u1)), PCons (ps2,(x2,t2),(y2,u2)) -> x1 = x2 && equal t1 t2 && y1 = y2 = equal u1 u2 && equal_ps ps1 ps2
    |PDrop ps1, PDrop ps2 -> equal_ps ps1 ps2
    |(PNil _|PCons _|PDrop _),_ -> false
  and equal_sub s1 s2 =
    match s1,s2 with
    |[],[] -> true
    |(x1,t1)::s1,(x2,t2)::s2 -> x1 = x2 && equal t1 t2 && equal_sub s1 s2
    |([] |(_::_)),_ -> false
  in equal (normalize e1 env) (normalize e2 env)

let checkEqual e1 e2 env =
  if (isEqual e1 e2 env) then () else error ~pos:e1.pos "got %s but %s is expected"
                                            (to_string e1) (to_string e2)


let rec print_vars l = match l with
  |[] -> ";"
  |t::q -> Printf.sprintf "%s %s" (string_of_var t) (print_vars q)
                                            
(** Type inference *)
let rec type_inference e env =
  match e.desc with
  |Var x -> begin try Env.ty_var x env
                  with Not_found -> error "unknown identifier %s" (string_of_var x)
            end
  |Coh (c,u) -> checkT u (PS.env_of_ps c);
                (*debug "ps_vars : %s" (print_vars (ps_vars c));
                debug "free_vars : %s" (print_vars (free_vars u));*)
                if List.included (ps_vars c) (free_vars u) then u
                else
                  let f,g = match u.desc with
                  |Arr(a,f,g) -> (f,g)  
                  |_ -> error "nor algebraic"
                  in
                  let i = PS.dim c in
                  let pss = PS.source (i-1) c and pst = PS.target (i-1) c in
                  (checkT f (PS.env_of_ps pss); checkT g (PS.env_of_ps pst);
                  if List.included (ps_vars pss) (free_vars f) && List.included (ps_vars pst) (free_vars g) then u
                  else error "not algebraic" )
  |Sub(t,s) -> begin match t.desc with
               |Coh(c,_) -> check_sub s (PS.env_of_ps c) env;
                            let ty = type_inference t env in mk ~pos:e.pos ~show:e.show (Sub (ty,s))
               |_ ->  assert (false)
               end
  |(Obj |Arr _ |Badsub _) -> error "this expression does not have a type"
and checkT e env =
  match e.desc with
  |Obj -> ()
  |Arr (t,u,v) -> checkT t env; checkType u t env; checkType v t env
  |_ -> error "expression %s is not a valid type" (to_string e) 
and checkType e1 e2 env =
  checkEqual (type_inference e1 env) e2 env 
(** TODO : write the functions check_ps and check_sub *)
and check_sub s c env =
  match s,c with
  |[],[] -> ()
  |(x,t)::s, (y,(None,u))::c when x = y ->
    check_sub s c env;
    checkT u c;
    checkEqual (substitute u s) (type_inference t env) env
  |_,_ -> error "not a correct substitution"
    
                                        
let infer e env = normalize (type_inference (normalize e env) env) env
    
  
let renew_vars e env =
  match e.desc with
  |Coh(ps,t) -> let ps,s = PS.rename_vars ps in
                (mk ~pos:e.pos ~show:e.show (Coh(ps, substitute t s)), List.append (PS.env_of_ps ps) env) 
  |_ -> (e,env)
