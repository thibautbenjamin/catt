open Common
open Stdlib

type var =
  | Name of string
  | New of string * int

type expr =
  {
    desc : desc;
    pos : Pos.t;
  }
and desc =
  | Var of var
  | Type
  | HomType
  | Cat
  | Obj
  | Arr of expr * expr * expr
  | Pi of var * expr * expr
  | Lambda of var * expr * expr
  | App of expr * expr
  | Coh of string * ps * expr
  | Functor of expr * expr
  (** Application of a functor*)
  | Aptor of expr * expr
  (** Transfer of coherences using functoriality*)
  | Functorial of string * ps * expr * expr
and ps =
  | PStart of (var * expr)
  | PExt of ps * (var * expr) * (var * expr)
  | PDrop of ps

let mk ?pos desc =
  let pos = match pos with
    | None -> Pos.dummy
    | Some pos ->  pos
  in
  { desc; pos }

 let rec ps_fold_right f ps s =
    match ps with
    | PStart x -> f x s
    | PExt (ps,x,y) ->
       let s = f y s in
       let s = f x s in
       ps_fold_right f ps s
    | PDrop ps -> ps_fold_right f ps s
    
let rec free_vars e =
  match e.desc with
  | Var x -> [x]
  | Type | HomType | Obj | Cat -> []
  | Arr (t,u,v) -> (free_vars t) @ (free_vars u) @ (free_vars v)
  | Pi (x,t,u) -> (free_vars t) @ (List.remove x (free_vars u))
  | Lambda (x,t,u) -> (free_vars t)@(List.remove x (free_vars u))
  | App (f,x) -> (free_vars f)@(free_vars x)
  | Coh (c,ps,t) -> ps_fold_right (fun (x,t) l -> (free_vars t)@(List.remove x l)) ps (free_vars t)
  | Functor (c,d) -> (free_vars c)@(free_vars d)
  | Aptor (f,x) -> (free_vars f)@(free_vars x)
      
let string_of_var = function
  | Name s -> s
  | New (s,k) -> s^(Printf.sprintf ".%d" k)

let rec to_string e =
  match e.desc with
  | Var x -> string_of_var x
  | Type -> "Type"
  | HomType -> "HomType"
  | Cat -> "Cat"
  | Obj -> "*" 
  | Arr (t,a,b) -> (*Printf.sprintf "%s | %s → %s" (to_string t) (to_string a) (to_string b)*)
                   Printf.sprintf "%s | %s -> %s" (to_string t) (to_string a) (to_string b)
  | Pi (x,t,e) -> (*Printf.sprintf "∀(%s : %s), %s" (string_of_var x) (to_string t) (to_string e)*)
     if List.mem x (free_vars e) then Printf.sprintf "(%s : %s) => %s" (string_of_var x) (to_string t) (to_string e)
     else Printf.sprintf "%s => %s" (to_string t) (to_string e)
  | Lambda (x,t,e) -> (*Printf.sprintf "fun (%s : %s) ↦ %s" (string_of_var x) (to_string t) (to_string e)*)
                      Printf.sprintf "fun (%s : %s) => %s" (string_of_var x) (to_string t) (to_string e)
  | App (f,e) -> Printf.sprintf "%s (%s)" (to_string f) (to_string e)
  | Coh (str,ps,t) -> "Coh_"^str (*Printf.sprintf "coh %s => %s " (string_of_ps ps) (to_string t)*)
  | Functor (e1,e2) -> (*Printf.sprintf "%s ⇒ %s" (to_string e1) (to_string e2)*)
                       Printf.sprintf "Functor(%s,%s)" (to_string e1) (to_string e2)
  | Aptor (f,e) -> (* Printf.sprintf "Ap(%s, %s)" (to_string f) (to_string e) *)
                      Printf.sprintf "%s.(%s)" (to_string f) (to_string e)
  | Functorial _ -> "Functoriality"
and string_of_ps = function
  | PStart (x,t) -> Printf.sprintf "(%s: %s)" (string_of_var x) (to_string t)
  | PExt (ps, (x1, t1), (x2, t2)) -> string_of_ps ps ^ (Printf.sprintf " (%s: %s) (%s: %s)"
                         (string_of_var x1) (to_string t1) (string_of_var x2) (to_string t2)) 
  | PDrop ps -> (string_of_ps ps )^ " ! "

let string_of_expr = to_string
                                      
(** Substitutions *)
let refresh =
  let k = ref 0 in
  function
  | Name x | New(x,_) -> incr k; New(x, !k)

let rec subst s e =
  let desc = 
    match e.desc with
    | Var x -> begin try (List.assoc x s).desc with Not_found -> Var x end
    | Type -> Type
    | HomType -> HomType
    | Cat -> Cat
    | Obj -> Obj
    | Arr (t,a,b) -> Arr (subst s t, subst s a, subst s b) 
    | Pi (x,t,e) -> let x' = refresh x in
                    let s' = ((x, mk ~pos:e.pos (Var x'))::s) in
                    Pi (x', subst s t, subst s' e) 
    | Lambda (x,t,e) -> let x' = refresh x in
                        let s' = ((x, mk ~pos:e.pos (Var x'))::s) in
                        Lambda (x', subst s t, subst s' e)
    | App (f,e) -> App (subst s f, subst s e)
    | Coh (str,ps,t) -> let ps,s = subst_ps s ps in Coh (str,ps, subst s t)
    | Functor (e1, e2) -> Functor (subst s e1, subst s e2)
    | Aptor (f,e) -> Aptor (subst s f, subst s e)
    | Functorial (str,ps,f,t) -> let ps,s = subst_ps s ps in Functorial (str,ps,subst s f, subst s t)
  in
  mk ~pos:e.pos desc

and subst_ps s ps =
  let rec aux ps = match ps with   
    | PStart (x,t) -> let x' = refresh x in
                      let is = ((x, mk (Var x'))::s) in
                      (PStart (x', subst s t),is)
    | PExt (ps,(x1,t1),(x2,t2)) -> let x1' = refresh x1 in
                                   let x2' = refresh x2 in
                                   let ps,is = aux ps in
                                   let is' = ((x1, mk (Var x1'))::is) in
                                   let is'' = ((x2, mk (Var x2'))::is') in
                                   (PExt (ps,(x1',subst is t1),(x2',subst is' t2)),is'')
    | PDrop ps -> let ps,is = aux ps in (PDrop ps, is)
  in aux ps
         
module Env = struct
  type t = (var * (expr option * expr)) list

  let rec string_of_env (env:t) =
    match env with
    |(x,(Some e, t))::env -> (string_of_env env)^ Printf. sprintf "%s = %s : %s \n" (string_of_var x) (to_string e) (to_string t)
    |(x,(None, t))::env -> (string_of_env env) ^ Printf.sprintf "%s : %s \n" (string_of_var x) (to_string t)
    |[] -> ""

  let to_string = string_of_env

  let add (env:t) x ?value t : t = (x,(value,t))::env                      
                    
  let ty_var x env =
    try
      snd (List.assoc x env)
    with
      Not_found -> error "variable %s is not known in the environnement" (string_of_var x) 

  let val_var x env =
    try
      fst (List.assoc x env)
    with
      Not_found -> error "variable %s is not known in the environnement" (string_of_var x) 
  let ext x ?value t (env:t) = (x,(value,t))::env
                                            
end
               
module PS = struct
  type t = ps

  exception Invalid
 
  let to_string  = string_of_ps   

  let rec marker = function
    | PStart (x,tx) -> (x,tx)
    | PExt (ps,_,y) -> y
    | PDrop ps ->
       let f,tf = marker ps in
       match tf.desc with
       | Arr (_,x,{desc = Var y}) ->
          let t =
            let rec aux = function
              | PStart (a,t) -> assert (a = y); t
              | PExt (ps,(a,ta),(b,tb)) ->
                 if a = y then ta
                 else if b = y then tb
                 else aux ps
              | PDrop ps -> aux ps
            in aux ps
          in y,t
       | _ -> raise Invalid
                     
  let rec free_vars = function
    | PStart (x,_) -> [x]
    | PExt (ps,(x,_),(y,_)) -> y::x::(free_vars ps)
    | PDrop ps -> free_vars ps

  let make l : t =
    let (a,ta,l) = match l with
      |(a, ta)::l -> begin match ta.desc with
                     | App(o, c) -> begin match o.desc with
                                    | Obj -> (a,ta,l)
                                    | _ -> error "pasting scheme must start with an object"
                                    end
                     | Obj -> a,ta,l
                     | _ -> error "pasting scheme must start with an object"
                     end
      |[] -> error "pasting scheme cannot be empty"
    in
    let rec aux ps = function
      | ((x,tx)::(y,ty)::l) as l'  -> begin
          match ty.desc with
          | Arr (_, {desc = Var source}, {desc = Var targ}) ->
             if (x <> targ) then
               error ~pos:ty.pos "not a pasting scheme (types do not match: target of the arrow is %s, but %s was expected)"
                     (string_of_var targ) (string_of_var x);
             let (a,ta) = marker ps in
             if a = source then
               let fv = free_vars ps in
               assert (not (List.mem y fv));
               assert (not (List.mem x fv));
               let ps = PExt (ps,(x,tx),(y,ty)) in
               aux ps l
             else
               aux (PDrop ps) l'
          | _ -> error ~pos:ty.pos "not a pasting scheme (types do not match : got %s, but an arrow was expected)" (string_of_expr ty)
        end          
      | [] -> ps
      | [x,tx] ->  error ~pos:tx.pos "This is not a pasting scheme (invalid parity)"
    in
    aux (PStart (a,ta)) l

  let rec height = function
    | PStart _ -> 0
    | PExt (ps,_,_) -> (height ps) + 1
    | PDrop ps -> (height ps) - 1

  let rec dim = function
    | PStart _ -> 0
    | PExt (ps,_,_) -> max (dim ps) (height ps + 1)
    | PDrop ps -> dim ps

  let source i ps =
    assert (i >= 0);
    let rec aux = function
      | PStart _ as ps -> ps 
      | PExt (ps,_,_) when height ps >= i -> aux ps
      | PExt (ps,y,f) -> PExt(aux ps,y,f)
      | PDrop ps when height ps > i -> aux ps
      | PDrop ps -> PDrop (aux ps)
    in aux ps

  let target i ps =
    assert (i >= 0);
    let replace g = function
      | PStart x -> PStart g
      | PExt (ps,y,f) -> PExt (ps,y,g)
      | _ -> assert false
    in
    let rec aux = function
      | PStart _ as ps -> ps
      | PExt (ps,_,_) when height ps > i -> aux ps
      | PExt (ps,y,f) when height ps = i -> replace y (aux ps)
      | PExt (ps,y,f) -> PExt (aux ps,y,f)
      | PDrop ps when height ps > i -> aux ps
      | PDrop ps -> PDrop (aux ps)
    in
    aux ps
                      
  let rec map f = function
    | PStart x -> PStart (f x)
    | PExt (ps,x,y) ->
       let ps = map f ps in
       let x = f x in
       let y = f y in
       PExt (ps,x,y)
    | PDrop ps -> PDrop (map f ps)

  let rec fold_left f s = function
    | PStart x -> f s x
    | PExt (ps,x,y) ->
       let s = fold_left f s ps in
       let s = f s x in
       f s y
    | PDrop ps -> fold_left f s ps

  let rec fold_left2 f s ps1 ps2 =
    match ps1, ps2 with
    | PStart x1, PStart x2 -> f s x1 x2
    | PExt (ps1,y1,f1), PExt(ps2,y2,f2) ->
       let s = fold_left2 f s ps1 ps2 in
       let s = f s y1 y2 in
       f s f1 f2
    | PDrop ps1, PDrop ps2 -> fold_left2 f s ps1 ps2
    | (PStart _  | PExt _ | PDrop _), _ -> assert false

  let rec fold_right f ps s =
    match ps with
    | PStart x -> f x s
    | PExt (ps,x,y) ->
       let s = f y s in
       let s = f x s in
       fold_right f ps s
    | PDrop ps -> fold_right f ps s
end

let rec normalize e env =
  (*debug "normalizing %s" (to_string e);*)
  match e.desc with
  | Var x -> let value = (try Env.val_var x env with Not_found -> None) in
             begin match value with
             | None -> e
             | Some e -> normalize e env
             end
  | Type | Cat -> e
  | HomType -> mk ~pos:e.pos HomType
  | Obj -> mk ~pos:e.pos Obj
  | Arr (t,u,v) -> mk ~pos:e.pos (Arr (normalize t env, normalize u env, normalize v env))
  | Pi (x,t,u) -> mk ~pos:e.pos (Pi (x, normalize t env, normalize u (Env.ext x t env)))
  | Lambda (x,t,u) -> mk ~pos:e.pos (Lambda (x, normalize t env, normalize u (Env.ext x t env)))
  | App (f,x) -> let x = normalize x env in
                 begin match (normalize f env).desc with
                 |Lambda (a,_,u) -> normalize (subst [(a,x)] u) env
                 |f -> mk ~pos:e.pos (App (mk f,x))
                 end
  | Coh (str, ps, u) -> let (ps, env) = normalize_ps ps env in mk ~pos:e.pos (Coh (str, ps, normalize u env))
  | Functor (e1,e2) -> mk ~pos:e.pos (Functor (normalize e1 env, normalize e2 env))
  | Aptor (f,x) -> mk ~pos:e.pos (Aptor (normalize f env, normalize x env))
  | Functorial (str,ps,f,t) ->
     let f = normalize f env in
     let (ps, env) = normalize_ps ps env in
     mk ~pos:e.pos (Functorial (str,ps,f,normalize t env))
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
    
let isEqual e1 e2 env =
  let rec equal e1 e2 = 
  match e1.desc, e2.desc with
  | Var x1, Var x2 -> x1 = x2
  | Type, Type -> true
  | HomType, HomType -> true
  | Cat, Cat -> true
  | Obj, Obj -> true
  | Arr (t1,u1,v1), Arr (t2,u2,v2) -> equal t1 t2 && equal u1 u2 && equal v1 v2
  | Pi (x1,t1,u1), Pi (x2,t2,u2) -> equal t1 t2 && (equal u1 (subst [(x2, (mk (Var x1)))] u2)) 
  | Lambda (x1,t1,u1), Lambda (x2,t2,u2) -> equal t1 t2 && (equal u1 (subst [(x2, (mk (Var x1)))] u2))
  | App (f1,x1), App (f2,x2) -> equal f1 f2 && equal x1 x2
  | Coh (_,ps1,u1), Coh(_,ps2,u2) -> let eq,sub = equal_ps ps1 ps2 in eq && equal u1 (subst sub u2)
  | Functor (e1,e2), Functor (g1,g2) -> equal e1 g1 && equal e2 g2
  | Aptor (f1,e1), Aptor (f2,e2) -> equal f1 f2 && equal e1 e2
  | (Var _ | Type | HomType | Cat | Obj | Arr _ | Pi _ | Lambda _ | App _ | Coh _ | Functor _ | Aptor _ ) , _ -> false
and equal_ps ps1 ps2 =
  match ps1, ps2 with
  | PStart(x1,t1), PStart(x2,t2) -> (equal t1 t2, [(x2, (mk (Var x1)))])
  | PExt (ps1,(x1,t1),(x2,t2)), PExt (ps2,(y1,u1),(y2,u2)) -> let (eq,sub) = equal_ps ps1 ps2  in
                                                              let sub1 = ((y1, (mk (Var x1)))::sub) in
                                                              let sub2 = ((y2, (mk (Var x2)))::sub1) in
                                                              (eq && equal t1 (subst sub u1) && equal t2 (subst sub1 u2), sub2)
                                                               
  | PDrop ps1, PDrop ps2 -> equal_ps ps1 ps2
  | _ -> (false, [])
  in equal (normalize e1 env) (normalize e2 env)
           
let checkEqual e1 e2 env =
  if (isEqual e1 e2 env) then () else error ~pos:e1.pos "got %s but %s is expected" (to_string e1) (to_string e2)

let rec instantiate t c =
  (*debug "instantiating %s" (to_string t);*)
  let t = match t.desc with
  | Arr (t,u,v) -> mk (Arr (instantiate t c, instantiate u c, instantiate v c))
  | Var x -> t
  | Obj -> mk (App (t, mk (Var c)))
  | Coh (str,ps,u) -> mk (App (t, mk (Var c)))
  | App (f,x) -> mk (App (instantiate f c, instantiate x c))
  | _ -> error "trying to instantiate %s, but it is not a categorical term" (to_string t)
  in (*debug "instantiated as %s" (to_string t);*) t
                                                 
let rec infer e env =
  (*debug "infering type of %s" (to_string e);*)
  let res = match e.desc with
  | Var x -> Env.ty_var x env
  | Type -> mk Type
  | HomType -> let c = refresh (Name "_c") in mk (Pi (c, (mk Cat), mk Type))
  | Cat -> mk Type
  | Obj -> let c = refresh (Name "_c") in mk (Pi (c, (mk Cat), mk (App (mk HomType,mk (Var c)))))
  | Arr (t,u,v) -> let cat = isHomType t env in
                   checkType u t env; checkType v t env;
                   (mk (App (mk HomType, cat)))
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
     | Pi (a,t,u) -> if isEqual tx t env
                     then subst [(a,x)] u
                     else error ~pos:e.pos "got %s, but %s is expected" (to_string tx) (to_string t) 
     | _ -> error ~pos:f.pos "got %s : %s but a function in expected" (to_string f) (to_string tf) end
  | (Coh (str,ps,t)) -> let c = refresh (Name "_c") in
                        let homC = mk (App (mk HomType, mk (Var c))) in  
                        let env = ref (Env.add env c (mk Cat)) in
                        let ps =
                          PS.map
                            (fun (x,t) ->
                              let t = instantiate t c in
                              let t = normalize t !env in
                              checkType t (homC) !env;
                              env := Env.add !env x t;
                              x,t
                            ) ps
                        in 
                        let env = !env in
                        let t = normalize t env in
                        let t = instantiate t c in
                        checkType t homC env;
                        begin
                          let f,g =
                            match t.desc with
                            | Arr (_,f,g) -> f,g
                            | _ -> assert false
                          in
                          let fv = PS.free_vars ps in
                          let rec close_vars f =
                            match (infer f env).desc with
                              | Arr (_,x,y) -> List.union (close_vars x) (List.union (close_vars y) (free_vars f))
                              | App ({desc = Obj},c) -> checkType c (mk Cat) env; free_vars f
                              | t -> assert (t = Obj); free_vars f
                          in
                          let fvf = close_vars f in
                          let fvg = close_vars g in
                          if not (List.included fv fvf && List.included fv fvg) then
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
                                error ~pos:t.pos "not algebraic: %s not used in %s" bad (to_string (mk (Coh (str,ps,t))));
                            end;
                        end;                       
                        mk (Pi (c, mk Cat, PS.fold_right (fun (x,t) u -> mk (Pi (x,t,u))) ps t))
  | Functor (e1,e2) -> checkType e1 (mk Cat) env; checkType e2 (mk Cat) env; mk Type
  | Aptor (f,x) -> let c,d = isFunct f env in
                   let homC = mk (App (mk HomType, c)) (*and homD = mk (App (mk HomType, d))*) in
                   let tx = infer x env in
                   checkType tx homC env;
                   let rec aux ty =
                     match ty.desc with
                     | Var _ -> if isEqual ty c env then d else ty
                     | Obj -> mk Obj
                     | Arr (t,u,v) -> mk (Arr (aux t, mk (Aptor(f,u)), mk (Aptor(f,v))))
                     | App (e,x) -> mk (App (aux e, aux x))
                     | _ -> error "got %s" (to_string ty)
                   in aux tx
 (* | Functorial (str,ps,f,t) ->
     let c,d = isFuncType f env in
     let env = ref env in
     let ps =
       PS.map
         (fun (x,t) ->
           let t = instantiate_withFunct t f c d in
           let t = normalize t !env in
           checkType t (homC) !env;
           env := Env.add !env x t;
           x,t
         ) ps
     in
     let env = !env in
     let t = normalize t env in
     let t = instantiate_withFunct t f c d in
     checkType t homC env;
     begin
                          let f,g =
                            match t.desc with
                            | Arr (_,f,g) -> f,g
                            | _ -> assert false
                          in
                          let fv = PS.free_vars ps in
                          let rec close_vars f =
                            match (infer f env).desc with
                              | Arr (_,x,y) -> List.union (close_vars x) (List.union (close_vars y) (free_vars f))
                              | App ({desc = Obj},c) -> checkType c (mk Cat) env; free_vars f
                              | t -> assert (t = Obj); free_vars f
                          in
                          let fvf = close_vars f in
                          let fvg = close_vars g in
                          if not (List.included fv fvf && List.included fv fvg) then
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
                                error ~pos:t.pos "not algebraic: %s not used in %s" bad (to_string (mk (Coh (str,ps,t))));
                            end;
                        end;                       
                        mk (Pi (c, mk Cat, PS.fold_right (fun (x,t) u -> mk (Pi (x,t,u))) ps t)) *)     
  in (* debug "type of %s infered to be %s" (to_string e) (to_string res); *) res
               
and checkType e1 e2 env =
  checkEqual (infer e1 env) e2 env
and isType e env =
  let te = infer e env in
  match (normalize te env).desc with
  | Type -> () 
  | App (a,b) -> checkEqual a (mk HomType) env; checkType b (mk Cat) env
  | _ -> error ~pos:e.pos "got %s : %s but a type is expected" (to_string e) (to_string te)
and isHomType e env =
  let te = infer e env in
  match (normalize te env).desc with
  | App (a,b) -> checkEqual a (mk HomType) env; checkType b (mk Cat) env; b
  | _ -> error ~pos:e.pos "got %s : %s but a HomType is expected" (to_string e) (to_string te)
and isFunct f env =
  let tf = infer f env in
  match (normalize tf env).desc with
  | Functor (c,d) -> c,d                
  | _ -> error ~pos:f.pos "got %s  : %s but a functor is expected" (to_string f) (to_string tf)   

               
type cmd =
  | Decl of var * expr
  | Hyp of var * expr
  | Check of expr
  | Eval of expr
  | Env

type prog = cmd list

(** TODO : avoid calling twice infer e env in the Decl case (in string_of_cmd and in exec_cmd)*)
let string_of_cmd env cmd=
  match cmd with
  | Decl (x,e) -> Printf.sprintf "let %s = %s : %s" (string_of_var x) (to_string e) (to_string (infer e env))
  | Hyp (x,e) -> Printf.sprintf "hyp %s : %s" (string_of_var x) (to_string e)
  | Check e -> Printf.sprintf "check %s \n %s : %s" (to_string e) (to_string e) (to_string (infer e env))
  | Eval e -> Printf.sprintf "eval %s \n %s = %s" (to_string e) (to_string e) (to_string (normalize e env))
  | Env -> Printf.sprintf "Environnement: \n------------- \n%s-------------" (Env.to_string env)

let exec_cmd env cmd =
  command "%s" (string_of_cmd env cmd);
  match cmd with
  | Decl (x,e) -> (x,(Some e, infer e env))::env
  | Hyp (x,e) -> isType e env; (x, (None, e))::env
  | Check e -> env
  | Eval e -> env
  | Env -> env
            
let exec prog =
  let rec aux env = function
    |[] -> ()
    |(t::l)  -> aux (exec_cmd env t) l
  in aux [] prog
  
