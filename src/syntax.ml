open Kernel
open Common

type var =
  |Name of string
  |New of string * int

let kvar_of_var v =
  match v with
  |Name s -> Kernel.Var.Name s
  |New (s,i) -> Kernel.Var.New (s,i)

let string_of_var v =
  match v with
  |Name s -> s
  |New (s,i) -> Printf.sprintf "%s.%d" s i
                               
type expr =
  |Var of var
  |Obj
  |Arr of expr * expr * expr
  |Coh of ((var * expr) list) * expr
  |Sub of expr * (expr list)

type env =
  (var * expr) list
                   
let refresh =
  let k = ref 0 in
  function
  | Name x | New(x,_) -> incr k; New(x, !k)


let rec to_string e =
  match e with
  |Var x -> string_of_var x
  |Obj -> "*"
  |Arr (t,u,v) -> Printf.sprintf "%s | %s -> %s" (to_string t) (to_string u) (to_string v)
  |Coh (ps,u) -> Printf.sprintf "Coh{%s |- %s}" (string_of_ps ps) (to_string u)
  |Sub (t,s) -> Printf.sprintf "Sub(%s,%s)" (string_of_sub s) (to_string t)
and string_of_ps ps =
  match ps with
  |[] -> ""
  |(x,t)::ps -> Printf.sprintf "(%s:%s) %s" (string_of_var x) (to_string t) (string_of_ps ps)
and string_of_sub s =
  match s with
  |[] -> ""
  |t::s -> Printf.sprintf"%s; %s" (to_string t) (string_of_sub s)



                         
let rec replace x y l =
  match l with
  |[] -> [(x,y)]
  |(x',y')::l when x' = x -> (x,y)::l
  |(x',y')::l -> (x',y')::(replace x y l)
and  refresh_ps ps l =
  match ps with
  |[] -> [],l
  |(x,t)::ps -> let y = refresh x in
                let ps,l = refresh_ps ps (replace x y l) in 
                let t = change_vars t l in
                ((y,t)::ps,l)                                 
and change_vars e l =
  match e with
  |Var x -> (try Var (List.assoc x l) with Not_found -> e)
  |Obj -> e
  |Arr (t,u,v) -> Arr (change_vars t l, change_vars u l, change_vars v l)
  |Coh (ps,t) -> let ps,l = refresh_ps ps l in Coh (ps, change_vars t l) 
  |Sub (t,s) -> let s = List.map (fun x -> change_vars x l) s in Sub (change_vars t l, s) 



let rec replace_env_vars e env =
  match e with
  |Var x -> (try List.assoc x env with Not_found -> e)
  |Obj -> e
  |Arr (t,u,v) -> Arr (replace_env_vars t env, replace_env_vars u env, replace_env_vars v env)
  |Coh (ps,t) -> Coh (ps, replace_env_vars t env)
  |Sub (t,s) -> Sub (replace_env_vars t env, List.map (fun x -> replace_env_vars x env) s)  
                                                                     


let rec mk_ctx kenv (env:env) l =
  let rec aux kenv l ctx = 
    match l with
    |[] -> (kenv, ctx)
    |(x,t)::l -> let kenv,t = kexpr_of_expr kenv env t in
                 let kenv,ctx = Kernel.add_ctx (kenv,ctx) (kvar_of_var x) t in
                 aux kenv l ctx
  in aux kenv l (Kernel.empty_ctx)
and kexpr_of_expr (kenv:Kernel.env) (env:env) (e:expr) : Kernel.env * Kernel.expr =
  let e = change_vars e [] in
  let e = replace_env_vars e env in
  let find_ctx kenv t =
    match t with
    |Coh(ps,u) -> mk_ctx kenv env ps
    |_ -> kenv,empty_ctx
  in
  let rec aux kenv e (c:Kernel.ctx) =
    match e with
    |Var v -> (kenv, Kernel.Expr.Var (kvar_of_var v))
    |Obj -> (kenv, Kernel.Expr.Obj)
    |Arr (t,u,v) -> let (kenv,t) = aux kenv t c in
                    let (kenv,u) = aux kenv u c in
                    let (kenv,v) = aux kenv v c in 
                    (kenv, Kernel.Expr.Arr (t,u,v))
    |Coh (ps,u) ->  let (kenv,c) = mk_ctx kenv env ps in
                    let (kenv,u) = aux kenv u c in
                    (kenv, Kernel.Expr.Coh (Kernel.mk_ps c,u))
    |Sub (t,s) -> let (kenv,tar) = find_ctx kenv t in
                  let (kenv,t) = aux kenv t tar in
                  let kenv,s = map_kexpr_of_expr kenv c s in
                  (kenv, Kernel.Expr.Sub (t,Kernel.mk_sub kenv s c tar))
  and map_kexpr_of_expr kenv c l =
  match l with
  |[] -> kenv,[]
  |e::l -> let kenv,l = map_kexpr_of_expr kenv c l in
           let kenv,e = aux kenv e c
           in kenv,(e::l) 

  in let (kenv,ctx) = find_ctx kenv e in aux kenv e ctx
         
