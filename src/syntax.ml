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
  |Arr of expr * expr
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
  |Arr (u,v) -> Printf.sprintf "%s -> %s" (to_string u) (to_string v)
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

let rec replace_env_vars e env =
  match e with
  |Var x -> (try List.assoc x env with Not_found -> e)
  |Obj -> e
  |Arr (u,v) -> Arr (replace_env_vars u env, replace_env_vars v env)
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
    |Arr (u,v) -> let (kenv,u) = aux kenv u c in
                  let (kenv,v) = aux kenv v c in 
                  (kenv, Kernel.Expr.PArr (u,v))
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
         
