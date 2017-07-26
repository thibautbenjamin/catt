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
                                                                     


let kexpr_of_expr kenv (env:env) (e:expr) : Kernel.expr =
  let rec mk_ctx  l =
    let rec aux (l : (var * expr) list) ctx = 
      match l with
      |[] -> ctx
      |(x,t)::l -> let t = translate t ctx in
                   let ctx = Kernel.add_ctx kenv ctx (kvar_of_var x) t in
                   aux l ctx
    in aux l (Kernel.empty_ctx)
  and find_ctx t =
    match t with
    |Coh(ps,u) -> mk_ctx ps
    |_ -> empty_ctx	   
  and translate (e:expr) (c:Kernel.ctx) =
    match e with
    |Var v -> let v = kvar_of_var v in
	      if Kernel.in_ctx c v
	      then Kernel.Expr.CVar v
	      else Kernel.Expr.EVar v
    |Obj -> Kernel.Expr.Obj
    |Arr (u,v) -> let u = translate u c in
                  let v = translate v c in 
                  Kernel.Expr.PArr (u,v)
    |Coh (ps,u) ->  let c = mk_ctx ps in
                    let u = translate u c in
                    Kernel.Expr.Coh (Kernel.mk_ps c,u)
    |Sub (t,s) -> let tar = find_ctx t in
                  let t = translate t tar in
                  let s = map_kexpr_of_expr c s in
                  Kernel.Expr.Sub (t,Kernel.mk_sub kenv s c tar)
  and map_kexpr_of_expr c l =
    match l with
    |[] -> []
    |e::l -> let l = map_kexpr_of_expr c l in
             let e = translate e c
             in (e::l) 
  in let e = replace_env_vars e env in translate e (find_ctx e)
         
