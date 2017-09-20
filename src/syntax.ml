open Kernel
open Common

type var =
  |Name of string

let kvar_of_var v =
  match v with
  |Name s -> Kernel.Var.Name s

let kevar_of_var v =
  match v with
  |Name s -> Kernel.EVar.Name s
			       
let string_of_var v =
  match v with
  |Name s -> s
                               
type expr =
  |Var of var
  |Obj
  |Arr of expr * expr
  |Coh of ((var * expr) list) * expr
  |Sub of expr * (expr list)
                   
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

		    
let rec translate kenv (c:Kernel.ctx) (e:expr) =
  let translate = translate kenv in
  match e with
  |Var v -> let kv = kvar_of_var v in
	    Kernel.Expr.CVar kv
  |Obj -> Kernel.Expr.Obj
  |Arr (u,v) -> let u = translate c u in
                let v = translate c v in 
                Kernel.Expr.PArr (u,v)
  |Sub (t,s) -> let t = translate_ecoh kenv t in
                  let s = List.map (translate c) s in
                  Kernel.Expr.Sub (t,Kernel.mk_sub kenv s)
  |Coh _ -> failwith "unsubstituted coherence" 
and translate_ecoh kenv (e:expr) =
  match e with
  |Var v ->
      let kv = kevar_of_var v in
      Kernel.mk_fold kv
    |Coh (ps,u) ->
      let c = mk_ctx kenv ps in
      let u = translate kenv c u in
      Kernel.mk_unfold (Kernel.mk_coh kenv (Kernel.mk_ps c) u)
    |(Obj |Arr _ |Sub _) -> failwith "wrong term under substitution"
and mk_ctx kenv l =
  let rec aux (l : (var * expr) list) ctx = 
    match l with
    |[] -> ctx
    |(x,t)::l ->
      let t = translate kenv ctx t in
      let ctx = Kernel.add_ctx kenv ctx (kvar_of_var x) t in
      aux l ctx
  in aux l (Kernel.empty_ctx)

let coh_of_expr kenv e = 
  match e with
  |Coh (ps,u) ->
    let c = mk_ctx kenv ps in
    let u = translate kenv c u in
    Kernel.mk_coh kenv (Kernel.mk_ps c) u
  |_ -> failwith "can only declare coherences"
