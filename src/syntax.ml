open Kernel
open Common

type var =
  |Name of string
  |New of string * int

let kvar_of_var v =
  match v with
  |Name s -> Kernel.Var.Name s
  |New (s,i) -> Kernel.Var.New (s,i)

let kevar_of_var v =
  match v with
  |Name s -> Kernel.EVar.Name s
  |New (s,i) -> Kernel.EVar.New (s,i)

			       
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

		    
let coh_of_expr kenv (e:expr) : Kernel.coh =
  let rec mk_ctx  l =
    let rec aux (l : (var * expr) list) ctx = 
      match l with
      |[] -> ctx
      |(x,t)::l -> let t = translate ctx t in
                   let ctx = Kernel.add_ctx kenv ctx (kvar_of_var x) t in
                   aux l ctx
    in aux l (Kernel.empty_ctx)
  and translate (c:Kernel.ctx) (e:expr) =
    match e with
    |Var v -> let kv = kvar_of_var v in
	      Kernel.Expr.CVar kv
    |Obj -> Kernel.Expr.Obj
    |Arr (u,v) -> let u = translate c u in
                  let v = translate c v in 
                  Kernel.Expr.PArr (u,v)
    |Sub (t,s) -> let t = translate_ecoh t in
                  let s = List.map (translate c) s in
                  Kernel.Expr.Sub (t,Kernel.mk_sub kenv s)
    |Coh _ -> failwith "unsubstituted coherence" 
  and translate_ecoh (e:expr) =
    match e with
    |Var v ->
      let kv = kevar_of_var v in
      Kernel.Expr.Fold kv
    |Coh (ps,u) ->
      let c = mk_ctx ps in
      let u = translate c u in
      Kernel.Expr.Unfold (Kernel.mk_coh kenv (Kernel.mk_ps c) u)
    |(Obj |Arr _ |Sub _) -> failwith "wrong term under substitution"
  in match e with
     |Coh (ps,u) ->
       let c = mk_ctx ps in
       let u = translate c u in
       Kernel.mk_coh kenv (Kernel.mk_ps c) u
     |_ -> failwith "can only declare coherences"
         
