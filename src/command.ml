open Kernel
open Common
open ExtSyntax

let debug = true
       
type cmd =
  |Decl of var * expr
(** Add the possibility to check terms in a given context for debugging and as an help to the user *)
(*  |Check of expr list * expr *)
		   
type prog = cmd list

let coh_of_expr env e = 
  if debug then
    match e with
    |Coh (ps,u) ->
      let c = mk_ctx env ps in
      Kernel.mk_coh env c u
    |_ -> failwith "can only declare coherences"
  else
    try
      match e with
      |Coh (ps,u) ->
	let c = mk_ctx env ps in
	Kernel.mk_coh env c u
      |_ -> failwith "can only declare coherences"
    with
    |UnknownId s  -> error "unknown identifier %s" s
    |UnknownCoh s  -> error "unknown coherence name %s" s
    |IsNotType s -> error "got %s, but a type was expected" s
    |HasNoType s -> error "the term %s has no type" s
    |NotEqual (s1,s2) -> error "got %s, but %s was expected" s1 s2
			       
let exec_cmd env cmd =
  match cmd with
  | Decl (x,e) ->
     let () = command "let %s = %s"
		      (Var.to_string x)
		      (string_of_expr e)
     in
     let e = coh_of_expr env e 
     in
     let env = Kernel.add_env env (EVar.mk x) e
     in 
     let () = info "%s is defined" (Kernel.coh_to_string e true) in
     env
(*  |Check (l,e) ->
    let () = command "check %s" (to_string e) in
    let ctx = mk_ctx kenv l in
    let e = translate kenv ctx e in
    let ty = Kernel.infer kenv ctx e 
    in let () = info "type %s" (Kernel.expr_to_string ty true) *)
                                       
let exec prog =
  let rec aux env = function
    |[] -> ()
    |(t::l)  -> aux (exec_cmd env t) l
in aux Kernel.empty_env prog
