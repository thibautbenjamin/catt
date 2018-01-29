open Kernel
open Settings
open Common
open ExtSyntax
open MacrosEnvironnement
open Unravel

       
type cmd =
  |DeclCoh of var * expr
(** Add the possibility to check terms in a given context for debugging and as an help to the user *)
  |Check of ((var* expr) list) * expr * expr 
  |Decl of var * (var * expr) list * expr * expr
	                                  
type prog = cmd list
			       
let exec_cmd env cmd =
  match cmd with
  | DeclCoh (x,e) ->
     let () = command "let %s = %s"
		      (Var.to_string x)
		      (string_of_expr e)
     in
     let e = unravel e in
     let env =
       if !debug_mode then 
	 Kernel.add_env env x e
       else
	 try Kernel.add_env env x e
	 with
	 |UnknownId s  -> error "unknown identifier %s" s
	 |UnknownCoh s  -> error "unknown coherence name %s" s
	 |IsNotType s -> error "got %s, but a type was expected" s
	 |HasNoType s -> error "the term %s has no type" s
	 |NotEqual (s1,s2) -> error "got %s, but %s was expected" s1 s2
     in 
     let () = info  "defined" in
     env
  | Check (l, e, t) ->
     let e = unravel e and t = unravel t in
     let () = command "check %s : %s" (string_of_expr e) (string_of_expr t) in
     let c = Kernel.mk_ctx env l in
     let () = Kernel.checkType env c (Kernel.mk_expr env c e) (Kernel.mk_expr env c t) in
     let () = info "checked"
     in env
  | Decl (v,l,e,t) ->
     let e = unravel e and t = unravel t in
     let () = command "let %s : %s" (string_of_expr e) (string_of_expr t) in
     let c = Kernel.mk_ctx env l in
     let () = Kernel.checkType env c (Kernel.mk_expr env c e) (Kernel.mk_expr env c t) in
     let l = List.map fst l in
     let l = select l e in
     mEnv := (v, (fun l' -> replace l l' e)) :: (! mEnv);
     let () = info "defined"
     in env
     
                                       
let exec prog =
  let rec aux env = function
    |[] -> ()
    |(t::l)  -> aux (exec_cmd env t) l
in aux Kernel.empty_env prog
