open Kernel
open Settings
open Common
open ExtSyntax
open MacrosEnvironnement
open Unravel

       
type cmd =
  |DeclCoh of var * expr
(** Add the possibility to check terms in a given context for debugging and as an help to the user *)
  |Check of ((var* expr) list) * expr * (expr option) 
  |Decl of var * (var * expr) list * expr * (expr option)
	                                  
type prog = cmd list
			       
let exec_cmd cmd =
  match cmd with
  | DeclCoh (x,e) ->
     let () = command "let %s = %s"
		      (Var.to_string x)
		      (string_of_expr e)
     in
     let e = unravel e in
     let env =
       if !debug_mode then 
	 Kernel.add_env x e
       else
	 try Kernel.add_env x e
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
     let e = unravel e in
     let c = Kernel.mk_ctx l in
     begin
     match t with
     |Some t -> let t = unravel t in
                let () = command "check %s : %s" (string_of_expr e) (string_of_expr t) in
                let () = Kernel.checkType c (Kernel.mk_expr c e) (Kernel.mk_expr c t) in
                info "checked"
     |None -> let () = command "check %s " (string_of_expr e) in
              let t = Kernel.infer c (Kernel.mk_expr c e) in
              info "checked term %s type %s" (string_of_expr e) (string_of_kexpr t)
     end
  | Decl (v,l,e,t) ->
     let e = unravel e in
     let c = Kernel.mk_ctx l in
     let t = match t with
     |Some t -> let t = unravel t in 
                let () = command "let %s : %s" (string_of_expr e) (string_of_expr t) in
                let t = Kernel.mk_expr c t in
                let () = Kernel.checkType c (Kernel.mk_expr c e) t in
                t
     |None -> let () = command "let %s " (string_of_expr e) in
              let t = Kernel.infer c (Kernel.mk_expr c e) in t
     in
     let l = List.map fst l in
     let l = select l e in
     mEnv := (v, (fun l' -> replace l l' e)) :: (! mEnv);
     info "defined term of type %s" (string_of_kexpr t)
     
                                       
let rec exec prog =
  let rec aux = function
    |[] -> ()
    |(t::l)  -> exec_cmd t; aux l
  in Kernel.init_env; aux prog
