open Kernel
open Common
open Syntax

type cmd =
  |Decl of var * expr

type prog = cmd list

let exec_cmd kenv env cmd =
  match cmd with
  | Decl (x,e) ->
     let () = command "let %s = %s" (string_of_var x) (to_string e) in
     let kenv,ke = kexpr_of_expr kenv env e in
     let kenv =
       try
	 Kernel.add_env kenv (kvar_of_var x) ke
       with
       |Kernel.UnknownId s  -> error "Unknown Identifier %s" s
     in 
     let () = info "%s is defined" (Kernel.to_string ke true true) in
     (kenv,((x,e)::env))
                                       
let exec prog =
  let rec aux (kenv,env) = function
    |[] -> ()
    |(t::l)  -> aux (exec_cmd kenv env t) l
in aux (Kernel.empty_env,[]) prog
