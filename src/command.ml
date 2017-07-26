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
     let ke = kexpr_of_expr kenv env e in
     let kenv =
       try
	 Kernel.add_env kenv (kvar_of_var x) ke
       with
       |Kernel.UnknownId s  -> error "unknown identifier %s" s
       |Kernel.IsNotType s -> error "got %s, but a type was expected" s
       |Kernel.HasNoType s -> error "the term %s has no type" s
       |Kernel.NotEqual (s1,s2) -> error "got %s, but %s was expected" s1 s2
     in 
     let () = info "%s is defined" (Kernel.to_string ke true true) in
     (kenv,((x,e)::env))
                                       
let exec prog =
  let rec aux (kenv,env) = function
    |[] -> ()
    |(t::l)  -> aux (exec_cmd kenv env t) l
in aux (Kernel.empty_env,[]) prog
