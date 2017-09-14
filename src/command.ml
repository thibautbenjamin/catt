open Kernel
open Common
open Syntax

type cmd =
  |Decl of var * expr

type prog = cmd list

let exec_cmd kenv cmd =
  match cmd with
  | Decl (x,e) ->
     let () = command "let %s = %s" (string_of_var x) (to_string e) in
     let ke = 
     try
       coh_of_expr kenv e 
     with
     |Kernel.UnknownId s  -> error "unknown identifier %s" s
     |Kernel.UnknownCoh s  -> error "unknown coherence name %s" s
     |Kernel.IsNotType s -> error "got %s, but a type was expected" s
     |Kernel.HasNoType s -> error "the term %s has no type" s
     |Kernel.NotEqual (s1,s2) -> error "got %s, but %s was expected" s1 s2
     in
     let kenv = Kernel.add_env kenv (kevar_of_var x) ke
     in 
     let () = info "%s is defined" (Kernel.coh_to_string ke true true) in
     kenv
                                       
let exec prog =
  let rec aux kenv = function
    |[] -> ()
    |(t::l)  -> aux (exec_cmd kenv t) l
in aux Kernel.empty_env prog
