open Syntax
open Common
open Env
open Infer
       

type cmd =
  | Decl of var * expr
  | Hyp of var * expr
  | Check of expr
  | Eval of expr
  | Env

type prog = cmd list

let string_of_cmd env ?inf cmd=
  match cmd with
  | Decl (x,e) -> Printf.sprintf "let %s = %s" (string_of_var x) (to_string e)
  | Hyp (x,e) -> Printf.sprintf "hyp %s : %s" (string_of_var x) (to_string e)
  | Check e -> Printf.sprintf "check %s" (to_string e)
  | Eval e -> Printf.sprintf "eval %s" (to_string e) 
  | Env -> Printf.sprintf "Environnement:"

let exec_cmd env cmd =
  command "%s" (string_of_cmd env cmd);
  match cmd with
  | Decl (x,e) ->
     answer "%s = %s : %s is defined \n" (string_of_var x) (to_string e) (to_string (infer e env));
     (x,(Some e, infer e env))::env
  | Hyp (x,e) ->
     answer "%s : %s is assumed \n" (string_of_var x) (to_string e);
     isType e env; (x, (None, e))::env
  | Check e ->
     answer "%s : %s \n" (to_string e) (to_string (infer e env));
     env
  | Eval e ->
     answer "%s = %s \n" (to_string e) (to_string (normalize e env));
     env
  | Env ->
     answer "------------- \n%s------------- \n" (Env.to_string env);
      env


             
let exec prog =
  let rec aux env = function
    |[] -> ()
    |(t::l)  -> aux (exec_cmd env t) l
  in aux [] prog
  
