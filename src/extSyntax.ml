module Var = struct
  type t =
  |Name of string

  let to_string v =
  match v with
  |Name s -> s
end

type var = Var.t
type expr =
  |Var of var
  |Obj
  |Arr of expr * expr
  |Coh of ((var * expr) list) * expr
  |Sub of expr * (expr list)
       
let rec string_of_expr e =
  match e with
  |Var x -> Var.to_string x
  |Obj -> "*"
  |Arr (u,v) ->
    Printf.sprintf "%s -> %s"
		   (string_of_expr u)
		   (string_of_expr v)
  |Coh (ps,u) ->
    Printf.sprintf "Coh{%s |- %s}"
		   (string_of_ps ps)
		   (string_of_expr u)
  |Sub (t,s) ->
    Printf.sprintf "Sub(%s,%s)"
		   (string_of_sub s)
		   (string_of_expr t)
and string_of_ps ps =
  match ps with
  |[] -> ""
  |(x,t)::ps ->
    Printf.sprintf "(%s:%s) %s"
		   (Var.to_string x)
		   (string_of_expr t)
		   (string_of_ps ps)
and string_of_sub s =
  match s with
  |[] -> ""
  |t::s -> Printf.sprintf"%s; %s"
			 (string_of_expr t)
			 (string_of_sub s)

