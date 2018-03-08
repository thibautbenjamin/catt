module Var = struct
  type t =
  |Name of string
  |New of int
	     
  let to_string v =
  match v with
  |Name s -> s
  |New i -> "_" ^ string_of_int i

  let mk s = Name s

  let equal u v = match u,v with
    |Name s, Name s' -> s = s'
    |New a, New b -> a = b
    |_,_ -> false
end

type var = Var.t
	     
type expr =
  |Var of var
  |Obj
  |Arr of rexpr * rexpr
  |Coh of ((var * rexpr) list) * rexpr
  |Sub of rexpr * (rexpr list)
and rexpr = expr * bool (* bool is true iff the expression has implicit arguments *)
                   
let rec string_of_expr e =
  match e with
  |Var x -> Var.to_string x
  |Obj -> "*"
  |Arr (u,v) ->
    Printf.sprintf "%s -> %s"
		   (string_of_rexpr u)
		   (string_of_rexpr v)
  |Coh (ps,u) ->
    Printf.sprintf "Coh{%s |- %s}"
		   (string_of_ps ps)
		   (string_of_rexpr u)
  |Sub (t,s) ->
    Printf.sprintf "(%s %s)"
		   (string_of_rexpr t)
		   (string_of_sub s)
and string_of_ps ps =
  match ps with
  |[] -> ""
  |(x,t)::ps ->
    Printf.sprintf "(%s:%s) %s"
		   (Var.to_string x)
		   (string_of_rexpr t)
		   (string_of_ps ps)
and string_of_sub s =
  match s with
  |[] -> ""
  |t::[] -> Printf.sprintf "%s" (string_of_rexpr t)
  |t::s -> Printf.sprintf"%s %s"
			 (string_of_rexpr t)
			 (string_of_sub s)
and string_of_rexpr (e,_) = string_of_expr e
