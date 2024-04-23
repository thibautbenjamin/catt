open Std
open Raw_types

let string_of_builtin = function
  | Comp -> "comp"
  | Id -> "id"

let rec string_of_ty e =
  match e with
  | Letin_ty (v,e,ty) ->
    Printf.sprintf "let %s = %s in %s"
      (Var.to_string v)
      (string_of_tm e)
      (string_of_ty ty)
  | ObjR -> "*"
  | ArrR (u,v) -> Printf.sprintf "%s -> %s" (string_of_tm u) (string_of_tm v)
and string_of_tm e =
  match e with
  | Letin_tm (v,e,tm) ->
    Printf.sprintf "let %s = %s in %s"
      (Var.to_string v)
      (string_of_tm e)
      (string_of_tm tm)
  | VarR x -> Var.to_string x
  | Sub (t,s,None) ->
    Printf.sprintf "(%s %s)"
      (string_of_tm t)
      (string_of_sub s)
  | Sub (t,s,Some susp) ->
    Printf.sprintf "(!%i %s %s)"
      susp
      (string_of_tm t)
      (string_of_sub s)
  | Builtin (name,s,None) ->
    Printf.sprintf "(_builtin_%s %s)"
      (string_of_builtin name)
      (string_of_sub s)
  | Builtin (name,s,Some susp) ->
    Printf.sprintf "(!%i _builtin_%s %s)"
      susp
      (string_of_builtin name)
      (string_of_sub s)
  | Op (l,t) ->
    Printf.sprintf "op_{%s}(%s)"
      (Opposite.op_data_to_string l)
      (string_of_tm t)
  | Inverse t ->
    Printf.sprintf "I(%s)" (string_of_tm t)
  | Unit t ->
    Printf.sprintf "U(%s)" (string_of_tm t)
  | Meta -> "_"
and string_of_sub s=
  match s with
  | []-> ""
  | (t, n)::s -> Printf.sprintf "%s %s" (string_of_sub s)(string_of_functed_tm t n)
and string_of_functed_tm t n =
  if n <= 0 then
    Printf.sprintf "%s" (string_of_tm t)
  else
    Printf.sprintf "[%s]" (string_of_functed_tm t (n-1))


(** remove the let in in a term *)
let rec replace_tm l e =
  match e with
  | VarR a ->
    begin
      try replace_tm l (List.assoc a l)
      with
        Not_found -> VarR a
    end
  | Sub (e,s,susp) ->
    Sub(replace_tm l e, replace_sub l s,susp)
  | Builtin (name,s,susp) ->
    Builtin(name,replace_sub l s,susp)
  | Op(op_data,t) -> Op(op_data, replace_tm l t)
  | Inverse(t) -> Inverse (replace_tm l t)
  | Unit(t) -> Unit (replace_tm l t)
  | Letin_tm (v,t,tm) -> replace_tm ((v,t)::l) tm
  | Meta -> Meta
and replace_sub l s =
  match s with
  | [] -> []
  | (t,f)::s -> (replace_tm l t, f)::(replace_sub l s)
and replace_ty l t =
  match t with
  | ObjR -> t
  | ArrR(u,v) -> ArrR (replace_tm l u, replace_tm l v)
  | Letin_ty (v,t,ty) -> replace_ty ((v,t)::l) ty

let remove_let_tm e =
  replace_tm [] e

let remove_let_ty e =
  replace_ty [] e

let rec var_in_ty x ty =
  match ty with
  | ObjR -> false
  | ArrR (u,v) ->
    var_in_tm x u || var_in_tm x v
  | Letin_ty _ -> Error.fatal("letin_ty constructors cannot appear here")
and var_in_tm x tm =
  match tm with
  | VarR v -> x = v
  | Sub(_,s,_) | Builtin (_,s,_) -> List.exists (fun (t,_) -> var_in_tm x t) s
  | Inverse t -> var_in_tm x t
  | Unit t -> var_in_tm x t
  | Meta -> false
  | Op(_,t) -> var_in_tm x t
  | Letin_tm _ -> Error.fatal("letin_tm constructors cannot appear here")
