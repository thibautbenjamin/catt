open Std
open Common

(** A raw type. *)
type ty =
  | Letin_ty of Var.t * tm * ty
  | Obj
  | Arr of tm * tm
  (** A raw term. *)
and tm =
  | Letin_tm of Var.t * tm * tm
  | Var of Var.t
  | Sub of tm * (tm  * bool) list * int option

let rec string_of_ty e =
  match e with
  | Letin_ty (v,e,ty) ->
    Printf.sprintf "let %s = %s in %s"
      (Var.to_string v)
      (string_of_tm e)
      (string_of_ty ty)
  | Obj -> "*"
  | Arr (u,v) -> Printf.sprintf "%s -> %s" (string_of_tm u) (string_of_tm v)
and string_of_tm e =
  match e with
  | Letin_tm (v,e,tm) ->
    Printf.sprintf "let %s = %s in %s"
      (Var.to_string v)
      (string_of_tm e)
      (string_of_tm tm)
  | Var x -> Var.to_string x
  | Sub (t,s,None) ->
    Printf.sprintf "(%s %s)"
      (string_of_tm t)
      (string_of_sub s)
  | Sub (t,s,Some susp) ->
    Printf.sprintf "(!%i %s %s)"
      susp
      (string_of_tm t)
      (string_of_sub s)
and string_of_sub s=
  match s with
  | []-> ""
  | (t, true)::s -> Printf.sprintf "%s [%s]" (string_of_sub s)(string_of_tm t)
  | (t, false)::s -> Printf.sprintf "%s %s" (string_of_sub s) (string_of_tm t)

(** remove the let in in a term *)
let rec replace_tm l e =
  match e with
  | Var a ->
    begin
      try replace_tm l (List.assoc a l)
      with
        Not_found -> Var a
    end
  | Sub (e,s,susp) ->
    Sub(replace_tm l e, replace_sub l s,susp)
  | Letin_tm (v,t,tm) -> replace_tm ((v,t)::l) tm
and replace_sub l s =
  match s with
  | [] -> []
  | (t,f)::s -> (replace_tm l t, f)::(replace_sub l s)
and replace_ty l t =
  match t with
  | Obj -> t
  | Arr(u,v) -> Arr (replace_tm l u, replace_tm l v)
  | Letin_ty (v,t,ty) -> replace_ty ((v,t)::l) ty

let remove_let_tm e =
  replace_tm [] e

let remove_let_ty e =
  replace_ty [] e

let rec var_in_ty x ty =
  match ty with
  | Obj -> false
  | Arr (u,v) ->
    var_in_tm x u || var_in_tm x v
  | Letin_ty _ -> assert false
and var_in_tm x tm =
  match tm with
  | Var v -> x = v
  | Sub(_,s,_) -> List.exists (fun (t,_) -> var_in_tm x t) s
  | Letin_tm _ -> assert false
