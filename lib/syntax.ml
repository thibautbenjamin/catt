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
  | Sub of tm * (tm list) * int option * (int list)

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
  | Sub (t,s,None,l) ->
    Printf.sprintf "(%s %s)"
      (string_of_tm t)
      (string_of_sub s l 0)
  | Sub (t,s,Some susp,l) ->
    Printf.sprintf "(S%i %s %s)"
      susp
      (string_of_tm t)
      (string_of_sub s l 0)
and string_of_sub s l i=
  match s,l with
  | [],_ -> ""
  | t::[], k::_ when k = i ->
    Printf.sprintf "[%s]" (string_of_tm t)
  | t::[], _ ->
    Printf.sprintf "%s" (string_of_tm t)
  | t::s, k::l when k = i ->
    Printf.sprintf "%s [%s]" (string_of_sub s l (i+1))(string_of_tm t)
  | t::s,l ->
    Printf.sprintf "%s %s" (string_of_sub s l (i+1)) (string_of_tm t)

(** remove the let in in a term *)
let rec replace_tm l e =
  match e with
  | Var a ->
    begin
      try replace_tm l (List.assoc a l)
      with
        Not_found -> Var a
    end
  | Sub (e,s,susp,func) ->
    Sub(replace_tm l e, List.map (replace_tm l) s,susp,func)
  | Letin_tm (v,t,tm) -> replace_tm ((v,t)::l) tm
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
  | Sub(_,s,_,_) -> List.exists (fun t -> var_in_tm x t) s
  | Letin_tm _ -> assert false
