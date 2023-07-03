open Std

  (** A raw type. *)
  type ty =
    | Letin_ty of Variables.t * tm * ty
    | Obj
    | Arr of tm * tm
  (** A raw term. *)
   and tm =
    | Letin_tm of Variables.t * tm * tm
    | Var of Variables.t
    | Sub of tm * (tm list) * (int list) (* list of variables that are functorialised *)

let rec string_of_ty e =
    match e with
    | Letin_ty (v,e,ty) -> Printf.sprintf "let %s = %s in %s" (Variables.to_string v) (string_of_tm e) (string_of_ty ty)
    | Obj -> "*"
    | Arr (u,v) -> Printf.sprintf "%s -> %s" (string_of_tm u) (string_of_tm v)
  (*TODO : print functorialization*)
  and string_of_tm e =
    match e with
    | Letin_tm (v,e,tm) -> Printf.sprintf "let %s = %s in %s" (Variables.to_string v) (string_of_tm e) (string_of_tm tm)
    | Var x -> Variables.to_string x
    | Sub (t,s,l) -> Printf.sprintf "(%s %s)" (string_of_tm t) (string_of_sub s l 0)
  and string_of_sub s l i=
    match s,l with
    | [],_ -> ""
    | t::[], k::_ when k = i -> Printf.sprintf "[%s]" (string_of_tm t)
    | t::[], _ -> Printf.sprintf "%s" (string_of_tm t)
    | t::s, k::l when k = i -> Printf.sprintf "[%s] %s" (string_of_tm t) (string_of_sub s l (i+1))
    | t::s,l -> Printf.sprintf "%s %s" (string_of_tm t) (string_of_sub s l (i+1))

  (** List the variables of an non-checked term (ie only the explicit variables)*)
  let rec list_vars e =
    match e with
    | Letin_tm _ -> assert false
    | Var v -> [v]
    | Sub (_,l,_) -> List.unions (List.map list_vars l)

  (** remove the let in in a term *)
  let rec replace_tm l e =
    match e with
    | Var a ->
       begin
         try replace_tm l (List.assoc a l)
         with
           Not_found -> Var a
       end
    | Sub (e,s,func) -> Sub(replace_tm l e, List.map (replace_tm l) s,func)
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

  (** replace the term Var v1 by the term Var v2 in the list l *)
  let rec replace_tm_list l v1 v2 =
    match l with
    |[] -> []
    |(Var v)::l when v == v1-> (Var v2)::l
    |t::l -> t::(replace_tm_list l v1 v2)
