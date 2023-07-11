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
  | Meta
  | Nat of Common.Var.t * tm * tm

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
  | Meta -> "_"
  | Nat _ -> assert false (*TODO*)
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
  | Meta -> Meta
  | Nat _ as t -> t
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
  | Meta -> false
  | Letin_tm _ -> assert false
  | Nat _ -> assert false (* TODO *)

let rec dim_ty ctx = function
  | Obj -> 0
  | Arr(u,_) -> 1 + dim_tm ctx u
  | Letin_ty _ -> assert false
and dim_tm ctx = function
  | Var v -> dim_ty ctx (List.assoc v ctx)
  | Sub(Var v,s,i) ->
    let func = if List.exists (fun (_,bool) -> bool) s then 1 else 0 in
    let d = Environment.dim_output v in
    let
      susp = match i with
      | None -> 0
      | Some i -> i
    in
    d+func+susp
  | Meta -> 0
  | Nat _ -> assert false (* TODO *)
  | Letin_tm _ | Sub _ -> assert false

let rec dim_sub ctx = function
  | [] -> 0, false
  | (t,f)::s ->
    let (d1,f1) = dim_sub ctx s in
    let d2 = dim_tm ctx t in
    (max d1 d2, f||f1)

let rec infer_susp_tm ctx = function
  | Var v -> Var v
  | Sub(Var v,s,i) ->
    let s = infer_susp_sub ctx s in
    begin
      match i with
      | None ->
        let inp = Environment.dim_input v in
        let d,f = dim_sub ctx s in
        let func = if f then 1 else 0 in
        let newsusp = Some (d - inp - func) in
        Sub(Var v,s,newsusp)
      | Some i -> Sub(Var v,s,Some i)
    end
  | Meta -> Meta
  | Nat _ -> assert false (* TODO *)
  | Letin_tm _ | Sub _ -> assert false
and infer_susp_sub ctx = function
  | [] -> []
  | (tm,b)::s -> (infer_susp_tm ctx tm, b)::(infer_susp_sub ctx s)

let infer_susp_ty ctx = function
  | Obj -> Obj
  | Arr(u,v) -> Arr(infer_susp_tm ctx u, infer_susp_tm ctx v)
  | Letin_ty _ -> assert false
