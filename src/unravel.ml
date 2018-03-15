open List
open Stdlib
open Var
open Kernel
open Kernel.Expr
open MacrosEnvironnement
open Common


let rec aux1 l = match l with
  |[] -> "[]"
  |(t::q) -> (Var.to_string t) ^ " " ^ (aux1 q)

let rec aux2 l = match l with
  |[] -> "[]"
  |(t::q) -> (string_of_tm t) ^ " " ^ (aux2 q)

let rec unravel_tm ctx (e : tm) =
  match e with
    |Var v -> e, [v]
    |Sub (e,l) ->
      (let e = unravel_tm ctx e and res = List.map (unravel_tm ctx) l in
       let l = List.map fst res and vars = List.unions (List.map snd res) in 
       match fst e with
      | Var v when List.mem v (List.map fst (!mEnv)) ->
         (List.assoc v (!mEnv)) (List.map (fun x -> fst (mk_tm ctx x)) l), vars
      | _ -> Sub (fst e,l), vars)
    |Tm tm -> assert(false) (* e, [] *)
and unravel_ty ctx (e : ty) =
  match e with
    |Obj -> e
    |Arr (u,v) -> Arr (fst (unravel_tm ctx u), fst (unravel_tm ctx v))
    |Ty ty -> assert(false) (* e *)
  
(* check all occurences of variables of l in e and replace them with terms of l' *)  
let rec replace l l' e : tm =
  match e with
  |Var a -> replace_var l l' a
  |Sub (e,s) -> Sub(replace l l' e, List.map (replace l l') s)
  |Tm tm -> e
and replace_var l l' a =
  match l, l' with
  |(u::q1),(v::q2) -> if Var.equal a u then v
                      else replace_var q1 q2 a 
  |[],[] -> Var a
  |_,_ -> error "wrong number of arguments"

let rec replace_bis l e : tm =
  match e with
  |Var a ->
    begin
      try List.assoc a l with
        Not_found -> Var a
    end
  |Sub (e,s) -> Sub(replace_bis l e, List.map (replace_bis l) s)
  |Tm tm -> e
