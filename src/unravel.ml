open ExtSyntax
open Kernel
open MacrosEnvironnement
open Common

let rec aux l = match l with
  |[] -> ""
  |(t::q) -> (string_of_expr t) ^ " " ^ (aux q)

let rec unravel ctx (e,b) =
  match e with
    |Var v -> (e,b)
    |Obj -> (e,b)
    |Arr (u,v) -> (Arr (unravel ctx u, unravel ctx v),b)
    |Coh (l,e) -> (Coh (l, unravel (mk_ctx l) e),b)
    |Sub (e,l) ->
      let e = unravel ctx e and l = List.map (unravel ctx) l in
      match fst e with
      | Var v when List.mem v (List.map fst (!mEnv)) ->
         (List.assoc v (!mEnv)) (List.map (Kernel.elab ctx) l)
      | _ -> (Sub (e,l),b)

(* select only the variables of l appearing in expression e *)
let rec select l e =
  match l with
  |[] -> []
  |(t::q) -> if contains t e then t :: (select q e) else select q e
and contains v e = 
  match fst e with
  |Var a -> Var.equal a v
  |Obj -> false
  |Arr(a,b) -> (contains v a) || (contains v b)
  |Coh (_,_) -> false
  |Sub (e,s) -> List.fold_left (fun a -> (fun b -> a || b)) false
                (List.map (contains v) s)
               
(* check all occurences of variables of l in e and replace them with terms of l' *)  
let rec replace l l' e : rexpr =
  let (e,elab) = e in
  match e with
  |Var a -> replace_var l l' a
  |Obj -> e,elab
  |Arr(a,b) -> (Arr(replace l l' a, replace l l' b),elab)
  |Coh (_,_) -> e,elab
  |Sub (e,s) -> Sub(replace l l' e, List.map (replace l l') s), elab
and replace_var l l' a =
  match l, l' with
  |(u::q1),(v::q2) -> if Var.equal a u then v
                      else replace_var q1 q2 a 
  |[],[] -> (Var a, true)
  |_,_ -> error "wrong number of arguments"
