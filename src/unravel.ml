open ExtSyntax
open MacrosEnvironnement
open Common

let rec aux l = match l with
  |[] -> ""
  |(t::q) -> (string_of_expr t) ^ " " ^ (aux q)

       
let rec unravel e =
  match e with
  |Var v -> e
  |Obj -> e
  |Arr (u,v) -> Arr (unravel u, unravel v)
  |Coh (l,e) -> Coh (l, unravel e)
  |Sub (e,l) ->
    let e = unravel e and l = List.map unravel l in
    match e with
    | Var v when List.mem v (List.map fst (!mEnv)) ->
       (List.assoc v (!mEnv)) l
    | _ -> Sub (e,l)


(* select only the variables of l appearing in expression e *)
let rec select l e =
  match l with
  |[] -> []
  |(t::q) -> if contains t e then t :: (select q e) else select q e
and contains v e = 
  match e with
  |Var a -> Var.equal a v
  |Obj -> false
  |Arr(a,b) -> (contains v a) || (contains v b)
  |Coh (_,_) -> false
  |Sub (e,s) -> List.fold_left (fun a -> (fun b -> a || b)) false (List.map (contains v) s)
               
(* check all occurences of variables of l in e and replace them with variables of l' *)  
let rec replace l l' e =
  let e = unravel e in
  match l,l' with
  |[],[] -> e
  |(u::q1),(v::q2) ->
    let e = (replace q1 q2 e) in replace_var u v e
  |_,_ -> error "wrong number of arguments"
and replace_var u t e =
  match e with
  |Var a -> if Var.equal a u then t else e
  |Obj -> e
  |Arr(a,b) -> Arr(replace_var u t a, replace_var u t b)
  |Coh (_,_) -> e
  |Sub (e,s) -> Sub(replace_var u t e, List.map (replace_var u t) s)
