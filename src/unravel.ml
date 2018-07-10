open List
open Stdlib
open Kernel
open Kernel.Expr
open MacrosEnvironnement
open Common

let rec print l =
  match l with
  | t::q -> Printf.sprintf "%s %s" (Var.to_string t) (print q)
  | [] -> ""
       
let rec unravel_tm ctx (e : tm) =
  match e with
  | Var v -> e
  | Sub (e,l) ->
     (let e = unravel_tm ctx e and l = List.map (unravel_tm ctx) l in
      match e with
      | Var v when List.mem v (List.map fst (!mEnv)) ->
         (List.assoc v (!mEnv)) (ctx, List.map (fun x -> fst (mk_tm ctx x)) l)
      | _ -> Sub (e,l))
  | Tm tm -> e
          
and unravel_ty ctx (e : ty) =
  match e with
  | Obj -> e
  | Arr (u,v) -> Arr (unravel_tm ctx u, unravel_tm ctx v)
  | Ty ty -> e 

(* list of variables of a term *)
(* let rec list_vars e = *)
(*   match e with *)
(*   | Var v -> [v] *)
(*   | Sub (e,l) -> List.unions (List.map list_vars l) *)
(*   | Tm tm -> list_expl_vars tm *)
                
(* replace variables of e using the association list l *)  
let rec replace l e : tm =
  match e with
  | Var a ->
     begin
       try List.assoc a l
       with
         Not_found -> Var a
     end
  | Sub (e,s) -> Sub(replace l e, List.map (replace l) s)
  | Tm tm -> e

(* Select the variables of l needed to recover the entire list, and set them as explicit arguments*)
let rec select l =
  match l with
  | [] -> []
  | (h::t) -> (h, not(appears (fst h) t)):: (select t)
and appears v l =
  match l with
  | [] -> false
  | (h::t) -> let (tm,ty) = h in (contains_ty v ty || appears v t)
and contains_ty v ty =
  match ty with
  | Obj -> false
  | Arr(t,u) -> contains_tm v t || contains_tm v u
  | Ty _ -> assert (false)
and contains_tm v tm =
  match tm with
  | Var u -> (u = v) 
  | Sub(e,l) -> List.fold_left (fun x -> fun y -> x||y) false (List.map (contains_tm v) l)
  | Tm _ -> assert (false)

                  
exception Completed of ((Var.t * ty) * tm option * bool) list
let complete c l l' v =
  let rec create_assoc l l' =
    match l,l' with
    | ((a,false)::t),l' -> (a, None, false)::(create_assoc t l')
    | ((a,true)::t),(h'::t') -> (a,Some h', true)::(create_assoc t t') 
    | ((a,true)::t),[] -> failwith (Printf.sprintf "not enough arguments given for the operation %s" (Var.to_string v))
    | [],(_::_) -> failwith (Printf.sprintf "too many arguments given for the operation %s" (Var.to_string v))
    | [],[] -> []
  in
  let rec next l res =
    match l with
    | ((a,Some b,true)::l) -> (a,b, ((a,Some b, false)::l))
    | ((a,None,true)::l) -> assert(false)
    | (h::l) -> let (x,y,z) = next l res in (x,y,h::z)
    | [] -> raise (Completed res)
  in
  let rec loop assoc =
    let (a,b,assoc) = next assoc assoc in
    let assoc = unify c (snd a) b assoc in
    loop (assoc)
  in
  let rec clear l =
    match l with
    | (((a,_),Some b,_)::l) -> (a,b) :: (clear l)
    | ((a, None,_)::_) -> assert(false)
    | [] -> []
  in
  let assoc = create_assoc l l' in
  try loop assoc
  with Completed res -> clear res
