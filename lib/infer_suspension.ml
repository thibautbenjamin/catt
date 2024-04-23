open Common
open Raw_types
module Infer_suspension(Strictness : StrictnessLv)
= struct
  module Environment = Environment.Environment(Strictness)

let rec dim_ty ctx = function
  | ObjR -> 0
  | ArrR(u,_) -> 1 + dim_tm ctx u
  | Letin_ty _ -> Error.fatal("letin_ty constructors cannot appear here")
and dim_tm ctx = function
  | VarR v -> dim_ty ctx (List.assoc v ctx)
  | (Sub(VarR _,s,i) | Builtin(_,s,i)) as t ->
    let func = List.fold_left (fun i (_,j) -> max i j) 0 s in
    let d = match t with
      | Sub (VarR v, _,_) -> Environment.dim_output v
      | Builtin(name, _,_) ->
        begin
          match name with
          | Comp -> 1
          | Id -> 1
        end
      | _ -> assert false
    in
    let
      susp = match i with
      | None -> 0
      | Some i -> i
    in
    d+func+susp
  | Meta -> 0
  | Op(_,tm) -> dim_tm ctx tm
  | Inverse t -> dim_tm ctx t
  | Unit t -> dim_tm ctx t + 1
  | Letin_tm _ -> Error.fatal("letin_tm constructors cannot appear here")
  | Sub _ -> Error.fatal ("ill-formed term")

let rec dim_sub ctx = function
  | [] -> 0, 0
  | (t,f)::s ->
    let (d1,f1) = dim_sub ctx s in
    let d2 = dim_tm ctx t in
    (max d1 d2, max f f1)

let rec tm ctx = function
  | VarR v -> VarR v
  | Sub(VarR _,s,i) | Builtin (_,s,i) as t ->
    let s = sub ctx s in
    begin
      match i with
      | None ->
        let inp = match t with
          | Sub (VarR v,_,_) -> Environment.dim_input v
          | Builtin(name,_,_) ->
            begin
              match name with
              | Comp -> 1
              | Id -> 0
            end
          | _ -> assert false
        in
        let d,func = dim_sub ctx s in
        let newsusp = Some (d - inp - func) in
        begin
          match t with
          | Sub (VarR v, _,_) -> Sub(VarR v,s,newsusp)
          | Builtin(name,_,_) -> Builtin(name,s,newsusp)
          | _ -> assert false
        end
      | Some _ -> t
    end
  | Op(l,t) -> Op(l,tm ctx t)
  | Inverse t -> Inverse (tm ctx t)
  | Unit t -> Unit (tm ctx t)
  | Meta -> Meta
  | Letin_tm _ | Sub _ -> assert false
and sub ctx = function
  | [] -> []
  | (t,i)::s -> (tm ctx t, i)::(sub ctx s)

let ty ctx = function
  | ObjR -> ObjR
  | ArrR(u,v) -> ArrR(tm ctx u, tm ctx v)
  | Letin_ty _ -> assert false



end
