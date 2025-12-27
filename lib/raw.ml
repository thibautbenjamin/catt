open Std
open Common
open Raw_types

let string_of_builtin = function
  | Comp -> "comp"
  | Id -> "id"
  | Conecomp (n, k, m) -> Printf.sprintf "conecomp(%d,%d,%d)" n k m
  | Cylcomp (n, k, m) -> Printf.sprintf "cylcomp(%d,%d,%d)" n k m
  | Cylstack n -> Printf.sprintf "cylstack(%d)" n

let string_of_inv inv =
  match inv with
  | LInv -> "left"
  | RInv -> "right"
  | Lunit -> "ε"
  | Runit -> "η"
  | Lwit -> "Iε"
  | Rwit -> "Iη"

let rec string_of_ty e =
  match e with
  | Letin_ty (v, e, ty) ->
      Printf.sprintf "let %s = %s in %s" (Var.to_string v) (string_of_tm e)
        (string_of_ty ty)
  | ObjR -> "*"
  | ArrR (u, v) -> Printf.sprintf "%s -> %s" (string_of_tm u) (string_of_tm v)
  | InvR u -> Printf.sprintf "Inv(%s)" (string_of_tm u)

and string_of_tm e =
  match e with
  | Letin_tm (v, e, tm) ->
      Printf.sprintf "let %s = %s in %s" (Var.to_string v) (string_of_tm e)
        (string_of_tm tm)
  | VarR x -> Var.to_string x
  | Sub (t, s, None, b) ->
      Printf.sprintf "(%s%s %s)"
        (if b then "@" else "")
        (string_of_tm t) (string_of_sub s)
  | Sub (t, s, Some susp, b) ->
      Printf.sprintf "(%s!%i %s %s)"
        (if b then "@" else "")
        susp (string_of_tm t) (string_of_sub s)
  | BuiltinR b -> Printf.sprintf "_builtin_%s" (string_of_builtin b)
  | Op (l, t) ->
      Printf.sprintf "op_{%s}(%s)"
        (Opposite.op_data_to_string l)
        (string_of_tm t)
  | Inverse t -> Printf.sprintf "I(%s)" (string_of_tm t)
  | Unit t -> Printf.sprintf "U(%s)" (string_of_tm t)
  | Meta -> "_"
  | ISR (inv, u) -> Printf.sprintf "%s(%s)" (string_of_inv inv) (string_of_tm u)
  | CanR (tm, args) ->
      Printf.sprintf "can(%s,{%s})" (string_of_tm tm) (string_of_tms args)
  | CoindR (t0, t1, t2, t3, t4, t5, t6) ->
      Printf.sprintf
        "coind \n\
         \t term: %s \n\
         \t left: %s \n\
         \t right:%s \n\
         \t ε: %s \n\
         \t η : %s \n\
         \t Iε: %s \n\
         \t Iη : %s" (string_of_tm t0) (string_of_tm t1) (string_of_tm t2)
        (string_of_tm t3) (string_of_tm t4) (string_of_tm t5) (string_of_tm t6)
  | RecR (t0, t1, t2, t3, t4, t5, t6) ->
      Printf.sprintf
        "rec \n\
         \t term: %s \n\
         \t left: %s \n\
         \t right:%s \n\
         \t ε: %s \n\
         \t η : %s \n\
         \t Iε: %s \n\
         \t Iη : %s" (string_of_tm t0) (string_of_tm t1) (string_of_tm t2)
        (string_of_tm t3) (string_of_tm t4) (string_of_tm t5) (string_of_tm t6)

and string_of_tms list =
  match list with
  | [] -> ""
  | tm :: tms -> Printf.sprintf "%s %s" (string_of_tm tm) (string_of_tms tms)

and string_of_sub s =
  match s with
  | [] -> ""
  | (t, n) :: s ->
      Printf.sprintf "%s %s" (string_of_sub s) (string_of_functed_tm t n)

and string_of_functed_tm t n =
  if n <= 0 then Printf.sprintf "%s" (string_of_tm t)
  else Printf.sprintf "[%s]" (string_of_functed_tm t (n - 1))

(** remove the let in in a term *)
let rec replace_tm l e =
  match e with
  | VarR a -> ( try replace_tm l (List.assoc a l) with Not_found -> VarR a)
  | Sub (e, s, susp, b) -> Sub (replace_tm l e, replace_sub l s, susp, b)
  | BuiltinR _ -> e
  | Op (op_data, t) -> Op (op_data, replace_tm l t)
  | Inverse t -> Inverse (replace_tm l t)
  | Unit t -> Unit (replace_tm l t)
  | Letin_tm (v, t, tm) -> replace_tm ((v, t) :: l) tm
  | Meta -> Meta
  | ISR (inv, u) -> ISR (inv, replace_tm l u)
  | CanR (tm, tms) -> CanR (replace_tm l tm, List.map (replace_tm l) tms)
  | CoindR (t0, t1, t2, t3, t4, t5, t6) ->
      CoindR
        ( replace_tm l t0,
          replace_tm l t1,
          replace_tm l t2,
          replace_tm l t3,
          replace_tm l t4,
          replace_tm l t5,
          replace_tm l t6 )
  | RecR (t0, t1, t2, t3, t4, t5, t6) ->
      RecR
        ( replace_tm l t0,
          replace_tm l t1,
          replace_tm l t2,
          replace_tm l t3,
          replace_tm l t4,
          replace_tm l t5,
          replace_tm l t6 )

and replace_sub l s =
  match s with
  | [] -> []
  | (t, f) :: s -> (replace_tm l t, f) :: replace_sub l s

and replace_ty l t =
  match t with
  | ObjR -> t
  | ArrR (u, v) -> ArrR (replace_tm l u, replace_tm l v)
  | Letin_ty (v, t, ty) -> replace_ty ((v, t) :: l) ty
  | InvR u -> InvR (replace_tm l u)

let remove_let_tm e = replace_tm [] e
let remove_let_ty e = replace_ty [] e

let rec var_in_ty x ty =
  match ty with
  | ObjR -> false
  | ArrR (u, v) -> var_in_tm x u || var_in_tm x v
  | Letin_ty _ -> Error.fatal "letin_ty constructors cannot appear here"
  | InvR u -> var_in_tm x u

and var_in_tm x tm =
  match tm with
  | VarR v -> x = v
  | Sub (_, s, _, _) -> List.exists (fun (t, _) -> var_in_tm x t) s
  | BuiltinR _ -> false
  | Inverse t -> var_in_tm x t
  | Unit t -> var_in_tm x t
  | Meta -> false
  | Op (_, t) -> var_in_tm x t
  | Letin_tm _ -> Error.fatal "letin_tm constructors cannot appear here"
  | ISR (_, u) -> var_in_tm x u
  | CoindR (t, _, _, _, _, _, _) | RecR (t, _, _, _, _, _, _) -> var_in_tm x t
  | CanR _ ->
      Error.fatal
        "testing if a variable belongs to an invertibility structure is not \
         defined"

let rec dim_ty ctx = function
  | ObjR -> 0
  | ArrR (u, _) -> 1 + dim_tm ctx u
  | Letin_ty _ -> Error.fatal "letin_ty constructors cannot appear here"
  | InvR u -> dim_tm ctx u

and dim_tm ctx = function
  | VarR v -> (
      try dim_ty ctx (List.assoc v ctx)
      with Not_found -> Error.unknown_id (Var.to_string v))
  | Sub (tmR, s, i, _) ->
      let func = List.fold_left (fun i (_, j) -> max i j) 0 s in
      let d =
        match tmR with
        | VarR v -> Environment.dim_output v
        | BuiltinR b -> dim_builtin b
        | _ -> Error.fatal "ill-formed term"
      in
      let susp = match i with None -> 0 | Some i -> i in
      d + func + susp
  | BuiltinR b -> dim_builtin b
  | Meta -> 0
  | Op (_, tm) -> dim_tm ctx tm
  | Inverse t -> dim_tm ctx t
  | Unit t -> dim_tm ctx t + 1
  | Letin_tm _ -> Error.fatal "letin_tm constructors cannot appear here"
  | CanR _ | CoindR _ | RecR _ ->
      Error.fatal "dimension of invertibility structure undefined"
  | ISR (inv, t) -> (
      match inv with
      | LInv | RInv -> dim_tm ctx t
      | Lunit | Runit -> dim_tm ctx t + 1
      | Lwit | Rwit ->
          Error.fatal "dimension of invertibility structure undefined")

and dim_builtin = function
  | Comp -> 1
  | Id -> 1
  | Conecomp (n, _, m) | Cylcomp (n, _, m) -> max n m
  | Cylstack n -> n

let rec dim_sub ctx = function
  | [] -> (0, 0)
  | (t, f) :: s ->
      let d1, f1 = dim_sub ctx s in
      let d2 = dim_tm ctx t in
      (max d1 d2, max f f1)

let rec infer_susp_tm ctx = function
  | VarR v -> VarR v
  | Sub (tmR, s, i, b) -> (
      let s = infer_susp_sub ctx s in
      match i with
      | None ->
          let inp =
            match tmR with
            | VarR v -> Environment.dim_input v
            | BuiltinR b -> (
                match b with
                | Comp -> 1
                | Id -> 0
                | Conecomp (n, _, _) | Cylcomp (n, _, _) | Cylstack n -> n)
            | _ -> assert false
          in
          let d, func = dim_sub ctx s in
          let newsusp = Some (d - inp - func) in
          Sub (tmR, s, newsusp, b)
      | Some _ -> Sub (tmR, s, i, b))
  | BuiltinR b -> BuiltinR b
  | Op (l, tm) -> Op (l, infer_susp_tm ctx tm)
  | Inverse t -> Inverse (infer_susp_tm ctx t)
  | Unit t -> Unit (infer_susp_tm ctx t)
  | Meta -> Meta
  | Letin_tm _ -> assert false
  | ISR (inv, t) -> ISR (inv, infer_susp_tm ctx t)
  | CanR (t, tms) -> CanR (infer_susp_tm ctx t, List.map (infer_susp_tm ctx) tms)
  | CoindR (t0, t1, t2, t3, t4, t5, t6) ->
      CoindR
        ( infer_susp_tm ctx t0,
          infer_susp_tm ctx t1,
          infer_susp_tm ctx t2,
          infer_susp_tm ctx t3,
          infer_susp_tm ctx t4,
          infer_susp_tm ctx t5,
          infer_susp_tm ctx t6 )
  | RecR (t0, t1, t2, t3, t4, t5, t6) ->
      RecR
        ( infer_susp_tm ctx t0,
          infer_susp_tm ctx t1,
          infer_susp_tm ctx t2,
          infer_susp_tm ctx t3,
          infer_susp_tm ctx t4,
          infer_susp_tm ctx t5,
          infer_susp_tm ctx t6 )

and infer_susp_sub ctx = function
  | [] -> []
  | (tm, i) :: s -> (infer_susp_tm ctx tm, i) :: infer_susp_sub ctx s

let infer_susp_ty ctx = function
  | ObjR -> ObjR
  | ArrR (u, v) -> ArrR (infer_susp_tm ctx u, infer_susp_tm ctx v)
  | Letin_ty _ -> assert false
  | InvR u -> InvR (infer_susp_tm ctx u)
