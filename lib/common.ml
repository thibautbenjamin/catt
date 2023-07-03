module Var = struct
  type t =
    | Name of string
    | New of int
    | Db of int (* storing de Bruijn levels for coherences *)

  let to_string v =
    match v with
    | Name s -> s
    | New i -> "_" ^ string_of_int i
    | Db i -> "." ^ string_of_int i

  let make_var s = Name s

  let check_equal v1 v2 =
    match v1, v2 with
    | Name s1, Name s2 ->
      if not (String.equal s1 s2) then raise (Error.NotEqual(s1,s2)) else ()
    | New i, New j ->
      if  i != j then raise (Error.NotEqual(to_string v1, to_string v2)) else ()
    | Db i, Db j -> if
      i != j then raise (Error.NotEqual(to_string v1, to_string v2)) else ()
    | Name _, New _ | Name _, Db _
    | New _ , Name _ | New _, Db _
    | Db _, Name _| Db _, New _
      -> raise (Error.NotEqual(to_string v1, to_string v2))

  let increase_lv v i m =
    match v with
    | Db j -> if  j == 0 then Db (i) else Db (j + m)
    | Name _ | New _ -> assert false

  let suspend = function
    | Db i -> Db (i+2)
    | Name _ | New _ as v -> v
end

type ps = Br of ps list

type ty =
  | Obj
  | Arr of ty * tm * tm
and tm =
  | Var of Var.t
  | Coh of ps * ty * sub_ps
and sub_ps = tm list

type ctx = (Var.t * ty) list

type sub = (Var.t * tm) list