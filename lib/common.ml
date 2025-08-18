exception NotEqual of string * string
exception DoubledVar of string
exception WrongNumberOfArguments
exception NotInImage

type ps = Br of ps list

let rec disc = function 0 -> Br [] | n -> Br [ disc (n - 1) ]

module Var = struct
  type t =
    | Name of string
    | New of int
    | Db of int (* storing de Bruijn levels for coherences *)
    | Plus of t (* x+ funct. copy of var x *)
    | Bridge of t (* x~ funct. var of x *)

  let rec to_string v =
    match v with
    | Name s -> s
    | New i -> "_" ^ string_of_int i
    | Db i -> "." ^ string_of_int i
    | Plus v -> to_string v ^ "+"
    | Bridge v -> to_string v ^ "~"

  let make_var s = Name s

  let rec check_equal v1 v2 =
    match (v1, v2) with
    | Name s1, Name s2 ->
        if not (String.equal s1 s2) then raise (NotEqual (s1, s2)) else ()
    | New i, New j ->
        if i != j then raise (NotEqual (to_string v1, to_string v2)) else ()
    | Db i, Db j ->
        if i != j then raise (NotEqual (to_string v1, to_string v2)) else ()
    | Plus v1, Plus v2 | Bridge v1, Bridge v2 -> check_equal v1 v2
    | _, _ -> raise (NotEqual (to_string v1, to_string v2))

  let rec suspend_n v n =
    match v with
    | Db i -> Db (i + (2 * n))
    | Plus v -> Plus (suspend_n v n)
    | Bridge v -> Bridge (suspend_n v n)
    | (Name _ | New _) as v -> v

  let suspend v = suspend_n v 1
  let next_fresh = ref 0

  let fresh () =
    let fresh = New !next_fresh in
    incr next_fresh;
    fresh
end

(* For application *)
type pp_data = string * int * (Var.t * int) list list

let rec take n l =
  match l with h :: t when n > 0 -> h :: take (n - 1) t | _ -> []

type op_data = int list
