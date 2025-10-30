exception NotEqual of string * string
exception DoubledVar of string
exception WrongNumberOfArguments
exception NotInImage

type ps = Br of ps list

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

  let rec is_equal v1 v2 =
    match (v1, v2) with
    | Name s1, Name s2 -> String.equal s1 s2
    | New i, New j -> i = j
    | Db i, Db j -> i = j
    | Plus v1, Plus v2 | Bridge v1, Bridge v2 -> is_equal v1 v2
    | _, _ -> false

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

type ('a, 'b) ty =
  | Meta_ty of int
  | Obj
  | Arr of ('a, 'b) ty * ('a, 'b) tm * ('a, 'b) tm

and ('a, 'b) tm =
  | Var of Var.t
  | Meta_tm of int
  | Coh of 'a * ('a, 'b) sub_ps
  | App of 'b * ('a, 'b) sub

and ('a, 'b) sub_ps = (('a, 'b) tm * bool) list
and ('a, 'b) sub = (Var.t * (('a, 'b) tm * bool)) list

type ('a, 'b) ctx = (Var.t * (('a, 'b) ty * bool)) list
type ('a, 'b) meta_ctx = (int * ('a, 'b) ty) list
type ('a, 'b) constr = ('a, 'b) tm * ('a, 'b) ty
type ('a, 'b) value = VCoh of 'a | VTm of 'b
type ('a, 'b) decls = (('a, 'b) value * string) list

(* For application *)
type pp_data = string * int * (Var.t * int) list list

let rec take n l =
  match l with h :: t when n > 0 -> h :: take (n - 1) t | _ -> []

type op_data = int list

(* For managing theories *)
type strictness = Weak | Idempotent | Units | UAssociators
type invertibility = int option
type postulates = TerminalObject

type theory = {
  strictness : strictness;
  invertibility : invertibility;
  postulates : postulates list;
}

let vanilla_theory =
  { strictness = Weak; invertibility = None; postulates = [] }
