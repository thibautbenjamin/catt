type var =
  | Name of string
  | New of int
  | Db of int (* storing de Bruijn levels for coherences *)

let string_of_var v =
  match v with
  | Name s -> s
  | New i -> "_" ^ string_of_int i
  | Db i -> "." ^ string_of_int i

let make_var s = Name s

(** Environment variables (i.e. defined coherences or let definitions). *)
module EVar
: sig
  type t
  val to_string : t -> string
  val make : var -> t
  val to_var : t -> var
  val new_fresh : unit -> t
end
=
struct
  type t = var

  let next_fresh = ref (New 0)

  let to_string v =
    string_of_var v

  let make v = v

  let to_var v = v

  let new_fresh () =
    let res = !next_fresh in
    let nxt = match res with
           |New k -> New (k+1)
           |Name _ | Db _  -> assert false
    in next_fresh := nxt; res
end

(** Context variables (i.e. "arguments of functions"). *)
module CVar
: sig
    type t
    val to_string : t -> string
    val make : var -> t
    val to_var : t -> var
end
=
struct
  type t = var

  let to_string v =
    string_of_var v

  let make v = v

  let to_var v = v
end
