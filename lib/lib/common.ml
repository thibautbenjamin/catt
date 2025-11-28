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

type pp_data = string * int * (Var.t * int) list list

(* module type KernelS = sig *)
(*   type tm *)
(*   type ty *)
(*   type ctx *)
(*   type sub *)
(*   type sub_ps *)
(*   type constr *)

(*   module rec Coh : sig *)
(*     type t *)
(*     type innertm = Tm.t *)

(*     val ps : t -> PS.t *)
(*     val forget : t -> ps * ty * pp_data *)
(*     val suspend : t -> t *)
(*     val is_equal : t -> t -> bool *)
(*     val check_equal : t -> t -> unit *)
(*     val is_inv : t -> bool *)
(*     val to_string : ?unroll:bool -> t -> string *)
(*     val dim : t -> int *)
(*     val src : t -> tm *)
(*     val tgt : t -> tm *)
(*     val check : ps -> ty -> pp_data -> t *)
(*     val ty : t -> Ty.t *)
(*     val check_noninv : ps -> tm -> tm -> pp_data -> t *)
(*     val check_inv : ps -> tm -> tm -> pp_data -> t *)
(*     val noninv_srctgt : t -> tm * tm * ty *)
(*     val func_data : t -> (Var.t * int) list list *)
(*     val apply_ps : (ps -> ps) -> (ty -> ty) -> (pp_data -> pp_data) -> t -> t *)

(*     val apply : *)
(*       (ctx -> ctx) -> (ty -> ty) -> (pp_data -> pp_data) -> t -> t * sub *)
(*   end *)

(*   and Ty : sig *)
(*     type t = private { c : Ctx.t; e : expr; unchecked : ty } *)
(*     and expr = Obj | Arr of t * Tm.t * Tm.t *)
(*   end *)

(*   and Tm : sig *)
(*     type expr = Var of Var.t | Coh of Coh.t * Sub.t | App of Tm.t * Sub.t *)
(*     and t *)

(*     val ty : t -> ty *)
(*     val forget : t -> tm *)
(*     val constr : t -> constr *)
(*     val ctx : t -> ctx *)
(*     val name : t -> string option *)
(*     val full_name : t -> string option *)
(*     val func_data : t -> (Var.t * int) list list option *)
(*     val of_coh : Coh.t -> t *)
(*     val develop : t -> tm *)
(*     val pp_data : t -> pp_data option *)
(*     val to_string : t -> string *)
(*     val is_equal : t -> t -> bool *)
(*     val check : ctx -> ?ty:ty -> ?name:pp_data -> tm -> t *)

(*     val apply : *)
(*       (ctx -> ctx) -> (tm -> tm) -> (pp_data -> pp_data) -> t -> t * sub *)
(*   end *)

(*   and Sub : sig *)
(*     type t *)
(*   end *)

(*   and Ctx : sig *)
(*     type t *)

(*     val check : ctx -> t *)
(*   end *)

(*   and PS : sig *)
(*     exception Invalid *)

(*     type t = ps *)

(*     val mk : Ctx.t -> t *)
(*   end *)
(* end *)

(* module type SyntaxS = sig *)
(*   type checked_tm *)
(*   type checked_coh *)

(*   type ty = Meta_ty of int | Obj | Arr of ty * tm * tm *)

(*   and tm = *)
(*     | Var : Var.t -> tm *)
(*     | Meta_tm : int -> tm *)
(*     | Coh : *)
(*         (module KernelS *)
(*            with type tm = tm *)
(*             and type ty = ty *)
(*             and type ctx = ctx *)
(*             and type sub = sub *)
(*             and type sub_ps = sub_ps *)
(*             and type constr = constr *)
(*             and type Coh.t = checked_coh *)
(*             and type Tm.t = checked_tm) *)
(*         * checked_coh *)
(*         * sub_ps *)
(*         -> tm *)
(*     | App : *)
(*         (module KernelS *)
(*            with type tm = tm *)
(*             and type ty = ty *)
(*             and type ctx = ctx *)
(*             and type sub = sub *)
(*             and type sub_ps = sub_ps *)
(*             and type constr = constr *)
(*             and type Coh.t = checked_coh *)
(*             and type Tm.t = checked_tm) *)
(*         * checked_tm *)
(*         * sub *)
(*         -> tm *)

(*   and sub_ps = (tm * bool) list *)
(*   and sub = (Var.t * (tm * bool)) list *)
(*   and ctx = (Var.t * (ty * bool)) list *)
(*   and constr = tm * ty *)

(*   type meta_ctx = (int * ty) list *)
(*   type value = VCoh of checked_coh | VTm of checked_tm *)
(*   type decls = (value * string) list *)
(* end *)

type ('a, 'b) pty =
  | Meta_ty of int
  | Obj
  | Arr of ('a, 'b) pty * ('a, 'b) ptm * ('a, 'b) ptm

and ('a, 'b) ptm =
  | Var of Var.t
  | Meta_tm of int
  | Coh of 'a * ('a, 'b) psub_ps
  | App of 'b * ('a, 'b) psub

and ('a, 'b) psub_ps = (('a, 'b) ptm * bool) list
and ('a, 'b) psub = (Var.t * (('a, 'b) ptm * bool)) list

type ('a, 'b) pctx = (Var.t * (('a, 'b) pty * bool)) list
type ('a, 'b) pconstr = ('a, 'b) ptm * ('a, 'b) pty

module type KernelS = sig
  module rec Coh : sig
    type t
    type innertm = Tm.t

    val ps : t -> PS.t
    val forget : t -> ps * (Coh.t, Tm.t) pty * pp_data
    val suspend : t -> t
    val is_equal : t -> t -> bool
    val check_equal : t -> t -> unit
    val is_inv : t -> bool
    val to_string : ?unroll:bool -> t -> string
    val dim : t -> int
    val src : t -> (Coh.t, Tm.t) ptm
    val tgt : t -> (Coh.t, Tm.t) ptm
    val check : ps -> (Coh.t, Tm.t) pty -> pp_data -> t
    val ty : t -> Ty.t

    val check_noninv :
      ps -> (Coh.t, Tm.t) ptm -> (Coh.t, Tm.t) ptm -> pp_data -> t

    val check_inv : ps -> (Coh.t, Tm.t) ptm -> (Coh.t, Tm.t) ptm -> pp_data -> t

    val noninv_srctgt :
      t -> (Coh.t, Tm.t) ptm * (Coh.t, Tm.t) ptm * (Coh.t, Tm.t) pty

    val func_data : t -> (Var.t * int) list list

    val apply_ps :
      (ps -> ps) ->
      ((Coh.t, Tm.t) pty -> (Coh.t, Tm.t) pty) ->
      (pp_data -> pp_data) ->
      t ->
      t

    val apply :
      ((Coh.t, Tm.t) pctx -> (Coh.t, Tm.t) pctx) ->
      ((Coh.t, Tm.t) pty -> (Coh.t, Tm.t) pty) ->
      (pp_data -> pp_data) ->
      t ->
      t * (Coh.t, Tm.t) psub
  end

  and Ty : sig
    type t
    and expr = Obj | Arr of t * Tm.t * Tm.t
  end

  and Tm : sig
    type t

    val ty : t -> (Coh.t, Tm.t) pty
    val forget : t -> (Coh.t, Tm.t) ptm
    val constr : t -> (Coh.t, Tm.t) pconstr
    val ctx : t -> (Coh.t, Tm.t) pctx
    val name : t -> string option
    val full_name : t -> string option
    val func_data : t -> (Var.t * int) list list option
    val of_coh : Coh.t -> t
    val develop : t -> (Coh.t, Tm.t) ptm
    val pp_data : t -> pp_data option
    val to_string : t -> string
    val is_equal : t -> t -> bool

    val check :
      (Coh.t, Tm.t) pctx ->
      ?ty:(Coh.t, Tm.t) pty ->
      ?name:pp_data ->
      (Coh.t, Tm.t) ptm ->
      t

    val apply :
      ((Coh.t, Tm.t) pctx -> (Coh.t, Tm.t) pctx) ->
      ((Coh.t, Tm.t) ptm -> (Coh.t, Tm.t) ptm) ->
      (pp_data -> pp_data) ->
      t ->
      t * (Coh.t, Tm.t) psub
  end

  and PS : sig
    type t = ps
    type inner_ctx

    val mk : inner_ctx -> t
  end

  module Ctx : sig
    type t

    val check : (Coh.t, Tm.t) pctx -> t
    val to_string : t -> string
    val forget : t -> (Coh.t, Tm.t) pctx
    val is_equal : t -> t -> bool
    val check_equal : t -> t -> unit
  end

  module Sub : sig
    type t
  end

  type ty = (Coh.t, Tm.t) pty
  type tm = (Coh.t, Tm.t) ptm
  type sub = (Coh.t, Tm.t) psub
  type sub_ps = (Coh.t, Tm.t) psub_ps
  type ctx = (Coh.t, Tm.t) pctx
  type constr = (Coh.t, Tm.t) pconstr
  type meta_ctx = (int * ty) list
  type value = VCoh of Coh.t | VTm of Tm.t
  type decls = (value * string) list
end

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
