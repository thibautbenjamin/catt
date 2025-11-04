open Std
open Common

module Make (Core : Core.S) = struct
  exception IsObj
  exception IsCoh
  exception InvalidSubTarget of string * string
  exception MetaVariable

  open Core

  (** Operations on substitutions. *)
  module rec Sub : sig
    type t

    val to_list : t -> Tm.t list
    val check : Ctx.t -> (Coh.t, Tm.t) sub -> Ctx.t -> t
    val forget : t -> (Coh.t, Tm.t) sub
    val src : t -> Ctx.t
    val tgt : t -> Ctx.t
  end = struct
    type t = {
      list : Tm.t list;
      src : Ctx.t;
      tgt : Ctx.t;
      unchecked : (Coh.t, Tm.t) sub;
    }

    let to_list s = s.list
    let src s = s.src
    let tgt s = s.tgt

    module Core = struct
      module PS = PS
      module Coh = Coh
      module Tm = Tm
    end

    open Syntax.Make (Core)

    let check src s tgt =
      Io.info ~v:5
        (lazy
          (Printf.sprintf
             "building kernel substitution : source = %s; substitution = %s; \
              target = %s"
             (Ctx.to_string src) (Printing.sub_to_string s) (Ctx.to_string tgt)));
      let sub_exn =
        InvalidSubTarget (Printing.sub_to_string_debug s, Ctx.to_string tgt)
      in
      let rec aux src s tgt =
        let expr s tgt =
          match (s, Ctx.value tgt) with
          | [], [] -> []
          | _ :: _, [] | [], _ :: _ -> raise sub_exn
          | (x1, _) :: _, (x2, _) :: _ when x1 <> x2 -> raise sub_exn
          | (_, (t, _)) :: s, (_, a) :: _ ->
              let sub = aux src s (Ctx.tail tgt) in
              let t = Tm.check (Ctx.forget src) t in
              let asub =
                Unchecked.ty_apply_sub (Ty.forget a) (Sub.forget sub)
              in
              if not (Equality.is_equal_ty (Tm.ty t) asub) then
                raise
                  (NotEqual
                     ( Printing.ty_to_string (Tm.ty t),
                       Printing.ty_to_string asub ));

              t :: sub.list
        in
        { list = expr s tgt; src; tgt; unchecked = s }
      in
      aux src s tgt

    let forget s = s.unchecked
  end

  (** A context, associating a type to each context variable. *)
  and Ctx : sig
    type t

    val empty : unit -> t
    val tail : t -> t
    val to_string : t -> string
    val ty_var : t -> Var.t -> Ty.t
    val domain : t -> Var.t list
    val value : t -> (Var.t * Ty.t) list
    val extend : t -> expl:bool -> Var.t -> (Coh.t, Tm.t) ty -> t
    val forget : t -> (Coh.t, Tm.t) ctx
    val check : (Coh.t, Tm.t) ctx -> t
    val check_notin : t -> Var.t -> unit
    val is_equal : t -> t -> bool
    val check_equal : t -> t -> unit
  end = struct
    type t = { c : (Var.t * Ty.t) list; unchecked : (Coh.t, Tm.t) ctx }

    module Core = struct
      module PS = PS
      module Coh = Coh
      module Tm = Tm
    end

    open Syntax.Make (Core)

    let tbl : (ctx, Ctx.t) Hashtbl.t = Hashtbl.create 7829

    let tail ctx =
      match (ctx.c, ctx.unchecked) with
      | [], (_ :: _ | []) -> Error.fatal "computing tail of an empty context"
      | _ :: _, [] -> Error.fatal "safe and unchecked context out of sync"
      | _ :: c, _ :: unchecked -> { c; unchecked }

    let ty_var ctx x =
      try List.assoc x ctx.c
      with Not_found -> raise (Error.UnknownId (Var.to_string x))

    let empty () = { c = []; unchecked = [] }
    let domain ctx = List.map fst ctx.c
    let value ctx = ctx.c
    let forget c = c.unchecked
    let to_string ctx = Printing.ctx_to_string (forget ctx)

    let is_equal ctx1 ctx2 =
      ctx1 == ctx2 || Equality.is_equal_ctx (forget ctx1) (forget ctx2)

    let check_equal ctx1 ctx2 =
      if not (is_equal ctx1 ctx2) then
        raise
          (NotEqual
             ( Printing.ctx_to_string (forget ctx1),
               Printing.ctx_to_string (forget ctx2) ))

    let check_notin ctx x =
      try
        ignore (List.assoc x ctx.c);
        raise (DoubledVar (Var.to_string x))
      with Not_found -> ()

    let extend ctx ~expl x t =
      let ty = Ty.check ctx t in
      Ctx.check_notin ctx x;
      {
        c = (x, ty) :: Ctx.value ctx;
        unchecked = (x, (t, expl)) :: Ctx.forget ctx;
      }

    let check c =
      match Hashtbl.find_opt tbl c with
      | Some ctx -> ctx
      | None ->
          let ctx =
            List.fold_right
              (fun (x, (t, expl)) c -> Ctx.extend ~expl c x t)
              c (Ctx.empty ())
          in
          Hashtbl.add tbl c ctx;
          ctx
  end

  and Ty : sig
    type t

    val to_string : t -> string
    val is_obj : t -> bool
    val is_equal : t -> t -> bool
    val check_equal : t -> t -> unit
    val morphism : Tm.t -> Tm.t -> Ty.t
    val forget : t -> (Coh.t, Tm.t) ty
    val check : Ctx.t -> (Coh.t, Tm.t) ty -> t
    val apply_sub : t -> Sub.t -> t
    val retrieve_arrow : t -> Tm.t * Tm.t
    val under_type : t -> t
    val source : t -> Tm.t
    val target : t -> Tm.t
    val ctx : t -> Ctx.t
    val dim : t -> int
  end = struct
    module Core = struct
      module PS = PS
      module Coh = Coh
      module Tm = Tm
    end

    open Syntax.Make (Core)

    (** A type exepression. *)
    type expr = Obj | Arr of t * Tm.t * Tm.t

    and t = { c : Ctx.t; e : expr; unchecked : ty }

    let tbl : (Ctx.t * ty, Ty.t) Hashtbl.t = Hashtbl.create 7829
    let is_obj t = t.e = Obj

    let retrieve_arrow ty =
      match ty.e with
      | Obj ->
          Error.fatal
            "calling source and target on a type that is not an arrow type"
      | Arr (_, u, v) -> (u, v)

    let under_type ty =
      match ty.e with Obj -> raise IsObj | Arr (a, _, _) -> a

    let source ty = match ty.e with Obj -> raise IsObj | Arr (_, u, _) -> u
    let target ty = match ty.e with Obj -> raise IsObj | Arr (_, _, v) -> v

    let rec check c t =
      Io.info ~v:5
        (lazy
          (Printf.sprintf "building kernel type %s in context %s"
             (Printing.ty_to_string t) (Ctx.to_string c)));
      match Hashtbl.find_opt tbl (c, t) with
      | Some ty -> ty
      | None ->
          let e =
            match t with
            | Obj -> Obj
            | Arr (a, u, v) ->
                let achecked = check c a in
                let u = Tm.check (Ctx.forget c) ~ty:a u in
                let v = Tm.check (Ctx.forget c) ~ty:a v in
                Arr (achecked, u, v)
            | Meta_ty _ -> raise MetaVariable
          in
          let ty = { c; e; unchecked = t } in
          Hashtbl.add tbl (c, t) ty;
          ty

    let forget t = t.unchecked
    let to_string ty = Printing.ty_to_string (forget ty)

    let is_equal ty1 ty2 =
      Ctx.is_equal ty1.c ty2.c && Equality.is_equal_ty (forget ty1) (forget ty2)

    let check_equal ty1 ty2 =
      if not (is_equal ty1 ty2) then
        raise
          (NotEqual
             ( Printing.ty_to_string (forget ty1),
               Printing.ty_to_string (forget ty2) ))

    let morphism t1 t2 =
      let a = Tm.ty t1 in
      let c = Tm.ctx t1 in
      if
        not
          (Equality.is_equal_ctx c (Tm.ctx t2)
          && Equality.is_equal_ty a (Tm.ty t2))
      then
        raise
          (NotEqual (Printing.ty_to_string a, Printing.ty_to_string (Tm.ty t2)));
      let c = Ctx.check c in
      let a_checked = check c a in
      {
        c;
        e = Arr (a_checked, t1, t2);
        unchecked = Arr (a, Tm.forget t1, Tm.forget t2);
      }

    let apply_sub t s =
      Ctx.check_equal t.c (Sub.tgt s);
      check (Sub.src s) (Unchecked.ty_apply_sub (forget t) (Sub.forget s))

    let ctx t = t.c
    let rec dim t = match t.e with Obj -> 0 | Arr (a, _, _) -> 1 + dim a
  end
end
