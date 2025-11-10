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
    type expr = Tm.t list

    type t = private {
      list : expr;
      src : Ctx.t;
      tgt : Ctx.t;
      unchecked : (Coh.t, Tm.t) sub;
    }

    val check : Ctx.t -> (Coh.t, Tm.t) sub -> Ctx.t -> t
    val check_to_ps : Ctx.t -> (Coh.t, Tm.t) sub_ps -> PS.t -> Sub.t
  end = struct
    type expr = Tm.t list

    type t = {
      list : expr;
      src : Ctx.t;
      tgt : Ctx.t;
      unchecked : (Coh.t, Tm.t) sub;
    }

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
      let aux src s (tgt : Ctx.t) =
        let rec list s (tgt : (Var.t * Ty.t) list) =
          match (s, tgt) with
          | [], [] -> []
          | _ :: _, [] | [], _ :: _ -> raise sub_exn
          | (x1, _) :: _, (x2, _) :: _ when x1 <> x2 -> raise sub_exn
          | (_, (t, _)) :: s, (_, a) :: tgt_tail ->
              let sub_checked = list s tgt_tail in
              let t = Tm.check (Ctx.forget src) t in
              let asub = Unchecked.ty_apply_sub (Ty.forget a) s in
              if not (Equality.is_equal_ty (Tm.ty t) asub) then
                raise
                  (NotEqual
                     ( Printing.ty_to_string (Tm.ty t),
                       Printing.ty_to_string asub ));

              t :: sub_checked
        in
        { list = list s tgt.c; src; tgt; unchecked = s }
      in
      aux src s tgt

    let check_to_ps src s (tgt_ps : PS.t) =
      let tgt = Ctx.of_ps tgt_ps in
      let s_assoc =
        try List.map2 (fun (x, _) (t, e) -> (x, (t, e))) tgt.c s
        with Invalid_argument _ ->
          Error.fatal "uncaught wrong number of arguments"
      in
      check src s_assoc tgt
  end

  (** A context, associating a type to each context variable. *)
  and Ctx : sig
    type t = private { c : (Var.t * Ty.t) list; unchecked : (Coh.t, Tm.t) ctx }

    val empty : unit -> t
    val to_string : t -> string
    val ty_var : t -> Var.t -> Ty.t
    val domain : t -> Var.t list
    val extend : t -> expl:bool -> Var.t -> (Coh.t, Tm.t) ty -> t
    val forget : t -> (Coh.t, Tm.t) ctx
    val check : (Coh.t, Tm.t) ctx -> t
    val check_notin : t -> Var.t -> unit
    val is_equal : t -> t -> bool
    val check_equal : t -> t -> unit
    val of_ps : PS.t -> t
  end = struct
    type t = { c : (Var.t * Ty.t) list; unchecked : (Coh.t, Tm.t) ctx }

    open Syntax.Make (Core)

    let tbl : (ctx, Ctx.t) Hashtbl.t = Hashtbl.create 7829

    let ty_var ctx x =
      try List.assoc x ctx.c
      with Not_found -> raise (Error.UnknownId (Var.to_string x))

    let empty () = { c = []; unchecked = [] }
    let domain ctx = List.map fst ctx.c
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
      let ty = Ty.check_with_ctx ctx.unchecked t in
      Ctx.check_notin ctx x;
      { c = (x, ty) :: ctx.c; unchecked = (x, (t, expl)) :: Ctx.forget ctx }

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

    let of_ps ps = check (Unchecked.ps_to_ctx ps)
  end
end
