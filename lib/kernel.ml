open Std
open Common
open Unchecked_types
open Unchecked

exception IsObj
exception IsCoh
exception InvalidSubTarget of string * string
exception MetaVariable

(** Operations on substitutions. *)
module rec Sub : sig
  type t

  val check_to_ps : Ctx.t -> Unchecked_types(Coh).sub_ps -> PS.t -> t
  val forget : t -> Unchecked_types(Coh).sub
  val free_vars : t -> Var.t list
  val src : t -> Ctx.t
  val tgt : t -> Ctx.t
end = struct
  type t = {
    list : Tm.t list;
    src : Ctx.t;
    tgt : Ctx.t;
    unchecked : Unchecked_types(Coh).sub;
  }

  let src s = s.src
  let tgt s = s.tgt

  open Unchecked (Coh)
  module Unchecked = Make (Coh)
  module Types = Unchecked_types (Coh)

  let tbl : (Ctx.t * PS.t * Types.sub_ps, Sub.t) Hashtbl.t = Hashtbl.create 7829
  let free_vars s = List.concat (List.map Tm.free_vars s.list)

  let check src s tgt =
    Io.info ~v:5
      (lazy
        (Printf.sprintf
           "building kernel substitution : source = %s; substitution = %s; \
            target = %s"
           (Ctx.to_string src)
           (Unchecked.sub_to_string s)
           (Ctx.to_string tgt)));
    let sub_exn =
      InvalidSubTarget (Unchecked.sub_to_string s, Ctx.to_string tgt)
    in
    let rec aux src s tgt =
      let expr s tgt =
        match (s, Ctx.value tgt) with
        | [], [] -> []
        | _ :: _, [] | [], _ :: _ -> raise sub_exn
        | (x1, _) :: _, (x2, _) :: _ when x1 <> x2 -> raise sub_exn
        | (_, t) :: s, (_, a) :: _ ->
            let sub = aux src s (Ctx.tail tgt) in
            let t = Tm.check src t in
            Ty.check_equal (Tm.typ t) (Ty.apply_sub a sub);
            t :: sub.list
      in
      { list = expr s tgt; src; tgt; unchecked = s }
    in
    aux src s tgt

  let check_to_ps src s tgt_ps =
    match Hashtbl.find_opt tbl (src, tgt_ps, s) with
    | Some sub -> sub
    | None ->
        let tgt = PS.to_ctx tgt_ps in
        let s_assoc =
          try List.map2 (fun (x, _) (t, _) -> (x, t)) (Ctx.value tgt) s
          with Invalid_argument _ ->
            Error.fatal "uncaught wrong number of arguments"
        in
        let sub = check src s_assoc tgt in
        Hashtbl.add tbl (src, tgt_ps, s) sub;
        sub

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
  val extend : t -> expl:bool -> Var.t -> Unchecked_types(Coh).ty -> t
  val forget : t -> Unchecked_types(Coh).ctx
  val check : Unchecked_types(Coh).ctx -> t
  val check_notin : t -> Var.t -> unit
  val _check_equal : t -> t -> unit
end = struct
  type t = { c : (Var.t * Ty.t) list; unchecked : Unchecked_types(Coh).ctx }

  open Unchecked (Coh)
  module Unchecked = Make (Coh)

  let tbl : (Unchecked_types(Coh).ctx, Ctx.t) Hashtbl.t = Hashtbl.create 7829

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
  let to_string ctx = Unchecked.ctx_to_string (forget ctx)

  let _check_equal ctx1 ctx2 =
    if ctx1 == ctx2 then ()
    else Unchecked.check_equal_ctx (forget ctx1) (forget ctx2)

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

(** Operations on pasting schemes. *)
and PS : sig
  exception Invalid

  type t

  val to_string : t -> string
  val mk : Ctx.t -> t
  val to_ctx : t -> Ctx.t
  val bdry : t -> t
  val source : t -> Sub.t
  val target : t -> Sub.t
  val forget : t -> ps
  val check_equal : t -> t -> unit
end = struct
  exception Invalid

  open Unchecked (Coh)
  module Unchecked = Make (Coh)

  (** A pasting scheme. *)
  type ps_derivation =
    | PNil of (Var.t * Ty.t)
    | PCons of ps_derivation * (Var.t * Ty.t) * (Var.t * Ty.t)
    | PDrop of ps_derivation

  type t = { tree : ps; ctx : Ctx.t }

  (* TODO:fix level of explicitness here *)

  let tbl : (Ctx.t, PS.t) Hashtbl.t = Hashtbl.create 7829

  (** Create a context from a pasting scheme. *)
  let old_rep_to_ctx ps =
    let rec list ps =
      match ps with
      | PDrop ps -> list ps
      | PCons (ps, (x1, t1), (x2, t2)) ->
          (x2, (Ty.forget t2, true)) :: (x1, (Ty.forget t1, true)) :: list ps
      | PNil (x, t) -> [ (x, (Ty.forget t, true)) ]
    in
    Ctx.check (list ps)

  (** Dangling variable. *)
  let rec marker (ps : ps_derivation) =
    match ps with
    | PNil (x, t) -> (x, t)
    | PCons (_, _, f) -> f
    | PDrop ps ->
        let _, tf = marker ps in
        let v = try Ty.target tf with IsObj -> raise Invalid in
        let y = try Tm.to_var v with IsCoh -> raise Invalid in
        let t =
          let rec aux = function
            | PNil (x, t) ->
                assert (x = y);
                t
            | PCons (ps, (y', ty), (f, tf)) ->
                if y' = y then ty else if f = y then tf else aux ps
            | PDrop ps -> aux ps
          in
          aux ps
        in
        (y, t)

  (** Create a pasting scheme from a context. *)
  let make_old (l : Ctx.t) =
    let rec close ps tx =
      if Ty.is_obj tx then ps
      else
        let tx = Ty.under_type tx in
        close (PDrop ps) tx
    in
    let build l =
      let x0, ty, l =
        match l with
        | (x, ty) :: l when Ty.is_obj ty -> (x, ty, l)
        | _ -> raise Invalid
      in
      let rec aux ps = function
        | (y, ty) :: (f, tf) :: l as l1 ->
            let _, u, v =
              try Ty.retrieve_arrow tf with IsObj -> raise Invalid
            in
            let fx, fy =
              try (Tm.to_var u, Tm.to_var v) with IsCoh -> raise Invalid
            in
            if y <> fy then raise Invalid;
            let x, _ = marker ps in
            if x = fx then (
              let varps = Ctx.domain (old_rep_to_ctx ps) in
              if List.mem f varps then raise (DoubledVar (Var.to_string f));
              if List.mem y varps then raise (DoubledVar (Var.to_string y));
              let ps = PCons (ps, (y, ty), (f, tf)) in
              aux ps l)
            else aux (PDrop ps) l1
        | [ (_, _) ] -> raise Invalid
        | [] ->
            let _, tx = marker ps in
            close ps tx
      in
      aux (PNil (x0, ty)) l
    in
    build (List.rev (Ctx.value l))

  (* assumes that all ps are completed with enough PDrop in the end *)
  let make_tree ps =
    let rec find_previous ps list =
      match ps with
      | PNil x -> (Br list, PNil x)
      | PCons (ps, _, _) -> (Br list, ps)
      | PDrop _ as ps ->
          let p, ps = build_till_previous ps in
          (Br p, ps)
    and build_till_previous ps =
      match ps with
      | PNil x -> ([], PNil x)
      | PCons (ps, _, _) -> ([], ps)
      | PDrop ps ->
          let p, ps = find_previous ps [] in
          let prev, ps = build_till_previous ps in
          (p :: prev, ps)
    in
    Br (fst (build_till_previous ps))

  let mk (l : Ctx.t) =
    match Hashtbl.find_opt tbl l with
    | Some ps -> ps
    | None ->
        let oldrep = make_old l in
        let ps = { tree = make_tree oldrep; ctx = l } in
        Hashtbl.add tbl l ps;
        ps

  let forget ps = ps.tree
  let to_string ps = Unchecked.ps_to_string (forget ps)

  (** Create a context from a pasting scheme. *)
  let to_ctx ps = ps.ctx

  let bdry ps = mk (Ctx.check (Unchecked.ps_to_ctx (Unchecked.ps_bdry ps.tree)))

  let source ps =
    Sub.check_to_ps (to_ctx ps) (Unchecked.ps_src ps.tree) (bdry ps)

  let target ps =
    Sub.check_to_ps (to_ctx ps) (Unchecked.ps_tgt ps.tree) (bdry ps)

  let check_equal ps1 ps2 =
    if ps1.tree == ps2.tree then ()
    else Unchecked.check_equal_ps ps1.tree ps2.tree
end

and Ty : sig
  type t

  val to_string : t -> string
  val free_vars : t -> Var.t list
  val is_full : Ctx.t -> t -> bool
  val is_obj : t -> bool
  val check_equal : t -> t -> unit
  val morphism : Tm.t -> Tm.t -> Ty.t
  val forget : t -> Unchecked_types(Coh).ty
  val check : Ctx.t -> Unchecked_types(Coh).ty -> t
  val apply_sub : t -> Sub.t -> t
  val retrieve_arrow : t -> t * Tm.t * Tm.t
  val under_type : t -> t
  val target : t -> Tm.t
  val dim : t -> int
end = struct
  (** A type exepression. *)
  type expr = Obj | Arr of t * Tm.t * Tm.t

  and t = { e : expr; unchecked : Unchecked_types(Coh).ty }

  open Unchecked (Coh)
  module Unchecked = Make (Coh)
  module Types = Unchecked_types (Coh)

  let tbl : (Ctx.t * Types.ty, Ty.t) Hashtbl.t = Hashtbl.create 7829
  let is_obj t = t.e = Obj

  let retrieve_arrow ty =
    match ty.e with Obj -> raise IsObj | Arr (a, u, v) -> (a, u, v)

  let under_type ty = match ty.e with Obj -> raise IsObj | Arr (a, _, _) -> a
  let target ty = match ty.e with Obj -> raise IsObj | Arr (_, _, v) -> v

  let rec check c t =
    Io.info ~v:5
      (lazy
        (Printf.sprintf "building kernel type %s in context %s"
           (Unchecked.ty_to_string t) (Ctx.to_string c)));
    match Hashtbl.find_opt tbl (c, t) with
    | Some ty -> ty
    | None ->
        let e =
          match t with
          | Obj -> Obj
          | Arr (a, u, v) ->
              let a = check c a in
              let u = Tm.check c ~ty:a u in
              let v = Tm.check c ~ty:a v in
              Arr (a, u, v)
          | Meta_ty _ -> raise MetaVariable
        in
        let ty = { e; unchecked = t } in
        Hashtbl.add tbl (c, t) ty;
        ty

  (** Free variables of a type. *)
  let rec free_vars ty =
    match ty.e with
    | Obj -> []
    | Arr (t, u, v) ->
        List.unions [ free_vars t; Tm.free_vars u; Tm.free_vars v ]

  let is_full c t = List.included (Ctx.domain c) (free_vars t)
  let forget t = t.unchecked
  let to_string ty = Unchecked.ty_to_string (forget ty)

  (** Test for equality. *)
  let check_equal ty1 ty2 = Unchecked.check_equal_ty (forget ty1) (forget ty2)

  let morphism t1 t2 =
    let a1 = Tm.ty t1 in
    let a2 = Tm.ty t2 in
    check_equal a1 a2;
    {
      e = Arr (a1, t1, t2);
      unchecked = Arr (forget a1, Tm.forget t1, Tm.forget t2);
    }

  let apply_sub t s =
    check (Sub.src s) (Unchecked.ty_apply_sub (forget t) (Sub.forget s))

  let rec dim t = match t.e with Obj -> 0 | Arr (a, _, _) -> 1 + dim a
end

(** Operations on terms. *)
and Tm : sig
  type t

  val to_var : t -> Var.t
  val typ : t -> Ty.t
  val free_vars : t -> Var.t list
  val is_full : Ctx.t -> t -> bool
  val forget : t -> Unchecked_types(Coh).tm
  val check : Ctx.t -> ?ty:Ty.t -> Unchecked_types(Coh).tm -> t
  val apply_sub : t -> Sub.t -> t
  val preimage : t -> Sub.t -> t
  val ty : t -> Ty.t
end = struct
  type expr = Var of Var.t  (** a context variable *) | Coh of Coh.t * Sub.t
  and t = { ty : Ty.t; e : expr; unchecked : Unchecked_types(Coh).tm }

  let typ t = t.ty

  open Unchecked (Coh)
  module Unchecked = Make (Coh)
  module Types = Unchecked_types (Coh)

  let tbl : (Ctx.t * Types.tm, Tm.t) Hashtbl.t = Hashtbl.create 7829
  let to_var tm = match tm.e with Var v -> v | Coh _ -> raise IsCoh

  let free_vars tm =
    let fvty = Ty.free_vars tm.ty in
    match tm.e with Var x -> x :: fvty | Coh (_, sub) -> Sub.free_vars sub

  let is_full c tm = List.included (Ctx.domain c) (free_vars tm)
  let forget tm = tm.unchecked

  let check c ?ty t =
    Io.info ~v:5
      (lazy
        (Printf.sprintf "building kernel term %s in context %s"
           (Unchecked.tm_to_string t) (Ctx.to_string c)));
    let tm =
      match Hashtbl.find_opt tbl (c, t) with
      | Some tm -> tm
      | None -> (
          match t with
          | Var x ->
              let e, ty = (Var x, Ctx.ty_var c x) in
              { ty; e; unchecked = t }
          | Meta_tm _ -> raise MetaVariable
          | Coh (coh, s) ->
              let sub = Sub.check_to_ps c s (Coh.ps coh) in
              let e, ty = (Coh (coh, sub), Ty.apply_sub (Coh.ty coh) sub) in
              let tm = { ty; e; unchecked = t } in
              Hashtbl.add tbl (c, t) tm;
              tm)
    in
    match ty with
    | None -> tm
    | Some ty ->
        Ty.check_equal ty tm.ty;
        tm

  let apply_sub t sub =
    let c = Sub.src sub in
    let ty = Ty.apply_sub t.ty sub in
    let t = Unchecked.tm_apply_sub (forget t) (Sub.forget sub) in
    check c ~ty t

  let preimage t sub =
    let c = Sub.tgt sub in
    let t = Unchecked.tm_sub_preimage (forget t) (Sub.forget sub) in
    check c t

  let ty t = t.ty
end

(** A coherence. *)
and Coh : sig
  type t

  val ps : t -> PS.t
  val ty : t -> Ty.t
  val check : ps -> Unchecked_types(Coh).ty -> coh_pp_data -> t

  val check_noninv :
    ps -> Unchecked_types(Coh).tm -> Unchecked_types(Coh).tm -> coh_pp_data -> t

  val check_inv :
    ps -> Unchecked_types(Coh).tm -> Unchecked_types(Coh).tm -> coh_pp_data -> t

  val to_string : t -> string
  val is_inv : t -> bool

  val noninv_srctgt :
    t ->
    Unchecked_types(Coh).tm * Unchecked_types(Coh).tm * Unchecked_types(Coh).ty

  val forget : t -> ps * Unchecked_types(Coh).ty * coh_pp_data
  val func_data : t -> (Var.t * int) list
  val check_equal : t -> t -> unit
  val dim : t -> int
end = struct
  type cohInv = { ps : PS.t; ty : Ty.t }
  type cohNonInv = { ps : PS.t; src : Tm.t; tgt : Tm.t; total_ty : Ty.t }
  type t = Inv of cohInv * coh_pp_data | NonInv of cohNonInv * coh_pp_data

  module Types = Unchecked_types (Coh)

  let tbl : (ps * Types.ty, Coh.t) Hashtbl.t = Hashtbl.create 7829

  let tbl_inv : (ps * Types.tm * Types.tm, Coh.t) Hashtbl.t =
    Hashtbl.create 7829

  let tbl_noninv : (ps * Types.tm * Types.tm, Coh.t) Hashtbl.t =
    Hashtbl.create 7829

  exception NotAlgebraic

  open Unchecked (Coh)
  module Unchecked = Make (Coh)

  let ps = function Inv (data, _) -> data.ps | NonInv (data, _) -> data.ps

  let ty = function
    | Inv (data, _) -> data.ty
    | NonInv (data, _) -> data.total_ty

  let is_inv = function Inv (_, _) -> true | NonInv (_, _) -> false

  let algebraic ps ty name =
    let ctx = PS.to_ctx ps in
    if Ty.is_full ctx ty then Inv ({ ps; ty }, name)
    else
      let _, src, tgt =
        try Ty.retrieve_arrow ty with IsObj -> raise NotAlgebraic
      in
      try
        let src_inclusion = PS.source ps in
        let src = Tm.preimage src src_inclusion in
        if not (Tm.is_full (Sub.tgt src_inclusion) src) then raise NotAlgebraic
        else
          let tgt_inclusion = PS.target ps in
          let tgt = Tm.preimage tgt tgt_inclusion in
          if not (Tm.is_full (Sub.tgt tgt_inclusion) tgt) then
            raise NotAlgebraic
          else NonInv ({ ps; src; tgt; total_ty = ty }, name)
      with NotInImage -> raise NotAlgebraic

  let check ps_unchkd t_unchkd ((name, _, _) as pp_data) =
    Io.info ~v:5
      (lazy
        (Printf.sprintf "checking coherence (%s,%s)"
           (Unchecked.ps_to_string ps_unchkd)
           (Unchecked.ty_to_string t_unchkd)));
    match Hashtbl.find_opt tbl (ps_unchkd, t_unchkd) with
    | Some coh -> coh
    | None -> (
        try
          let cps = Ctx.check (Unchecked.ps_to_ctx ps_unchkd) in
          let ps = PS.mk cps in
          let t = Ty.check cps t_unchkd in
          let coh = algebraic ps t pp_data in
          Hashtbl.add tbl (ps_unchkd, t_unchkd) coh;
          coh
        with
        | NotAlgebraic ->
            Error.not_valid_coherence name
              (Printf.sprintf "type %s not algebraic in pasting scheme %s"
                 (Unchecked.ty_to_string t_unchkd)
                 Unchecked.(ctx_to_string (ps_to_ctx ps_unchkd)))
        | DoubledVar s ->
            Error.not_valid_coherence name
              (Printf.sprintf "variable %s appears twice in the context" s))

  let check_noninv ps_unchkd src_unchkd tgt_unchkd name =
    match Hashtbl.find_opt tbl_noninv (ps_unchkd, src_unchkd, tgt_unchkd) with
    | Some coh -> coh
    | None ->
        let ps = PS.mk (Ctx.check (Unchecked.ps_to_ctx ps_unchkd)) in
        let src_inclusion = PS.source ps in
        let tgt_inclusion = PS.target ps in
        let bdry = PS.bdry ps in
        let cbdry = PS.to_ctx bdry in
        let src = Tm.check cbdry src_unchkd in
        if not (Tm.is_full cbdry src) then raise NotAlgebraic
        else
          let tgt = Tm.check cbdry tgt_unchkd in
          if not (Tm.is_full cbdry tgt) then raise NotAlgebraic
          else
            let total_ty =
              Ty.morphism
                (Tm.apply_sub src src_inclusion)
                (Tm.apply_sub tgt tgt_inclusion)
            in
            let coh = NonInv ({ ps; src; tgt; total_ty }, name) in
            Hashtbl.add tbl_noninv (ps_unchkd, src_unchkd, tgt_unchkd) coh;
            coh

  let check_inv ps_unchkd src_unchkd tgt_unchkd name =
    match Hashtbl.find_opt tbl_inv (ps_unchkd, src_unchkd, tgt_unchkd) with
    | Some coh -> coh
    | None ->
        let ctx = Ctx.check (Unchecked.ps_to_ctx ps_unchkd) in
        let ps = PS.mk ctx in
        let src = Tm.check ctx src_unchkd in
        let tgt = Tm.check ctx tgt_unchkd in
        let ty = Ty.morphism src tgt in
        if Ty.is_full ctx ty then (
          let coh = Inv ({ ps; ty }, name) in
          Hashtbl.add tbl_inv (ps_unchkd, src_unchkd, tgt_unchkd) coh;
          coh)
        else raise NotAlgebraic

  let data c =
    match c with
    | Inv (d, pp_data) -> (d.ps, d.ty, pp_data)
    | NonInv (d, pp_data) -> (d.ps, d.total_ty, pp_data)

  let to_string c =
    let ps, ty, pp_data = data c in
    if not !Settings.unroll_coherences then
      Unchecked.coh_pp_data_to_string pp_data
    else Printf.sprintf "Coh(%s,%s)" (PS.to_string ps) (Ty.to_string ty)

  let noninv_srctgt c =
    match c with
    | Inv (_, _) -> Error.fatal "non-invertible data of an invertible coh"
    | NonInv (d, _) ->
        (Tm.forget d.src, Tm.forget d.tgt, Ty.forget (Tm.ty d.src))

  let dim c =
    let ty = match c with Inv (d, _) -> d.ty | NonInv (d, _) -> d.total_ty in
    Ty.dim ty

  let func_data = function
    | Inv (_, (_, _, func)) | NonInv (_, (_, _, func)) -> func

  let forget c =
    let ps, ty, pp_data = data c in
    (PS.forget ps, Ty.forget ty, pp_data)

  let check_equal coh1 coh2 =
    if coh1 == coh2 then ()
    else
      match (coh1, coh2) with
      | Inv (d1, _), Inv (d2, _) ->
          PS.check_equal d1.ps d2.ps;
          Ty.check_equal d1.ty d2.ty
      | NonInv (d1, _), NonInv (d2, _) ->
          PS.check_equal d1.ps d2.ps;
          Ty.check_equal d1.total_ty d2.total_ty
      | Inv _, NonInv _ | NonInv _, Inv _ ->
          raise (NotEqual (to_string coh1, to_string coh2))
end

module U = Unchecked (Coh)
module Unchecked = U.Make (Coh)

let check check_fn name =
  let v = 2 in
  let fname = if !Settings.verbosity >= v then Lazy.force name else "" in
  Io.info ~v (lazy ("checking " ^ fname));
  try check_fn () with
  | NotEqual (s1, s2) ->
      Error.untypable
        (if !Settings.verbosity >= v then fname else Lazy.force name)
        (Printf.sprintf "%s and %s are not equal" s1 s2)
  | InvalidSubTarget (s, tgt) ->
      Error.untypable
        (if !Settings.verbosity >= v then fname else Lazy.force name)
        (Printf.sprintf "substitution %s does not apply from context %s" s tgt)
  | Error.UnknownId s ->
      Error.untypable
        (if !Settings.verbosity >= v then fname else Lazy.force name)
        (Printf.sprintf "unknown identifier :%s" s)
  | MetaVariable ->
      Error.incomplete_constraints
        (if !Settings.verbosity >= v then fname else Lazy.force name)

let check_type ctx a =
  let ty = lazy ("type: " ^ Unchecked.ty_to_string a) in
  check (fun () -> Ty.check ctx a) ty

let check_term ctx ?ty t =
  let ty = Option.map (check_type ctx) ty in
  let tm = lazy ("term: " ^ Unchecked.tm_to_string t) in
  check (fun () -> Tm.check ctx ?ty t) tm

let check_coh ps ty pp_data =
  let c = lazy ("coherence: " ^ Unchecked.coh_pp_data_to_string pp_data) in
  check (fun () -> Coh.check ps ty pp_data) c
