open Std
open Common
module CoreSignature = Core

exception IsCoh
exception IsObj
exception MetaVariable

module Make (Theory : Theory.S) = struct
  (** Operations on substitutions. *)
  module rec Sub : sig
    type t = B.Sub.t

    val check : B.Ctx.t -> (Coh.t, Tm.t) sub -> B.Ctx.t -> B.Sub.t
    val check_to_ps : B.Ctx.t -> (Coh.t, Tm.t) sub_ps -> PS.t -> B.Sub.t
  end = struct
    include B.Sub

    let check_to_ps src s (tgt_ps : PS.t) =
      let tgt = tgt_ps.ctx in
      let s_assoc =
        try List.map2 (fun (x, _) (t, e) -> (x, (t, e))) tgt.c s
        with Invalid_argument _ ->
          Error.fatal "uncaught wrong number of arguments"
      in
      check src s_assoc tgt
  end

  (** Operations on pasting schemes. *)
  and PS : sig
    exception Invalid

    type t = private { tree : ps; ctx : B.Ctx.t }

    val to_string : t -> string
    val mk : B.Ctx.t -> t
    val bdry : t -> t
    val source : t -> B.Sub.t
    val target : t -> B.Sub.t
    val is_equal : t -> t -> bool
  end = struct
    exception Invalid

    module Ctx = B.Ctx
    module Ty = B.Ty
    open Syntax.Make (Core)

    (** A pasting scheme. *)
    type ps_derivation =
      | PNil of (Var.t * Ty.t)
      | PCons of ps_derivation * (Var.t * Ty.t) * (Var.t * Ty.t)
      | PDrop of ps_derivation

    type t = { tree : ps; ctx : Ctx.t }

    let tbl : (Ctx.t, PS.t) Hashtbl.t = Hashtbl.create 7829

    (** Create a context from a pasting scheme. *)
    let old_rep_to_ctx ps =
      let rec list ps =
        match ps with
        | PDrop ps -> list ps
        | PCons (ps, (x1, t1), (x2, t2)) ->
            (x2, (t2.unchecked, true)) :: (x1, (t1.unchecked, true)) :: list ps
        | PNil (x, t) -> [ (x, (t.unchecked, true)) ]
      in
      Ctx.check (list ps)

    (** Dangling variable. *)
    let rec marker (ps : ps_derivation) =
      match ps with
      | PNil (x, t) -> (x, t)
      | PCons (_, _, f) -> f
      | PDrop ps ->
          let _, tf = marker ps in
          let v = match tf.e with Obj -> raise Invalid | Arr (_, _, v) -> v in
          let y = try Tm.to_var v with B.IsCoh -> raise Invalid in
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
      let rec close ps (tx : Ty.t) =
        match tx.e with Obj -> ps | Arr (tx, _, _) -> close (PDrop ps) tx
      in
      let build l =
        let x0, ty, l =
          match (l : (Var.t * Ty.t) list) with
          | (x, ({ e = Obj; _ } as ty)) :: l -> (x, ty, l)
          | _ -> raise Invalid
        in
        let rec aux ps (l : (Var.t * Ty.t) list) =
          match l with
          | (y, ty) :: (f, ({ e = Arr (_, u, v); _ } as tf)) :: l as l1 ->
              let fx, fy =
                try (Tm.to_var u, Tm.to_var v) with B.IsCoh -> raise Invalid
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
          | _ :: _ :: _ | [ (_, _) ] -> raise Invalid
          | [] ->
              let _, tx = marker ps in
              close ps tx
        in
        aux (PNil (x0, ty)) l
      in
      build (List.rev l.c)

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

    let to_string ps = Printing.ps_to_string ps.tree

    let bdry ps =
      mk (Ctx.check (Unchecked.ps_to_ctx (Unchecked.ps_bdry ps.tree)))

    let source ps = Sub.check_to_ps ps.ctx (Unchecked.ps_src ps.tree) (bdry ps)
    let target ps = Sub.check_to_ps ps.ctx (Unchecked.ps_tgt ps.tree) (bdry ps)

    let is_equal ps1 ps2 =
      ps1.tree == ps2.tree || Equality.is_equal_ps ps1.tree ps2.tree
  end

  (** Operations on terms. *)
  and Tm : sig
    type expr = Var of Var.t | Coh of Coh.t * B.Sub.t | App of Tm.t * B.Sub.t

    and t = private {
      ty : B.Ty.t;
      e : expr;
      unchecked : (Coh.t, t) tm;
      mutable developped : (Coh.t, t) tm option;
      name : pp_data option;
    }

    (* Data extraction *)
    val to_var : t -> Var.t
    val ty : t -> (Coh.t, Tm.t) ty
    val ctx : t -> (Coh.t, Tm.t) ctx
    val forget : t -> (Coh.t, Tm.t) tm
    val constr : t -> (Coh.t, Tm.t) constr
    val name : t -> string option
    val full_name : t -> string option
    val func_data : t -> (Var.t * int) list list option
    val pp_data : t -> pp_data option
    val to_string : t -> string

    (* Production of terms *)
    val of_coh : Coh.t -> t

    val check_in_ctx :
      B.Ctx.t -> ?ty:B.Ty.t -> ?name:pp_data -> (Coh.t, Tm.t) tm -> t

    val check :
      (Coh.t, Tm.t) ctx ->
      ?ty:(Coh.t, Tm.t) ty ->
      ?name:pp_data ->
      (Coh.t, Tm.t) tm ->
      t

    val apply_sub : t -> B.Sub.t -> t
    val preimage : t -> B.Sub.t -> t
    val develop : t -> (Coh.t, Tm.t) tm

    val apply :
      ((Coh.t, Tm.t) ctx -> (Coh.t, Tm.t) ctx) ->
      ((Coh.t, Tm.t) tm -> (Coh.t, Tm.t) tm) ->
      (pp_data -> pp_data) ->
      t ->
      t * (Coh.t, Tm.t) sub

    val is_equal : t -> t -> bool
  end = struct
    open Syntax.Make (Core)
    module Ty = B.Ty
    module Ctx = B.Ctx

    type expr = Var of Var.t | Coh of Coh.t * B.Sub.t | App of Tm.t * B.Sub.t

    type t = {
      ty : Ty.t;
      e : expr;
      unchecked : tm;
      mutable developped : tm option;
      name : pp_data option;
    }

    let ty t = t.ty.unchecked
    let tbl : (B.Ctx.t * tm, Tm.t) Hashtbl.t = Hashtbl.create 7829
    let forget tm = tm.unchecked
    let constr tm = (forget tm, ty tm)

    let check_in_ctx c ?ty ?name t =
      Io.info ~v:5
        (lazy
          (Printf.sprintf "building kernel term %s in context %s"
             (Printing.tm_to_string t) (Ctx.to_string c)));
      let tm =
        match Hashtbl.find_opt tbl (c, t) with
        | Some tm -> tm
        | None -> (
            match t with
            | Var x ->
                let e, ty = (Var x, Ty.check c (Ctx.ty_var c x).unchecked) in
                { ty; e; unchecked = t; developped = Some t; name }
            | Meta_tm _ -> raise MetaVariable
            | Coh (coh, s) ->
                let sub = Sub.check_to_ps c s (Coh.ps coh) in
                let e, ty = (Coh (coh, sub), Ty.apply_sub (Coh.ty coh) sub) in
                let tm = { ty; e; unchecked = t; developped = Some t; name } in
                Hashtbl.add tbl (c, t) tm;
                tm
            | App (u, s) ->
                let ty = u.ty in
                let sub = Sub.check c s ty.c in
                let e, ty = (App (u, sub), Ty.apply_sub ty sub) in
                let tm = { ty; e; unchecked = t; developped = None; name } in
                Hashtbl.add tbl (c, t) tm;
                tm)
      in
      match ty with
      | None -> tm
      | Some ty ->
          Ty.check_equal ty tm.ty;
          tm

    let check c ?ty ?name tm =
      let c = Ctx.check c in
      let ty = Option.map (Ty.check c) ty in
      check_in_ctx c ?ty ?name tm

    let develop tm =
      match tm.developped with
      | Some t -> t
      | None ->
          let dev =
            match tm.e with
            | Var _ | Coh (_, _) -> tm.unchecked
            | App (t, s) ->
                let dt = Tm.develop t in
                let s = s.unchecked in
                Unchecked.tm_apply_sub dt s
          in
          tm.developped <- Some dev;
          dev

    let to_var tm =
      match tm.e with
      | Var v -> v
      | Coh _ -> raise IsCoh
      | App _ -> (
          match develop tm with
          | Var v -> v
          | Coh _ -> raise IsCoh
          | App _ | Meta_tm _ -> assert false)

    let apply_sub t (sub : B.Sub.t) =
      Ctx.check_equal sub.tgt t.ty.c;
      let c = sub.src in
      let ty = Ty.apply_sub t.ty sub in
      let t = Unchecked.tm_apply_sub (forget t) sub.unchecked in
      check_in_ctx c ~ty t

    let preimage t (sub : B.Sub.t) =
      Ctx.check_equal sub.src t.ty.c;
      let c = sub.tgt in
      let t = Unchecked.tm_sub_preimage (forget t) sub.unchecked in
      check_in_ctx c t

    let is_equal t1 t2 =
      Ctx.is_equal t1.ty.c t2.ty.c
      && Equality.is_equal_tm t1.unchecked t2.unchecked

    let apply fun_ctx fun_tm fun_pp_data tm =
      let c = fun_ctx (Ctx.forget tm.ty.c) in
      let db_sub = Unchecked.db_level_sub_inv c in
      let c, _, _ = Unchecked.db_levels c in
      let c = Ctx.check c in
      let newexp = Unchecked.tm_apply_sub (fun_tm (forget tm)) db_sub in
      let name =
        Option.map
          (fun pp_data ->
            Display_maps.pp_data_rename (fun_pp_data pp_data) db_sub)
          tm.name
      in
      (check_in_ctx c ?name newexp, db_sub)

    let ctx t = Ctx.forget t.ty.c
    let name t = Option.map Printing.pp_data_to_string t.name
    let full_name t = Option.map Printing.full_name t.name
    let func_data t = Option.map (fun (_, _, f) -> f) t.name
    let pp_data t = t.name

    let to_string t =
      match full_name t with
      | Some name -> name
      | None -> Printing.tm_to_string (forget t)

    let of_coh coh =
      let ps, _, pp_data = Coh.forget coh in
      let id = Unchecked.identity_ps ps in
      let ctx = Unchecked.ps_to_ctx ps in
      check_in_ctx (Ctx.check ctx) ~name:pp_data (Coh (coh, id))
  end

  (** A coherence. *)
  and Coh : sig
    type t
    type innertm = Tm.t

    val ps : t -> PS.t
    val ty : t -> B.Ty.t
    val src : t -> (t, Tm.t) tm
    val tgt : t -> (t, Tm.t) tm
    val suspend : t -> t
    val check : ps -> (t, Tm.t) ty -> pp_data -> t
    val check_noninv : ps -> (t, Tm.t) tm -> (t, Tm.t) tm -> pp_data -> t
    val check_inv : ps -> (t, Tm.t) tm -> (t, Tm.t) tm -> pp_data -> t
    val to_string : ?unroll:bool -> t -> string
    val is_inv : t -> bool
    val noninv_srctgt : t -> (t, Tm.t) tm * (t, Tm.t) tm * (t, Tm.t) ty
    val forget : t -> ps * (t, Tm.t) ty * pp_data
    val func_data : t -> (Var.t * int) list list
    val is_equal : t -> t -> bool
    val check_equal : t -> t -> unit
    val dim : t -> int

    val apply_ps :
      (ps -> ps) ->
      ((t, Tm.t) ty -> (t, Tm.t) ty) ->
      (pp_data -> pp_data) ->
      t ->
      t

    val apply :
      ((t, Tm.t) ctx -> (t, Tm.t) ctx) ->
      ((t, Tm.t) ty -> (t, Tm.t) ty) ->
      (pp_data -> pp_data) ->
      t ->
      t * (t, Tm.t) sub
  end = struct
    module Ty = B.Ty

    type innertm = Tm.t
    type cohInv = { ps : PS.t; ty : Ty.t }
    type cohNonInv = { ps : PS.t; src : Tm.t; tgt : Tm.t; total_ty : Ty.t }
    type t = Inv of cohInv * pp_data | NonInv of cohNonInv * pp_data

    open Syntax.Make (Core)

    let tbl : (ps * ty, Coh.t) Hashtbl.t = Hashtbl.create 7829
    let tbl_inv : (ps * tm * tm, Coh.t) Hashtbl.t = Hashtbl.create 7829
    let tbl_noninv : (ps * tm * tm, Coh.t) Hashtbl.t = Hashtbl.create 7829

    module A = struct
      module Theory = Theory
      module PS = PS
      module Sub = B.Sub
      module Coh = Coh
      module Tm = Tm
      module Ctx = B.Ctx
      module Ty = B.Ty
    end

    module Fullness = Fullness.Make (A)
    module Ctx = B.Ctx

    exception NotAlgebraic

    let ps = function Inv (data, _) -> data.ps | NonInv (data, _) -> data.ps

    let ty = function
      | Inv (data, _) -> data.ty
      | NonInv (data, _) -> data.total_ty

    let src c =
      match (ty c).e with Obj -> raise IsObj | Arr (_, s, _) -> Tm.forget s

    let tgt c =
      match (ty c).e with Obj -> raise IsObj | Arr (_, _, t) -> Tm.forget t

    let is_inv = function Inv (_, _) -> true | NonInv (_, _) -> false

    let algebraic ps ty name =
      match Fullness.check ps ty with
      | Inv ->
          Ctx.check_equal ps.ctx ty.c;
          Inv ({ ps; ty }, name)
      | NonInv (src, tgt) ->
          Ctx.check_equal ps.ctx ty.c;
          NonInv ({ ps; src; tgt; total_ty = ty }, name)
      | No -> raise NotAlgebraic

    let register ps t ((name, _, _) as pp_data) =
      try
        let coh = algebraic ps t pp_data in
        Hashtbl.add tbl (ps.tree, t.unchecked) coh;
        coh
      with
      | NotAlgebraic ->
          Error.not_valid_coherence name
            (Printf.sprintf "type %s not algebraic in pasting scheme %s"
               (Printing.ty_to_string t.unchecked)
               (Printing.ctx_to_string (Unchecked.ps_to_ctx ps.tree)))
      | DoubledVar s ->
          Error.not_valid_coherence name
            (Printf.sprintf "variable %s appears twice in the context" s)

    let check ps_unchkd t_unchkd name =
      Io.info ~v:5
        (lazy
          (Printf.sprintf "checking coherence (%s,%s)"
             (Printing.ps_to_string ps_unchkd)
             (Printing.ty_to_string t_unchkd)));
      match Hashtbl.find_opt tbl (ps_unchkd, t_unchkd) with
      | Some coh -> coh
      | None ->
          let cps = Ctx.check (Unchecked.ps_to_ctx ps_unchkd) in
          let ps = PS.mk cps in
          let t = Ty.check cps t_unchkd in
          register ps t name

    let check_noninv ps_unchkd src_unchkd tgt_unchkd name =
      match Hashtbl.find_opt tbl_noninv (ps_unchkd, src_unchkd, tgt_unchkd) with
      | Some coh -> coh
      | None ->
          let ps = PS.mk (Ctx.check (Unchecked.ps_to_ctx ps_unchkd)) in
          let src_inclusion = PS.source ps in
          let tgt_inclusion = PS.target ps in
          let bdry = PS.bdry ps in
          let src = Tm.check_in_ctx bdry.ctx src_unchkd in
          let tgt = Tm.check_in_ctx bdry.ctx tgt_unchkd in
          let total_ty =
            Ty.morphism
              (Tm.apply_sub src src_inclusion)
              (Tm.apply_sub tgt tgt_inclusion)
          in
          register ps total_ty name

    let check_inv ps_unchkd src_unchkd tgt_unchkd name =
      match Hashtbl.find_opt tbl_inv (ps_unchkd, src_unchkd, tgt_unchkd) with
      | Some coh -> coh
      | None ->
          let ctx = Ctx.check (Unchecked.ps_to_ctx ps_unchkd) in
          let ps = PS.mk ctx in
          let src = Tm.check_in_ctx ctx src_unchkd in
          let tgt = Tm.check_in_ctx ctx tgt_unchkd in
          let ty = Ty.morphism src tgt in
          register ps ty name

    let data c =
      match c with
      | Inv (d, pp_data) -> (d.ps, d.ty, pp_data)
      | NonInv (d, pp_data) -> (d.ps, d.total_ty, pp_data)

    let to_string ?(unroll = false) c =
      let ps, ty, pp_data = data c in
      if unroll || !Settings.unroll_coherences then
        Printf.sprintf "Coh(%s,%s)" (PS.to_string ps) (Ty.to_string ty)
      else Printing.pp_data_to_string pp_data

    let noninv_srctgt c =
      match c with
      | Inv (_, _) -> Error.fatal "non-invertible data of an invertible coh"
      | NonInv (d, _) -> (Tm.forget d.src, Tm.forget d.tgt, d.src.ty.unchecked)

    let dim c =
      let ty =
        match c with Inv (d, _) -> d.ty | NonInv (d, _) -> d.total_ty
      in
      Ty.dim ty

    let func_data = function
      | Inv (_, (_, _, func)) | NonInv (_, (_, _, func)) -> func

    let forget c =
      let ps, ty, pp_data = data c in
      (ps.tree, ty.unchecked, pp_data)

    let is_equal coh1 coh2 =
      coh1 == coh2
      ||
      match (coh1, coh2) with
      | Inv (d1, _), Inv (d2, _) ->
          PS.is_equal d1.ps d2.ps && Ty.is_equal d1.ty d2.ty
      | NonInv (d1, _), NonInv (d2, _) ->
          PS.is_equal d1.ps d2.ps && Ty.is_equal d1.total_ty d2.total_ty
      | Inv _, NonInv _ | NonInv _, Inv _ -> false

    let suspend coh =
      let ps, ty, pp_data = forget coh in
      check (Unchecked.suspend_ps ps) (Unchecked.suspend_ty ty)
        (Unchecked.suspend_pp_data pp_data)

    let check_equal coh1 coh2 =
      if not (is_equal coh1 coh2) then
        raise (NotEqual (to_string coh1, to_string coh2))

    let apply_ps fun_ps fun_ty fun_pp_data coh =
      let ps, ty, pp = forget coh in
      let ps = fun_ps ps in
      let pp_data = fun_pp_data pp in
      let ty = fun_ty ty in
      check ps ty pp_data

    let apply fun_ctx fun_ty fun_pp_data coh =
      let ps, ty, pp = forget coh in
      let ctx = fun_ctx (Unchecked.ps_to_ctx ps) in
      let ps = (PS.mk (Ctx.check ctx)).tree in
      let db_sub = Unchecked.db_level_sub_inv ctx in
      let pp_data = Display_maps.pp_data_rename (fun_pp_data pp) db_sub in
      let ty = Unchecked.ty_apply_sub (fun_ty ty) db_sub in
      (check ps ty pp_data, db_sub)
  end

  and Core :
    (CoreSignature.S
      with type PS.t = PS.t
      with type Coh.t = Coh.t
      with type Coh.innertm = Tm.t
      with type Tm.t = Tm.t) = struct
    module PS = PS
    module Tm = Tm
    module Coh = Coh
  end

  and B : sig
    exception IsObj
    exception IsCoh
    exception InvalidSubTarget of string * string
    exception MetaVariable

    module rec Sub : sig
      type t = private {
        list : Tm.t list;
        src : Ctx.t;
        tgt : Ctx.t;
        unchecked : (Coh.t, Tm.t) sub;
      }

      val check : Ctx.t -> (Coh.t, Tm.t) sub -> Ctx.t -> t
    end

    and Ctx : sig
      type t = private {
        c : (Var.t * Ty.t) list;
        unchecked : (Coh.t, Tm.t) ctx;
      }

      val to_string : t -> string
      val ty_var : t -> Var.t -> Ty.t
      val domain : t -> Var.t list
      val forget : t -> (Coh.t, Tm.t) ctx
      val check : (Coh.t, Tm.t) ctx -> t
      val is_equal : t -> t -> bool
      val check_equal : t -> t -> unit
    end

    and Ty : sig
      type t = private { c : Ctx.t; e : expr; unchecked : (Coh.t, Tm.t) ty }
      and expr = Obj | Arr of t * Tm.t * Tm.t

      val to_string : t -> string
      val is_equal : t -> t -> bool
      val check_equal : t -> t -> unit
      val morphism : Tm.t -> Tm.t -> Ty.t
      val check : Ctx.t -> (Coh.t, Tm.t) ty -> t
      val apply_sub : t -> Sub.t -> t
      val dim : t -> int
    end
  end =
    Builder.Make (Core)

  module Ty = B.Ty
  module Ctx = B.Ctx
  include Syntax.Make (Core)

  let check check_fn name =
    let v = 2 in
    let fname = if !Settings.verbosity >= v then Lazy.force name else "" in
    Io.info ~v (lazy ("checking " ^ fname));
    try check_fn () with
    | NotEqual (s1, s2) ->
        Error.untypable
          (if !Settings.verbosity >= v then fname else Lazy.force name)
          (Printf.sprintf "%s and %s are not equal" s1 s2)
    | B.InvalidSubTarget (s, tgt) ->
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
    let ty = lazy ("type: " ^ Printing.ty_to_string a) in
    check (fun () -> Ty.check ctx a) ty

  let check_term ctx ?ty ?name t =
    let ty = Option.map (check_type ctx) ty in
    let tm = lazy ("term: " ^ Printing.tm_to_string t) in
    check (fun () -> Tm.check_in_ctx ctx ?ty ?name t) tm

  let check_constr ?name ctx constr =
    let ctx = Ctx.check ctx in
    let t, ty = constr in
    let ty = if !Settings.debug then None else Some ty in
    check_term ctx ?ty ?name t

  let check_coh ps ty pp_data =
    let c = lazy ("coherence: " ^ Printing.pp_data_to_string pp_data) in
    check (fun () -> Coh.check ps ty pp_data) c

  let check_sub src s tgt =
    ignore @@ Sub.check (Ctx.check src) s (Ctx.check tgt)
end
