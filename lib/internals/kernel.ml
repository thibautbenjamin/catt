open Std
open Common
module CoreSignature = Core

exception IsCoh
exception MetaVariable

module Make (Theory : Theory.S) = struct
  (** Operations on substitutions. *)
  module rec Sub : sig
    type t = B.Sub.t

    val check : B.Ctx.t -> (Coh.t, Tm.t) sub -> B.Ctx.t -> B.Sub.t
    val check_to_ps : B.Ctx.t -> (Coh.t, Tm.t) sub_ps -> PS.t -> B.Sub.t
    val forget : B.Sub.t -> (Coh.t, Tm.t) sub
    val free_vars : B.Sub.t -> Var.t list
    val src : B.Sub.t -> B.Ctx.t
    val tgt : B.Sub.t -> B.Ctx.t
  end = struct
    include B.Sub

    let free_vars s = List.concat (List.map Tm.free_vars (to_list s))

    let check_to_ps src s tgt_ps =
      let tgt = PS.to_ctx tgt_ps in
      let s_assoc =
        try List.map2 (fun (x, _) (t, e) -> (x, (t, e))) (Ctx.value tgt) s
        with Invalid_argument _ ->
          Error.fatal "uncaught wrong number of arguments"
      in
      check src s_assoc tgt
  end

  (** A context, associating a type to each context variable. *)
  and Ctx : sig
    type t = B.Ctx.t

    val to_string : t -> string
    val ty_var : t -> Var.t -> B.Ty.t
    val domain : t -> Var.t list
    val value : t -> (Var.t * B.Ty.t) list
    val forget : t -> (Coh.t, Tm.t) ctx
    val check : (Coh.t, Tm.t) ctx -> t
    val is_equal : t -> t -> bool
    val check_equal : t -> t -> unit
  end =
    B.Ctx

  (** Operations on pasting schemes. *)
  and PS : sig
    exception Invalid

    type t

    val to_string : t -> string
    val mk : Ctx.t -> t
    val to_ctx : t -> Ctx.t
    val bdry : t -> t
    val source : t -> B.Sub.t
    val target : t -> B.Sub.t
    val forget : t -> ps
    val is_equal : t -> t -> bool
  end = struct
    exception Invalid

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
          let v = try Ty.target tf with B.IsObj -> raise Invalid in
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
              let u, v =
                try Ty.retrieve_arrow tf with B.IsObj -> raise Invalid
              in
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
    let to_string ps = Printing.ps_to_string (forget ps)

    (** Create a context from a pasting scheme. *)
    let to_ctx ps = ps.ctx

    let bdry ps =
      mk (Ctx.check (Unchecked.ps_to_ctx (Unchecked.ps_bdry ps.tree)))

    let source ps =
      Sub.check_to_ps (to_ctx ps) (Unchecked.ps_src ps.tree) (bdry ps)

    let target ps =
      Sub.check_to_ps (to_ctx ps) (Unchecked.ps_tgt ps.tree) (bdry ps)

    let is_equal ps1 ps2 =
      ps1.tree == ps2.tree || Equality.is_equal_ps ps1.tree ps2.tree
  end

  and Ty : sig
    type t = B.Ty.t

    val to_string : t -> string
    val free_vars : t -> Var.t list
    val contains_all_vars : t -> bool
    val is_full : t -> bool
    val is_obj : t -> bool
    val is_equal : t -> t -> bool
    val check_equal : t -> t -> unit
    val morphism : Tm.t -> Tm.t -> t
    val forget : t -> (Coh.t, Tm.t) ty
    val check : B.Ctx.t -> (Coh.t, Tm.t) ty -> t
    val apply_sub : t -> B.Sub.t -> t
    val retrieve_arrow : t -> Tm.t * Tm.t
    val under_type : t -> t
    val source : t -> Tm.t
    val target : t -> Tm.t
    val ctx : t -> B.Ctx.t
    val dim : t -> int
  end = struct
    include B.Ty

    let rec free_vars (ty : t) =
      if Ty.is_obj ty then []
      else
        let t, u, v = (Ty.under_type ty, Ty.source ty, Ty.target ty) in
        List.unions [ free_vars t; Tm.free_vars u; Tm.free_vars v ]

    (* TODO: remove is_full *)
    let contains_all_vars (t : t) =
      List.included (Ctx.domain (Ty.ctx t)) (free_vars t)

    let is_full t = contains_all_vars t
  end

  (** Operations on terms. *)
  and Tm : sig
    type t

    (* Data extraction *)
    val to_var : t -> Var.t
    val typ : t -> Ty.t
    val ty : t -> (Coh.t, Tm.t) ty
    val bdry : t -> t * t
    val ctx : t -> (Coh.t, Tm.t) ctx
    val forget : t -> (Coh.t, Tm.t) tm
    val constr : t -> (Coh.t, Tm.t) constr
    val name : t -> string option
    val full_name : t -> string option
    val func_data : t -> (Var.t * int) list list option
    val pp_data : t -> pp_data option
    val to_string : t -> string

    (* Variable uses *)
    val free_vars : t -> Var.t list
    val contains_all_vars : t -> bool
    val is_full : t -> bool

    (* Production of terms *)
    val of_coh : Coh.t -> t

    val check_in_ctx :
      Ctx.t -> ?ty:Ty.t -> ?name:pp_data -> (Coh.t, Tm.t) tm -> t

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

    type expr = Var of Var.t | Coh of Coh.t * B.Sub.t | App of Tm.t * B.Sub.t

    and t = {
      ty : Ty.t;
      e : expr;
      unchecked : tm;
      mutable developped : tm option;
      name : pp_data option;
    }

    let typ t = t.ty
    let ty t = Ty.forget t.ty
    let tbl : (Ctx.t * tm, Tm.t) Hashtbl.t = Hashtbl.create 7829

    let free_vars tm =
      let fvty = Ty.free_vars tm.ty in
      match tm.e with
      | Var x -> x :: fvty
      | Coh (_, sub) | App (_, sub) -> Sub.free_vars sub

    (* TODO: remove is_full *)
    let contains_all_vars tm =
      List.included (Ctx.domain (Ty.ctx tm.ty)) (free_vars tm)

    let is_full tm = contains_all_vars tm
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
                let e, ty = (Var x, Ty.check c (Ty.forget (Ctx.ty_var c x))) in
                { ty; e; unchecked = t; developped = Some t; name }
            | Meta_tm _ -> raise MetaVariable
            | Coh (coh, s) ->
                let sub = Sub.check_to_ps c s (Coh.ps coh) in
                let e, ty = (Coh (coh, sub), Ty.apply_sub (Coh.ty coh) sub) in
                let tm = { ty; e; unchecked = t; developped = Some t; name } in
                Hashtbl.add tbl (c, t) tm;
                tm
            | App (u, s) ->
                let ty = Tm.typ u in
                let sub = Sub.check c s (Ty.ctx ty) in
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
                let s = Sub.forget s in
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

    let apply_sub t sub =
      Ctx.check_equal (Sub.tgt sub) (Ty.ctx t.ty);
      let c = Sub.src sub in
      let ty = Ty.apply_sub t.ty sub in
      let t = Unchecked.tm_apply_sub (forget t) (Sub.forget sub) in
      check_in_ctx c ~ty t

    let preimage t sub =
      Ctx.check_equal (Sub.src sub) (Ty.ctx t.ty);
      let c = Sub.tgt sub in
      let t = Unchecked.tm_sub_preimage (forget t) (Sub.forget sub) in
      check_in_ctx c t

    let is_equal t1 t2 =
      Ctx.is_equal (Ty.ctx t1.ty) (Ty.ctx t2.ty)
      && Equality.is_equal_tm t1.unchecked t2.unchecked

    let apply fun_ctx fun_tm fun_pp_data tm =
      let c = fun_ctx (Ctx.forget (Ty.ctx (typ tm))) in
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

    let bdry t = (Ty.source (typ t), Ty.target (typ t))
    let ctx t = Ctx.forget (Ty.ctx (typ t))
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
    val ty : t -> Ty.t
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
    type innertm = Tm.t
    type cohInv = { ps : PS.t; ty : Ty.t }
    type cohNonInv = { ps : PS.t; src : Tm.t; tgt : Tm.t; total_ty : Ty.t }
    type t = Inv of cohInv * pp_data | NonInv of cohNonInv * pp_data

    open Syntax.Make (Core)

    let tbl : (ps * ty, Coh.t) Hashtbl.t = Hashtbl.create 7829
    let tbl_inv : (ps * tm * tm, Coh.t) Hashtbl.t = Hashtbl.create 7829
    let tbl_noninv : (ps * tm * tm, Coh.t) Hashtbl.t = Hashtbl.create 7829

    exception NotAlgebraic

    let ps = function Inv (data, _) -> data.ps | NonInv (data, _) -> data.ps

    let ty = function
      | Inv (data, _) -> data.ty
      | NonInv (data, _) -> data.total_ty

    let src c = Tm.forget (Ty.source (ty c))
    let tgt c = Tm.forget (Ty.target (ty c))
    let is_inv = function Inv (_, _) -> true | NonInv (_, _) -> false

    let algebraic ps ty name =
      let module Fullness = Fullness.Make (Theory) (Sub) (PS) (Tm) (Ty) in
      match Fullness.check ps ty with
      | Inv ->
          Ctx.check_equal (PS.to_ctx ps) (Ty.ctx ty);
          Inv ({ ps; ty }, name)
      | NonInv (src, tgt) ->
          Ctx.check_equal (PS.to_ctx ps) (Ty.ctx ty);
          NonInv ({ ps; src; tgt; total_ty = ty }, name)
      | No -> raise NotAlgebraic

    let check ps_unchkd t_unchkd ((name, _, _) as pp_data) =
      Io.info ~v:5
        (lazy
          (Printf.sprintf "checking coherence (%s,%s)"
             (Printing.ps_to_string ps_unchkd)
             (Printing.ty_to_string t_unchkd)));
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
                   (Printing.ty_to_string t_unchkd)
                   (Printing.ctx_to_string (Unchecked.ps_to_ctx ps_unchkd)))
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
          let src = Tm.check_in_ctx cbdry src_unchkd in
          if not (Tm.is_full src) then raise NotAlgebraic
          else
            let tgt = Tm.check_in_ctx cbdry tgt_unchkd in
            if not (Tm.is_full tgt) then raise NotAlgebraic
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
          let src = Tm.check_in_ctx ctx src_unchkd in
          let tgt = Tm.check_in_ctx ctx tgt_unchkd in
          let ty = Ty.morphism src tgt in
          if Ty.is_full ty then (
            let coh = Inv ({ ps; ty }, name) in
            Hashtbl.add tbl_inv (ps_unchkd, src_unchkd, tgt_unchkd) coh;
            coh)
          else raise NotAlgebraic

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
      | NonInv (d, _) ->
          (Tm.forget d.src, Tm.forget d.tgt, Ty.forget (Tm.typ d.src))

    let dim c =
      let ty =
        match c with Inv (d, _) -> d.ty | NonInv (d, _) -> d.total_ty
      in
      Ty.dim ty

    let func_data = function
      | Inv (_, (_, _, func)) | NonInv (_, (_, _, func)) -> func

    let forget c =
      let ps, ty, pp_data = data c in
      (PS.forget ps, Ty.forget ty, pp_data)

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
      let ps = PS.forget (PS.mk (Ctx.check ctx)) in
      let db_sub = Unchecked.db_level_sub_inv ctx in
      let pp_data = Display_maps.pp_data_rename (fun_pp_data pp) db_sub in
      let ty = Unchecked.ty_apply_sub (fun_ty ty) db_sub in
      (check ps ty pp_data, db_sub)
  end

  and Core :
    (CoreSignature.S
      with type PS.t = PS.t
      with type Coh.t = Coh.t
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
      type t

      val to_list : t -> Tm.t list
      val check : Ctx.t -> (Coh.t, Tm.t) sub -> Ctx.t -> t
      val forget : t -> (Coh.t, Tm.t) sub
      val src : t -> Ctx.t
      val tgt : t -> Ctx.t
    end

    and Ctx : sig
      type t

      val to_string : t -> string
      val ty_var : t -> Var.t -> Ty.t
      val domain : t -> Var.t list
      val value : t -> (Var.t * Ty.t) list
      val forget : t -> (Coh.t, Tm.t) ctx
      val check : (Coh.t, Tm.t) ctx -> t
      val is_equal : t -> t -> bool
      val check_equal : t -> t -> unit
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
    end
  end =
    Builder.Make (Core)

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
