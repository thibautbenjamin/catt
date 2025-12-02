open Common
module CoreSignature = Core

exception IsCoh
exception IsObj
exception MetaVariable

module Make (Theory : sig
  val theory : theory
end) =
struct
  module rec RTy :
    (Signature.TyS
      with type checked_tm = K.Tm.t
       and type checked_coh = K.Coh.t
       and type checked_sub = K.Sub.t
       and type checked_ctx = K.Ctx.t) = struct
    open K
    open Syntax.Make (Core)

    type checked_ctx = Ctx.t
    type checked_coh = Coh.t
    type checked_tm = Tm.t
    type checked_sub = Sub.t

    type expr = Obj | Arr of t * Tm.t * Tm.t  (** A type exepression. *)
    and t = { c : Ctx.t; e : expr; unchecked : ty }

    let tbl : (Ctx.t * ty, Ty.t) Hashtbl.t = Hashtbl.create 7829
    let ctx t = t.c
    let expr t = t.e

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

    let check_with_ctx ctx ty = check (Ctx.check ctx) ty
    let to_string ty = Printing.ty_to_string ty.unchecked

    let is_equal ty1 ty2 =
      Ctx.is_equal ty1.c ty2.c
      && Equality.is_equal_ty ty1.unchecked ty2.unchecked

    let check_equal ty1 ty2 =
      if not (is_equal ty1 ty2) then
        raise
          (NotEqual
             ( Printing.ty_to_string ty1.unchecked,
               Printing.ty_to_string ty2.unchecked ))

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

    let apply_sub t (s : Sub.t) =
      Ctx.check_equal t.c s.tgt;
      check s.src (Unchecked.ty_apply_sub t.unchecked s.unchecked)

    let rec dim t = match t.e with Obj -> 0 | Arr (a, _, _) -> 1 + dim a
    let forget t = t.unchecked
  end

  (** Operations on terms. *)
  and RTm :
    (Signature.TmS
      with type checked_coh = K.Coh.t
       and type checked_sub = K.Sub.t
       and type checked_ty = K.Ty.t
       and type checked_ctx = K.Ctx.t) = struct
    open K
    open Syntax.Make (Core)

    type checked_coh = Coh.t
    type checked_sub = Sub.t
    type checked_ty = Ty.t
    type checked_ctx = Ctx.t
    type expr = Var of Var.t | Coh of Coh.t * Sub.t | App of Tm.t * Sub.t

    type t = {
      ty : Ty.t;
      e : expr;
      unchecked : tm;
      mutable developped : tm option;
      name : pp_data option;
    }

    let typ t = t.ty
    let ty t = Ty.forget t.ty
    let checked_ty t = t.ty
    let expr t = t.e
    let tbl : (Ctx.t * tm, Tm.t) Hashtbl.t = Hashtbl.create 7829
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
                let e, ty = (Var x, Ty.(check c (forget (Ctx.ty_var c x)))) in
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

    let preimage t sub =
      Ctx.check_equal (Sub.src sub) (Ty.ctx t.ty);
      let c = Sub.tgt sub in
      let t = Unchecked.tm_sub_preimage (forget t) (Sub.forget sub) in
      check_in_ctx c t

    let apply_sub t (sub : Sub.t) =
      Ctx.check_equal sub.tgt (Ty.ctx t.ty);
      let c = sub.src in
      let ty = Ty.apply_sub t.ty sub in
      let t = Unchecked.tm_apply_sub (forget t) sub.unchecked in
      check_in_ctx c ~ty t

    let is_equal t1 t2 =
      Ctx.is_equal (Ty.ctx t1.ty) (Ty.ctx t2.ty)
      && Equality.is_equal_tm t1.unchecked t2.unchecked

    let apply fun_ctx fun_tm fun_pp_data tm =
      let c = fun_ctx (Ctx.forget (Ty.ctx tm.ty)) in
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

    let ctx t = Ctx.forget (Ty.ctx t.ty)
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
  and RCoh :
    (Signature.CohS
      with type innertm = K.Tm.t
       and type checked_ps = K.PS.t
       and type checked_tm = K.Tm.t
       and type checked_ty = K.Ty.t) = struct
    open K

    type innertm = Tm.t
    type checked_ps = PS.t
    type checked_tm = Tm.t
    type checked_ty = Ty.t
    type cohInv = { ps : PS.t; ty : Ty.t }
    type cohNonInv = { ps : PS.t; src : Tm.t; tgt : Tm.t; total_ty : Ty.t }
    type t = Inv of cohInv * pp_data | NonInv of cohNonInv * pp_data

    open Syntax.Make (Core)

    let tbl : (ps * ty, Coh.t) Hashtbl.t = Hashtbl.create 7829
    let tbl_inv : (ps * tm * tm, Coh.t) Hashtbl.t = Hashtbl.create 7829
    let tbl_noninv : (ps * tm * tm, Coh.t) Hashtbl.t = Hashtbl.create 7829

    module Fullness = Fullness.Make (K)

    exception NotAlgebraic

    let ps = function Inv (data, _) -> data.ps | NonInv (data, _) -> data.ps

    let ty = function
      | Inv (data, _) -> data.ty
      | NonInv (data, _) -> data.total_ty

    let src c =
      match Ty.expr (ty c) with
      | Obj -> raise IsObj
      | Arr (_, s, _) -> Tm.forget s

    let tgt c =
      match Ty.expr (ty c) with
      | Obj -> raise IsObj
      | Arr (_, _, t) -> Tm.forget t

    let is_inv = function Inv (_, _) -> true | NonInv (_, _) -> false

    let algebraic ps ty name =
      match Fullness.check ps ty with
      | Inv ->
          Ctx.check_equal (Ctx.of_ps ps) (Ty.ctx ty);
          Inv ({ ps; ty }, name)
      | NonInv (src, tgt) ->
          Ctx.check_equal (Ctx.of_ps ps) (Ty.ctx ty);
          NonInv ({ ps; src; tgt; total_ty = ty }, name)
      | No -> raise NotAlgebraic

    let register ps t ((name, _, _) as pp_data) =
      try
        let coh = algebraic ps t pp_data in
        Hashtbl.add tbl (ps, Ty.forget t) coh;
        coh
      with
      | NotAlgebraic ->
          Error.not_valid_coherence name
            (Printf.sprintf "type %s not algebraic in pasting scheme %s"
               (Printing.ty_to_string (Ty.forget t))
               (Printing.ctx_to_string (Unchecked.ps_to_ctx ps)))
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
          let src = Tm.check_in_ctx (Ctx.of_ps bdry) src_unchkd in
          let tgt = Tm.check_in_ctx (Ctx.of_ps bdry) tgt_unchkd in
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
      | NonInv (d, _) -> (Tm.forget d.src, Tm.forget d.tgt, Tm.ty d.src)

    let dim c =
      let ty =
        match c with Inv (d, _) -> d.ty | NonInv (d, _) -> d.total_ty
      in
      Ty.dim ty

    let func_data = function
      | Inv (_, (_, _, func)) | NonInv (_, (_, _, func)) -> func

    let forget c =
      let ps, ty, pp_data = data c in
      (ps, Ty.forget ty, pp_data)

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
      let ps = PS.mk (Ctx.check ctx) in
      let db_sub = Unchecked.db_level_sub_inv ctx in
      let pp_data = Display_maps.pp_data_rename (fun_pp_data pp) db_sub in
      let ty = Unchecked.ty_apply_sub (fun_ty ty) db_sub in
      (check ps ty pp_data, db_sub)
  end

  (** Operations on pasting schemes. *)
  and RPS :
    (Signature.PSS with type inner_ctx = K.Ctx.t and type checked_sub = K.Sub.t) =
  struct
    open K
    open Syntax.Make (Core)

    type checked_sub = Sub.t
    type inner_ctx = Ctx.t

    (** A pasting scheme. *)
    type ps_derivation =
      | PNil of (Var.t * Ty.t)
      | PCons of ps_derivation * (Var.t * Ty.t) * (Var.t * Ty.t)
      | PDrop of ps_derivation

    type t = ps

    let tbl : (Ctx.t, t) Hashtbl.t = Hashtbl.create 7829

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
          let v =
            match Ty.expr tf with Obj -> raise InvalidPS | Arr (_, _, v) -> v
          in
          let y = try Tm.to_var v with IsCoh -> raise InvalidPS in
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
        match Ty.expr tx with
        | Obj -> ps
        | Arr (tx, _, _) -> close (PDrop ps) tx
      in
      let build l =
        let x0, ty, l =
          match (l : (Var.t * Ty.t) list) with
          | (x, ty) :: l -> (
              match Ty.expr ty with Obj -> (x, ty, l) | _ -> raise InvalidPS)
          | _ -> raise InvalidPS
        in
        let rec aux ps (l : (Var.t * Ty.t) list) =
          match l with
          | (y, ty) :: (f, tf) :: l as l1 -> (
              match Ty.expr tf with
              | Arr (_, u, v) ->
                  let fx, fy =
                    try (Tm.to_var u, Tm.to_var v)
                    with IsCoh -> raise InvalidPS
                  in
                  if y <> fy then raise InvalidPS;
                  let x, _ = marker ps in
                  if x = fx then (
                    let varps = Ctx.domain (old_rep_to_ctx ps) in
                    if List.mem f varps then
                      raise (DoubledVar (Var.to_string f));
                    if List.mem y varps then
                      raise (DoubledVar (Var.to_string y));
                    let ps = PCons (ps, (y, ty), (f, tf)) in
                    aux ps l)
                  else aux (PDrop ps) l1
              | _ -> raise InvalidPS)
          | _ :: [] -> raise InvalidPS
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
          let ps = make_tree oldrep in
          Hashtbl.add tbl l ps;
          ps

    let to_string ps = Printing.ps_to_string ps
    let bdry ps = mk (Ctx.check (Unchecked.ps_to_ctx (Unchecked.ps_bdry ps)))

    let source ps =
      Sub.check_to_ps (Ctx.of_ps ps) (Unchecked.ps_src ps) (bdry ps)

    let target ps =
      Sub.check_to_ps (Ctx.of_ps ps) (Unchecked.ps_tgt ps) (bdry ps)

    let is_equal ps1 ps2 = ps1 == ps2 || Equality.is_equal_ps ps1 ps2
  end

  and Core :
    (CoreSignature.S
      with type Ty.t = RTy.t
       and type Coh.t = RCoh.t
       and type Tm.t = RTm.t) = struct
    module PS = RPS
    module Ty = RTy
    module Tm = RTm
    module Coh = RCoh

    type ty = (Coh.t, Tm.t) pty
    type tm = (Coh.t, Tm.t) ptm
    type sub = (Coh.t, Tm.t) psub
    type sub_ps = (Coh.t, Tm.t) psub_ps
    type ctx = (Coh.t, Tm.t) pctx
    type constr = (Coh.t, Tm.t) pconstr
    type meta_ctx = (int * ty) list
    type value = (Coh.t, Tm.t) pvalue
    type decls = (value * string) list
  end

  and K :
    (KernelSignature.S
      with type Coh.t = RCoh.t
       and type Ty.t = RTy.t
       and type Tm.t = RTm.t) = struct
    exception InvalidPS

    let theory = Theory.theory

    module B : sig
      open Core

      module Ctx :
        Signature.CtxS
          with type checked_ty = Ty.t
           and type checked_tm = Tm.t
           and type checked_coh = Coh.t
           and type checked_ps = PS.t

      module Sub :
        Signature.SubS
          with type checked_tm = Tm.t
           and type checked_coh = Coh.t
           and type checked_ctx = Ctx.t
    end =
      Builder.Make (Core)

    module PS = RPS
    module Coh = RCoh
    module Ty = RTy
    module Tm = RTm
    module Ctx = B.Ctx
    module Sub = B.Sub

    type ty = Core.ty
    type tm = Core.tm
    type sub = Core.sub
    type sub_ps = Core.sub_ps
    type ctx = Core.ctx
    type constr = Core.constr
    type meta_ctx = Core.meta_ctx
    type value = (Coh.t, Tm.t) pvalue
    type decls = (value * string) list
  end

  include Syntax.Make (Core)
  include K

  let check check_fn name =
    let v = 2 in
    let fname = if !Settings.verbosity >= v then Lazy.force name else "" in
    Io.info ~v (lazy ("checking " ^ fname));
    try check_fn () with
    | NotEqual (s1, s2) ->
        Error.untypable
          (if !Settings.verbosity >= v then fname else Lazy.force name)
          (Printf.sprintf "%s and %s are not equal" s1 s2)
    | Builder.InvalidSubTarget (s, tgt) ->
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

let known_kernels : (theory, (module KernelExt.S)) Hashtbl.t = Hashtbl.create 7

let make theory =
  match Hashtbl.find_opt known_kernels theory with
  | Some k -> k
  | None ->
      let module K = Make (struct
        let theory = theory
      end) in
      let k = (module K : KernelExt.S) in
      Hashtbl.add known_kernels theory k;
      k
