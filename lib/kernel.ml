open Std
open Common
open Unchecked_types
open Unchecked

exception IsObj
exception IsInv
exception IsNotVar
exception IsCoh
exception InvalidSubTarget of string * string
exception MetaVariable

(** Operations on substitutions. *)
module rec Sub : sig
  type t

  val check : Ctx.t -> Unchecked_types(Coh)(Tm).sub -> Ctx.t -> t
  val check_to_ps : Ctx.t -> Unchecked_types(Coh)(Tm).sub_ps -> PS.t -> t
  val forget : t -> Unchecked_types(Coh)(Tm).sub
  val free_vars : t -> Var.t list
  val src : t -> Ctx.t
  val tgt : t -> Ctx.t
  val args_of_dim : int -> t -> Tm.t list
end = struct
  type t = {
    list : Tm.t list;
    src : Ctx.t;
    tgt : Ctx.t;
    unchecked : Unchecked_types(Coh)(Tm).sub;
  }

  let src s = s.src
  let tgt s = s.tgt

  open Unchecked (Coh) (Tm)
  module Unchecked = Make (Coh) (Tm)
  module Types = Unchecked_types (Coh) (Tm)

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
      InvalidSubTarget (Unchecked.sub_to_string_debug s, Ctx.to_string tgt)
    in
    let rec aux src s tgt =
      let expr s tgt =
        match (s, Ctx.value tgt) with
        | [], [] -> []
        | _ :: _, [] | [], _ :: _ -> raise sub_exn
        | (x1, _) :: _, (x2, _) :: _ when x1 <> x2 -> raise sub_exn
        | (_, (t, _)) :: s, (_, a) :: _ ->
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
          try List.map2 (fun (x, _) (t, e) -> (x, (t, e))) (Ctx.value tgt) s
          with Invalid_argument _ ->
            Error.fatal "uncaught wrong number of arguments"
        in
        let sub = check src s_assoc tgt in
        Hashtbl.add tbl (src, tgt_ps, s) sub;
        sub

  let forget s = s.unchecked

  let args_of_dim n s =
    let rec provide s tgt =
      match (s, tgt) with
      | [], [] -> []
      | tm :: s, (_, ty) :: tgt when Ty.dim ty == n -> tm :: provide s tgt
      | _ :: s, _ :: tgt -> provide s tgt
      | _, _ -> assert false
    in
    provide s.list (Ctx.value s.tgt)
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
  val extend : t -> expl:bool -> Var.t -> Unchecked_types(Coh)(Tm).ty -> t
  val forget : t -> Unchecked_types(Coh)(Tm).ctx
  val check : Unchecked_types(Coh)(Tm).ctx -> t
  val check_notin : t -> Var.t -> unit
  val check_equal : t -> t -> unit
  val check_walking_equiv : t -> unit
  val l_equiv_incl : t -> Unchecked_types(Coh)(Tm).sub
  val r_equiv_incl : t -> Unchecked_types(Coh)(Tm).sub
end = struct
  type t = { c : (Var.t * Ty.t) list; unchecked : Unchecked_types(Coh)(Tm).ctx }

  open Unchecked_types (Coh) (Tm)
  open Unchecked (Coh) (Tm)
  module Unchecked = Make (Coh) (Tm)

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
  let to_string ctx = Unchecked.ctx_to_string (forget ctx)

  let check_equal ctx1 ctx2 =
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

  let check_walking_equiv ctx =
    let check c =
      match c with
      | [] | [ _ ] -> assert false
      | (_, ty) :: ((x, _) :: _ as ctx) ->
          let x' = Ty.base_inv ty in
          let x' = Tm.to_var x' in
          Var.check_equal x x';
          let rec check_disk c =
            match c with
            | [] -> assert false
            | [ (_, ty) ] -> if not (Ty.is_obj ty) then assert false
            | (_, arr) :: (y, _) :: ((x, _) :: _ as ctx) ->
                let _, x', y' = Ty.retrieve_arrow arr in
                let x' = Tm.to_var x' in
                let y' = Tm.to_var y' in
                Var.check_equal x x';
                Var.check_equal y y';
                check_disk ctx
            | _ -> assert false
          in
          check_disk ctx
    in
    check ctx.c

  let inverse_ty ty =
    match ty with
    | Obj | Inv _ -> assert false
    | Arr (ty, u, v) -> Arr (ty, v, u)
    | Meta_ty _ -> assert false

  let l_equiv_incl ctx =
    let ctx = forget ctx in
    let sc = Unchecked.suspend_ctx ctx in
    match ctx with
    | (v, (Inv (a, u), _)) :: _ ->
        let src = Constr.comp (IS (LInv, Var v), inverse_ty a) (u, a) in
        let y = Constr.id (Constr.tgt 1 (u, a)) in
        let l =
          (IS (Lwit, Var v), true)
          :: (IS (Lunit, Var v), false)
          :: (fst y, false)
          :: Constr.characteristic_sub_ps src
        in
        List.map2 (fun (x, (_, b)) (t, _) -> (x, (t, b))) sc l
    | _ -> assert false

  let r_equiv_incl ctx =
    let ctx = forget ctx in
    let sc = Unchecked.suspend_ctx ctx in
    match ctx with
    | (v, (Inv (a, u), _)) :: _ ->
        let x = Constr.id (Constr.src 1 (u, a)) in
        let src = Constr.comp (u, a) (IS (RInv, Var v), inverse_ty a) in
        let l =
          (IS (Rwit, Var v), true)
          :: (IS (Runit, Var v), false)
          :: (fst x, false)
          :: Constr.characteristic_sub_ps src
        in
        List.map2 (fun (x, (_, b)) (t, _) -> (x, (t, b))) sc l
    | _ -> assert false
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

  open Unchecked (Coh) (Tm)
  module Unchecked = Make (Coh) (Tm)

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
  val is_full : t -> bool
  val is_obj : t -> bool
  val check_equal : t -> t -> unit
  val morphism : Tm.t -> Tm.t -> Ty.t
  val forget : t -> Unchecked_types(Coh)(Tm).ty
  val check : Ctx.t -> Unchecked_types(Coh)(Tm).ty -> t
  val apply_sub : t -> Sub.t -> t
  val retrieve_arrow : t -> t * Tm.t * Tm.t
  val under_type : t -> t
  val source : t -> Tm.t
  val target : t -> Tm.t
  val ctx : t -> Ctx.t
  val dim : t -> int
  val base_inv : t -> Tm.t
  val inv : Tm.t -> Ty.t
end = struct
  open Unchecked (Coh) (Tm)
  module Unchecked = Make (Coh) (Tm)
  module Types = Unchecked_types (Coh) (Tm)

  (** A type exepression. *)
  type expr = Obj | Arr of t * Tm.t * Tm.t | Inv of Tm.t

  and t = { c : Ctx.t; e : expr; unchecked : Types.ty }

  let tbl : (Ctx.t * Types.ty, Ty.t) Hashtbl.t = Hashtbl.create 7829
  let is_obj t = t.e = Obj

  let is_globular t =
    match t.e with Obj | Arr (_, _, _) -> true | Inv _ -> false

  let base_inv t = match t.e with Inv u -> u | _ -> assert false

  let retrieve_arrow ty =
    match ty.e with
    | Obj -> raise IsObj
    | Arr (a, u, v) -> (a, u, v)
    | Inv _ -> raise IsInv

  let under_type ty =
    match ty.e with
    | Obj -> raise IsObj
    | Arr (a, _, _) -> a
    | Inv _ -> raise IsInv

  let source ty =
    match ty.e with
    | Obj -> raise IsObj
    | Arr (_, u, _) -> u
    | Inv _ -> raise IsInv

  let target ty =
    match ty.e with
    | Obj -> raise IsObj
    | Arr (_, _, v) -> v
    | Inv _ -> raise IsInv

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
              assert (is_globular a);
              let u = Tm.check c ~ty:a u in
              let v = Tm.check c ~ty:a v in
              Arr (a, u, v)
          | Meta_ty _ -> raise MetaVariable
          | Inv (a, u) ->
              let a = Ty.check c a in
              let u = Tm.check c ~ty:a u in
              let _ = retrieve_arrow a in
              Inv u
        in
        let ty = { c; e; unchecked = t } in
        Hashtbl.add tbl (c, t) ty;
        ty

  (** Free variables of a type. *)
  let rec free_vars ty =
    match ty.e with
    | Obj -> []
    | Arr (t, u, v) ->
        List.unions [ free_vars t; Tm.free_vars u; Tm.free_vars v ]
    | Inv u -> Tm.free_vars u

  let is_full t = List.included (Ctx.domain t.c) (free_vars t)
  let forget t = t.unchecked
  let to_string ty = Unchecked.ty_to_string (forget ty)

  let inv t =
    match (Tm.typ t).e with
    | Obj | Inv _ -> assert false
    | Arr (_, _, _) ->
        let e = Inv t in
        let c = (Tm.typ t).c in
        { c; e; unchecked = Inv (Tm.ty t, Tm.forget t) }

  (** Test for equality. *)
  let check_equal ty1 ty2 =
    Ctx.check_equal ty1.c ty2.c;
    Unchecked.check_equal_ty (forget ty1) (forget ty2)

  let morphism t1 t2 =
    let a1 = Tm.typ t1 in
    let a2 = Tm.typ t2 in
    check_equal a1 a2;
    {
      c = a1.c;
      e = Arr (a1, t1, t2);
      unchecked = Arr (forget a1, Tm.forget t1, Tm.forget t2);
    }

  let apply_sub t s =
    Ctx.check_equal t.c (Sub.tgt s);
    check (Sub.src s) (Unchecked.ty_apply_sub (forget t) (Sub.forget s))

  let ctx t = t.c

  let rec dim t =
    match t.e with
    | Obj -> 0
    | Arr (a, _, _) -> 1 + dim a
    | Inv u -> dim (Tm.typ u)
end

(** Operations on terms. *)
and Tm : sig
  type t

  (* Data extraction *)
  val to_var : t -> Var.t
  val typ : t -> Ty.t
  val ty : t -> Unchecked_types(Coh)(Tm).ty
  val bdry : t -> t * t
  val ctx : t -> Unchecked_types(Coh)(Tm).ctx
  val forget : t -> Unchecked_types(Coh)(Tm).tm
  val constr : t -> Unchecked_types(Coh)(Tm).constr
  val name : t -> string option
  val full_name : t -> string option
  val func_data : t -> (Var.t * int) list list option
  val pp_data : t -> pp_data option
  val to_string : t -> string

  (* Variable uses *)
  val free_vars : t -> Var.t list
  val is_full : t -> bool

  (* Production of terms *)
  val of_coh : Coh.t -> t

  val check :
    Ctx.t -> ?ty:Ty.t -> ?name:pp_data -> Unchecked_types(Coh)(Tm).tm -> t

  val apply_sub : t -> Sub.t -> t
  val preimage : t -> Sub.t -> t
  val develop : t -> Unchecked_types(Coh)(Tm).tm

  val apply :
    (Unchecked_types(Coh)(Tm).ctx -> Unchecked_types(Coh)(Tm).ctx) ->
    (Unchecked_types(Coh)(Tm).tm -> Unchecked_types(Coh)(Tm).tm) ->
    (pp_data -> pp_data) ->
    t ->
    t * Unchecked_types(Coh)(Tm).sub
end = struct
  open Unchecked (Coh) (Tm)
  module Unchecked = Make (Coh) (Tm)
  module Types = Unchecked_types (Coh) (Tm)
  module Display_maps = Unchecked.Display_maps

  type expr =
    | Var of Var.t
    | Coh of Coh.t * Sub.t
    | App of Tm.t * Sub.t
    | IS of inv * Tm.t
    | Can of Tm.t * Tm.t list
    | Coind of Tm.t * Tm.t * Tm.t * Tm.t * Tm.t * Tm.t * Tm.t
    | Rec of Tm.t * Tm.t * Tm.t * Tm.t * Tm.t * Tm.t * Tm.t

  and t = {
    ty : Ty.t;
    e : expr;
    unchecked : Types.tm;
    mutable developped : Types.tm option;
    name : pp_data option;
  }

  let typ t = t.ty
  let ty t = Ty.forget t.ty
  let tbl : (Ctx.t * Types.tm, Tm.t) Hashtbl.t = Hashtbl.create 7829

  let to_var tm =
    match tm.e with
    | Var v -> v
    | Coh _ | App _ -> raise IsCoh
    | _ -> raise IsNotVar

  let rec free_vars tm =
    let fvty = Ty.free_vars tm.ty in
    match tm.e with
    | Var x -> x :: fvty
    | Coh (_, sub) | App (_, sub) -> Sub.free_vars sub
    | IS (_, t) -> free_vars t
    | Can (t, _) -> free_vars t
    | Coind (t, _, _, _, _, _, _) -> free_vars t
    | Rec (t, _, _, _, _, _, _) -> free_vars t

  let is_full tm = List.included (Ctx.domain (Ty.ctx tm.ty)) (free_vars tm)
  let forget tm = tm.unchecked
  let constr tm = (forget tm, ty tm)

  let lunit_ty c tm linv =
    let t = constr tm in
    let linv = constr linv in
    let y = constr (Ty.target tm.ty) in
    let ty = Constr.arr (Constr.comp linv t) (Constr.id y) in
    Ty.check c ty

  let runit_ty c tm rinv =
    let t = constr tm in
    let rinv = constr rinv in
    let x = constr (Ty.source tm.ty) in
    let ty = Constr.arr (Constr.comp t rinv) (Constr.id x) in
    Ty.check c ty

  let rec args_max_coh c tm =
    let tm = Tm.develop tm in
    let tm = check c tm in
    match tm.e with
    | Var _ | App _ | Coind _ | Rec _ | Can _ | IS _ -> assert false
    | Coh (c, sub) ->
        let n = Coh.dim c in
        Sub.args_of_dim n sub

  and check c ?ty ?name t =
    Io.info ~v:5
      (lazy
        (Printf.sprintf "building\n    kernel term %s in context %s"
           (Unchecked.tm_to_string t) (Ctx.to_string c)));
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
              tm
          | IS (inv, tm) ->
              let tm_checked = check c tm in
              let base_inv = Ty.base_inv tm_checked.ty in
              let _, x, y = Ty.retrieve_arrow base_inv.ty in
              let e = IS (inv, tm_checked) in
              let ty =
                match inv with
                | LInv -> Ty.morphism y x
                | RInv -> Ty.morphism y x
                | Lunit ->
                    let linv = check c (IS (LInv, tm)) in
                    lunit_ty c base_inv linv
                | Runit ->
                    let rinv = check c (IS (RInv, tm)) in
                    runit_ty c base_inv rinv
                | Lwit ->
                    let linv = check c (IS (LInv, tm)) in
                    let ty = lunit_ty c base_inv linv in
                    Ty.check c (Inv (Ty.forget ty, IS (Lunit, tm)))
                | Rwit ->
                    let rinv = check c (IS (RInv, tm)) in
                    let ty = runit_ty c base_inv rinv in
                    Ty.check c (Inv (Ty.forget ty, IS (Runit, tm)))
              in
              let tm = { ty; e; unchecked = t; developped = Some t; name } in
              Hashtbl.add tbl (c, t) tm;
              tm
          | Can (tm, tms) ->
              let tm = check c tm in
              let args = args_max_coh c tm in
              let rec check_next args invs =
                match (args, invs) with
                | t :: args, e :: invs ->
                    let e = Tm.check c ~ty:(Ty.inv t) e in
                    let invs = check_next args invs in
                    e :: invs
                | [], [] -> []
                | _ ->
                    Error.fatal
                      "wrong number of arguments in canonical structure"
              in
              let tms = check_next args tms in
              let e = Can (tm, tms) in
              let ty = Ty.inv tm in
              let tm = { ty; e; unchecked = t; developped = Some t; name } in
              Hashtbl.add tbl (c, t) tm;
              tm
          | Coind (t0, t1, t2, t3, t4, t5, t6) ->
              let t0_checked = check c t0 in
              let _, x, y = Ty.retrieve_arrow t0_checked.ty in
              let t1_checked = check c ~ty:(Ty.morphism y x) t1 in
              let t2_checked = check c ~ty:(Ty.morphism y x) t2 in
              let t3_checked =
                check c ~ty:(lunit_ty c t0_checked t1_checked) t3
              in
              let t4_checked =
                check c ~ty:(runit_ty c t0_checked t2_checked) t4
              in
              let t5_checked = check c ~ty:(Ty.inv t3_checked) t5 in
              let t6_checked = check c ~ty:(Ty.inv t4_checked) t6 in
              let e =
                Coind
                  ( t0_checked,
                    t1_checked,
                    t2_checked,
                    t3_checked,
                    t4_checked,
                    t5_checked,
                    t6_checked )
              in
              let ty = Ty.inv t0_checked in
              let tm = { ty; e; unchecked = t; developped = Some t; name } in
              Hashtbl.add tbl (c, t) tm;
              tm
          | Rec (t0, t1, t2, t3, t4, (v0, v1, t5), (v2, v3, t6)) ->
              Ctx.check_walking_equiv c;
              let t0_checked = check c t0 in
              let _, x, y = Ty.retrieve_arrow t0_checked.ty in
              let t1_checked = check c ~ty:(Ty.morphism y x) t1 in
              let t2_checked = check c ~ty:(Ty.morphism y x) t2 in
              let t3_checked =
                check c ~ty:(lunit_ty c t0_checked t1_checked) t3
              in
              let t4_checked =
                check c ~ty:(runit_ty c t0_checked t1_checked) t4
              in
              let ih v w =
                Ctx.extend
                  (Ctx.extend c ~expl:true v
                     (Unchecked.ty_apply_sub
                        (Unchecked.suspend_ty (Ty.forget (Ty.inv t0_checked)))
                        (Ctx.l_equiv_incl c)))
                  ~expl:true w
                  (Unchecked.ty_apply_sub
                     (Unchecked.suspend_ty (Ty.forget (Ty.inv t0_checked)))
                     (Ctx.r_equiv_incl c))
              in
              let weaken v w =
                Sub.check (ih v w) (Unchecked.identity (Ctx.forget c)) c
              in
              let ty5 = Ty.apply_sub (Ty.inv t3_checked) (weaken v0 v1) in
              let t5_checked = check (ih v0 v1) ~ty:ty5 t5 in
              let ty6 = Ty.apply_sub (Ty.inv t4_checked) (weaken v2 v3) in
              let t6_checked = check (ih v2 v3) ~ty:ty6 t6 in
              let e =
                Rec
                  ( t0_checked,
                    t1_checked,
                    t2_checked,
                    t3_checked,
                    t4_checked,
                    t5_checked,
                    t6_checked )
              in
              let ty = Ty.inv t0_checked in
              let tm = { ty; e; unchecked = t; developped = Some t; name } in
              Hashtbl.add tbl (c, t) tm;
              tm)
    in
    match ty with
    | None -> tm
    | Some ty ->
        Ty.check_equal ty tm.ty;
        tm

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
          | _ -> tm.unchecked
        in
        tm.developped <- Some dev;
        dev

  let apply_sub t sub =
    Ctx.check_equal (Sub.tgt sub) (Ty.ctx t.ty);
    let c = Sub.src sub in
    let ty = Ty.apply_sub t.ty sub in
    let t = Unchecked.tm_apply_sub (forget t) (Sub.forget sub) in
    check c ~ty t

  let preimage t sub =
    Ctx.check_equal (Sub.src sub) (Ty.ctx t.ty);
    let c = Sub.tgt sub in
    let t = Unchecked.tm_sub_preimage (forget t) (Sub.forget sub) in
    check c t

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
    (check c ?name newexp, db_sub)

  let bdry t = (Ty.source (typ t), Ty.target (typ t))
  let ctx t = Ctx.forget (Ty.ctx (typ t))
  let name t = Option.map Unchecked.pp_data_to_string t.name
  let full_name t = Option.map Unchecked.full_name t.name
  let func_data t = Option.map (fun (_, _, f) -> f) t.name
  let pp_data t = t.name

  let to_string t =
    match full_name t with
    | Some name -> name
    | None -> Unchecked.tm_to_string (forget t)

  let of_coh coh =
    let ps, _, pp_data = Coh.forget coh in
    let id = Unchecked.identity_ps ps in
    let ctx = Unchecked.ps_to_ctx ps in
    check (Ctx.check ctx) ~name:pp_data (Coh (coh, id))
end

(** A coherence. *)
and Coh : sig
  type t

  val ps : t -> PS.t
  val ty : t -> Ty.t
  val src : t -> Unchecked_types(Coh)(Tm).tm
  val tgt : t -> Unchecked_types(Coh)(Tm).tm
  val check : ps -> Unchecked_types(Coh)(Tm).ty -> pp_data -> t

  val check_noninv :
    ps ->
    Unchecked_types(Coh)(Tm).tm ->
    Unchecked_types(Coh)(Tm).tm ->
    pp_data ->
    t

  val check_inv :
    ps ->
    Unchecked_types(Coh)(Tm).tm ->
    Unchecked_types(Coh)(Tm).tm ->
    pp_data ->
    t

  val to_string : t -> string
  val is_inv : t -> bool

  val noninv_srctgt :
    t ->
    Unchecked_types(Coh)(Tm).tm
    * Unchecked_types(Coh)(Tm).tm
    * Unchecked_types(Coh)(Tm).ty

  val forget : t -> ps * Unchecked_types(Coh)(Tm).ty * pp_data
  val func_data : t -> (Var.t * int) list list
  val check_equal : t -> t -> unit
  val dim : t -> int

  val apply_ps :
    (ps -> ps) ->
    (Unchecked_types(Coh)(Tm).ty -> Unchecked_types(Coh)(Tm).ty) ->
    (pp_data -> pp_data) ->
    t ->
    t

  val apply :
    (Unchecked_types(Coh)(Tm).ctx -> Unchecked_types(Coh)(Tm).ctx) ->
    (Unchecked_types(Coh)(Tm).ty -> Unchecked_types(Coh)(Tm).ty) ->
    (pp_data -> pp_data) ->
    t ->
    t * Unchecked_types(Coh)(Tm).sub
end = struct
  type cohInv = { ps : PS.t; ty : Ty.t }
  type cohNonInv = { ps : PS.t; src : Tm.t; tgt : Tm.t; total_ty : Ty.t }
  type t = Inv of cohInv * pp_data | NonInv of cohNonInv * pp_data

  module Types = Unchecked_types (Coh) (Tm)

  let tbl : (ps * Types.ty, Coh.t) Hashtbl.t = Hashtbl.create 7829

  let tbl_inv : (ps * Types.tm * Types.tm, Coh.t) Hashtbl.t =
    Hashtbl.create 7829

  let tbl_noninv : (ps * Types.tm * Types.tm, Coh.t) Hashtbl.t =
    Hashtbl.create 7829

  exception NotAlgebraic

  open Unchecked (Coh) (Tm)
  module Unchecked = Make (Coh) (Tm)
  module Display_maps = Unchecked.Display_maps

  let ps = function Inv (data, _) -> data.ps | NonInv (data, _) -> data.ps

  let ty = function
    | Inv (data, _) -> data.ty
    | NonInv (data, _) -> data.total_ty

  let src c = Tm.forget (Ty.source (ty c))
  let tgt c = Tm.forget (Ty.target (ty c))
  let is_inv = function Inv (_, _) -> true | NonInv (_, _) -> false

  let algebraic ps ty name =
    if Ty.is_full ty then (
      Ctx.check_equal (PS.to_ctx ps) (Ty.ctx ty);
      Inv ({ ps; ty }, name))
    else
      let _, src, tgt =
        try Ty.retrieve_arrow ty with IsObj -> raise NotAlgebraic
      in
      try
        let src_inclusion = PS.source ps in
        let src = Tm.preimage src src_inclusion in
        if not (Tm.is_full src) then raise NotAlgebraic
        else
          let tgt_inclusion = PS.target ps in
          let tgt = Tm.preimage tgt tgt_inclusion in
          if not (Tm.is_full tgt) then raise NotAlgebraic
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
        if not (Tm.is_full src) then raise NotAlgebraic
        else
          let tgt = Tm.check cbdry tgt_unchkd in
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
        let src = Tm.check ctx src_unchkd in
        let tgt = Tm.check ctx tgt_unchkd in
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

  let to_string c =
    let ps, ty, pp_data = data c in
    if not !Settings.unroll_coherences then Unchecked.pp_data_to_string pp_data
    else Printf.sprintf "Coh(%s,%s)" (PS.to_string ps) (Ty.to_string ty)

  let noninv_srctgt c =
    match c with
    | Inv (_, _) -> Error.fatal "non-invertible data of an invertible coh"
    | NonInv (d, _) ->
        (Tm.forget d.src, Tm.forget d.tgt, Ty.forget (Tm.typ d.src))

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

and Constr : sig
  val arr :
    Unchecked_types(Coh)(Tm).constr ->
    Unchecked_types(Coh)(Tm).constr ->
    Unchecked_types(Coh)(Tm).ty

  val comp :
    Unchecked_types(Coh)(Tm).constr ->
    Unchecked_types(Coh)(Tm).constr ->
    Unchecked_types(Coh)(Tm).constr

  val id : Unchecked_types(Coh)(Tm).constr -> Unchecked_types(Coh)(Tm).constr

  val src :
    int -> Unchecked_types(Coh)(Tm).constr -> Unchecked_types(Coh)(Tm).constr

  val tgt :
    int -> Unchecked_types(Coh)(Tm).constr -> Unchecked_types(Coh)(Tm).constr

  val characteristic_sub_ps :
    Unchecked_types(Coh)(Tm).constr -> Unchecked_types(Coh)(Tm).sub_ps
end = struct
  open Unchecked_types (Coh) (Tm)
  open Unchecked (Coh) (Tm)
  module Unchecked = Make (Coh) (Tm)

  let to_tm (tm, _) = tm
  let characteristic_sub_ps (tm, ty) = (tm, true) :: Unchecked.ty_to_sub_ps ty
  let dim (_, ty) = Unchecked.dim_ty ty
  let arr (tm1, ty1) (tm2, _) = Arr (ty1, tm1, tm2)

  let rec bdry n (t, ty) =
    match (n, ty) with
    | 0, _ -> ((t, ty), (t, ty))
    | 1, Arr (b, s, t) -> ((s, b), (t, b))
    | _, Arr (b, s, _) -> bdry (n - 1) (s, b)
    | _, _ -> assert false

  let src n t = fst (bdry n t)
  let tgt n t = snd (bdry n t)
  let rec iter n f base = if n <= 0 then base else f (iter (n - 1) f base)

  let suspend_coh i coh =
    iter i
      (Coh.apply_ps Unchecked.suspend_ps Unchecked.suspend_ty
         Unchecked.suspend_pp_data)
      coh

  let id_coh =
    Coh.check (Br []) (Arr (Obj, Var (Db 0), Var (Db 0))) ("builtin_id", 0, [])

  let tdb i = Var (Var.Db i)
  let tree i = Br (List.init i (fun _ -> Br []))
  let x i = if i = 0 then (tdb 0, Obj) else (tdb ((2 * i) - 1), Obj)

  let comp_n i =
    let ps = tree i in
    let pp_data = (Printf.sprintf "builtin_comp%i" i, 0, []) in
    Coh.check_noninv ps (fst (x 0)) (fst (x 0)) pp_data

  let comp_n constrs =
    let constrs_rev = List.rev constrs in
    let first = function [] -> assert false | h :: _ -> h in
    let rec glue_subs = function
      | [ c ] -> characteristic_sub_ps c
      | c :: constrs ->
          (to_tm c, true) :: (to_tm (tgt 1 c), false) :: glue_subs constrs
      | [] -> assert false
    in
    let l = List.length constrs in
    let c = first constrs in
    let d = dim c in
    ( Coh (suspend_coh (d - 1) (comp_n l), glue_subs constrs_rev),
      arr (src 1 c) (tgt 1 (first constrs_rev)) )

  let comp c1 c2 = comp_n [ c1; c2 ]

  let id constr =
    let d = dim constr in
    (Coh (suspend_coh d id_coh, characteristic_sub_ps constr), arr constr constr)
end

module U = Unchecked (Coh) (Tm)
module Unchecked = U.Make (Coh) (Tm)
module Display_maps = Unchecked.Display_maps

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

let check_term ctx ?ty ?name t =
  let ty = Option.map (check_type ctx) ty in
  let tm = lazy ("term: " ^ Unchecked.tm_to_string t) in
  check (fun () -> Tm.check ctx ?ty ?name t) tm

let check_constr ?name ctx constr =
  let ctx = Ctx.check ctx in
  let t, ty = constr in
  let ty = if !Settings.debug then None else Some ty in
  check_term ctx ?ty ?name t

let check_coh ps ty pp_data =
  let c = lazy ("coherence: " ^ Unchecked.pp_data_to_string pp_data) in
  check (fun () -> Coh.check ps ty pp_data) c

let check_sub src s tgt = ignore @@ Sub.check (Ctx.check src) s (Ctx.check tgt)
