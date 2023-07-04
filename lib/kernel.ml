open Std
open Common

(** Operations on substitutions. *)
module rec Sub : sig
  type t
  val check_to_ps : Ctx.t -> sub_ps -> PS.t -> t
  val forget : t -> sub
  val free_vars : t -> Var.t list
  val src : t -> Ctx.t
  val tgt : t -> Ctx.t
end
  = struct
  type t = {list : Tm.t list; src : Ctx.t; tgt : Ctx.t; unchecked : sub}

  let src s = s.src
  let tgt s = s.tgt

  let free_vars s =
    List.concat (List.map Tm.free_vars s.list)

  let rec check src s tgt =
    Io.info ~v:3 "building kernel substitution \
                  : source = %s; substitution = %s; target = %s"
      (Ctx.to_string src)
      (Unchecked.sub_to_string s)
      (Ctx.to_string tgt);
    let expr (s : sub) tgt =
      match s, Ctx.value tgt with
      | [], [] -> []
      | (_::_,[] |[],_::_) -> raise Error.NotValid
      | (x1,_)::_, (x2,_)::_ when x1 <> x2 -> raise Error.NotValid
      | (_,t)::s, (_,a)::_ ->
	 let sub = check src s (Ctx.tail tgt) in
         let t = Tm.check src t in
	 Ty.check_equal (Tm.typ t) (Ty.apply a sub);
	 t::sub.list
    in
    {list = expr s tgt; src; tgt; unchecked = s}

  let check_to_ps src s tgt =
    let tgt = PS.to_ctx tgt in
    let s = List.map2 (fun (x,_) t -> (x,t)) (Ctx.value tgt) s in
    check src s tgt

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
  val extend : t -> expl:bool -> Var.t -> ty -> t
  val forget : t -> ctx
  val check : ctx -> t
  val check_notin : t -> Var.t -> unit
  val check_equal : t -> t -> unit
end
  =
struct
  type t = {c : (Var.t * Ty.t) list; unchecked : ctx}

  let tail ctx =
    match ctx.c, ctx.unchecked with
    | [],(_::_|[]) -> assert false
    | _::_,[] -> assert false
    | _::c,_::unchecked -> {c;unchecked}

  let ty_var ctx x =
    try List.assoc x ctx.c
    with Not_found -> raise (Error.UnknownId (Var.to_string x))

  let empty () = {c  = []; unchecked = []}

  let domain ctx = List.map fst ctx.c
  let value ctx = ctx.c
  let forget c = c.unchecked
  let to_string ctx =
    Unchecked.ctx_to_string (forget ctx)
  let check_equal ctx1 ctx2 =
    Unchecked.check_equal_ctx (forget ctx1) (forget ctx2)

  let check_notin ctx x =
    try
      ignore (List.assoc x ctx.c);
      raise (Error.DoubleDef (Var.to_string x))
    with Not_found -> ()

  let extend ctx ~expl x t =
    let ty = Ty.check ctx t in
    Ctx.check_notin ctx x;
    {c = (x,ty)::(Ctx.value ctx); unchecked = (x, (t,expl))::(Ctx.forget ctx)}

  let check c =
    List.fold_right
      (fun (x,(t,expl)) c -> Ctx.extend ~expl c x t )
      c
      (Ctx.empty ())
end

(** Operations on pasting schemes. *)
and PS : sig
  type t
  val mk : Ctx.t -> t
  val domain : t -> Var.t list
  val to_ctx : t -> Ctx.t
  val dim : t -> int
  val source : int -> t -> Var.t list
  val target : int -> t -> Var.t list
  val forget : t -> ps
end
  =
struct
  exception Invalid

  (** A pasting scheme. *)
  type oldrep =
    | PNil of (Var.t * Ty.t)
    | PCons of oldrep * (Var.t * Ty.t) * (Var.t * Ty.t)
    | PDrop of oldrep

  type newt = { tree : ps; ctx : Ctx.t}

  type t = {oldrep : oldrep; newrep : newt}

  (** Create a context from a pasting scheme. *)
  (* TODO:fix level of explicitness here *)
  let old_rep_to_ctx ps =
    let rec list ps =
      match ps with
      |PDrop ps -> list ps
      |PCons (ps,(x1,t1),(x2,t2)) ->
        (x2,(Ty.forget t2, true))::(x1,(Ty.forget t1, true))::(list ps)
      |PNil (x,t) -> [(x,(Ty.forget t, true))]
    in Ctx.check (list ps)

  (** Domain of definition. *)
  let domain ps = Ctx.domain ps.newrep.ctx

  (** Dangling variable. *)
  let rec marker (ps : oldrep) =
    match ps with
    | PNil (x,t) -> x,t
    | PCons (_,_,f) -> f
    | PDrop ps ->
       let _,tf = marker ps in
       match (Ty.expr tf) with
       | Ty.Arr (_,_,v) ->
          let y =
            match Tm.expr v with
            | Tm.Var y -> y
            | Tm.Coh _ -> raise Invalid
          in
          let t =
            let rec aux = function
              | PNil (x,t) -> assert (x = y); t
              | PCons (ps,(y',ty),(f,tf)) ->
                 if y' = y then ty
                 else if f = y then tf
                 else aux ps
              | PDrop ps -> aux ps
            in
            aux ps
          in
          y,t
       | _ -> raise Invalid

  (** Create a pasting scheme from a context. *)
  let make_old (l : Ctx.t)  =
    let rec close ps tx =
      match Ty.expr tx with
      | Obj -> ps
      | Arr (tx,_,_) -> close (PDrop ps) tx
    in
    let build l =
      let x0,ty,l =
        match l with
        | (x,ty)::l when Ty.is_obj ty -> x,ty,l
        | _ -> raise Invalid
      in
      let rec aux ps = function
        | ((y,ty)::(f,tf)::l) as l1 ->
           begin
             match Ty.expr tf with
             | Arr (_,u,v) ->
                let fx,fy =
                  match Tm.expr u,Tm.expr v with
                  | Var fx, Var fy -> fx, fy
                  | Var _, Coh _ | Coh _, Var _ | Coh _, Coh _ -> raise Invalid
                in
                if (y <> fy) then raise Invalid;
                let x,_ = marker ps in
                if x = fx then
                  let varps = Ctx.domain (old_rep_to_ctx ps) in
                  if (List.mem f varps) then
                    raise (Error.DoubledVar (Var.to_string f));
                  if (List.mem y varps) then
                    raise (Error.DoubledVar (Var.to_string y));
                  let ps = PCons (ps,(y,ty),(f,tf)) in
                  aux ps l
                  else
                  aux (PDrop ps) l1
             | _ -> raise Invalid
           end
        | [_,_] -> raise Invalid
        | [] ->
	   let _,tx = marker ps in close ps tx
      in
      aux (PNil (x0,ty)) l
    in build (List.rev (Ctx.value l))

  (* assumes that all ps are completed with enough PDrop in the end *)
  let make_tree ps =
    let rec find_previous ps list =
      match ps with
      | PNil x -> (Br list, PNil x)
      | PCons (ps,_,_) -> (Br list, ps)
      | PDrop _ as ps ->
         let p,ps = build_till_previous ps in
         Br p, ps
    and build_till_previous ps =
      match ps with
      | PNil x -> [], PNil x
      | PCons (ps,_,_) -> [], ps
      | PDrop ps ->
         let p,ps = find_previous ps [] in
         let prev,ps = build_till_previous ps in
                 p::prev, ps
    in
    Br (fst (build_till_previous ps))

  let mk (l : Ctx.t) =
    let oldrep = make_old l in
    {oldrep; newrep = {tree = make_tree oldrep; ctx = l}}

  let forget ps = ps.newrep.tree

  (** Create a context from a pasting scheme. *)
  let to_ctx ps =
    ps.newrep.ctx

  (** Height of a pasting scheme. *)
  let rec height_old = function
    | PNil _ -> 0
    | PCons (ps,_,_) -> height_old ps + 1
    | PDrop ps -> height_old ps - 1

  (** Dimension of a pasting scheme. *)
  let rec dim_old = function
    | PNil _ -> 0
    | PCons (ps,_,_) -> max (dim_old ps) (height_old ps + 1)
    | PDrop ps -> dim_old ps

  (* let height ps = height_old ps.oldrep *)
  let dim ps = dim_old ps.oldrep

  (** Source of a pasting scheme. *)
  let source_old i ps =
    assert (i >= 0);
    let rec aux = function
      | PNil (x,_) -> [x]
      | PCons (ps,_,_) when height_old ps >= i -> aux ps
      | PCons (ps,(y,_),(f,_)) -> f :: y :: (aux ps)
      | PDrop ps when height_old ps > i -> aux ps
      | PDrop ps -> (aux ps)
    in
    aux ps

  let source i ps = source_old i ps.oldrep

  (** Target of a pasting scheme. *)
  let target_old i ps =
    assert (i >= 0);
    let replace g = function
      | [] -> assert false
      | _::l -> g::l
    in
    let rec aux = function
      | PNil (x,_) -> [x]
      | PCons (ps,_,_) when height_old ps > i -> aux ps
      | PCons (ps,(y,_),_) when height_old ps = i -> replace y (aux ps)
      | PCons (ps,(y,_),(f,_)) -> f :: y :: (aux ps)
      | PDrop ps when height_old ps > i -> aux ps
      | PDrop ps -> aux ps
    in
    aux ps

  let target i ps = target_old i ps.oldrep
end
and Ty : sig
  type expr =
    private
    | Obj
    | Arr of t * Tm.t * Tm.t
  and t
  val free_vars : t -> Var.t list
  val is_obj : t -> bool
  val check_equal : t -> t -> unit
  val forget : t -> ty
  val check : Ctx.t -> ty -> t
  val apply : t -> Sub.t -> t
  val expr : t -> expr
end
  =
struct
  (** A type exepression. *)
  type expr =
    | Obj
    | Arr of t * Tm.t * Tm.t
  and t = {c : Ctx.t; e : expr; unchecked : ty}

  let expr t = t.e

  let is_obj t = (t.e = Obj)

  let rec check c t =
    Io.info ~v:3 "building kernel type %s in context %s"
    (Unchecked.ty_to_string t) (Ctx.to_string c);
    let e =
      match t with
      | Obj -> Obj
      | Arr(a,u,v) ->
         let a = check c a in
         let u = Tm.check c u in
         let v = Tm.check c v in
         Arr(a,u,v)
      | Meta_ty _ -> raise Error.MetaVariable
  in {c; e; unchecked = t}

  (** Free variables of a type. *)
  let rec free_vars ty =
    match ty.e with
    | Obj -> []
    | Arr (t,u,v) -> List.unions [free_vars t; Tm.free_vars u; Tm.free_vars v]

  let forget t = t.unchecked

  let _to_string ty =
    Unchecked.ty_to_string (forget ty)

  (** Test for equality. *)
  let check_equal ty1 ty2 =
    Ctx.check_equal ty1.c ty2.c;
    Unchecked.check_equal_ty (forget ty1) (forget ty2)

  let apply t s =
    Ctx.check_equal t.c (Sub.tgt s);
    check (Sub.src s) (Unchecked.ty_apply_sub (forget t) (Sub.forget s))
end

(** Operations on terms. *)
and Tm : sig
  type expr =
    private
    | Var of Var.t (** a context variable *)
    | Coh of Coh.t * Sub.t
  type t
  val typ : t -> Ty.t
  val free_vars : t -> Var.t list
  val check : Ctx.t -> ?ty : ty -> tm -> t
  val expr : t -> expr
end
  =
struct
  type expr =
    | Var of Var.t (** a context variable *)
    | Coh of Coh.t * Sub.t
  and t = {ty : Ty.t; e : expr; unchecked : tm}

  let typ t = t.ty
  let expr t = t.e

  let free_vars tm =
    match tm.e with
    | Var x -> [x]
    | Coh (_,sub) -> Sub.free_vars sub

  let forget tm = tm.unchecked
  let _to_string tm = Unchecked.tm_to_string (forget tm)

  let check c ?ty t =
    Io.info ~v:3 "building kernel term %s in context %s"
      (Unchecked.tm_to_string t)
      (Ctx.to_string c);
    let tm =
      match t with
      | Common.Var x ->
         let e, ty  = Var x, Ty.check c (Ty.forget (Ctx.ty_var c x)) in
         ({ty; e; unchecked = t})
      | Meta_tm _ -> raise Error.MetaVariable
      | Common.Coh (ps,ty,s) ->
         let coh = Coh.check ps ty [] in
         let sub = Sub.check_to_ps c s (Coh.ps coh) in
         let e, ty = Coh(coh,sub), Ty.apply (Coh.ty coh) sub in
         {ty; e; unchecked = t}
    in match ty with
       | None -> tm
       | Some ty ->
          let ty = Ty.check c ty in
          Ty.check_equal ty tm.ty; tm
end

(** A coherence. *)
and Coh : sig
  type t
  val ps : t -> PS.t
  val ty : t -> Ty.t
  val check : ps -> ty -> (Var.t * int) list -> t
end
=
struct
  type t = PS.t * Ty.t * (Var.t * int) list

  let ps (ps,_,_) = ps
  let ty (_,t,_) = t

  let algebraic ps t l =
    if List.included (PS.domain ps) (Ty.free_vars t)
    then (ps,t,l)
    else
      let a,f,g = match Ty.expr t with
        | Arr(a,f,g) -> (a,f,g)
        | _ -> raise Error.NotAlgebraic
      in
      let i = PS.dim ps in
      let pss, pst = PS.source (i-1) ps, PS.target (i-1) ps in
      let fvf = List.union (Tm.free_vars f) (Ty.free_vars a) in
      let fvg = List.union (Tm.free_vars g) (Ty.free_vars a) in
      if (List.set_equal pss fvf && List.set_equal pst fvg)
      then (ps,t,l)
      else raise Error.NotAlgebraic

  let check ps t names =
    Io.info ~v:3 "checking coherence (%s,%s)"
      (Unchecked.ps_to_string ps)
      (Unchecked.ty_to_string t);
    let cps = Ctx.check (Unchecked.ps_to_ctx ps) in
    let ps = PS.mk cps in
    let t = Ty.check cps t in
    algebraic ps t names
end
