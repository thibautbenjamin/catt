open Std

exception IsObj
exception IsCoh
exception InvalidSubTarget of string * string
exception NotEqual of string * string
exception DoubledVar of string
exception MetaVariable

module Var = struct
  type t =
    | Name of string
    | New of int
    | Db of int (* storing de Bruijn levels for coherences *)

  let to_string v =
    match v with
    | Name s -> s
    | New i -> "_" ^ string_of_int i
    | Db i -> "." ^ string_of_int i

  let make_var s = Name s

  let check_equal v1 v2 =
    match v1, v2 with
    | Name s1, Name s2 ->
      if not (String.equal s1 s2) then raise (NotEqual(s1,s2)) else ()
    | New i, New j ->
      if  i != j then raise (NotEqual(to_string v1, to_string v2)) else ()
    | Db i, Db j -> if
      i != j then raise (NotEqual(to_string v1, to_string v2)) else ()
    | Name _, New _ | Name _, Db _
    | New _ , Name _ | New _, Db _
    | Db _, Name _| Db _, New _
      -> raise (NotEqual(to_string v1, to_string v2))

  let increase_lv v i m =
    match v with
    | Db j -> if  j == 0 then Db (i) else Db (j + m)
    | Name _ | New _ -> Error.fatal "expecting a de-bruijn level"

  let suspend = function
    | Db i -> Db (i+2)
    | Name _ | New _ as v -> v
end

(** Operations on substitutions. *)
module rec Sub : sig
  type t
  val check_to_ps : Ctx.t -> Unchecked_types.sub_ps -> PS.t -> t
  val forget : t -> Unchecked_types.sub
  val free_vars : t -> Var.t list
  val src : t -> Ctx.t
  val tgt : t -> Ctx.t
end
= struct
  type t = {list : Tm.t list;
            src : Ctx.t;
            tgt : Ctx.t;
            unchecked : Unchecked_types.sub}

  let src s = s.src
  let tgt s = s.tgt

  let free_vars s =
    List.concat (List.map Tm.free_vars s.list)

  let check src s tgt =
    Io.info ~v:3
      (lazy
        (Printf.sprintf
           "building kernel substitution \
            : source = %s; substitution = %s; target = %s"
           (Ctx.to_string src)
           (Unchecked.sub_to_string s)
           (Ctx.to_string tgt)));
    let sub_exn = InvalidSubTarget(Unchecked.sub_to_string s, Ctx.to_string tgt) in
    let rec aux src s tgt =
      let expr s tgt =
        match s, Ctx.value tgt with
        | [], [] -> []
        | (_::_,[] |[],_::_) -> raise sub_exn
        | (x1,_)::_, (x2,_)::_ when x1 <> x2 -> raise sub_exn
        | (_,t)::s, (_,a)::_ ->
	  let sub = aux src s (Ctx.tail tgt) in
          let t = Tm.check src t in
          Ty.check_equal (Tm.typ t) (Ty.apply a sub);
          t::sub.list
      in
      {list = expr s tgt; src; tgt; unchecked = s}
    in
    aux src s tgt

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
  val extend : t -> expl:bool -> Var.t -> Unchecked_types.ty -> t
  val forget : t -> Unchecked_types.ctx
  val check : Unchecked_types.ctx -> t
  val check_notin : t -> Var.t -> unit
  val check_equal : t -> t -> unit
end = struct
  type t = {c : (Var.t * Ty.t) list;
            unchecked : Unchecked_types.ctx}

  let tail ctx =
    match ctx.c, ctx.unchecked with
    | [],(_::_|[]) -> Error.fatal "computing tail of an empty context"
    | _::_,[] -> Error.fatal "safe and unchecked context out of sync"
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
      raise (DoubledVar (Var.to_string x))
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
  val to_string : t -> string
  val mk : Ctx.t -> t
  val domain : t -> Var.t list
  val to_ctx : t -> Ctx.t
  val dim : t -> int
  val source : int -> t -> Var.t list
  val target : int -> t -> Var.t list
  val forget : t -> Unchecked_types.ps
end
=
struct
  exception Invalid

  (** A pasting scheme. *)
  type oldrep =
    | PNil of (Var.t * Ty.t)
    | PCons of oldrep * (Var.t * Ty.t) * (Var.t * Ty.t)
    | PDrop of oldrep

  type newt = { tree : Unchecked_types.ps; ctx : Ctx.t}

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
      let v =  try Ty.target tf  with IsObj -> raise Invalid in
      let y = try Tm.to_var v with IsCoh -> raise Invalid in
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

  (** Create a pasting scheme from a context. *)
  let make_old (l : Ctx.t)  =
    let rec close ps tx =
      if Ty.is_obj tx then ps
      else
        let tx = Ty.under_type tx in
        close (PDrop ps) tx
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
            let _,u,v =
              try Ty.retrieve_arrow tf with IsObj -> raise Invalid
            in
            let fx,fy =
              try Tm.to_var u, Tm.to_var v with IsCoh -> raise Invalid
            in
            if (y <> fy) then raise Invalid;
            let x,_ = marker ps in
            if x = fx then
              let varps = Ctx.domain (old_rep_to_ctx ps) in
              if (List.mem f varps) then
                raise (DoubledVar (Var.to_string f));
              if (List.mem y varps) then
                raise (DoubledVar (Var.to_string y));
              let ps = PCons (ps,(y,ty),(f,tf)) in
              aux ps l
            else
              aux (PDrop ps) l1
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
      | PNil x -> (Unchecked_types.Br list, PNil x)
      | PCons (ps,_,_) -> (Unchecked_types.Br list, ps)
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
    Unchecked_types.Br (fst (build_till_previous ps))

  let mk (l : Ctx.t) =
    let oldrep = make_old l in
    {oldrep; newrep = {tree = make_tree oldrep; ctx = l}}

  let forget ps = ps.newrep.tree

  let to_string ps = Unchecked.ps_to_string (forget ps)

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
      | [] -> Error.fatal "could not find a replacement"
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
  type t
  val to_string : t -> string
  val free_vars : t -> Var.t list
  val is_obj : t -> bool
  val check_equal : t -> t -> unit
  val forget : t -> Unchecked_types.ty
  val check : Ctx.t -> Unchecked_types.ty -> t
  val apply : t -> Sub.t -> t
  val retrieve_arrow : t -> (t * Tm.t * Tm.t)
  val under_type : t -> t
  val target : t -> Tm.t
end
=
struct
  (** A type exepression. *)
  type expr =
    | Obj
    | Arr of t * Tm.t * Tm.t
  and t = {c : Ctx.t; e : expr; unchecked : Unchecked_types.ty}

  let is_obj t = (t.e = Obj)

  let retrieve_arrow ty =
    match ty.e with
    | Obj -> raise IsObj
    | Arr(a,u,v) -> a,u,v

  let under_type ty =
    match ty.e with
    | Obj -> raise IsObj
    | Arr(a,_,_) -> a

  let target ty =
    match ty.e with
    | Obj -> raise IsObj
    | Arr(_,_,v) -> v

  let rec check c t =
    Io.info ~v:3
      (lazy
        (Printf.sprintf
           "building kernel type %s in context %s"
           (Unchecked.ty_to_string t)
           (Ctx.to_string c)));
    let e =
      match t with
      | Obj -> Obj
      | Arr(a,u,v) ->
        let a = check c a in
        let u = Tm.check c u in
        let v = Tm.check c v in
        Arr(a,u,v)
      | Meta_ty _ -> raise MetaVariable
    in {c; e; unchecked = t}

  (** Free variables of a type. *)
  let rec free_vars ty =
    match ty.e with
    | Obj -> []
    | Arr (t,u,v) -> List.unions [free_vars t; Tm.free_vars u; Tm.free_vars v]

  let forget t = t.unchecked

  let to_string ty =
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
  type t
  val to_var : t -> Var.t
  val typ : t -> Ty.t
  val free_vars : t -> Var.t list
  val check : Ctx.t -> ?ty:Ty.t -> Unchecked_types.tm -> t
end
=
struct
  type expr =
    | Var of Var.t (** a context variable *)
    | Coh of Coh.t * Sub.t
  and t = {ty : Ty.t; e : expr; unchecked : Unchecked_types.tm}

  let typ t = t.ty

  let to_var tm =
    match tm.e with
    | Var v -> v
    | Coh _ -> raise IsCoh

  let free_vars tm =
    match tm.e with
    | Var x -> [x]
    | Coh (_,sub) -> Sub.free_vars sub

  let forget tm = tm.unchecked
  let _to_string tm = Unchecked.tm_to_string (forget tm)

  let check c ?ty t =
    Io.info ~v:3
      (lazy
        (Printf.sprintf
           "building kernel term %s in context %s"
           (Unchecked.tm_to_string t)
           (Ctx.to_string c)));
    let tm =
      match t with
      | Var x ->
        let e, ty  = Var x, Ty.check c (Ty.forget (Ctx.ty_var c x)) in
        ({ty; e; unchecked = t})
      | Meta_tm _ -> raise MetaVariable
      | Coh (coh,s) ->
        let coh = Coh.check coh [] in
        let sub = Sub.check_to_ps c s (Coh.ps coh) in
        let e, ty = Coh(coh,sub), Ty.apply (Coh.ty coh) sub in
        {ty; e; unchecked = t}
    in match ty with
    | None -> tm
    | Some ty -> Ty.check_equal ty tm.ty; tm
end

(** A coherence. *)
and Coh : sig
  type t
  val ps : t -> PS.t
  val ty : t -> Ty.t
  val algebraic : PS.t -> Ty.t ->  (Var.t * int) list -> t
  val check : Unchecked_types.coh -> (Var.t * int) list -> t
  val to_string : t -> string
  val forget : t -> Unchecked_types.ps * Unchecked_types.ty
end
=
struct
  type t = PS.t * Ty.t * (Var.t * int) list
  exception NotAlgebraic

  let ps (ps,_,_) = ps
  let ty (_,t,_) = t

  let algebraic ps t l =
    if List.included (PS.domain ps) (Ty.free_vars t)
    then (ps,t,l)
    else
      let a,f,g =
        try Ty.retrieve_arrow t with IsObj -> raise NotAlgebraic
      in
      let i = PS.dim ps in
      let pss, pst = PS.source (i-1) ps, PS.target (i-1) ps in
      let fvf = List.union (Tm.free_vars f) (Ty.free_vars a) in
      let fvg = List.union (Tm.free_vars g) (Ty.free_vars a) in
      if (List.set_equal pss fvf && List.set_equal pst fvg)
      then (ps,t,l)
      else raise NotAlgebraic

  let check coh names =
    try
      match coh with
      | Unchecked_types.Cohdecl (ps,t) ->
        Io.info ~v:3
          (lazy
            (Printf.sprintf "checking coherence (%s,%s)"
               (Unchecked.ps_to_string ps)
               (Unchecked.ty_to_string t)));
        let cps = Ctx.check (Unchecked.ps_to_ctx ps) in
        let ps = PS.mk cps in
        let t = Ty.check cps t in
        Coh.algebraic ps t names
      | Unchecked_types.Cohchecked c -> c
    with
    | NotAlgebraic ->
      let ty = match coh with
        | Unchecked_types.Cohdecl (_, t) -> Unchecked.ty_to_string t
        | Unchecked_types.Cohchecked c -> Ty.to_string (Coh.ty c)
      in Error.not_valid_coherence (Unchecked.coh_to_string coh)
        (Printf.sprintf "type %s not algebraic in pasting scheme" ty)
    | DoubledVar(s) ->
      Error.not_valid_coherence (Unchecked.coh_to_string coh) (Printf.sprintf "variable %s appears twice in the context" s)



  let forget (ps,ty,_) = PS.forget ps, Ty.forget ty

  let to_string (ps,ty,_) =
    Printf.sprintf "Coh(%s,%s)" (PS.to_string ps) (Ty.to_string ty)
end


and Unchecked_types : sig
  type ps = Br of ps list

  type ty =
    | Meta_ty of int
    | Obj
    | Arr of ty * tm * tm
  and tm =
    | Var of Var.t
    | Meta_tm of int
    | Coh of coh * sub_ps
  and coh =
    | Cohdecl of ps * ty
    | Cohchecked of Coh.t
  and sub_ps = tm list
  type ctx = (Var.t * (ty * bool)) list
  type sub = (Var.t * tm) list
  type meta_ctx = ((int * ty) list)
end = struct
  type ps = Br of ps list

  type ty =
    | Meta_ty of int
    | Obj
    | Arr of ty * tm * tm
  and tm =
    | Var of Var.t
    | Meta_tm of int
    | Coh of coh * sub_ps
  and coh =
    | Cohdecl of ps * ty
    | Cohchecked of Coh.t
  and sub_ps = tm list

  type ctx = (Var.t * (ty * bool)) list

  type sub = (Var.t * tm) list

  type meta_ctx = ((int * ty) list)

end
and Unchecked : sig
  val ps_to_string : Unchecked_types.ps -> string
  val ty_to_string : Unchecked_types.ty -> string
  val tm_to_string : Unchecked_types.tm -> string
  val sub_ps_to_string : Unchecked_types.sub_ps -> string
  val ctx_to_string : Unchecked_types.ctx -> string
  val sub_to_string : Unchecked_types.sub -> string
  val coh_to_string : Unchecked_types.coh -> string
  val meta_ctx_to_string : Unchecked_types.meta_ctx -> string
  val check_equal_ty : Unchecked_types.ty -> Unchecked_types.ty -> unit
  val check_equal_coh : Unchecked_types.coh -> Unchecked_types.coh -> unit
  val check_equal_ctx : Unchecked_types.ctx -> Unchecked_types.ctx -> unit
  val tm_apply_sub : Unchecked_types.tm -> Unchecked_types.sub -> Unchecked_types.tm
  val ty_apply_sub : Unchecked_types.ty -> Unchecked_types.sub -> Unchecked_types.ty
  val rename_ty : Unchecked_types.ty -> (Var.t * int) list -> Unchecked_types.ty
  val db_levels : Unchecked_types.ctx -> Unchecked_types.ctx * (Var.t * int) list * int
  val ps_to_ctx : Unchecked_types.ps -> Unchecked_types.ctx
  val sub_ps_to_sub : Unchecked_types.sub_ps -> Unchecked_types.ps -> Unchecked_types.sub * Unchecked_types.ctx
  val two_fresh_vars : Unchecked_types.ctx -> Var.t * Var.t
  val identity_ps : Unchecked_types.ctx -> Unchecked_types.sub_ps
  val tm_contains_vars : Unchecked_types.tm -> Var.t list -> bool
  val dim_ty : Unchecked_types.ty -> int
  val dim_ctx : Unchecked_types.ctx -> int
  val dim_ps : Unchecked_types.ps -> int
  val suspend_ps : Unchecked_types.ps -> Unchecked_types.ps
  val suspend_ty : Unchecked_types.ty -> Unchecked_types.ty
  val suspend_tm : Unchecked_types.tm -> Unchecked_types.tm
  val suspend_ctx : Unchecked_types.ctx -> Unchecked_types.ctx
  val suspend_sub_ps : Unchecked_types.sub_ps -> Unchecked_types.sub_ps
end = struct
  let rec ps_to_string = function
    | Unchecked_types.Br l -> Printf.sprintf "[%s]"
                (List.fold_left
                   (fun s ps -> Printf.sprintf "%s%s" (ps_to_string ps) s)
                   ""
                   l)

  let rec ty_to_string = function
    | Unchecked_types.Meta_ty i -> Printf.sprintf "_ty%i" i
    | Unchecked_types.Obj -> "*"
    | Unchecked_types.Arr (a,u,v) ->
      Printf.sprintf "%s | %s -> %s"
        (ty_to_string a)
        (tm_to_string u)
        (tm_to_string v)
  and tm_to_string = function
    | Unchecked_types.Var v -> Var.to_string v
    | Unchecked_types.Meta_tm i -> Printf.sprintf "_tm%i" i
    | Unchecked_types.Coh (c,s) ->
      Printf.sprintf "%s[%s]"
        (coh_to_string c)
        (sub_ps_to_string s)
  and sub_ps_to_string = function
    | [] -> ""
    | t::s -> Printf.sprintf "%s %s" (sub_ps_to_string s)  (tm_to_string t)
  and coh_to_string = function
    | Unchecked_types.Cohdecl(ps,ty) ->
      Printf.sprintf "coh(%s,%s)"
        (ps_to_string ps)
        (ty_to_string ty)
    | Unchecked_types.Cohchecked c ->
      Coh.to_string c

  let rec ctx_to_string = function
    | [] -> ""
    | (x,(t,true))::c ->
      Printf.sprintf "%s (%s: %s)"
        (ctx_to_string c)
        (Var.to_string x)
        (ty_to_string t)
    | (x,(t,false))::c ->
      Printf.sprintf "%s {%s: %s}"
        (ctx_to_string c)
        (Var.to_string x)
        (ty_to_string t)
  let rec sub_to_string = function
    | [] -> ""
    | (x,t)::s ->
      Printf.sprintf "%s (%s: %s)"
        (sub_to_string s)
        (Var.to_string x)
        (tm_to_string t)

  let rec meta_ctx_to_string = function
    | [] -> ""
    | (i,t)::c ->
      Printf.sprintf "%s (_tm%i: %s)"
        (meta_ctx_to_string c)
        i
        (ty_to_string t)

  let rec check_equal_ps ps1 ps2 =
    match ps1, ps2 with
    | Unchecked_types.Br [], Unchecked_types.Br[] -> ()
    | Unchecked_types.Br (ps1::l1), Unchecked_types.Br(ps2::l2) ->
      check_equal_ps ps1 ps2;
      List.iter2 check_equal_ps l1 l2
    | Unchecked_types.Br[], Unchecked_types.Br (_::_) | Unchecked_types.Br(_::_), Unchecked_types.Br[] ->
      raise (NotEqual (ps_to_string ps1, ps_to_string ps2))

  let rec check_equal_ty ty1 ty2 =
    match ty1, ty2 with
    | Unchecked_types.Meta_ty i, Unchecked_types.Meta_ty j ->
      if i <> j then raise (NotEqual(string_of_int i, string_of_int j))
    | Unchecked_types.Obj, Unchecked_types.Obj -> ()
    | Unchecked_types.Arr(ty1, u1, v1), Unchecked_types.Arr(ty2, u2, v2) ->
      check_equal_ty ty1 ty2;
      check_equal_tm u1 u2;
      check_equal_tm v1 v2
    | Obj, Arr _ | Arr _, Obj
    | Meta_ty _, Obj | Meta_ty _, Arr _
    | Obj, Meta_ty _ | Arr _, Meta_ty _ ->
      raise (NotEqual (ty_to_string ty1, ty_to_string ty2))
  and check_equal_tm tm1 tm2 =
    match tm1, tm2 with
    | Var v1, Var v2 -> Var.check_equal v1 v2
    | Meta_tm i, Meta_tm j ->
      if i <> j then raise (NotEqual(string_of_int i, string_of_int j))
    | Coh(coh1, s1), Coh(coh2, s2) ->
      check_equal_coh coh1 coh2;
      check_equal_sub_ps s1 s2
    | Var _, Coh _ | Coh _, Var _
    | Meta_tm _, Var _| Meta_tm _, Coh _
    | Var _, Meta_tm _ | Coh _, Meta_tm _ ->
      raise (NotEqual (tm_to_string tm1, tm_to_string tm2))
  and check_equal_coh coh1 coh2 =
    match coh1, coh2 with
    | Cohdecl(ps1, ty1), Cohdecl(ps2, ty2) ->
      check_equal_ps ps1 ps2;
      check_equal_ty ty1 ty2
    | Cohchecked(coh1), Cohdecl(ps2,ty2) ->
      let ps1, ty1 = Coh.forget coh1 in
      check_equal_ps ps1 ps2;
      check_equal_ty ty1 ty2
    | Cohdecl(ps1,ty1), Cohchecked(coh2) ->
      let ps2, ty2 = Coh.forget coh2 in
      check_equal_ps ps1 ps2;
      check_equal_ty ty1 ty2
    | Cohchecked(coh1), Cohchecked(coh2) ->
      let ps1, ty1 = Coh.forget coh1 in
      let ps2, ty2 = Coh.forget coh2 in
      check_equal_ps ps1 ps2;
      check_equal_ty ty1 ty2
  and check_equal_sub_ps s1 s2 =
    List.iter2 check_equal_tm s1 s2

  let rec check_equal_ctx ctx1 ctx2 =
    match ctx1, ctx2 with
    | [], [] -> ()
    | (v1,(t1,_))::c1, (v2,(t2,_))::c2 ->
      Var.check_equal v1 v2;
      check_equal_ty t1 t2;
      check_equal_ctx c1 c2
    | _::_,[] | [],_::_ ->
      raise (NotEqual (ctx_to_string ctx1, ctx_to_string ctx2))

  let rec tm_do_on_variables tm f =
    match tm with
    | Unchecked_types.Var v -> (f v)
    | Meta_tm i -> Unchecked_types.Meta_tm i
    | Coh(c,s) -> Coh (c, sub_ps_do_on_variables s f)
  and sub_ps_do_on_variables s f = List.map (fun t -> tm_do_on_variables t f) s

  let rec ty_do_on_variables ty f =
    match ty with
    | Unchecked_types.Meta_ty i -> Unchecked_types.Meta_ty i
    | Obj -> Obj
    | Arr(a,u,v) ->
      Arr(ty_do_on_variables a f, tm_do_on_variables u f, tm_do_on_variables v f)

  let var_apply_sub v s =
    match List.assoc_opt v s with
    | Some t -> t
    | None -> Unchecked_types.Var v
  let tm_apply_sub tm s = tm_do_on_variables tm (fun v -> var_apply_sub v s)
  let ty_apply_sub ty s = ty_do_on_variables ty (fun v -> var_apply_sub v s)
  let _sub_apply_sub s1 s2 = List.map (fun (v,t) -> (v,tm_apply_sub t s2)) s1

  (* rename is applying a variable to de Bruijn levels substitutions *)
  let rename_ty ty l = ty_do_on_variables ty (fun v -> Unchecked_types.Var (Db (List.assoc v l)))

  let rec db_levels c =
    match c with
    | [] -> [], [], -1
    | (x,(t,expl))::c ->
      let c,l,max = db_levels c in
      if List.mem_assoc x l then
        raise (DoubledVar(Var.to_string x))
      else
        let lvl = max + 1 in
        (Var.Db lvl, (rename_ty t l, expl)) ::c, (x, lvl)::l, lvl

  let increase_lv_ty ty i m =
    ty_do_on_variables ty (fun v -> Unchecked_types.Var (Var.increase_lv v i m))

  let suspend_ps ps = Unchecked_types.Br [ps]

  let rec suspend_ty = function
    | Unchecked_types.Obj -> Unchecked_types.Arr(Obj, Var (Db 0), Var (Db 1))
    | Arr(a,v,u) -> Arr(suspend_ty a, suspend_tm v, suspend_tm u)
    | Meta_ty _ -> Error.fatal "meta-variables should be resolved"
  and suspend_tm = function
    | Var v -> Var (Var.suspend v)
    | Coh (c,s) -> Coh(suspend_coh c, suspend_sub_ps s)
    | Meta_tm _ -> Error.fatal "meta-variables should be resolved"
  and suspend_coh = function
    | Cohdecl (p,t) -> Cohdecl(suspend_ps p, suspend_ty t)
    | Cohchecked c ->
      let p,t = Coh.ps c, Coh.ty c in
      let p,t = PS.forget p, Ty.forget t in
      Cohdecl(suspend_ps p, suspend_ty t)
  and suspend_sub_ps = function
    | [] -> [Var (Var.Db 1); Var (Var.Db 0)]
    | t::s -> (suspend_tm t) :: (suspend_sub_ps s)

  let rec suspend_ctx = function
    | [] -> (Var.Db 1, (Unchecked_types.Obj, false)) :: (Var.Db 0, (Obj, false)) :: []
    | (v,(t,expl))::c -> (Var.suspend v, (suspend_ty t, expl)) :: (suspend_ctx c)

  let ps_to_ctx ps =
    let rec ps_to_ctx_aux ps =
      match ps with
      | Unchecked_types.Br [] -> [(Var.Db 0), (Unchecked_types.Obj, true)], 0, 0
      | Br l ->
        ps_concat (List.map
                     (fun ps ->
                        let ps,_,m = ps_to_ctx_aux ps in
                        (suspend_ctx  ps, 1, m+2))
                     l)
    and ps_concat = function
      | [] -> Error.fatal "empty is not a pasting scheme"
      | ps :: [] -> ps
      | ps :: l -> ps_glue (ps_concat l) ps
    and ps_glue (p1,t1,m1) (p2,t2,m2) =
      List.append (chop_and_increase p2 t1 m1) p1, t2+m1, m1+m2
    and chop_and_increase ctx i m =
      match ctx with
      | [] -> Error.fatal "empty is not a pasting scheme"
      | _ :: [] -> []
      | (v,(t,expl)) :: ctx ->
        let v = Var.increase_lv v i m in
        let t = increase_lv_ty t i m in
        let ctx = chop_and_increase ctx i m in
        (v,(t,expl))::ctx
    in
    let c,_,_ = ps_to_ctx_aux ps in c

  let sub_ps_to_sub s ps =
    let ps = ps_to_ctx ps in
    List.map2 (fun t (x,_) -> (x,t)) s ps, ps

  let max_fresh_var c =
    let rec find_max c i =
      match c with
      | [] -> i
      | (Var.New j, _) :: c when j >= i -> find_max c j
      | ((Var.Name _ | Var.Db _ | Var.New _ ), _) :: c  -> find_max c i
    in
    find_max c 0

  let two_fresh_vars c =
    let i = max_fresh_var c in
    Var.New (i+1), Var.New (i+2)

  let rec identity_ps = function
    | [] -> []
    | (x,_)::c -> Unchecked_types.Var x :: (identity_ps c)

  let rec tm_contains_var t x =
    match t with
    | Unchecked_types.Var v -> v = x
    | Coh(_,s) -> List.exists (fun t -> tm_contains_var t x) s
    | Meta_tm _ -> Error.fatal "meta-variables should be resolved"

  let tm_contains_vars t l =
    List.exists (tm_contains_var t) l

  let rec dim_ty = function
    | Unchecked_types.Obj -> 0
    | Arr(a,_,_) -> 1 + dim_ty a
    | Meta_ty _ -> Error.fatal "meta-variables should be resolved"

  let rec dim_ctx = function
    | [] -> 0
    | (_,(t,_))::c -> max (dim_ctx c) (dim_ty t)

  let rec dim_ps = function
    | Unchecked_types.Br [] -> 0
    | Br l -> 1 + max_list_ps l
  and max_list_ps = function
    | [] -> 0
    | p::l -> max (dim_ps p) (max_list_ps l)
end

include Unchecked_types

let check_type ctx a =
  try Ty.check ctx a with
  | NotEqual(s1,s2) ->
    Error.untypable ("type: " ^ Unchecked.ty_to_string a) (Printf.sprintf "%s and %s are not equal" s1 s2)

let check_term ctx ?ty t =
  let ty = Option.map (check_type ctx) ty in
  let tm = "term: " ^ (Unchecked.tm_to_string t) in
  try Tm.check ctx ?ty t with
  | NotEqual(s1,s2) ->
    Error.untypable tm (Printf.sprintf "expected %s but received %s" s1 s2)
  | InvalidSubTarget (s,tgt) ->
    Error.untypable tm (Printf.sprintf "substitution %s does not apply from context %s" s tgt)
  | Error.UnknownId (s) ->
    Error.untypable tm (Printf.sprintf "unknown identifier :%s" s)
  | MetaVariable ->
    Error.incomplete_constraints tm
