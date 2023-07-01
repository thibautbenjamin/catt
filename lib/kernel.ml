open Std
open Settings
open Common
open Variables

type cvar = CVar.t

let var_of_cvar = CVar.to_var

(** Operations on substitutions. *)
module rec Sub : sig
  type t

  (* Structural functions *)
  val _check : Ctx.t -> Unchecked.sub -> Ctx.t -> t
  val check_to_ps : Ctx.t -> Unchecked.sub_ps -> PS.t -> t
  val _forget : t -> Unchecked.sub
  val _forget_to_ps : t -> Unchecked.sub_ps

  (* Syntactic properties *)
  val free_vars : t -> cvar list

  (* Printing *)
  val _to_string : t ->  string

  val src : t -> Ctx.t
  val tgt : t -> Ctx.t
end
  = struct
  (** A substitution. *)
  (* Variable names are given by the codomain. *)
  type t = {list : Tm.t list; src : Ctx.t; tgt : Ctx.t}

  (** Free context variables. *)
  let free_vars s =
    List.concat (List.map Tm.free_vars s.list)

  let src s = s.src
  let tgt s = s.tgt

  (** String representation of a substitution. We print only maximal elements *)
  let _to_string (s:t) =
    let rec print_list s c =
      match s,c with
      | [], c when Ctx.is_empty c -> ""
      | (u::s),c -> begin
          match Ctx.head c with
          | (_, (_,true)) ->
             Printf.sprintf "%s %s" (print_list s (Ctx.tail c)) (Tm.to_string u)
          | (_, (_,false)) -> Printf.sprintf "%s" (print_list s (Ctx.tail c))
        end
      | _ -> assert false
    in print_list s.list s.tgt

  let rec _check (src : Ctx.t) s tgt =
    let expr (s : Unchecked.sub) tgt =
      match s, Ctx.value tgt with
      | [], [] -> []
      | (_::_,[] |[],_::_) -> raise NotValid
      | (x1,_)::_, (x2,(_,_))::_ when x1 != (var_of_cvar x2) -> raise NotValid
      | (_,t)::s, (_,(a,_))::tgt ->
	 let sub = _check src s tgt in
         let t = Tm.check src t in
	 let ty = t.ty in
         (* TODO: replace this *)
	 Ty.check_equal src ty (Ty._from_unchecked src (Unchecked.ty_apply_sub (Ty._forget a) s));
	 t::sub.list
    in
    {list = expr s tgt; src; tgt}

  let check_to_ps src s tgt =
    let tgt = PS.to_ctx tgt in
    let s = List.map2 (fun (x,_) t -> (x,t)) tgt s in
    _check src s tgt

  let _forget s = List.map2 (fun (v,_) t -> (var_of_cvar v, Tm._forget t)) s.tgt s.list
  let _forget_to_ps s = List.map Tm._forget s.list
end

(** A context, associating a type to each context variable. *)
and Ctx
    :
sig
  type t = (cvar * (Ty.t * bool)) list

  (* Makers *)
  val empty : unit -> t

  (* Structural operations *)
  val head : t -> cvar * (Ty.t * bool)
  val tail : t -> t

  (* Syntactic properties *)
  val ty_var : t -> cvar -> Ty.t
  val domain : t -> cvar list
  val value : t -> (cvar * (Ty.t * bool)) list

  val _forget : t -> Unchecked.ctx
  val _check : Unchecked.ctx -> t
  val _extend : t -> var -> Unchecked.ty -> t


  (* Equality procedure *)
  val is_empty : t -> bool
  val check_equal : t -> t -> unit

  (* Printing *)
  val to_string : t -> string
end
  =
struct
  (** A context. Variables together with a type a a boolean indicating if the variable is explicit or implicit*)
  type t = (cvar * (Ty.t * bool)) list

  (** type of a variable in a context. *)
  let ty_var (ctx:t) x =
    try
      fst (List.assoc x ctx)
    with
    | Not_found -> raise (UnknownId (CVar.to_string x))

  (* ------ Makers ------ *)
  (** Empty context. *)
  let empty () = []

  (* ---------------------
      Structural operations
      --------------------- *)

  (** First element of a context. *)
  let head ctx =
    match ctx with
    |[] -> assert false
    |a::_ -> a

  (** Tail of a context. *)
  let tail ctx =
    match ctx with
    |[] -> assert false
    |_::l -> l

  (* --------------------
     Syntactic properties
     -------------------- *)
  (** Domain of definition of a context. *)
  let domain ctx = List.map fst ctx

  let value (ctx : t) = ctx

  (* -------------------
     Equality procedures
     ------------------- *)
  (** Is a context empty? *)
  let is_empty (c:t) =
    c = []

  (** Equality of contexts. *)
  let check_equal ctx1 ctx2 =
    let rec equal c (ctx1 : Ctx.t) (ctx2 : Ctx.t) =
      match (ctx1 :> t), (ctx2 :> t) with
      | [],[] -> ()
      | (v1,(x1,_))::_, (v2,(x2,_))::_ ->
         let t1 = Ctx.tail ctx1 and t2 = Ctx.tail ctx2 in
         if not (v1 = v2) then raise NotValid;
         Ty.check_equal c x1 x2;
         equal ctx1 t1 t2
      | _,_ -> raise NotValid
    in equal (Ctx.empty ()) ctx1 ctx2

     (* --------
      Printing
      -------- *)
  (** String representation of a context. *)
  let rec to_string ctx =
    match ctx with
    | [] -> ""
    | (x,(t,false))::c ->
       Printf.sprintf "%s {%s,%s}"
         (to_string c)
         (CVar.to_string x)
         (Ty.to_string t)
    | (x,(t,true))::c ->
       Printf.sprintf "%s (%s,%s)"
         (to_string c)
	 (CVar.to_string x)
         (Ty.to_string t)

  let _forget c = List.map (fun (x,(a,_)) -> (var_of_cvar x, Ty._forget a)) c

  let check_notin c x =
    try
      ignore (List.assoc x c);
      raise (DoubleDef (CVar.to_string x))
    with Not_found -> ()

  let _extend c x t =
    let t = Ty._from_unchecked c t in
    let x = CVar.make x in
    check_notin c x;
    (x,(t,true))::c

  let _check c = List.fold_right (fun (x,t) c -> _extend c x t) c (Ctx.empty ())
end

(** Operations on pasting schemes. *)
and PS
    :
sig
  type t

  (* Maker *)
  val mk : Ctx.t -> t

  (* Syntactic properties *)
  val domain : t -> cvar list
  val to_ctx : t -> Ctx.t

  (* Structural operations *)
  val dim : t -> int
  val source : int -> t -> cvar list
  val target : int -> t -> cvar list

  val _forget : t -> Unchecked.ps
  val check : Unchecked.ps -> t

  (* Printing *)
  val to_string : t -> string
end
  =
struct
  exception Invalid

  (** A pasting scheme. *)
  type oldrep =
    | PNil of (cvar * Ty.t)
    | PCons of oldrep * (cvar * Ty.t) * (cvar * Ty.t)
    | PDrop of oldrep

  type newt = { tree : Unchecked.ps; ctx : Ctx.t}

  type t = {oldrep : oldrep; newrep : newt}

     (* --------------------
      Syntactic properties
      -------------------- *)
  (** Create a context from a pasting scheme. *)
  let old_rep_to_ctx ps =
    match ps with
    |PNil (x,t) -> [(x,(t,true))]
    |_ ->
      let rec aux ps =
        match ps with
        |PDrop (PCons (ps,(x1,t1),(x2,t2))) -> let c = aux ps in
                                               (x2,(t2,true))::(x1,(t1, false))::c
        |PDrop ps -> aux ps
        |PCons (ps,(x1,t1),(x2,t2)) -> let c = aux ps in
                                       (x2,(t2,false))::(x1,(t1,false))::c
        |PNil (x,t) -> [(x,(t,false))]
      in (aux ps)

  (** Domain of definition. *)
  let domain ps = Ctx.domain ps.newrep.ctx

  (* -----
    Maker
    ----- *)
  (** Dangling variable. *)
  let rec marker (ps : oldrep) =
    match ps with
    | PNil (x,t) -> x,t
    | PCons (_,_,f) -> f
    | PDrop ps ->
       let _,tf = marker ps in
       let open Ty in
       let open Tm in
       match tf.e with
       | Ty.Arr (_,_,{e = Tm.CVar y; _}) ->
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
    let open Ty in
    let rec close ps tx =
      match tx.e with
      | Obj -> ps
      | Arr (tx,_,_) -> close (PDrop ps) tx
    in
    let build l =
      let x0,ty,l =
        match l with
        | (x,(ty,_))::l when ty.e = Obj -> x,ty,l
        | _ -> raise Invalid
      in
      let rec aux ps = function
        | ((y,(ty,_))::(f,(tf,_))::l) as l1 ->
           begin
             let open Tm in
             let open Ty in
             match tf.e with
             | Arr (_, {e = CVar fx; _}, {e = CVar fy; _}) ->
                if (y <> fy) then raise Invalid;
                let x,_ = marker ps in
                if x = fx then
                  let varps = Ctx.domain (old_rep_to_ctx ps) in
                  if (List.mem f varps) then raise (DoubledVar (CVar.to_string f));
                  if (List.mem y varps) then raise (DoubledVar (CVar.to_string y));
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
      | PNil x -> (Unchecked.Br list, PNil x)
      | PCons (ps,_,_) -> (Unchecked.Br list, ps)
      | PDrop _ as ps ->
         let p,ps = build_till_previous ps in
         Unchecked.Br p, ps
    and build_till_previous ps =
      match ps with
      | PNil x -> [], PNil x
      | PCons (ps,_,_) -> [], ps
      | PDrop ps ->
         let p,ps = find_previous ps [] in
         let prev,ps = build_till_previous ps in
                 p::prev, ps
    in
    Unchecked.Br (fst (build_till_previous ps))

  let mk (l : Ctx.t) =
    let oldrep = make_old l in
    {oldrep; newrep = {tree = make_tree oldrep; ctx = l}}

  let _forget ps = ps.newrep.tree

  let check ps =
    debug "checking ps %s" (Unchecked.ps_to_string ps);
    debug "corresponding context: %s" (Unchecked.(ctx_to_string (ps_to_ctx ps)));
    let res = PS.mk (Ctx._check (Unchecked.ps_to_ctx ps)) in
    (* sanity check: we have the tree we started from *)
    debug "original tree: %s, new tree: %s"
      (Unchecked.ps_to_string ps)
      (Unchecked.ps_to_string res.newrep.tree);
    assert (res.newrep.tree = ps);
    res

  (** Create a context from a pasting scheme. *)
  let to_ctx ps =
    ps.newrep.ctx

     (* ---------------------
      Structural operations
      --------------------- *)
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

  (* --------
     Printing
     -------- *)
  (** String representation of a pasting scheme. *)
  let _to_string_old ps =
    if !abbrev then
      Ctx.to_string (old_rep_to_ctx ps)
    else
      let rec print ps =
	match ps with
	| PNil (x,t) ->
	  Printf.sprintf "[(%s,%s)]"
	    (CVar.to_string x)
	    (Ty.to_string t)
	| PCons (ps,(x1,t1),(x2,t2)) ->
	  Printf.sprintf "%s [(%s,%s) (%s,%s)]"
	    (print ps)
	    (CVar.to_string x1)
	    (Ty.to_string t1)
	    (CVar.to_string x2)
	    (Ty.to_string t2)
	| PDrop ps ->
	  Printf.sprintf " %s ! "
	    (print ps)
      in print ps

  let to_string ps = Unchecked.ps_to_string ps.newrep.tree
end
and Ty : sig
  type expr =
    | Obj
    | Arr of t * Tm.t * Tm.t
  and t = {c : Ctx.t; e : expr}

  val free_vars : t -> cvar list
  val to_string : t -> string

  val check_equal : Ctx.t -> t -> t -> unit

  val _forget : t -> Unchecked.ty
  val _from_unchecked : Ctx.t -> Unchecked.ty -> t
  val apply : t -> Sub.t -> t
end
  =
struct
  (** A type exepression. *)
  type expr =
    | Obj
    | Arr of t * Tm.t * Tm.t
  and t = {c : Ctx.t; e : expr}

  let rec _from_unchecked c t =
    debug "building kernel type %s in context %s"
    (Unchecked.ty_to_string t) (Ctx.to_string c);
    let e =
      match t with
      | Unchecked.Obj -> Obj
      | Unchecked.Arr(a,u,v) ->
         let a = _from_unchecked c a in
         let u = Tm.check c u in
         let v = Tm.check c v in
         Arr(a,u,v)
  in {c; e}

  (** Free variables of a type. *)
  let rec free_vars ty =
    match ty.e with
    | Obj -> []
    | Arr (t,u,v) -> List.unions [free_vars t; Tm.free_vars u; Tm.free_vars v]

  let rec to_string ty =
    match ty.e with
    | Obj -> "*"
    | Arr (t,u,v) ->
       if !abbrev then
         Printf.sprintf "%s -> %s" (Tm.to_string u) (Tm.to_string v)
       else Printf.sprintf "%s | %s -> %s" (to_string t) (Tm.to_string u) (Tm.to_string v)

  (** Test for equality. *)
  let rec check_equal ctx ty1 ty2 =
    (* debug "checking equality between %s and %s" (to_string ty1)(to_string ty2); *)
    let equal = check_equal ctx in
    match ty1.e, ty2.e with
    |Obj,Obj -> ()
    |Arr(t1,u1,v1),Arr(t2,u2,v2) ->
      equal t1 t2; Tm.check_equal ctx u1 u2; Tm.check_equal ctx v1 v2
    |(Obj |Arr _),_ ->
      raise (NotEqual (to_string ty1, to_string ty2))

  let rec _forget t =
    match t.e with
    | Obj -> Unchecked.Obj
    | Arr (a,u,v) -> Unchecked.Arr (_forget a, Tm._forget u, Tm._forget v)

  let apply t s =
    Ctx.check_equal t.c (Sub.tgt s);
    _from_unchecked (Sub.src s) (Unchecked.ty_apply_sub (_forget t) (Sub._forget s))
end

(** Operations on terms. *)
and Tm
    :
sig
  type expr =
    | CVar of cvar
    | Coh of Coh.t * Sub.t
  and t = {c : Ctx.t; ty : Ty.t; e : expr}

  val typ : t -> Ty.t

  val free_vars : t -> cvar list
  val to_string : t -> string

  val check_equal : Ctx.t -> t -> t -> unit
  val check : Ctx.t -> Unchecked.tm -> t

  val _forget : t -> Unchecked.tm
end
  =
struct
  (** An expression. *)
  type expr =
    | CVar of cvar (** a context variable *)
    | Coh of Coh.t * Sub.t

  (** A term, i.e. an expression with given type in given context. *)
  and t = {c : Ctx.t; ty : Ty.t; e : expr}

  let typ t = t.ty

  let free_vars tm =
    match tm.e with
    | CVar x -> [x]
    | Coh (_,sub) -> Sub.free_vars sub

  let to_string tm =
    match tm.e with
    | CVar x -> CVar.to_string x
    | Coh (c,s) -> Printf.sprintf "%s[%s]" (Coh._to_string c) (Sub._to_string s)

  (* TODO: get rid of extra argument *)
  let check_equal _ tm1 tm2 =
    (* debug "checking equality between %s and %s" (to_string tm1)(to_string tm2); *)
    match tm1.e, tm2.e with
    | CVar x,CVar y ->
      if not (x = y)
      then
	raise (NotEqual (to_string tm1, to_string tm2))
      else ()
    | Coh _, CVar _ | CVar _, Coh _ -> assert false
    | Coh(_,_),Coh(_,_) -> assert false

  let _forget tm =
    match tm.e with
    | CVar v -> Unchecked.Var (CVar.to_var v)
    | Coh(c,s) ->
       let ps,t = Coh._forget c in
       let s = Sub._forget_to_ps s in
       Unchecked.Coh (ps,t,s)

  let check c t =
    debug "building kernel term %s in context %s" (Unchecked.tm_to_string t) (Ctx.to_string c);
    match t with
    | Unchecked.Var x ->
       let x = CVar.make x in
       let e, ty  = CVar x, Ctx.ty_var c x in
       ({c; ty; e})
    | Unchecked.Coh (ps,t,s) ->
       debug "checking the coherence pasting scheme";
       let coh = Coh.check ps t [] in
       debug "building the substitution to the pasting scheme";
       let sub = Sub.check_to_ps c s (Coh.ps coh) in
       debug "creating the term";
       let e, ty = Coh(coh,sub), Ty.apply (Coh.ty coh) sub in
       debug "all done";
       {c; ty; e}
end

(* -- Module with a specific type for well-defined coherences
    -- They are different from normal type, they need to be substituted *)
(** A coherence. *)
and Coh
    : sig
  type t = PS.t * Ty.t * (cvar * int) list

  val ps : t -> PS.t
  val ty : t -> Ty.t

  val _to_string : t -> string

  val _forget : t -> Unchecked.ps * Unchecked.ty
  val check : Unchecked.ps -> Unchecked.ty -> (cvar * int) list -> t
end
=
struct
  type t = PS.t * Ty.t * (cvar * int) list

  let ps (ps,_,_) = ps
  let ty (_,t,_) = t

  let algebraic ps t l =
    if List.included (PS.domain ps) (Ty.free_vars t)
    then (ps,t,l)
    else
      let open Ty in
      let a,f,g = match t.e with
        | Arr(a,f,g) -> (a,f,g)
        | _ -> raise NotAlgebraic
      in
      let i = PS.dim ps in
      let pss, pst = PS.source (i-1) ps, PS.target (i-1) ps in
      let fvf = List.union (Tm.free_vars f) (Ty.free_vars a) in
      let fvg = List.union (Tm.free_vars g) (Ty.free_vars a) in
      if (List.set_equal pss fvf && List.set_equal pst fvg)
      then (ps,t,l)
      else raise NotAlgebraic

  let check ps t names =
    let cps = Ctx._check (Unchecked.ps_to_ctx ps) in
    let ps = PS.mk cps in
    let t = Ty._from_unchecked cps t in
    algebraic ps t names

  let _to_string (ps,t,_) =
    Printf.sprintf "Coh {%s |- %s}"
      (PS.to_string ps)
      (Ty.to_string t)

  let _forget (ps,t,_) = (PS._forget ps, Ty._forget t)
end
