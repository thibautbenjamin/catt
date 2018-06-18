open Stdlib
open Settings
open Common
open PShape
open Var

(** Variables, before distinction between environment or context variables. *)
type var = Var.t

(** Environment variables (i.e. defined coherences). *)
module EVar
: sig 
  type t
  val to_string : t -> string
  val mk : var -> t
  val to_var : t -> var 
end
=
struct
  type t = var

  let to_string v =
    Var.to_string v

  let mk v = v

  let to_var v = v
end

(** Context variables (i.e. "arguments of functions"). *)
module CVar
: sig 
    type t
    val to_string : t -> string
    val mk : var -> t
    val to_var : t -> var
end
=
struct
  type t = var

  let to_string v =
    Var.to_string v
	       
  let mk v = v

  let to_var v = v 
end

type evar = EVar.t
type cvar = CVar.t

let var_of_cvar = CVar.to_var

(** Operations on substitutions. *)
(*
  Substitutions are lists of terms, they come with 	    
  - maker
  - equality decision procedure
  - application on a term 
 *)
module rec Sub
 :
sig
  type t = private (Tm.t list)

  (** Structural functions *)
  val mk : Expr.tm list -> Ctx.t -> PS.t  -> t
  val mk_elaborated : Expr.tm list -> Ctx.t -> PS.t -> t 
  val value : t -> Tm.t list
  val reinit : t -> PShape.pshape -> Expr.tm list
	   
  (** Syntactic properties *)		    
  val free_vars : t -> cvar list
  val applyTy : t -> Ctx.t -> Ctx.t -> Ty.t -> Ty.t
  val applyTm : t -> Ctx.t -> Ctx.t -> Tm.t -> Tm.t
  val dim : Ctx.t -> Expr.tm list -> int
           
  (** Equality procedures *)
  val checkEqual : Ctx.t -> t -> t -> unit

  (** Printing *)	
  val to_string : t -> PShape.pshape -> string
	   
  (** Well-definedness procedure *)
  val check : t  -> Ctx.t -> Ctx.t -> unit
end
  =
struct
  (** A substitution. *)
  (* In current implementation, the variable names are given by the codomain. *)
  (* TODO: add variable names *)
  type t = Tm.t list
	   
    (*  --------------------
      Syntactic properties
      -------------------- *)

  (** Free context variables. *)
  let free_vars (s:t) =
    List.concat (List.map Tm.free_vars s)

  (** Apply a substitution of given codomain to a variable. *)
  let rec apply_var (s:t) (tar:Ctx.t) x =
    match s,tar with
    |_,_ when Ctx.isEmpty tar ->
      raise (UnknownId (CVar.to_string x))
    |t::l, _ ->
      let open Tm in
      let ((y,_),tar) = (Ctx.head tar, Ctx.tail tar) in
      if y = x
      then t.e
      else apply_var l tar x
    |[], _ -> assert false

  (** Sequential composition of substitutions. *)
  let rec compose src tar s (s':t) =
    let open Expr in
    List.rev (List.map (fun t -> Tm (applyTm s tar src t)) s')
  (** Apply a substitution to a term. *)
  and applyTm (s:t) tar src tm =
    let open Tm in
    Ctx.checkSubCtx (tm.c) tar;
    (* Ctx.checkEqual (tm.c) tar; *)
    let e =
      match tm.e with
      |CVar x -> apply_var s tar x
      |Sub (t,s') ->
        let newtar = Cut.ps t in 
        Sub (t, Sub.mk_elaborated (compose src tar s (s' :> Tm.t list)) src newtar)
    in {c = src; ty = applyTy s tar src (Tm.infer tar tm); e = e}
  (** Apply a substitution to a type. *)
  and applyTy (s:t) tar src ty =
    let open Ty in
    Ctx.checkSubCtx (ty.c) tar;
    (* Ctx.checkEqual (ty.c) tar; *)
    let e = 
      match ty.e with
      |Obj -> Obj
      |Arr (a,u,v) -> Arr (applyTy s tar src a, applyTm s tar src u, applyTm s tar src v)
    in {c = src; e = e}

    (* -----------------
	Typing procedures
        -----------------  *)
  (** Check equality of substitutions. *)
  let rec checkEqual ctx (s1:t) (s2:t) = 
    match s1,s2 with
    |[],[] -> ()
    |t1::s1,t2::s2 ->
      Tm.checkEqual ctx t1 t2;
      checkEqual ctx s1 s2
    |_,_ -> raise NotValid

  (* TODO: use String.concat *)
  let rec print l =
    match l with
    |(t::q) -> Tm.to_string t ^ " " ^ print q
    |[] -> ""

  (** Check that a substitution is well-formed with given source and target. *)
  let rec check (s:t) src (tar:Ctx.t) =
    (* debug "substitution %s" (print s); *)
    match s,(tar :> (cvar * Ty.t) list)
    with
    |[],[] -> ()
    |(_::_,[] |[],_::_) -> raise NotValid
    |t::s,_ ->
      let ((x,u),tar) = (Ctx.head tar,Ctx.tail tar) in
      check s src tar;
      Ty.check tar u;
      (* debug "checking that term %s \n has type %s" (Tm.to_string t) (Ty.to_string (applyTy s tar src u)); *)
      Tm.checkType src t (applyTy s tar src u)
	
    (*  --------
	Printing
        --------  *)
  (** String representation of a substitution. We need a pasting scheme
     representation of the target in order to print only cells of locally
     maximal dimension. *)
  (* TODO: use a full pasting scheme and remove "pasting shapes" *)
  let to_string (s:t) ps =
    match s,ps with
    |u::[], PNil -> Printf.sprintf "%s" (Tm.to_string u)
    |_,_ ->
      let rec aux s ps = 
        if !implicit_print then
          match s,ps with
          |u::_::s, PDrop (PCons (ps)) ->
            let ps = aux s ps in
            let u = Tm.to_string u in
            if ps = "" then u else ps ^ " " ^ u
          |s , PDrop ps -> aux s ps
          |u::_::s , PCons ps -> aux s ps
          |s,PNil -> ""
          |_,_ -> assert(false)
        else
          match s with
          |[] -> ""
          |u::s ->
	    Printf.sprintf "%s %s"
	      (aux s ps)
	      (Tm.to_string u)
      in aux s ps

    (*  --------------------
	Structural functions
        --------------------  *)
  (** Given a list of terms of maximal dimension, complete it into a
     full-fledged substitution. *)
  let elaborate l src tar : t =
    (** Close downwards. *)
    let rec complete l x ty ps =
      match ps with
      |PNil ->
	[x]
      |PCons ps->
	let a',x',y' =
          let open Ty in
	  match ty.e with
	  |Arr(a',x',y') -> a',x',y'
	  |_ -> assert(false)
	in
	x::y'::(complete l x' a' ps)
      |(PDrop _) as ps -> find_max l ps
    (** Find next maximal term and close it downwards. *)
    and find_max l ps =
      match l,ps with
      |x::[], PNil ->
	let x,_ = Tm.mk src x in
	[x]
      |[],_ -> raise NotValid
      | _, PNil -> raise NotValid
      |f::l, PDrop(PCons(ps)) ->
	let f,_ = Tm.mk src f in
	let a,x,y =
          let open Ty in
	  match (Tm.infer src f).e with
	  |Arr(a,x,y) -> a,x,y
	  |_ -> assert false
	in
	let s = complete l x a ps in
	f::y::s
      |s,PDrop ps -> find_max s ps
      |s, PCons _ -> assert false
    in
    let s = find_max (List.rev l) (PS.shape tar) in
    check s src (Ctx.of_ps tar);
    s

  (** Construct a substutition (which is already closed downward). *)
  let mk_elaborated l src tar =
    let rec aux l (tar : Ctx.t) =
      match l,(tar :> (cvar * Ty.t) list) with
      |[],[] -> []
      |(_::_,[] |[],_::_) -> raise NotValid
      |t::s,_ ->
	let ((x,u),tar) = (Ctx.head tar,Ctx.tail tar) in
	let s = aux s tar in
	let (t,ty) = Tm.mk src t in
	let () = Ty.checkEqual src ty (applyTy s tar src u)
	in t::s
    in aux (List.rev l) (Ctx.of_ps tar)

  (** Create a substitution described by maximal elements. *)
  let mk l src tar =
    elaborate l src tar

  (** Representation of a substitution as a list. *)
  (* TODO: remove this and use appropriate functions *)
  let value t = t

  (** Dimension of a list of terms. *)
  (* TODO: this should be internal *)
  let dim ctx l =
    let rec max l i =
      match l with
      | [] -> i
      | t::l -> if t > i then max l t else max l i
    in
    let l = List.map (fun x -> Ty.dim (snd (Tm.mk ctx x))) l in
    match l with
    | t::l -> max l t
    | [] -> raise EmptySub

  (** Keep only the the maximal elements of a substitution ("unealborate"). *)
  let reinit (s:t) ps =
    match s,ps with
    |u::[], PNil -> [Tm.reinit u]
    |_,_ ->
      let rec aux s ps = 
        match s,ps with
        |u::_::s, PDrop (PCons (ps)) -> (Tm.reinit u) :: (aux s ps)
        |s , PDrop ps -> aux s ps
        |u::_::s , PCons ps -> aux s ps
        |s,PNil -> []
        |_,_ -> assert(false)
      in List.rev(aux s ps)
end

  (* -- Contexts are association lists of variables and terms in normal form.
   -- They are provided with 	    
	 - maker (normalization and well-definedness)
	 - equality decision procedure
    *)
(** A context, associating a type to each context variable. *)
and Ctx
    :
sig
  type t = private ((cvar * Ty.t) list)

  (* Makers *)
  val empty : unit -> t
  val add : t -> var -> Expr.ty -> t
  val add_norm : t -> var -> Ty.t -> t
  val mk : (var * Expr.ty) list -> t
  val of_ps : PS.t -> t
       
  (* Structural operations *)
  val head : t -> cvar * Ty.t
  val tail : t -> t
  val suspend : t -> int -> t
       
  (* Syntactic properties *)
  val ty_var : t -> cvar -> Ty.t
  val free_vars : t -> cvar list
  val mem : t -> cvar -> bool

  (* Equality procedure *)
  val isEmpty : t -> bool
  val checkSubCtx : t -> t -> unit
  val checkEqual : t -> t -> unit

  (* Printing *)
  val to_string : t -> string
end
  =
struct
  (** A context. *)
  (* TODO: reverse the order of lists *)
  type t = (cvar * Ty.t) list

  (** type of a variable in a context. *)
  let ty_var (ctx:t) x =
    try
      List.assoc x ctx
    with
    | Not_found -> raise (UnknownId (CVar.to_string x))

  (* ------ Makers ------ *)
  (** Empty context. *)
  let empty () = []

  let add_norm (ctx : Ctx.t) x u =
    let x = CVar.mk x in
    try
      ignore (List.assoc x (ctx :> (CVar.t * Ty.t) list));
      raise (DoubleDef (CVar.to_string x))
    with Not_found -> (ctx :> t)@[x,u]

  (** Add a typed variable to a context. *)
  let add (ctx : Ctx.t) x u : t =
    let u = Ty.mk ctx u in
    add_norm ctx x u

  (** Add a variable whose type is already constructed to a context. *)
  let add_norm ctx x u =
    Ty.check ctx u;
    add_norm ctx x u

  (** Create a context from a list of terms. *)
  let rec mk l =
    let rec aux l ctx =
      match l with
      | [] -> ctx
      | (x,t)::l ->
	 let ctx = Ctx.add ctx x t in
	 aux l ctx
    in aux l (Ctx.empty ()) 

  (** Create a context from a pasting scheme. *)
  let rec of_ps ps =
    let open PS in
    match ps with
    | PNil (x,t) -> [(x,t)]
    | PCons (ps,(x1,t1),(x2,t2)) -> (of_ps ps)@[(x1,t1);(x2,t2)]
    | PDrop ps -> of_ps ps


  (* ---------------------
      Structural operations
      --------------------- *)

  (* TODO: reverse.........*)
  (** First element of a context. *)
  let rec head ctx = match ctx with
    |[] -> assert false
    |a::[] -> a
    |_::ctx -> head ctx

  (** Tail of a context. *)
  let rec tail ctx = match ctx with 
    |[] -> assert false
    |_::[] -> []
    |a::ctx -> a::(tail ctx)

  (** Suspend a context, i.e. rempace types "*" by arrow types. *)
  let suspend (ctx : t) i =
    let open Var in
    let open Expr in
    assert (i>=1);
    let rec aux k c ty=
      match k with
      | k when k = i -> c,ty
      | k ->
	 let k' = k+1 in
	 let ty = Arr (Var (New (2*k-1)), Var (New (2*k))) in
	 let ty' = Arr (Var (New (2*k'-1)), Var (New (2*k'))) in
         aux k'
	   (Ctx.add 
	      (Ctx.add c (New ((2*k')-1)) ty)
	      (New (2*k'))
	      ty)
	   ty'
    in
    let ctx' =
      Ctx.add 
	(Ctx.add (Ctx.empty ()) (New 1) Obj)
	(New 2)
	Obj    
    in
    let ctx',ty = aux 1 ctx' (Arr (Var (New 1), Var (New 2))) in
    let open Ty in
    let rec comp c res = match c with
      | (x,tx)::c when tx.e = Obj-> comp c (Ctx.add res (var_of_cvar x) ty)
      | (x,tx)::c -> comp c (Ctx.add res (var_of_cvar x) (Ty.reinit tx))
      | [] -> res
    in
    comp ctx ctx'
       
  (* --------------------
     Syntactic properties
     -------------------- *)
  (** Domain of definition of a context. *)
  (* TODO: rename the function to something like "domain" *)
  (* TODO: check whether this function is really used *)
  let free_vars ctx = List.map fst ctx

  (** Check whether a variable belongs to a context. *)
  let rec mem (c:t) v =
    match c with
    | [] -> false
    | (x,u)::c when x = v -> true
    | _::c -> mem c v
	      
  (* -------------------
     Equality procedures
     ------------------- *)
  (** Is a context empty? *)
  let isEmpty (c:t) =
    c = []

  (** Check whether a context is included in another one. *)
  (* TODO: this is a bit worrying as a function, is it really necessary or can
     we get rid of it? *)
  let checkSubCtx ctx1 ctx2 =
    let rec sub c (ctx1 : Ctx.t) (ctx2 : Ctx.t) = 
      if Ctx.isEmpty ctx1 then ()
      else if Ctx.isEmpty ctx2 then raise NotValid
      else
        let (v1,x1),t1 = Ctx.head ctx1, Ctx.tail ctx1 in
        let (v2,x2),t2 = Ctx.head ctx2, Ctx.tail ctx2 in
        if not (v1 = v2) then
          sub c ctx1 t2
        else (Ty.checkEqual c x1 x2;
              sub ctx1 t1 t2)
    in sub (Ctx.empty ()) ctx1 ctx2

  (** Equality of contexts. *)
  let rec checkEqual ctx1 ctx2 =
    let rec equal c (ctx1 : Ctx.t) (ctx2 : Ctx.t) =
      match ((ctx1 :> (cvar * Ty.t) list),
             (ctx2 :> (cvar * Ty.t) list)) with
      | [],[] -> ()
      | _::_, _::_ ->
         let ((v1,x1),t1) = (Ctx.head ctx1, Ctx.tail ctx1) in
         let ((v2,x2),t2) = (Ctx.head ctx2, Ctx.tail ctx2) in
         if not (v1 = v2) then raise NotValid;
         Ty.checkEqual c x1 x2;
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
    | (x,t)::c ->
       Printf.sprintf "(%s,%s) %s"
	 (CVar.to_string x)
         (Ty.to_string t)
         (to_string c)
end


   (* -- Pasting schemes are specific contexts
    -- They are provided with 	    
	 - makers (normalization and well-definedness)
	 - equality decision procedure
	 - specific operations (height, dimension, source, target)
    *)
(** Operations on pasting schemes. *)
and PS
    :
sig
  type t = private
         | PNil of (cvar * Ty.t)
         | PCons of t * (cvar * Ty.t) * (cvar * Ty.t)
         | PDrop of t

  (* Maker *)
  val mk : Ctx.t -> t

  (* Syntactic properties *)
  val free_vars : t -> cvar list
  (* val to_expr : t -> (var * Expr.ty) list *)

  (* Structural operations *)
  val height : t -> int
  val dim : t -> int
  val source : int -> t -> t
  val target : int -> t -> t
  val shape : t -> pshape
  val suspend : t -> int -> t
       
  (* Printing *)
  val to_string : t -> string
end
  =
struct
  exception Invalid

  (** A pasting scheme. *)
  type t =
    | PNil of (cvar * Ty.t)
    | PCons of PS.t * (cvar * Ty.t) * (cvar * Ty.t)
    | PDrop of PS.t

     (* --------------------
      Syntactic properties
      -------------------- *)
  (** Domain of definition. *)
  (* TODO: rename to domain. *)
  (* TODO: check whether this is useful. *)
  let free_vars ps = Ctx.free_vars (Ctx.of_ps ps)
		      
  (* -----
    Maker
    ----- *)
  (** Dangling variable. *)
  let rec marker ps =
    match ps with
    | PNil (x,t) -> x,t
    | PCons (ps,_,f) -> f
    | PDrop ps ->
       let f,tf = marker ps in
       let open Ty in
       let open Tm in
       match tf.e with
       | Ty.Arr (_,x,{e = Tm.CVar y}) ->
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
  let mk (l : Ctx.t) : t =
    let open Ty in 
    let rec close ps tx =
      match tx.e with
      | Obj -> ps
      | Arr (tx,_,_) -> close (PDrop ps) tx
    in
    let x0,ty,l =
      match (l :> (cvar*Ty.t) list) with
      | (x,ty)::l when ty.e = Obj -> x,ty,l
      | _ -> raise Invalid
    in
    let rec aux ps = function
      | (y,ty)::(f,tf)::l ->
         begin
           let open Tm in
           let open Ty in
           match tf.e with
           | Arr (_, {e = CVar fx}, {e = CVar fy}) ->
              if (y <> fy) then raise Invalid;
              let x,tx = marker ps in
              if x = fx then
                let fvps = PS.free_vars ps in
                if (List.mem f fvps) then raise (DoubledVar (CVar.to_string f));
                if (List.mem y fvps) then raise (DoubledVar (CVar.to_string y));
                let ps = PCons (ps,(y,ty),(f,tf)) in
                aux ps l
                else
                  aux (PDrop ps) ((y,ty)::(f,tf)::l)
           | _ -> raise Invalid
         end
      | [x,tx] -> raise Invalid
      | [] ->
	 let x,tx = marker ps in close ps tx 
    in
    aux (PNil (x0,ty)) l

     (* ---------------------
      Structural operations
      --------------------- *)
  (** Height of a pasting scheme. *)
  let rec height = function
    | PNil _ -> 0
    | PCons (ps,_,_) -> height ps + 1
    | PDrop ps -> height ps - 1

  (** Dimension of a pasting scheme. *)
  let rec dim = function
    | PNil _ -> 0
    | PCons (ps,_,_) -> max (dim ps) (height ps + 1)
    | PDrop ps -> dim ps

  (** Source of a pasting scheme. *)
  let source i ps =
    assert (i >= 0);
    let rec aux = function
      | PNil _ as ps -> ps
      | PCons (ps,_,_) when height ps >= i -> aux ps
      | PCons (ps,y,f) -> PCons (aux ps,y,f)
      | PDrop ps when height ps > i -> aux ps
      | PDrop ps -> PDrop (aux ps)
    in
    aux ps

  (** Target of a pasting scheme. *)
  let target i ps =
    assert (i >= 0);
    let replace g = function
      | PNil x -> PNil g
      | PCons (ps,y,f) -> PCons (ps,y,g)
      | _ -> assert false
    in
    let rec aux = function
      | PNil _ as ps -> ps
      | PCons (ps,_,_) when height ps > i -> aux ps
      | PCons (ps,y,f) when height ps = i -> replace y (aux ps)
      | PCons (ps,y,f) -> PCons (aux ps,y,f)
      | PDrop ps when height ps > i -> aux ps
      | PDrop ps -> PDrop (aux ps)
    in
    aux ps

  (* TODO: remove shapes *)
  let rec shape ps =
    match ps with
    |PNil _ -> PShape.PNil
    |PCons (ps,_,_) -> PShape.PCons (shape ps)
    |PDrop ps -> PShape.PDrop (shape ps)

  (** Suspend a pasting scheme. *)
  (* TODO: implement this more efficiently *)
  let rec suspend ps i =
    mk (Ctx.suspend (Ctx.of_ps ps) i)
       
  (* --------
     Printing
     -------- *)
  (** String representation of a pasting scheme. *)
  let to_string ps =
    if !abbrev
    then
      Ctx.to_string (Ctx.of_ps ps)
    else
      let rec print ps = 
	match ps with
	|PNil (x,t) ->
	  Printf.sprintf "[(%s,%s)]"
	    (CVar.to_string x)
	    (Ty.to_string t)
	|PCons (ps,(x1,t1),(x2,t2)) ->
	  Printf.sprintf "%s [(%s,%s) (%s,%s)]"
	    (print ps)
	    (CVar.to_string x1)
	    (Ty.to_string t1)
	    (CVar.to_string x2)
	    (Ty.to_string t2)
	|PDrop ps ->
	  Printf.sprintf " %s ! "
	    (print ps)
      in print ps	  
end

   (* -- Environnement is a association list of variable and coherences
    -- It is provided with 	    
	 - maker 
	 - association
    *)    
(** Operations on environments. *)
and Env
    :
sig
  type t
  val env : t ref
       
  (* Makers *)
  val init : unit
  val add : var -> Ctx.t -> Expr.ty -> unit

  (* Structural operation *)
  val val_var : evar -> int -> Coh.t
end
  =
struct
  (** An environment associates to each environment variable a coherence with
     various possible suspensions. *)
  type t = (evar * ((int * Coh.t) list)) list

  (** The environment, i.e. the list of defined variables. *)
  let env = ref ([] :> t)

  (* ------
     Makers
    ------ *)
  (** Initialize the environment. *)
  (* TODO: take a unit argument............*)
  let init = env := []

  (** Add a variable together with the corresponding coherence (i.e. the pasting scheme and the output type). *)
  (* TODO: take a coherence as argument *)
  let add x ps u =
    let u = 
      let c = PS.mk ps in
      Coh.mk c u in
    env := (EVar.mk x,[0,u])::!env

  (* --------------------
     Structural operation
     -------------------- *)	     
  (** Coherence associated to a variable. The second argument is the number of
     times we want to suspend. *)
  let val_var x i =
    let rec replace a b l =
      match l with
      | (x,y)::l when x = a -> (x,b)::(replace a b l)
      | (x,y)::l -> (x,y)::(replace a b l)
      | [] -> []
    in
    let cohfamily =
      try List.assoc x !env
      with Not_found -> raise (UnknownCoh (EVar.to_string x))
    in
    try List.assoc i cohfamily
    with Not_found ->
      let coh = try List.assoc 0 cohfamily with Not_found -> assert false in
      let ps = Coh.ps coh in
      let t = Ty.reinit (Coh.target coh) in
      let ps = PS.suspend ps i in
      let newcoh = (Coh.mk ps t) in
      env := replace x ((i,newcoh)::cohfamily) (!env); 
      newcoh
end

and Ty
    :
sig
  type expr = 
    | Obj
    | Arr of t * Tm.t * Tm.t
  and t = {c : Ctx.t; e : expr}
           
  val free_vars : t -> cvar list
  val to_string : t -> string

  val check : Ctx.t -> t -> unit
  val checkEqual : Ctx.t -> t -> t -> unit
  val mk : Ctx.t -> Expr.ty -> t
       
  val dim : t -> int
  val reinit : t -> Expr.ty
end
  =
struct
  (** A type exepression. *)
  type expr =
    | Obj
    | Arr of t * Tm.t * Tm.t
  and t = {c : Ctx.t; e : expr}

  exception Unknown

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

  (** Ensure that a type is well-formed in given context. *)
  let rec check ctx ty =
    try Ctx.checkSubCtx ty.c ctx with
    | _ -> check_hidden ctx ty.e
  and check_hidden ctx tye =
    match tye with
    | Obj -> ()
    | Arr (t,u,v) ->
       check ctx t;
       Tm.checkType ctx u t;
       Tm.checkType ctx v t

  (** Test for equality. *)
  let rec checkEqual ctx ty1 ty2 =
    (* debug "checking equality between %s and %s" (to_string ty1)(to_string ty2); *)
    let equal = checkEqual ctx in
    match ty1.e, ty2.e with
    |Obj,Obj -> ()
    |Arr(t1,u1,v1),Arr(t2,u2,v2) ->
      equal t1 t2; Tm.checkEqual ctx u1 u2; Tm.checkEqual ctx v1 v2
    |(Obj |Arr _),_ ->
      raise (NotEqual (to_string ty1, to_string ty2))

  (** Construct a type. *)
  let rec mk c (e : Expr.ty) =
    let already_known = Hashtbl.find_all Hash.tbty e in
    let rec aux l = match l with
      | [] -> raise Unknown
      | ty::q -> try Ctx.checkSubCtx ty.c c; ty with
                 |_ -> aux q
    in
    let open Expr in
    try aux already_known
    with Unknown ->
      let newty = 
        match e with
        | Obj -> {c = c; e = Obj}
        | Arr (u,v) ->
           let u,tu = Tm.mk c u in
           let v,tv = Tm.mk c v in
           let () = checkEqual c tu tv in {c = c; e = Arr(tu,u,v)}
        | Ty ty -> Ctx.checkSubCtx ty.c c; ty
      in Hashtbl.add Hash.tbty e newty; newty

  (** Dimension of a type. *)
  let rec dim ty =
    match ty.e with
    | Obj -> 0
    | Arr(a,t,u) -> 1 + dim a

  (** Expression from a type. *)
  (* TODO: can we remove this? *)
  let rec reinit t : Expr.ty =
    let open Expr in
    match t.e with
    | Obj -> Obj
    | Arr(_,u,v) -> Arr (Tm.reinit u, Tm.reinit v)
end

(** Operations on terms. *)
and Tm
    :
sig
  type expr = 
    | CVar of cvar
    | Sub of Cut.t * Sub.t
  and t = {c : Ctx.t; ty : Ty.t; e : expr}
           
  val free_vars : t -> cvar list
  val to_string : t -> string

  val infer : Ctx.t -> t -> Ty.t
  val checkEqual : Ctx.t -> t -> t -> unit
  val checkType : Ctx.t -> t -> Ty.t -> unit
  val mk : Ctx.t -> Expr.tm -> t * Ty.t
       
  val reinit : t -> Expr.tm
end
  =
struct
  (* TODO: change Cut to EVar *)
  (** An expression. *)
  type expr =
    | CVar of cvar (** a context variable *)
    | Sub of Cut.t * Sub.t (** a substituted environment variable *)
  (** A term, i.e. an expression with given type in given context. *)
  and t = {c : Ctx.t; ty : Ty.t; e : expr}

  exception Unknown
             
  let rec free_vars tm =
    match tm.e with
    | CVar x -> [x]
    | Sub (_,sub) -> Sub.free_vars sub
                     
  let rec to_string tm =
    match tm.e with
    | CVar x -> CVar.to_string x
    | Sub (t,s) -> let ps = Cut.ps t in Printf.sprintf "(%s %s)" (Cut.to_string t) (Sub.to_string s (PS.shape ps))

  let rec checkEqual ctx tm1 tm2 =
    (* debug "checking equality between %s and %s" (to_string tm1)(to_string tm2); *)
    match tm1.e, tm2.e with
    | CVar x,CVar y ->
      if not (x = y)
      then
	raise (NotEqual (to_string tm1, to_string tm2))
      else ()
    | Sub(t1,s1),Sub(t2,s2) ->
      let tar = Cut.checkEqual t1 t2 in
      Sub.checkEqual tar s1 s2
    | (CVar _|Sub _),_ ->
      raise (NotEqual (to_string tm1, to_string tm2))

  (** Infer the type of an expression. *)
  (* TODO: why do we need this? *)
  let infer_expr ctx tme =
    match tme with
    | CVar x -> Ctx.ty_var ctx x
    | Sub (e,s) ->
       let tar,ty = Cut.infer e in
       Sub.check s ctx tar;
       Sub.applyTy s tar ctx ty

  (** Infer the type of a term. *)
  let infer ctx tm =
    try Ctx.checkSubCtx tm.c ctx; tm.ty
    with _ -> infer_expr ctx tm.e

  (** Check that term has given type. *)
  let checkType ctx e t  =
    Ty.checkEqual ctx (infer ctx e) t

  (* TODO: do we really need this? *)
  let rec reinit tm : Expr.tm =
    let open Expr in
    match tm.e with
    | CVar v -> Var (CVar.to_var v)
    | Sub (t,s) -> Sub (Cut.reinit t, Sub.reinit s (PS.shape (Cut.ps t)))

  (** Create a term from an expression. *)
  (* TODO: return a value of type t instead of a pair *)
  let rec mk c e =
    let already_known = Hashtbl.find_all Hash.tbtm e in
    let rec aux l = match l with
      | [] -> raise Unknown
      | tm::q -> try Ctx.checkSubCtx tm.c c; (tm, tm.ty) with _ -> aux q
    in
    let open Expr in
    try aux already_known
    with Unknown ->
      let newtm,newty = 
        match e with
        | Var v ->
           let e = CVar (CVar.mk v) in
           let ty = infer_expr c e in
           ({c = c; ty = ty; e = e}, ty)
        | Sub (t,s) ->
           let t,tar = Cut.mk t (Sub.dim c s) in
           let s = Sub.mk s c tar in
           let e : expr = Sub (t,s) in
           let ty = infer_expr c e in
           ({c = c; ty = ty; e = e}, ty)
        | Tm tm -> try Ctx.checkSubCtx tm.c c; (tm, tm.ty)
                  with _ -> mk c (Tm.reinit tm)        
      in Hashtbl.add Hash.tbtm e newtm; newtm,newty
end

(* TODO: remove this *)
and Cut
    :
sig
  type t =
    | Fold of evar * int
  val to_string : t -> string
  val checkEqual : t -> t -> Ctx.t
  val infer : t -> Ctx.t * Ty.t
  val mk : Expr.tm -> int -> (t * PS.t)
  val reinit : t -> Expr.tm 
  val ps : t -> PS.t
end
  =
struct
  type t = 
    | Fold of evar * int (** an environment variable together with the number of times it was suspended *)

     let rec repeat s k =
       if k = 0 then "" else s^(repeat s (k-1))
       
     let to_string coh =
       match coh with
       |Fold (x,i) ->
         if !print_lifting then
           EVar.to_string x ^ (repeat "°" i)
         else EVar.to_string x
	
     let checkEqual e1 e2 =
       match e1, e2 with
       |Fold (x,i), Fold (y,j) -> Coh.checkEqual (Env.val_var x i) (Env.val_var y j)

     let infer coh =
       match coh with
       |Fold (x,i) ->
         let coh = Env.val_var x i in
         (Ctx.of_ps (Coh.ps coh), Coh.target coh)

     let ps coh =
       match coh with
       |Fold (x,i) -> let coh = Env.val_var x i in
                      Coh.ps coh
                      
     let mk e i =
       let open Expr in
       match e with
       |Var v ->
         let coh = Env.val_var (EVar.mk v) 0 in
         let ps = Coh.ps coh in
         let j = PS.dim ps in
         if j<=i then 
           let coh = Env.val_var (EVar.mk v) (i-j) in
           let ps = Coh.ps coh in
           (Fold ((EVar.mk v),i-j), ps)
         else failwith "arguments of the coherence have dimension too low"
       |Tm tm -> assert (false) (* TODO *)
       |(Sub _) -> raise BadUnderSub

     let reinit c : Expr.tm =
       let open Expr in
       match c with
       |Fold (v,i) -> Var (EVar.to_var v)                      
   end

(* -- Module with a specific type for well-defined coherences
    -- They are different from normal type, they need to be substituted *)    
(** A coherence. *)
and Coh    
    : sig
  type t = private (PS.t * Ty.t)   

  val mk : PS.t -> Expr.ty -> t
  val to_string : t -> string
  val checkEqual : t -> t -> Ctx.t
  val ps : t -> PS.t
  val target : t -> Ty.t
end
=
struct
  type t = PS.t * Ty.t
	    
  let check ps t = 
    if List.included (PS.free_vars ps) (Ty.free_vars t)
    then (ps,t)
    else
      let open Ty in
      let a,f,g = match t.e with
        |Arr(a,f,g) -> (a,f,g)  
        |_ -> raise NotAlgebraic
      in
      let i = PS.dim ps in
      let pss = PS.source (i-1) ps
      and pst = PS.target (i-1) ps in
      let ctxs = Ctx.of_ps pss
      and ctxt = Ctx.of_ps pst in
      let fvf = List.union (Tm.free_vars f) (Ty.free_vars a)
      and fvg = List.union (Tm.free_vars g) (Ty.free_vars a) in
      try
	let tf = Tm.infer ctxs f in
	let tg = Tm.infer ctxt g in
	begin
	  Ty.check ctxs tf;
	  Ty.check ctxt tg;
	  if List.included (PS.free_vars pss)
	       fvf &&
	       List.included (PS.free_vars pst)
		 fvg
	  then (ps,t) 
	  else raise NotAlgebraic
	end;
      with
      |UnknownId _ -> raise NotAlgebraic
		       
  let mk ps t =
    let t = Ty.mk (Ctx.of_ps ps) t in
    check ps t

  let to_string (ps,t) =
    Printf.sprintf "Coh {%s |- %s}"
      (PS.to_string ps)
      (Ty.to_string t)

  let checkEqual (ps1,t1) (ps2,t2) =
    let c1 = Ctx.of_ps ps1 and c2 = Ctx.of_ps ps2 in
    Ctx.checkEqual c1 c2;
    Ty.checkEqual c1 t1 t2; c1

  let ps (ps,t) = ps

  let target (ps,t) = t
end

(** Operations on raw terms. *)
and Expr
    :
sig
  type ty =
    | Obj
    | Arr of tm * tm
    | Ty of Ty.t        
  and tm =     
    | Var of var
    | Sub of tm * (tm list)
    | Tm of Tm.t

  val string_of_ty : ty -> string
  val string_of_tm : tm -> string

  val reinit : tm -> tm
  val unify_ty : Ctx.t -> ty -> ty -> ((Var.t * ty) * tm option * bool) list -> ((Var.t * ty) * tm option * bool) list
end
  =
struct
  type ty =
    | Obj
    | Arr of tm * tm
    | Ty of Ty.t        
  and tm =     
    | Var of var
    | Sub of tm * (tm list)
    | Tm of Tm.t

  exception UnableUnify
             
  let rec string_of_ty e =
    match e with
    | Obj -> "*"
    | Arr (u,v) ->
       Printf.sprintf "%s -> %s"
	 (string_of_tm u)
	 (string_of_tm v)
    | Ty ty -> Ty.to_string ty
  and string_of_tm e =
    match e with
    |Var x -> Var.to_string x
    |Sub (t,s) ->
      Printf.sprintf "(%s %s)"
	(string_of_tm t)
	(string_of_sub s)
    |Tm tm -> Tm.to_string tm

  and string_of_sub s =
    match s with
    |[] -> ""
    |t::[] -> Printf.sprintf "%s" (string_of_tm t)
    |t::s -> Printf.sprintf "%s %s"
	       (string_of_tm t)
               (string_of_sub s)

  let rec print l =
    match l with
    |(t::q) -> string_of_tm t ^ " " ^ print q
    |[] -> ""

  (** Remove partly verified terms. *)
  (* TODO: remove this *)
  let rec reinit tm =
    match tm with
    | Var _ -> tm  
    | Sub (tm,s) -> Sub (reinit tm, List.map reinit s)
    | Tm tm -> Tm.reinit tm

  (* TODO: document l *)
  let rec unify_tm (c : Ctx.t) (tm1 : tm) (tm2 : tm) l =
    (* debug "unifying %s with %s" (string_of_tm tm1) (string_of_tm tm2); *)
    match tm1 ,tm2 with
    | Var u, _ ->
       let rec replace l =
         match l with
         | (((v,ty), None, _)::l) when u = v -> ((v,ty), Some (Expr.Tm (fst (Tm.mk c tm2))), true)::l 
         | ((((v,ty), Some tm, _)::_) as l) when u = v -> l
         (* TODO : check compatibility between the constraints *)
         | a::l -> a::(replace l)
         | [] -> []
       in
       replace l
    | Sub(e,s), Sub (e',s') ->
       let rec aux s s' l =
         match s,s' with
         | (a::s),(a'::s') -> let l = unify_tm c a a' l in aux s s' l 
         | [],[] -> l
         | _,_ -> raise UnableUnify
       in
       aux s s' l
    | Tm _, _ -> assert false
    | _, Tm _ -> assert false
    | _, Var _ -> raise UnableUnify
                  
  let unify_ty (c : Ctx.t) (ty1 : ty) (ty2 : ty) l =
    match ty1 ,ty2 with
    | Obj, _ -> l
    | Arr(u,v), Arr(u',v') ->
       let l = unify_tm c u u' l
       in unify_tm c v v' l
    | Ty ty2, _ -> assert(false)
    | _, Ty _ -> assert(false)
    | _, _ -> raise UnableUnify
end

and Hash
    : sig
  val tbty : (Expr.ty, Ty.t) Hashtbl.t 
  val tbtm : (Expr.tm, Tm.t) Hashtbl.t 
end
  =
struct
  let tbty : (Expr.ty, Ty.t) Hashtbl.t = Hashtbl.create 10000
  let tbtm : (Expr.tm, Tm.t) Hashtbl.t = Hashtbl.create 10000
end

type kTm = Tm.t
type kTy = Ty.t

    
type env = Env.t
type ctx = Ctx.t
type ty = Expr.ty
type tm = Expr.tm
let string_of_ty = Expr.string_of_ty
let string_of_tm = Expr.string_of_tm
            
let init_env = Env.init
let add_env = Env.add
                
let mk_ctx = Ctx.mk
let mk_tm c e = let e,t = Tm.mk c e in Expr.Tm e, Expr.Ty t
let mk_ty c e = Expr.Ty (Ty.mk c e)
                        
let checkEqual c ty1 ty2 =
  let ty1 = Ty.mk c ty1 in
  let ty2 = Ty.mk c ty2 in
  Ty.checkEqual c ty1 ty2
              
let reinit = Expr.reinit

let unify c a b l =
  match b with
  |Expr.Tm b -> Expr.unify_ty c a (Ty.reinit (Tm.infer c b)) l
  |_ -> assert(false)    
