open Stdlib
open Settings
open Common
open PShape

(** Variables, before distinction between environment or context variables. *)
module Var = struct
  type t =
  | Name of string
  | New of int
	     
  let to_string v =
    match v with
    | Name s -> s
    | New i -> "_" ^ string_of_int i

  let make s = Name s
end

(** Environment variables (i.e. defined coherences). *)
module EVar
: sig
  type t
  val to_string : t -> string
  val make : Var.t -> t
  val to_var : t -> Var.t
end
=
struct
  type t = Var.t

  let to_string v =
    Var.to_string v

  let make v = v

  let to_var v = v
end

(** Context variables (i.e. "arguments of functions"). *)
module CVar
: sig 
    type t
    val to_string : t -> string
    val make : Var.t -> t
    val to_var : t -> Var.t
end
=
struct
  type t = Var.t

  let to_string v =
    Var.to_string v
	       
  let make v = v

  let to_var v = v 
end

type var = Var.t
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

  (* Structural functions *)
  val mk : Expr.tm list -> Ctx.t -> Ctx.t  -> t
  val mk_elaborated : Expr.tm list -> Ctx.t -> Ctx.t -> t 
  val value : t -> Tm.t list
  val reinit : t -> Ctx.t -> Expr.tm list
  val list_expl_vars : t -> Ctx.t -> Var.t list
	   
  (* Syntactic properties *)		    
  val free_vars : t -> cvar list
  val apply_Ty : t -> Ctx.t -> Ctx.t -> Ty.t -> Ty.t
  val apply_Tm : t -> Ctx.t -> Ctx.t -> Tm.t -> Tm.t
  val dim : Ctx.t -> Expr.tm list -> int
           
  (* Equality procedures *)
  val check_equal : Ctx.t -> t -> t -> unit

  (* Printing *)	
  val to_string : t -> Ctx.t -> string
	   
  (* Well-definedness procedure *)
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
    |_,_ when Ctx.is_empty tar ->
      raise (UnknownId (CVar.to_string x))
    |t::l, _ ->
      let open Tm in
      let (((y,_),_),tar) = (Ctx.head tar, Ctx.tail tar) in
      if y = x
      then t.e
      else apply_var l tar x
    |[], _ -> assert false

  let rec to_string (s:t) (c:Ctx.t) =
    match s,c with
    | [], c when Ctx.is_empty c -> ""
    | (u::s),c -> begin
        match Ctx.head c with
        | (_, Some true| _, None) -> Printf.sprintf "%s %s" (to_string s (Ctx.tail c)) (Tm.to_string u) 
        | _, Some false -> Printf.sprintf "%s" (to_string s (Ctx.tail c))
      end
    | _ -> assert false

  let rec print_list (s:t) =
    match s with
    |[] -> ""
    |(u::s) -> Printf.sprintf "%s %s" (print_list s) (Tm.to_string u)
                  
  (** Sequential composition of substitutions. *)
  let rec compose src tar s (s':t) =
    let open Expr in
    List.rev (List.map (fun t -> Tm (apply_Tm s tar src t)) s')
  (** Apply a substitution to a term. *)
  and apply_Tm (s:t) tar src tm =
    (* debug "applying substitution %s from source %s to target %s" (print_list s) (Ctx.to_string tar) (Ctx.to_string src); *)
    let open Tm in
    Ctx.check_sub_ctx (tm.c) tar;
    (* Ctx.checkEqual (tm.c) tar; *)
    let e =
      match tm.e with
      |CVar x -> apply_var s tar x
      |Sub (t,s') ->
        let newtar = Cut.ctx t in 
        Sub (t, Sub.mk_elaborated (compose src tar s (s' :> Tm.t list)) src newtar)
    in {c = src; ty = apply_Ty s tar src (Tm.infer tar tm); e = e}
  (** Apply a substitution to a type. *)
  and apply_Ty (s:t) tar src ty =
    let open Ty in
    Ctx.check_sub_ctx (ty.c) tar;
    let e = 
      match ty.e with
      | Obj -> Obj
      | Arr (a,u,v) -> Arr (apply_Ty s tar src a, apply_Tm s tar src u, apply_Tm s tar src v)
    in {c = src; e = e}

    (* -----------------
	Typing procedures
        -----------------  *)
  (** Check equality of substitutions. *)
  let rec check_equal ctx (s1:t) (s2:t) = 
    match s1,s2 with
    | [],[] -> ()
    | t1::s1,t2::s2 ->
       Tm.check_equal ctx t1 t2;
       check_equal ctx s1 s2
    | _,_ -> raise NotValid

  (* TODO: use String.concat *)
  let rec print l =
    match l with
    | (t::q) -> Tm.to_string t ^ " " ^ print q
    | [] -> ""

  (** Check that a substitution is well-formed with given source and target. *)
  let rec check (s:t) src (tar:Ctx.t) =
    (* debug "substitution %s" (print s); *)
    match s,Ctx.value tar
    with
    | [],[] -> ()
    | (_::_,[] |[],_::_) -> raise NotValid
    | t::s,_ ->
       let (((x,u),_),tar) = (Ctx.head tar,Ctx.tail tar) in
       check s src tar;
       Ty.check tar u;
       (* debug "checking that term %s \n has type %s" (Tm.to_string t) (Ty.to_string (applyTy s tar src u)); *)
       Tm.check_type src t (apply_Ty s tar src u)
	
    (*  --------
	Printing
        --------  *)
  (** String representation of a substitution. We need a pasting scheme
     representation of the target in order to print only cells of locally
     maximal dimension. *)
  (* TODO: use a full pasting scheme and remove "pasting shapes" *)
  (* let to_string (s:t) ps = *)
  (*   match s,ps with *)
  (*   | u::[], PNil -> Printf.sprintf "%s" (Tm.to_string u) *)
  (*   | _,_ -> *)
  (*      let rec aux s ps =  *)
  (*        if !implicit_print then *)
  (*          match s,ps with *)
  (*          | u::_::s, PDrop (PCons (ps)) -> *)
  (*             let ps = aux s ps in *)
  (*             let u = Tm.to_string u in *)
  (*             if ps = "" then u else ps ^ " " ^ u *)
  (*          | s , PDrop ps -> aux s ps *)
  (*          | u::_::s , PCons ps -> aux s ps *)
  (*          | s,PNil -> "" *)
  (*          | _,_ -> assert(false) *)
  (*        else *)
  (*          match s with *)
  (*          | [] -> "" *)
  (*          | u::s -> *)
  (*             Printf.sprintf "%s %s" *)
  (*               (aux s ps) *)
  (*               (Tm.to_string u) *)
  (*      in aux s ps *)



              
    (*  --------------------
	Structural functions
        --------------------  *)
  (** Given a list of terms of maximal dimension, complete it into a
     full-fledged substitution. *)
  (* let elaborate l src (tar : Ctx.marked) : t = *)
  (*   (\** Close downwards. *\) *)
  (*   let rec complete l x ty ps = *)
  (*     match ps with *)
  (*     | PNil -> *)
  (*        [x] *)
  (*     | PCons ps-> *)
  (*        let a',x',y' = *)
  (*          let open Ty in *)
  (*          match ty.e with *)
  (*          |Arr(a',x',y') -> a',x',y' *)
  (*          |_ -> assert(false) *)
  (*        in *)
  (*        x::y'::(complete l x' a' ps) *)
  (*     | (PDrop _) as ps -> find_max l ps *)
  (*   (\** Find next maximal term and close it downwards. *\) *)
  (*   and find_max l ps = *)
  (*     match l,ps with *)
  (*     | x::[], PNil -> *)
  (*        let x,_ = Tm.make src x in *)
  (*        [x] *)
  (*     | [],_ -> raise NotValid *)
  (*     |  _, PNil -> raise NotValid *)
  (*     | f::l, PDrop(PCons(ps)) -> *)
  (*        let f,_ = Tm.make src f in *)
  (*        let a,x,y = *)
  (*          let open Ty in *)
  (*          match (Tm.infer src f).e with *)
  (*          |Arr(a,x,y) -> a,x,y *)
  (*          |_ -> assert false *)
  (*        in *)
  (*        let s = complete l x a ps in *)
  (*        f::y::s *)
  (*     | s,PDrop ps -> find_max s ps *)
  (*     | s, PCons _ -> assert false *)
  (*   in *)
  (*   let s = find_max (List.rev l) (PS.shape tar) in *)
  (*   check s src tar; *)
  (*   s *)


  let rec print_list l = match l with
    |(t::q) -> Printf.sprintf "%s %s" (Expr.string_of_tm t) (print_list q) 
    |[] -> ""
  (* TODO : implement elaboration  of substitution with a marked context*)
  exception Completed of ((Var.t * Expr.ty) * Expr.tm option * bool) list
  let elaborate (l: Expr.tm list) src tar : Expr.tm list =
    (* debug "elaborating list %s in target context %s" (print_list l) (Ctx.to_string tar); *)
    let rec create_assoc tar l =
      match l with
      | (h::l')as l ->
         if Ctx.is_empty tar then failwith (Printf.sprintf "too many arguments given");
         let t = Ctx.tail tar in
         begin
           match Ctx.head tar with
           |a, Some false -> ((var_of_cvar (fst a), Ty.reinit (snd a)), None, false)::(create_assoc t l)
           |a, Some true -> ((var_of_cvar (fst a), Ty.reinit (snd a)), Some h, true)::(create_assoc t l')
           |_,None -> assert false
         end
      | [] -> if Ctx.is_empty tar then []
              else match Ctx.head tar with
                   |a, Some false -> ((var_of_cvar (fst a), Ty.reinit (snd a)), None, false)::(create_assoc (Ctx.tail tar) [])
                   |_, Some true -> failwith "not enough arguments given"
                   |_,None -> assert false
    in
    let rec next l res =
      match l with
      | ((a,Some b,true)::l) -> ((a, snd a),b, ((a,Some b, false)::l))
      | ((a,None,true)::l) -> assert(false)
      | (h::l) -> let (x,y,z) = next l res in (x,y,h::z)
      | [] -> raise (Completed res)
    in
    let rec loop assoc =
      let (a,b,assoc) = next assoc assoc in
      let assoc = Expr.unify_ty src (snd a) (Ty.reinit (snd (Tm.make src b))) assoc
      in loop (assoc)
    in
    let rec clear l =
      match l with
      | (((a,_),Some b,_)::l) -> b :: (clear l)
      | ((a, None,_)::_) -> assert(false)
      | [] -> []
    in
    let assoc = create_assoc tar l in
    try loop assoc
    with Completed res -> clear res
                                
              

  (** Construct a substutition (which is already closed downward). *)
  let mk_elaborated l src (tar : Ctx.t) =
    (* debug "building substitution %s in source %s and target %s" (print_list l) (Ctx.to_string src) (Ctx.to_string tar); *)
    let rec aux l (tar : Ctx.t) =
      match l,Ctx.value tar with
      |[],[] -> []
      |(_::_,[] |[],_::_) -> raise NotValid
      |t::s,_ ->
	let ((x,u),_),tar = (Ctx.head tar,Ctx.tail tar) in
	let s = aux s tar in
	let t,ty = Tm.make src t in
	let () = Ty.check_equal src ty (apply_Ty s tar src u)
	in t::s
    in aux (List.rev l) tar

  (** Create a substitution described by maximal elements. *)
  let mk l src tar =
    let list = elaborate (List.rev l) src tar in
    mk_elaborated (List.rev list) src tar

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
    (* debug "computing dimension of list %s" (print_list l); *)
    let l = List.map (fun x -> Ty.dim (snd (Tm.make ctx x))) l in
    match l with
    | t::l -> max l t
    | [] -> raise EmptySub

  (** Keep only the the maximal elements of a substitution ("unealborate"). *)
  (* let reinit (s:t) ps = *)
  (*   match s,ps with *)
  (*   |u::[], PNil -> [Tm.reinit u] *)
  (*   |_,_ -> *)
  (*     let rec aux s ps =  *)
  (*       match s,ps with *)
  (*       |u::_::s, PDrop (PCons (ps)) -> (Tm.reinit u) :: (aux s ps) *)
  (*       |s , PDrop ps -> aux s ps *)
  (*       |u::_::s , PCons ps -> aux s ps *)
  (*       |s,PNil -> [] *)
  (*       |_,_ -> assert(false) *)
  (*     in List.rev(aux s ps) *)


  let reinit (s:t) c =
    let rec aux s c = 
      match s,c with
      |[], c when Ctx.is_empty c -> []
      |(u::s),c -> begin
          match Ctx.head c with
          |(_, Some true | _, None) -> (Tm.reinit u)::(aux s (Ctx.tail c)) 
          |_, Some false -> aux s (Ctx.tail c)
        end
      |_,_ -> assert false
      in List.rev (aux s c)

  (** List the explicit variables of a substitution. *)
  (* let list_expl_vars (s:t) ps = *)
  (*   match s,ps with *)
  (*   |u::[], PNil -> Tm.list_expl_vars u *)
  (*   |_,_ -> *)
  (*     let rec aux s ps =  *)
  (*       match s,ps with *)
  (*       |u::_::s, PDrop (PCons (ps)) -> (Tm.list_expl_vars u) @ (aux s ps) *)
  (*       |s , PDrop ps -> aux s ps *)
  (*       |u::_::s , PCons ps -> aux s ps *)
  (*       |s,PNil -> [] *)
  (*       |_,_ -> assert(false) *)
  (*     in (aux s ps) *)

  let list_expl_vars (s:t) c =
    let rec aux s c = 
      match s,c with
      |[], c when Ctx.is_empty c -> []
      |(u::s),c -> begin
          match Ctx.head c with
          |(_, Some true | _, None) -> (Tm.list_expl_vars u)@(aux s (Ctx.tail c)) 
          |_, Some false -> aux s (Ctx.tail c)
        end
      |_,_ -> assert false
      in (aux s c)
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
  type t
                     
  (* Makers *)
  val empty : unit -> t
  val add : t -> Var.t -> Expr.ty -> t
  val add_norm : t -> Var.t -> Ty.t -> t
  val make : (Var.t * Expr.ty) list -> t
  val of_ps : PS.t -> t
       
  (* Structural operations *)
  val head : t -> (cvar * Ty.t) * bool option
  val tail : t -> t
  val suspend : t -> int -> t
       
  (* Syntactic properties *)
  val ty_var : t -> cvar -> Ty.t
  val domain : t -> cvar list
  val value : t -> (cvar * Ty.t) list
  val mem : t -> cvar -> bool
  val dim : t -> int

  (* Equality procedure *)
  val is_empty : t -> bool
  val check_sub_ctx : t -> t -> unit
  val check_equal : t -> t -> unit

  val mark : Ctx.t -> Ctx.t
                                
  (* Printing *)
  val to_string : t -> string
end
  =
struct
  (** A context. *)
  (* TODO: reverse the order of lists *)
  type ctx_list = (cvar * Ty.t) list
  type t = {list : ctx_list; marking : (bool list) option}

  (** type of a variable in a context. *)
  let ty_var (ctx:t) x =
    try
      List.assoc x ctx.list
    with
    | Not_found -> raise (UnknownId (CVar.to_string x))

  (* ------ Makers ------ *)
  (** Empty context. *)
  let empty () = {list = []; marking = None}

  (** adding an already marked term to a context (forgets the marking)*)
  let add_norm (ctx : Ctx.t) x u =
    let x = CVar.make x in
    try
      ignore (List.assoc x (ctx.list :> (CVar.t * Ty.t) list));
      raise (DoubleDef (CVar.to_string x))
    with Not_found -> {list = ctx.list@[x,u]; marking = None}

  (** Add a typed variable to a context. *)
  let add (ctx : Ctx.t) x u : t =
    let u = Ty.make ctx u in
    add_norm ctx x u

  (** Add a variable whose type is already constructed to a context. *)
  let add_norm ctx x u =
    Ty.check ctx u;
    add_norm ctx x u

  (** Create a context from a list of terms. *)
  let rec make l =
    let rec aux l ctx =
      match l with
      | [] -> ctx
      | (x,t)::l ->
	 let ctx = Ctx.add ctx x t in
	 aux l ctx
    in aux l (Ctx.empty ()) 

  (** Create a context from a pasting scheme. *)
  let of_ps ps =
    let open PS in
    match ps with
    |PNil (x,t) -> {list = [(x,t)]; marking = Some ([true])}
    |_ ->
      let rec aux ps =
        match ps with
        |PDrop (PCons (ps,(x1,t1),(x2,t2))) -> let c = aux ps in
                                               let mark = match c.marking with
                                                 |None -> assert false
                                                 |Some mark -> mark
                                               in
                                               {list = (c.list)@[(x1,t1);(x2,t2)]; marking = Some (mark@[false; true])}
        |PDrop ps -> aux ps
        |PCons (ps,(x1,t1),(x2,t2)) -> let c = aux ps in
                                       let mark = match c.marking with
                                         |None -> assert false
                                         |Some mark -> mark
                                       in
                                       {list = (c.list)@[(x1,t1);(x2,t2)]; marking = Some (mark@[false; false])}
        |PNil (x,t) -> {list = [(x,t)]; marking = Some [false]}
      in (aux ps)

  (* ---------------------
      Structural operations
      --------------------- *)

  (* TODO: reverse.........*)
  (** First element of a context. *)
  let rec head ctx = match ctx.list, ctx.marking with
    |[],_ -> assert false
    |a::[], Some (b::[]) -> a,Some b
    |a::[], None -> a,None
    |_::ctx, Some (_::mark) -> head {list = ctx; marking = Some mark}
    |_::ctx, None -> head {list = ctx; marking = None}
    |_,_ -> assert false

  (** Tail of a context. *)
  let rec tail ctx = match ctx.list, ctx.marking with 
    |[],_ -> assert false
    |_::[], Some (_::[]) -> {list = []; marking = Some []}
    |_::[], None -> {list = []; marking = None}
    |a::ctx, Some (b::mark) -> let tl = tail {list = ctx; marking = Some mark} in
                               let tl_mark = match tl.marking with
                                 |None -> assert false
                                 |Some tl_mark -> tl_mark
                               in
                               {list = a::tl.list; marking  = Some (b::tl_mark)}
    |a::ctx, None -> {list = a :: (tail {list = ctx; marking = None}).list; marking = None}
    |_,_ -> assert false

  (** Suspend a context, i.e. rempace types "*" by arrow types (forgets the marking).*)
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
    comp ctx.list ctx'
       
  (* --------------------
     Syntactic properties
     -------------------- *)
  (** Domain of definition of a context. *)
  let domain ctx = List.map fst ctx.list

  let value ctx = ctx.list
    
  (** Check whether a variable belongs to a context. *)
  let mem (c:t) v =
    let rec aux c =  
      match c with
      | [] -> false
      | (x,u)::c when x = v -> true
      | _::c -> aux c
    in aux c.list
	      
  (* -------------------
     Equality procedures
     ------------------- *)
  (** Is a context empty? *)
  let is_empty (c:t) =
    c.list = []

  (** Check whether a context is included in another one. *)
  (* TODO: this is a bit worrying as a function, is it really necessary or can
     we get rid of it? *)
  let check_sub_ctx ctx1 ctx2 =
    (* debug "checking that ctx %s is a sub of %s" (Ctx.to_string ctx1) (Ctx.to_string ctx2); *)
    let rec sub c (ctx1 : Ctx.t) (ctx2 : Ctx.t) =
      if Ctx.is_empty ctx1 then ()
      else if Ctx.is_empty ctx2 then raise NotValid
      else
        let ((v1,x1),_),t1 = Ctx.head ctx1, Ctx.tail ctx1 in
        let ((v2,x2),_),t2 = Ctx.head ctx2, Ctx.tail ctx2 in
        if not (v1 = v2) then
          sub c ctx1 t2
        else (Ty.check_equal c x1 x2;
              sub ctx1 t1 t2)
    in sub (Ctx.empty ()) ctx1 ctx2

  (** Equality of contexts. *)
  let rec check_equal ctx1 ctx2 =
    let rec equal c (ctx1 : Ctx.t) (ctx2 : Ctx.t) =
      match ((ctx1.list :> (cvar * Ty.t) list),
             (ctx2.list :> (cvar * Ty.t) list)) with
      | [],[] -> ()
      | _::_, _::_ ->
         let ((v1,x1),_),t1 = (Ctx.head ctx1, Ctx.tail ctx1) in
         let ((v2,x2),_),t2 = (Ctx.head ctx2, Ctx.tail ctx2) in
         if not (v1 = v2) then raise NotValid;
         Ty.check_equal c x1 x2;
         equal ctx1 t1 t2
      | _,_ -> raise NotValid
    in equal (Ctx.empty ()) ctx1 ctx2
	
  let mark c =
    let rec appears x c = match c with
      |(_,a)::q -> (List.mem x (Ty.free_vars a)) || (appears x q)
      |[] -> false
    in
    let rec traversal c =
      match c with
      |(a::c) -> (not (appears (fst a) c)) :: (traversal c)
      |[] -> []
    in {list = c.list ; marking = Some (traversal (c.list))}
             
     (* --------
      Printing
      -------- *)	      
  (** String representation of a context. *)
  let rec to_string ctx =
    match ctx.list, ctx.marking with
    | [],_ -> ""
    | (x,t)::c, Some (false::mark) ->
       Printf.sprintf "{%s,%s} %s"
	 (CVar.to_string x)
         (Ty.to_string t)
         (to_string {list = c; marking = Some mark})
    | (x,t)::c, Some (true::mark) ->
       Printf.sprintf "(%s,%s) %s"
	 (CVar.to_string x)
         (Ty.to_string t)
         (to_string {list = c; marking = Some mark})
    | (x,t)::c, None ->
       Printf.sprintf "(%s,%s) %s"
	 (CVar.to_string x)
         (Ty.to_string t)
         (to_string {list = c; marking = None})
    | _,_ -> assert false



  (** dimension of a context is the maximal dimension of its variables *)
  let dim ctx =
    let rec aux c i = match c with
      |[] -> i
      |(_,ty)::c when Ty.dim ty>i -> aux c (Ty.dim ty)
      |_::c -> aux c i
    in aux ctx.list 0
                             
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
  val domain : t -> cvar list
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
  let domain ps = Ctx.domain (Ctx.of_ps ps)
		      
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
      match (Ctx.value l) with
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
                let varps = PS.domain ps in
                if (List.mem f varps) then raise (DoubledVar (CVar.to_string f));
                if (List.mem y varps) then raise (DoubledVar (CVar.to_string y));
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
    if !abbrev then
      Ctx.to_string (Ctx.of_ps ps)
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
  val init : unit -> unit
  val add_coh : var -> Ctx.t -> Expr.ty -> unit
  val add_let : var -> Ctx.t -> Expr.tm -> unit

  (* Structural operation *)
  val ty_var :  evar -> int -> (Ctx.t * Ty.t)
  val check_equal : evar -> int -> Tm.t -> Sub.t -> evar -> int -> Tm.t -> Sub.t -> Ctx.t -> unit
  val dim_var : var -> int
  val ctx : evar -> int -> Ctx.t
  val elim : evar -> int -> Sub.t -> Ctx.t -> Ctx.t -> Tm.t -> Tm.t
end
  =
struct
  type value =
    |Coh of Coh.t 
    |Let of Tm.t 
  (** An environment associates to each environment variable a coherence with
     various possible suspensions. *)
  type t = (evar * ((int * value) list)) list

  (** The environment, i.e. the list of defined variables. *)
  let env = ref ([] :> t)

  (* ------
     Makers
    ------ *)
  (** Initialize the environment. *)
  let init () = env := []

  (** Add a variable together with the corresponding coherence (i.e. the pasting scheme and the output type). *)
  (* TODO: take a coherence as argument *)
  let add_coh x ps u =
    let u = 
      let c = PS.mk ps in
      Coh.mk c u in
    env := (EVar.make x,[0,Coh u])::!env


  let add_let x c u =
    let u = fst (Tm.make c u) in
    let u = Tm.mark_ctx u in
    env := (EVar.make x,[0,Let u])::!env

  (* --------------------
     Structural operation
     -------------------- *)	     
  (** Coherence associated to a variable. The second argument is the number of
     times we want to suspend. *)
  (* TODO : code the suspension when it is not a coherence *)
  let val_var x i =
    let rec replace a b l =
      match l with
      | (x,y)::l when x = a -> (x,b)::(replace a b l)
      | (x,y)::l -> (x,y)::(replace a b l)
      | [] -> []
    in
    let family =
      try List.assoc x !env
      with Not_found -> raise (UnknownCoh (EVar.to_string x))
    in
    try (List.assoc i family) 
    with Not_found ->
      try match (List.assoc 0 family) with
          |Coh coh ->
            let ps = Coh.ps coh in
            let t = Ty.reinit (Coh.target coh) in
            let ps = PS.suspend ps i in
            let newcoh = (Coh.mk ps t) in
            let newval = Coh newcoh in
            env := replace x ((i,newval)::family) (!env); 
            newval
          |Let tm ->
            let ct = tm.c in
            let ct = Ctx.suspend ct i in
            let tm = Tm.reinit tm in
            let newtm = fst (Tm.make ct tm) in
            let newtm = Tm.mark_ctx newtm in
            let newval = Let newtm in
            env := replace x ((i,newval)::family) (!env);
            newval
      with Not_found -> assert false

  (** Type of the expression associated to a variable, together with the context in which the type is valid *)
  let ty_var x i =
    let value = val_var x i in
    match value with
        |Coh coh -> (Ctx.of_ps (Coh.ps coh), Coh.target coh)
        |Let t -> (t.c, t.ty)

  let check_equal x i tm1 s1 y j tm2 s2 src =
    match (val_var x i, val_var y j) with
    |Coh c1, Coh c2 -> let ps = Coh.check_equal c1 c2 in Sub.check_equal ps s1 s2 
    |Let t1, Let t2 -> Tm.check_equal t1.c t1 t2; Sub.check_equal t1.c s1 s2
    |Let t, Coh c -> Tm.check_equal src (Sub.apply_Tm s1 t.c src t) tm2
    |Coh c, Let t -> Tm.check_equal src tm1 (Sub.apply_Tm s2 t.c src t)


  let dim_var v =
    let value = val_var (EVar.make v) 0 in
    match value with
    |Coh c -> PS.dim (Coh.ps c)
    |Let t -> Ctx.dim (t.c)

  let ctx x i =
    let value = val_var x i in
    match value with
    |Coh c -> (Ctx.of_ps (Coh.ps c))
    |Let t -> t.c

  let elim x i s src tar tm =
    let value = val_var x i in
    match value with
    |Coh c -> tm
    |Let t -> Sub.apply_Tm s src tar t 
    
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
  val check_equal : Ctx.t -> t -> t -> unit
  val make : Ctx.t -> Expr.ty -> t
       
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
    try Ctx.check_sub_ctx ty.c ctx with
    | _ -> check_hidden ctx ty.e
  and check_hidden ctx tye =
    match tye with
    | Obj -> ()
    | Arr (t,u,v) ->
       check ctx t;
       Tm.check_type ctx u t;
       Tm.check_type ctx v t

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

  (** Construct a type. *)
  let rec make c (e : Expr.ty) =
    let already_known = Hashtbl.find_all Hash.tbty e in
    let rec aux l = match l with
      | [] -> raise Unknown
      | ty::q -> try Ctx.check_sub_ctx ty.c c; ty with
                 |_ -> aux q
    in
    let open Expr in
    try aux already_known
    with Unknown ->
      let newty = 
        match e with
        | Obj -> {c = c; e = Obj}
        | Arr (u,v) ->
           let u,tu = Tm.make c u in
           let v,tv = Tm.make c v in
           let () = check_equal c tu tv in {c = c; e = Arr(tu,u,v)}
        | Ty ty -> Ctx.check_sub_ctx ty.c c; ty
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
  val check_equal : Ctx.t -> t -> t -> unit
  val check_type : Ctx.t -> t -> Ty.t -> unit
  val make : Ctx.t -> Expr.tm -> t * Ty.t
       
  val reinit : t -> Expr.tm
  val list_expl_vars : t -> Var.t list

  val mark_ctx : t -> t
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
    | Sub (t,s) -> let c = Cut.ctx t in Printf.sprintf "(%s %s)" (Cut.to_string t) (Sub.to_string s c)

  let rec check_equal ctx tm1 tm2 =
    (* debug "checking equality between %s and %s" (to_string tm1)(to_string tm2); *)
    match tm1.e, tm2.e with
    | CVar x,CVar y ->
      if not (x = y)
      then
	raise (NotEqual (to_string tm1, to_string tm2))
      else ()
    | Sub(t1,s1),Sub(t2,s2) ->
       Cut.check_equal t1 tm1 s1 t2 tm2 s2 ctx
      (* Sub.check_equal tar s1 s2 *)
    | (CVar _|Sub _),_ ->
      raise (NotEqual (to_string tm1, to_string tm2))

  (** Infer the type of an expression. *)
  let infer_expr ctx tme =
    match tme with
    | CVar x -> Ctx.ty_var ctx x
    | Sub (e,s) ->
       let tar,ty = Cut.infer e in
       Sub.check s ctx tar;
       Sub.apply_Ty s tar ctx ty

  (** Infer the type of a term. *)
  let infer ctx tm =
    try Ctx.check_sub_ctx tm.c ctx; tm.ty
    with _ -> infer_expr ctx tm.e

  (** Check that term has given type. *)
  let check_type ctx e t  =
    Ty.check_equal ctx (infer ctx e) t

  (* TODO: do we really need this? *)
  let rec reinit tm : Expr.tm =
    let open Expr in
    match tm.e with
    | CVar v -> Var (CVar.to_var v)
    | Sub (t,s) -> Sub (Cut.reinit t, Sub.reinit s (Cut.ctx t))

  let rec list_expl_vars tm : Var.t list =
    let open Expr in
    match tm.e with
    | CVar v -> [(CVar.to_var v)]
    | Sub (t,s) -> Sub.list_expl_vars s (Cut.ctx t)

  let mark_ctx t =
    {c = Ctx.mark t.c; ty = t.ty; e = t.e}
                                      
    
  (** Create a term from an expression. *)
  (* TODO: return a value of type t instead of a pair *)
  let rec print_list s =
    match s with
    |[] -> ""
    |(u::s) -> Printf.sprintf "%s %s" (print_list s) (Expr.string_of_tm u)

                              
  let rec make c e =
    let already_known = Hashtbl.find_all Hash.tbtm e in
    let rec aux l = match l with
      | [] -> raise Unknown
      | tm::q -> try Ctx.check_sub_ctx tm.c c; (tm, tm.ty) with _ -> aux q
    in
    let open Expr in
    try aux already_known
    with Unknown ->
      let newtm,newty = 
        match e with
        | Var v ->
           let e = CVar (CVar.make v) in
           let ty = infer_expr c e in
           ({c = c; ty = ty; e = e}, ty)
        | Sub (t,s) ->
           (* debug "caught substitution %s (%s)" (string_of_tm t) (print_list s); *)
           let t,tar = Cut.mk t (Sub.dim c s) in
           let s = Sub.mk s c tar in
           let e : expr = Sub (t,s) in
           let ty = infer_expr c e in
           (* debug "subsitution translated"; *)
           ({c = c; ty = ty; e = e}, ty)
        | Tm tm ->
           begin
             try Ctx.check_sub_ctx tm.c c; (tm, tm.ty)
             with _ -> make c (Tm.reinit tm)
           end
      in Hashtbl.add Hash.tbtm e newtm; newtm,newty
end

(* TODO: remove this *)
and Cut
    :
sig
  type t =
    | Fold of evar * int
  val to_string : t -> string
  val check_equal : t -> Tm.t -> Sub.t -> t -> Tm.t -> Sub.t -> Ctx.t -> unit
  val infer : t -> Ctx.t * Ty.t
  val mk : Expr.tm -> int -> (t * Ctx.t)
  val reinit : t -> Expr.tm
  val ctx : t -> Ctx.t
  (* val ps : t -> PS.t *)
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
	
     (* let check_equal e1 e2 = *)
     (*   match e1, e2 with *)
     (*   |Fold (x,i), Fold (y,j) -> Coh.check_equal (Env.val_var x i) (Env.val_var y j) *)

     let check_equal e1 tm1 s1 e2 tm2 s2 src =
       match e1, e2 with
       |Fold (x,i), Fold (y,j) -> Env.check_equal x i tm1 s1 y j tm2 s2 src
                             
     (* TODO: use ty_var instead of val_var*)
     (* let infer coh = *)
     (*   match coh with *)
     (*   |Fold (x,i) -> *)
     (*     let coh = Env.val_var x i in *)
     (*     (Ctx.of_ps (Coh.ps coh), Coh.target coh) *)

     let infer coh =
       match coh with
       |Fold (x,i) -> Env.ty_var x i
                                                  
     (* let ps coh = *)
     (*   match coh with *)
     (*   |Fold (x,i) -> let coh = Env.val_var x i in *)
     (*                  Coh.ps coh *)
                      
     let mk e i =
       let open Expr in
       match e with
       |Var v ->
         let j = Env.dim_var v in
         if j<=i then 
           let c,_ = Env.ty_var (EVar.make v) (i-j) in
           (Fold ((EVar.make v),i-j), c)
         else failwith "arguments of the coherence have dimension too low"
       |Tm tm -> assert (false) (* TODO *)
       |(Sub _) -> raise BadUnderSub

     let reinit c : Expr.tm =
       let open Expr in
       match c with
       |Fold (v,i) -> Var (EVar.to_var v)                      

     let ctx e =
       match e with
       |Fold (v,i) -> Env.ctx v i
end

(* -- Module with a specific type for well-defined coherences
    -- They are different from normal type, they need to be substituted *)    
(** A coherence. *)
and Coh    
    : sig
  type t = private (PS.t * Ty.t)   

  val mk : PS.t -> Expr.ty -> t
  val to_string : t -> string
  val check_equal : t -> t -> Ctx.t
  val ps : t -> PS.t
  val target : t -> Ty.t
end
=
struct
  type t = PS.t * Ty.t
	    
  let check ps t = 
    if List.included (PS.domain ps) (Ty.free_vars t)
    then (ps,t)
    else
      let open Ty in
      let a,f,g = match t.e with
        | Arr(a,f,g) -> (a,f,g)  
        | _ -> raise NotAlgebraic
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
	  if List.included (PS.domain pss)
	       fvf &&
	       List.included (PS.domain pst)
		 fvg
	  then (ps,t) 
	  else raise NotAlgebraic
	end;
      with
      |UnknownId _ -> raise NotAlgebraic
		       
  let mk ps t =
    let t = Ty.make (Ctx.of_ps ps) t in
    check ps t

  let to_string (ps,t) =
    Printf.sprintf "Coh {%s |- %s}"
      (PS.to_string ps)
      (Ty.to_string t)

  let check_equal (ps1,t1) (ps2,t2) =
    let c1 = Ctx.of_ps ps1 and c2 = Ctx.of_ps ps2 in
    Ctx.check_equal c1 c2;
    Ty.check_equal c1 t1 t2; c1

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
    | Sub of tm * tm list
    | Tm of Tm.t

  val string_of_ty : ty -> string
  val string_of_tm : tm -> string

  val reinit : tm -> tm
  val list_vars : tm -> Var.t list

  val unify_ty : Ctx.t -> ty -> ty -> ((Var.t * ty) * tm option * bool) list -> ((Var.t * ty) * tm option * bool) list
end
  =
struct
  (* TODO: do we really have to have Ty and Tm? It would be better to have raw
     terms as an independent module. *)
  (* TODO: this would allow us to have let in as a proper construction... *)
  (** A raw type. *)
  type ty =
    | Obj
    | Arr of tm * tm
    | Ty of Ty.t
  (** A raw term. *)
  and tm =     
    | Var of var
    | Sub of tm * (tm list)
    | Tm of Tm.t

  exception UnableUnify
             
  let rec string_of_ty e =
    match e with
    | Obj -> "*"
    | Arr (u,v) -> Printf.sprintf "%s -> %s" (string_of_tm u) (string_of_tm v)
    | Ty ty -> Ty.to_string ty
  and string_of_tm e =
    match e with
    | Var x -> Var.to_string x
    | Sub (t,s) -> Printf.sprintf "(%s %s)" (string_of_tm t) (string_of_sub s)
    | Tm tm -> Tm.to_string tm
  and string_of_sub s =
    match s with
    | [] -> ""
    | t::[] -> Printf.sprintf "%s" (string_of_tm t)
    | t::s -> Printf.sprintf "%s %s" (string_of_tm t) (string_of_sub s)

  (* TODO: use String.concat *)
  let rec print l =
    match l with
    | (t::q) -> string_of_tm t ^ " " ^ print q
    | [] -> ""

  (** Remove partly verified terms. *)
  (* TODO: remove this *)
  let rec reinit tm =
    match tm with
    | Var _ -> tm
    | Sub (tm,s) -> Sub (reinit tm, List.map reinit s)
    | Tm tm -> Tm.reinit tm

  (** List the variables of an non-checked term (ie only the explicit variables)*)
  let rec list_vars e =
    match e with
    | Var v -> [v]
    | Sub (e,l) -> List.unions (List.map list_vars l)
    | Tm tm -> Tm.list_expl_vars tm                       
                         
  (* TODO: document l *)
  let rec unify_tm (c : Ctx.t) (tm1 : tm) (tm2 : tm) l =
    (* debug "unifying %s with %s" (string_of_tm tm1) (string_of_tm tm2); *)
    match tm1 ,tm2 with
    | Var u, _ ->
       let rec replace l =
         match l with
         | (((v,ty), None, _)::l) when u = v -> ((v,ty), Some (Expr.Tm (fst (Tm.make c tm2))), true)::l 
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
let add_coh_env = Env.add_coh
let add_let_env = Env.add_let
                    
let mk_tm c e = let e,t = Tm.make c e in Expr.Tm e, Expr.Ty t
let mk_ty c e = Expr.Ty (Ty.make c e)
                        
let checkEqual c ty1 ty2 =
  let ty1 = Ty.make c ty1 in
  let ty2 = Ty.make c ty2 in
  Ty.check_equal c ty1 ty2
              
let reinit = Expr.reinit
let list_vars = Expr.list_vars

let unify c a b l =
  match b with
  | Expr.Tm b -> Expr.unify_ty c a (Ty.reinit (Tm.infer c b)) l
  | _ -> assert(false)    
