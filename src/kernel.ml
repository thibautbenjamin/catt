open Stdlib
open Settings
open Common
open Syntax

(** Environment variables (i.e. defined coherences). *)
module EVar
: sig
  type t
  val to_string : t -> string
  val make : var -> t
  val to_var : t -> var
end
=
struct
  type t = var

  let to_string v =
    string_of_var v

  let make v = v

  let to_var v = v
end

(** Context variables (i.e. "arguments of functions"). *)
module CVar
: sig 
    type t
    val to_string : t -> string
    val make : var -> t
    val to_var : t -> var
end
=
struct
  type t = var

  let to_string v =
    string_of_var v
	       
  let make v = v

  let to_var v = v 
end

type evar = EVar.t
type cvar = CVar.t

let var_of_cvar = CVar.to_var

(** Operations on substitutions. *)
module rec Sub
 :
sig
  type t

  (* Structural functions *)
  val mk : Tm.t list -> Ctx.t -> Ctx.t  -> t
  val mk_elaborated : Tm.t list -> Ctx.t -> Ctx.t -> t 
  val reinit : t -> tm list
  val list_expl_vars : t -> var list
	   
  (* Syntactic properties *)		    
  val free_vars : t -> cvar list
  val apply_Ty : t -> Ty.t -> Ty.t
  val apply_Tm : t -> Tm.t -> Tm.t
           
  (* Equality procedures *)
  val check_equal : t -> t -> unit

  (* Printing *)	
  val to_string : t ->  string

  val unify : Sub.t -> Sub.t -> ((CVar.t * Ty.t) * Tm.t option * bool) list -> ((CVar.t * Ty.t) * Tm.t option * bool) list
end
  =
struct
  (** A substitution. *)
  (* In current implementation, the variable names are given by the codomain. *)
  (* TODO: add variable names *)
  type t = {list : Tm.t list; src : Ctx.t; tar : Ctx.t}

	     
  (** Free context variables. *)
  let free_vars s =
    List.concat (List.map Tm.free_vars s.list)
                  
  (** Sequential composition of substitutions. *)
  let rec apply_list_var l tar x = 
      match l,tar with
      |_,_ when Ctx.is_empty tar ->
        assert false
      |t::l, _ ->
        let open Tm in
        let ((y,(_,_)),tar) = (Ctx.head tar, Ctx.tail tar) in
        if y = x
        then t.e
        else apply_list_var l tar x
      |[], _ -> assert false
  and compose_lists src tar s s' =
    List.rev (List.map (fun t -> apply_list_Tm s tar src t) s')
  (** Apply a substitution to a term. *)
  and apply_list_Tm s tar src tm =
    let open Tm in
    let e =
      match tm.e with
      |CVar x -> apply_list_var s tar x
      |Sub (x,v,s') ->
        let newtar = EnvVal.ctx v in 
        Sub (x,v, Sub.mk_elaborated (compose_lists src tar s s'.list) src newtar)
    in {c = src; ty = apply_list_Ty s tar src tm.ty; e = e}
  (** Apply a substitution to a type. *)
  and apply_list_Ty s tar src ty =
    let open Ty in
    let e = 
      match ty.e with
      | Obj -> Obj
      | Arr (a,u,v) -> let a,u,v = (apply_list_arr s tar src a u v) in Arr(a,u,v)
    in {c = src; e = e}
  (** Apply a substitution to a triple argument of an arrow
   This avoids computing the same type thrice, using that both terms have the same known type 
   This function is unsafe and thus is not exported and should be used only in one place *)
  and apply_list_arr s tar src ty tm1 tm2 =
    let ty = apply_list_Ty s tar src ty in
    let open Tm in
    let e1 = match tm1.e with
      |CVar x -> apply_list_var s tar x
      |Sub (x,v,s') ->
        let newtar = EnvVal.ctx v in 
        Sub (x,v, Sub.mk_elaborated (compose_lists src tar s s'.list) src newtar) in
    let e2 = match tm2.e with
      |CVar x -> apply_list_var s tar x
      |Sub (x,v,s') ->
        let newtar = EnvVal.ctx v in 
        Sub (x,v, Sub.mk_elaborated (compose_lists src tar s s'.list) src newtar) in
    (ty, {c = src; ty = ty; e = e1}, {c = src; ty = ty; e = e2})

  let apply_Tm s tm =
    let open Tm in
    Ctx.check_sub_ctx (tm.c) s.tar;
    apply_list_Tm s.list s.tar s.src tm

  let apply_Ty s ty =
    let open Ty in
    Ctx.check_sub_ctx (ty.c) s.tar;
    apply_list_Ty s.list s.tar s.src ty
      
  (** Check equality of substitutions. *)
  (* TODO : Check the sources too*)
  let check_equal (s1:t) (s2:t) =
    Ctx.check_equal s1.tar s2.tar;
    let ctx = s1.tar in
    let rec check_list s1 s2 = 
      match s1,s2 with
      | [],[] -> ()
      | t1::s1,t2::s2 ->
         Tm.check_equal ctx t1 t2;
         check_list s1 s2
      | _,_ -> raise NotValid
    in check_list s1.list s2.list 

  (** String representation of a substitution. We print only maximal elements *)
  let to_string (s:t) =
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
    in print_list s.list s.tar

  (** Given a list of terms of maximal dimension, complete it into a
     full-fledged substitution. *)
  exception Completed of ((CVar.t * Ty.t) * Tm.t option * bool) list
  let elaborate (l: Tm.t list) src tar : Tm.t list =
    (* debug "elaborating substitution %s in context %s" (print_list l) (Ctx.to_string tar); *)
    let rec create_assoc tar (l : Tm.t list) =
      match l with
      | (h::l')as l ->
         if Ctx.is_empty tar then failwith (Printf.sprintf "too many arguments given");
         let t = Ctx.tail tar in
         begin
           match Ctx.head tar with
           |(v, (tv, false)) -> ((v,tv), None, false)::(create_assoc t l)
           |(v, (tv, true)) -> ((v,tv), Some h, true)::(create_assoc t l')

         end
      | [] -> if Ctx.is_empty tar then []
              else match Ctx.head tar with
                   |(v,(tv, false)) -> ((v,tv), None, false)::(create_assoc (Ctx.tail tar) [])
                                                                                    
                   |_ -> failwith "not enough arguments given"
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
      let assoc = Ty.unify (snd a) (Tm.infer src b) assoc
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
  let mk_elaborated (l : Tm.t  list) src (tar : Ctx.t) =
    let rec aux l (tar : Ctx.t) =
      match l,Ctx.value tar with
      |[],[] -> []
      |(_::_,[] |[],_::_) -> raise NotValid
      |t::s,_ ->
	let (x,(u,_)),tar = (Ctx.head tar,Ctx.tail tar) in
	let s = aux s tar in
	let ty = Tm.infer src t in
	let () = Ty.check_equal src ty (apply_list_Ty s tar src u)
	in t::s
    in {list = aux (List.rev l) tar; src = src; tar = tar}

  (** Create a substitution described by maximal elements. *)
  let mk (l:Tm.t list) src tar = 
    let list = elaborate (List.rev l) src tar in
    mk_elaborated (List.rev list) src tar
                  
  (** Keep only the the maximal elements of a substitution ("unealborate"). *)
  let reinit (s:t) =
    let rec aux s c = 
      match s,c with
      |[], c when Ctx.is_empty c -> []
      |(u::s),c -> begin
          match Ctx.head c with
          |(_,(_,true)) -> (Tm.reinit u)::(aux s (Ctx.tail c)) 
          |(_,(_,false)) -> aux s (Ctx.tail c)
        end
      |_,_ -> assert false
      in List.rev (aux s.list s.tar)

  (** List the explicit variables of a substitution. *)
  let list_expl_vars (s:t) =
    let rec aux s c = 
      match s,c with
      |[], c when Ctx.is_empty c -> []
      |(u::s),c -> begin
          match Ctx.head c with
          |(_,(_,true)) -> (Tm.list_expl_vars u)@(aux s (Ctx.tail c)) 
          |(_,(_,false)) -> aux s (Ctx.tail c)
        end
      |_,_ -> assert false
    in (aux s.list s.tar)

  let unify s s' l =
    let rec unify_list s s' l = 
      match s ,s' with
      | (a::s),(a'::s') -> let l = Tm.unify a a' l in unify_list s s' l 
      | [],[] -> l
      | _,_ -> raise UnableUnify
    in unify_list s.list s'.list l


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
  type t = private (cvar * (Ty.t * bool)) list
                     
  (* Makers *)
  val empty : unit -> t
  val add : t -> var -> ty -> t
  val add_norm : t -> var -> Ty.t -> t
  val make : (var * ty) list -> t
  val of_ps : PS.t -> t
       
  (* Structural operations *)
  val head : t -> cvar * (Ty.t * bool)
  val tail : t -> t
  val suspend : t -> int -> t
       
  (* Syntactic properties *)
  val ty_var : t -> cvar -> Ty.t
  val domain : t -> cvar list
  val explicit_domain : t -> cvar list
  val max_used_var : t -> int
  val value : t -> (cvar * (Ty.t * bool)) list
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

  (** adding an already marked term to a context (forgets the marking)*)
  let add_norm (ctx : Ctx.t) x u =
    let x = CVar.make x in
    try
      ignore (List.assoc x (ctx :> t));
      raise (DoubleDef (CVar.to_string x))
    with Not_found -> (x,(u,false))::(ctx :> t)

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

  (* ---------------------
      Structural operations
      --------------------- *)

  (** First element of a context. *)
  let rec head ctx =
    match ctx with
    |[] -> assert false
    |a::_ -> a
           
  (** Tail of a context. *)
  let rec tail ctx =
    match ctx with 
    |[] -> assert false
    |_::l -> l
                   
       
  (* --------------------
     Syntactic properties
     -------------------- *)
  (** Domain of definition of a context. *)
  let domain ctx = List.map fst ctx

  let explicit_domain ctx = List.map fst (List.filter (fun x -> snd (snd x)) ctx)

  let value (ctx : t) = ctx
    
  (** Check whether a variable belongs to a context. *)
  let mem (c:t) v =
    let rec aux c =  
      match c with
      | [] -> false
      | (x,_)::c when x = v -> true
      | _::c -> aux c
    in aux c
	      
  (* -------------------
     Equality procedures
     ------------------- *)
  (** Is a context empty? *)
  let is_empty (c:t) =
    c = []

  let max_used_var ctx =
    let rec aux n l =
      match l with
      |[] -> n
      |v::l ->
        match CVar.to_var v with
        |Name _ -> aux n l 
        |New k -> aux (max k n) l
    in aux 0 (domain ctx)
          
  (** Suspend a context, i.e. rempace types "*" by arrow types (forgets the marking).*)
  let suspend (ctx : t) i =
    (* picking a fresh number for the new variable in context ctx*)
    let n = max_used_var ctx in 
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
	(Ctx.add (Ctx.empty ()) (New (n+1)) Obj)
	(New (n+2))
	Obj    
    in
    let ctx',ty = aux (n+1) ctx' (Arr (Var (New (n+1)), Var (New (n+2)))) in
    let open Ty in
    let rec comp c res = match c with
      | (x,(tx,_))::c when tx.e = Obj-> comp c (Ctx.add res (var_of_cvar x) ty)
      | (x,(tx,_))::c -> comp c (Ctx.add res (var_of_cvar x) (Ty.reinit tx))
      | [] -> res
    in
    comp (List.rev ctx) ctx'

          
  (** Check whether a context is included in another one. *)
  (* TODO: this is a bit worrying as a function, is it really necessary or can
     we get rid of it? *)
  let check_sub_ctx ctx1 ctx2 =
    (* debug "checking that ctx %s is a sub of %s" (Ctx.to_string ctx1) (Ctx.to_string ctx2); *)
    let rec sub c (ctx1 : Ctx.t) (ctx2 : Ctx.t) =
      if Ctx.is_empty ctx1 then ()
      else if Ctx.is_empty ctx2 then raise NotValid
      else
        let (v1,(x1,_)),t1 = Ctx.head ctx1, Ctx.tail ctx1 in
        let (v2,(x2,_)),t2 = Ctx.head ctx2, Ctx.tail ctx2 in
        if not (v1 = v2) then
          sub c ctx1 t2
        else (Ty.check_equal c x1 x2;
              sub ctx1 t1 t2)
    in sub (Ctx.empty ()) ctx1 ctx2

  (** Equality of contexts. *)
  let rec check_equal ctx1 ctx2 =
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
	
  let mark c =
    let rec appears x c = match c with
      |(_,(a,_))::q -> (List.mem x (Ty.free_vars a)) || (appears x q)
      |[] -> false
    in
    let rec traversal c =
      match c with
      |((x,(t,_))::c) -> (x, (t, (not (appears x c)))) :: (traversal c)
      |[] -> []
    in List.rev (traversal (List.rev c))
             
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
                      
  (** dimension of a context is the maximal dimension of its variables *)
  let dim ctx =
    let rec aux c i = match c with
      |[] -> i
      |(_,(ty,_))::c when Ty.dim ty>i -> aux c (Ty.dim ty)
      |_::c -> aux c i
    in aux ctx 0
                             
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
  val explicit_domain : t -> cvar list
  (* val to_expr : t -> (var * Expr.ty) list *)

  (* Structural operations *)
  val height : t -> int
  val dim : t -> int
  val source : int -> t -> t
  val target : int -> t -> t
  val suspend : t -> int -> t
  val functorialize : t -> cvar -> t * var
                              
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

  let explicit_domain ps = Ctx.explicit_domain (Ctx.of_ps ps)
		      
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
                  aux (PDrop ps) l1
             | _ -> raise Invalid
           end
        | [x,tx] -> raise Invalid
        | [] ->
	   let x,tx = marker ps in close ps tx 
      in
      aux (PNil (x0,ty)) l
    in build (List.rev (Ctx.value l))

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

  (** Suspend a pasting scheme. *)
  (* TODO: implement this more efficiently *)
  let rec suspend ps i =
    mk (Ctx.suspend (Ctx.of_ps ps) i)

  let functorialize ps v =
    let originalctx = Ctx.of_ps ps in
    let n = Ctx.max_used_var originalctx in
    let rec compute_ctx ps =
    match ps with
    |(PNil (x,_) as ps) when x = v ->
      let x = CVar.to_var x in
      let ctx1 = (Ctx.add (Ctx.of_ps ps) (New (n+1)) Obj) in
      Ctx.add ctx1 (New (n+2)) (Arr(Var x,Var (New (n+1))))
    |((PDrop (PCons (_,_,(x,ty)))) as ps) when x = v ->
      let x = CVar.to_var x in
      let ctx1 = Ctx.add (Ctx.of_ps ps) (New (n+1)) (Ty.reinit ty) in
      Ctx.add ctx1 (New (n+2)) (Arr(Var x, Var (New (n+1))))
    |(PDrop (PCons (ps,(x1,ty1),(x2,ty2)))) ->
      let x1 = CVar.to_var x1 and x2 = CVar.to_var x2 in
      let ty1 = Ty.reinit ty1 and ty2 = Ty.reinit ty2 in
      let ctx= compute_ctx ps in
      Ctx.add (Ctx.add ctx x1 ty1) x2 ty2
    |PDrop(ps) -> compute_ctx ps
    |PCons(ps,(x1,ty1),(x2,ty2)) ->
      let x1 = CVar.to_var x1 and x2 = CVar.to_var x2 in
      let ty1 = Ty.reinit ty1 and ty2 = Ty.reinit ty2 in
      let ctx = compute_ctx ps in
      Ctx.add (Ctx.add ctx x1 ty1) x2 ty2
    |PNil (x,_) -> assert(false)
    in
    let newps = compute_ctx ps in
    PS.mk newps,New(n+1)
      
      
    
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

and EnvVal
:
sig
  type t =
    |Coh of Coh.t
    |Let of Tm.t

  val mk_coh : Coh.t -> t
  val mk_let : Tm.t -> t

  val dim : t -> int
                         
  val suspend : t -> int -> t
  val functorialize : t -> cvar list -> var -> t
                         
  val ty :  t -> (Ctx.t * Ty.t)
  val ctx : t -> Ctx.t
  val check_equal : t -> Tm.t -> Sub.t -> t -> Tm.t -> Sub.t -> Ctx.t -> unit
end
= 
struct
  type t =
    |Coh of Coh.t
    |Let of Tm.t

  let mk_coh c = Coh c

  let mk_let t = Let t

  (* TODO : make a good notion of dimension for let definitions*)
  let dim value =  match value with
    |Coh c -> Coh.dim c
    |Let t -> Tm.dim t
                     
  let suspend v i =
    match v with
    |Coh coh ->
      let newcoh = Coh.suspend coh i in
      Coh newcoh
    |Let tm ->
      let newtm = Tm.suspend tm i in
      let newtm = Tm.mark_ctx newtm in
      Let newtm

  let ty value =
    match value with
    |Coh coh -> (Ctx.of_ps (Coh.ps coh), Coh.target coh)
    |Let t -> let open Tm in (t.c, t.ty)

  let ctx value =
    match value with
    |Coh c -> (Ctx.of_ps (Coh.ps c))
    |Let t -> let open Tm in t.c

  let functorialize v l evar =
    match l with
    |[] -> v
    |_ as l -> 
      match v with
      |Coh coh ->
        let newcoh = Coh.functorialize coh l evar in
        Coh newcoh
      |Let tm ->
        let newtm = Tm.functorialize tm l in
        Let newtm
                               
  let check_equal v1 tm1 s1 v2 tm2 s2 src =
    match (v1, v2) with
    |Coh c1, Coh c2 -> Sub.check_equal s1 s2
    |Let t1, Let t2 -> Tm.check_equal src (Sub.apply_Tm s1 t1) (Sub.apply_Tm s2 t2)
    |Let t, Coh c -> Tm.check_equal src (Sub.apply_Tm s1 t) tm2
    |Coh c, Let t -> Tm.check_equal src tm1 (Sub.apply_Tm s2 t)

end
    
(** Operations on environments. *)
(* TODO : Store functorialized coherence, to avoid computing them over and over again*)
(* TODO : Same with suspended coherences and all the combinations of both*)
and Env
:
sig
  type t
  val env : t ref
       
  (* Makers *)
  val init : unit -> unit
  val add_coh : var -> Coh.t -> unit
  val add_let : var -> Tm.t -> unit
  val val_var : EVar.t -> int -> int list -> EnvVal.t
end
  =
struct
  (** An environment associates to each environment variable a value together with its dimension *)
  type t = (evar * EnvVal.t) list

  (** The environment, i.e. the list of defined variables. *)
  let env = ref ([] :> t)

  (** Initialize the environment. *)
  let init () = env := []

  (** Add a variable together with the corresponding coherence*)
  let add_coh x u =
    let u = EnvVal.mk_coh u in 
    env := (EVar.make x,u)::!env

  (** Add a variable together with the corresponding let term*)
  let add_let x u =
    (* debug "adding %s" (Var.to_string x); *)
    let open Tm in
    let u = Tm.mark_ctx u in
    let u = EnvVal.mk_let u in
    env := (EVar.make x,u)::!env
                          
  (** Coherence associated to a variable. The second argument is the dimension for expected term *)
  let val_var x i func =
    (* debug "getting the value of id %s in env" (EVar.to_string x); *)
    let value =
      try List.assoc x !env
      with Not_found -> raise (UnknownCoh (EVar.to_string x))
    in
    let vars = List.rev (Ctx.explicit_domain (EnvVal.ctx value)) in
    let rec names l = match l with
      |[] -> []
      |i::l -> (List.get i vars)::(names l)
    in
    let value = EnvVal.functorialize value (names func) (EVar.to_var x) in
    let dim = EnvVal.dim value in
    let i = i - dim in
    if i >= 1 then EnvVal.suspend value i
    else value
    (* let i = i - dim in *)
    (* if i < 0 then failwith "dimension of arguments too low"; *)
    (* try (List.assoc i family)  *)
    (* with Not_found -> *)
    (*   try let newval = EnvVal.suspend (List.assoc 0 family) i *)
    (*       in env := replace x (dim,((i,newval)::family)) (!env); *)
    (*          newval *)
    (*   with Not_found -> assert false *)
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
  val make : Ctx.t -> ty -> t
       
  val dim : t -> int
  val reinit : t -> ty

  val unify : t -> t -> ((CVar.t * t) * Tm.t option * bool) list -> ((CVar.t * t) * Tm.t option * bool) list

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
  let rec make c e =
    let e = remove_let_ty e in
    let already_known = Hashtbl.find_all Hash.tbty e in
    let rec aux l = match l with
      | [] -> raise Unknown
      | ty::q -> try Ctx.check_sub_ctx ty.c c; ty with
                 |_ -> aux q
    in
    try aux already_known
    with Unknown ->
      let newty = 
        match e with
        | Obj -> {c = c; e = Obj}
        | Arr (u,v) ->
           let u,tu = Tm.make c u in
           let v,tv = Tm.make c v in
           let () = check_equal c tu tv in {c = c; e = Arr(tu,u,v)}
        | Letin_ty _ -> assert false
      in Hashtbl.add Hash.tbty e newty; newty

  (** Dimension of a type. *)
  let rec dim ty =
    match ty.e with
    | Obj -> 0
    | Arr(a,t,u) -> 1 + dim a

  (** Expression from a type. *)
  (* TODO: can we remove this? *)
  let rec reinit t : ty =
    match t.e with
    | Obj -> Obj
    | Arr(_,u,v) -> Arr (Tm.reinit u, Tm.reinit v)

  let rec unify (ty1 : t) (ty2 : t) l =
    match ty1.e ,ty2.e with
    | Obj, _ -> l
    | Arr(a,u,v), Arr(a',u',v') ->
       let l = unify a a' l in
       let l = Tm.unify u u' l
       in Tm.unify v v' l
    | _, _ -> raise UnableUnify

end

(** Operations on terms. *)
and Tm
    :
sig
  type expr = 
    | CVar of cvar
    | Sub of evar * EnvVal.t * Sub.t
  and t = {c : Ctx.t; ty : Ty.t; e : expr}
           
  val free_vars : t -> cvar list
  val to_string : t -> string

  val infer : Ctx.t -> t -> Ty.t
  val check_equal : Ctx.t -> t -> t -> unit
  val check_type : Ctx.t -> t -> Ty.t -> unit
  val make : Ctx.t -> tm -> t * Ty.t
  val dim : t -> int
                                  
  val reinit : t -> tm
  val list_expl_vars : t -> var list

  val mark_ctx : t -> t
  val suspend : t -> int -> t
  val functorialize : t -> cvar list -> t
                              
  val unify : t -> t -> ((CVar.t * Ty.t) * t option * bool) list -> ((CVar.t * Ty.t) * t option * bool) list

end
  =
struct
  (** An expression. *)
  type expr =
    | CVar of cvar (** a context variable *)
    | Sub of evar * EnvVal.t * Sub.t (** a substituted environment variable *)
  (** A term, i.e. an expression with given type in given context. *)
  and t = {c : Ctx.t; ty : Ty.t; e : expr}
            
  exception Unknown
             
  let rec free_vars tm =
    match tm.e with
    | CVar x -> [x]
    | Sub (_,_,sub) -> Sub.free_vars sub
                     
  let rec to_string tm =
    match tm.e with
    | CVar x -> CVar.to_string x
    | Sub (x,v,s) -> Printf.sprintf "(%s %s)" (EVar.to_string x) (Sub.to_string s)

  let rec check_equal ctx tm1 tm2 =
    (* debug "checking equality between %s and %s" (to_string tm1)(to_string tm2); *)
    match tm1.e, tm2.e with
    | CVar x,CVar y ->
      if not (x = y)
      then
	raise (NotEqual (to_string tm1, to_string tm2))
      else ()
    | Sub(x,v1,s1),Sub(y,v2,s2) ->
       EnvVal.check_equal v1 tm1 s1 v2 tm2 s2 ctx
    | (CVar _|Sub _),_ ->
       raise (NotEqual (to_string tm1, to_string tm2))

  (** Infer the type of an expression. *)
  let infer_expr ctx tme =
    match tme with
    | CVar x -> Ctx.ty_var ctx x
    | Sub (_,v,s) ->
       let tar,ty = EnvVal.ty v in
       Sub.apply_Ty s ty

  (** Infer the type of a term. *)
  let infer ctx tm =
    try Ctx.check_sub_ctx tm.c ctx; tm.ty
    with _ -> infer_expr ctx tm.e

  (** Check that term has given type. *)
  let check_type ctx e t  =
    Ty.check_equal ctx (infer ctx e) t

  (* TODO: do we really need this? *)
  let rec reinit tm =
    match tm.e with
    | CVar v -> Var (CVar.to_var v)
    | Sub (x,v,s) -> Sub (Var (EVar.to_var x), Sub.reinit s,[])

  let rec list_expl_vars tm : var list =
    match tm.e with
    | CVar v -> [(CVar.to_var v)]
    | Sub (_,v,s) -> Sub.list_expl_vars s

  let mark_ctx t =
    {c = Ctx.mark t.c; ty = t.ty; e = t.e}

  let suspend tm i =
    let ct = tm.c in
    let ct = Ctx.suspend ct i in
    let tm = reinit tm in
    fst (Tm.make ct tm)

  let functorialize tm l = assert false
                                 
  let dim tm =
    Ctx.dim tm.c
        
  (** Create a term from an expression. *)
  (* TODO: return a value of type t instead of a pair *)                    
  let rec make c e =
    let e = remove_let_tm e in
    let already_known = Hashtbl.find_all Hash.tbtm e in
    let rec aux l = match l with
      | [] -> raise Unknown
      | tm::q -> try Ctx.check_sub_ctx tm.c c; (tm, tm.ty) with _ -> aux q
    in
    try aux already_known
    with Unknown ->
      (* debug "building term %s" (string_of_tm e); *)
      let newtm,newty = 
        match e with
        | Var v ->
           let e = CVar (CVar.make v) in
           let ty = infer_expr c e in
           ({c = c; ty = ty; e = e}, ty)
        | Sub (t,s,func) ->
           let max_list l = let rec max l i =
                       match l with
                       | [] -> i
                       | t::l -> if t > i then max l t else max l i
                       in
                       match l with
                       | t::l -> max l t
                       | [] -> raise EmptySub in
           let s = List.map (Tm.make c) s in
           let i = (max_list (List.map (fun t -> Ty.dim (snd t)) s)) in
           let v,t = match t with
             |Var v -> let v = EVar.make v in (v, Env.val_var v i func)
             |(Sub (_,_,_) | Letin_tm(_,_,_)) -> assert false
           in let tar,ty = EnvVal.ty t in
           let s = Sub.mk (List.map fst s) c tar in
           let ty = Sub.apply_Ty s ty in
           ({c = c; ty = ty; e = Sub(v,t,s)}, ty)
        | Letin_tm _ -> assert false
      in Hashtbl.add Hash.tbtm e newtm; newtm,newty


  let rec unify (tm1 : t) (tm2 : t) l =
    match tm1.e, tm2.e with
    | CVar u, _ ->
       let rec replace l =
         match l with
         | (((v,ty), None, _)::l) when u = v -> ((v,ty), Some tm2, true)::l 
         | ((((v,ty), Some tm, _)::_) as l) when u = v -> l
         (* TODO : check compatibility between the constraints *)
         | a::l -> a::(replace l)
         | [] -> []
       in
       replace l
    | Sub(_,_,s), Sub (_,_,s') ->
       Sub.unify s s' l
    | _, CVar _ -> raise UnableUnify
end
  
(* -- Module with a specific type for well-defined coherences
    -- They are different from normal type, they need to be substituted *)    
(** A coherence. *)
and Coh    
    : sig
  type t = private (PS.t * Ty.t)   

  val mk : PS.t -> ty -> t
  val to_string : t -> string
  val check_equal : t -> t -> Ctx.t
  val ps : t -> PS.t
  val dim : t -> int
  val target : t -> Ty.t
  val suspend : t -> int -> t
  val functorialize : t -> cvar list -> var ->  t
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

  let dim (ps,t) = PS.dim ps
    
  let suspend (ps,t) i =
    let t = Ty.reinit t in
    let ps = PS.suspend ps i in
    (Coh.mk ps t)

  let functorialize (ps,t) l evar =
    match l with
    |[] -> assert(false)
    |v::l ->
      let rec funcps l = match l with
        |[] -> let ps,repl = PS.functorialize ps v in
               ps,[CVar.to_var v,repl]
        |(v::l) -> let ps,repl = funcps l in
                   let newps,newrepl = PS.functorialize ps v in
                   newps,(CVar.to_var v,newrepl)::repl
      in
      let newps,replacements = funcps l in
      let src = List.rev(List.map (fun v -> Var (CVar.to_var v)) (PS.explicit_domain ps)) in
      let rec replace_all repl l =
        match repl with
        |[] -> l
        |(v1,v2) :: repl -> replace_all repl (replace_tm_list l v1 v2)
      in
      let tgt = replace_all replacements src in
      let t = Arr(Sub(Var evar, src,[]),(Sub(Var evar, tgt,[]))) in
      (Coh.mk newps t) 
end

and Hash
    : sig
  val tbty : (ty, Ty.t) Hashtbl.t 
  val tbtm : (tm, Tm.t) Hashtbl.t 
end
  =
struct
  let tbty : (ty, Ty.t) Hashtbl.t = Hashtbl.create 10000
  let tbtm : (tm, Tm.t) Hashtbl.t = Hashtbl.create 10000
end

type kTm = Tm.t
type kTy = Ty.t

    
type env = Env.t
type ctx = Ctx.t

let init_env = Env.init
                 
let add_coh_env v ps t =
  let ps = PS.mk (Ctx.make ps) in
  let c = Coh.mk ps t in
  Env.add_coh v c

let add_let_env v c u =
  let c = Ctx.make c in
  let u,t = Tm.make c u in
  Env.add_let v u;
  Ty.to_string t

let add_let_env_of_ty v c u t =
  let c = Ctx.make c in
  let u,t' = Tm.make c u in
  let t = Ty.make c t in
  Ty.check_equal c t' t;
  Env.add_let v u;
  Ty.to_string t
               
                    
let mk_tm c e =
  let c = Ctx.make c in
  let e,t = Tm.make c e in
  (Tm.to_string e, Ty.to_string t)

let mk_tm_of_ty c e t =
  let c = Ctx.make c in
  let e,t' = Tm.make c e in
  let t = Ty.make c t in
  Ty.check_equal c t' t              

