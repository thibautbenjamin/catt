open Std
open Settings
open Common
open Syntax
open Gassoc
open Variables

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
  val _check : Ctx.t -> Unchecked.sub -> Ctx.t -> t
  val check_to_ps : Ctx.t -> Unchecked.sub_ps -> PS.t -> t
  val reinit : t -> tm list
  val _forget : t -> Unchecked.sub
  val _forget_to_ps : t -> Unchecked.sub_ps

  val list_expl_vars : t -> var list

  (* Syntactic properties *)
  val free_vars : t -> cvar list
  val apply_Ty : t -> Ty.t -> Ty.t
  val apply_Tm : t -> Tm.t -> Tm.t

  (* Equality procedures *)
  val check_equal : t -> t -> unit

  val explicit : t -> Tm.t list

  (* Printing *)
  val _to_string : t ->  string
  val to_string_func : t -> int list -> string

  val unify : Sub.t -> Sub.t -> ((CVar.t * Ty.t) * Tm.t option * bool) list -> ((CVar.t * Ty.t) * Tm.t option * bool) list

  val src : t -> Ctx.t
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

  let src s = s.src

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
      | Coh _ -> assert false
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
      |Coh _ -> assert false
      |Sub (x,v,s') ->
        let newtar = EnvVal.ctx v in
        Sub (x,v, Sub.mk_elaborated (compose_lists src tar s s'.list) src newtar) in
    let e2 = match tm2.e with
      |CVar x -> apply_list_var s tar x
      | Coh _ -> assert false
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
    in print_list s.list s.tar

  let to_string_func s l =
    let rec print_list s c i =
      match s,c with
      | [], c when Ctx.is_empty c -> ""
      | (u::s),c -> begin
          match Ctx.head c with
          | (_, (_,true)) when List.mem i l ->
             Printf.sprintf "%s [%s]" (print_list s (Ctx.tail c) (i-1)) (Tm.to_string u)
          | (_, (_,true)) ->
             Printf.sprintf "%s %s" (print_list s (Ctx.tail c) (i-1)) (Tm.to_string u)
          | (_, (_,false)) -> Printf.sprintf "%s" (print_list s (Ctx.tail c) i)
        end
      | _ -> assert false
    in print_list s.list s.tar (List.length (Ctx.explicit_domain s.tar))

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
      | ((_,None,true)::_) -> assert(false)
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
      | (((_,_),Some b,_)::l) -> b :: (clear l)
      | ((_, None,_)::_) -> assert(false)
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
	let (_,(u,_)),tar = (Ctx.head tar,Ctx.tail tar) in
	let s = aux s tar in
	let ty = Tm.infer src t in
	let () = Ty.check_equal src ty (apply_list_Ty s tar src u)
	in t::s
    in {list = aux (List.rev l) tar; src = src; tar = tar}

  (** Create a substitution described by maximal elements. *)
  let mk (l:Tm.t list) src tar =
    let list = elaborate (List.rev l) src tar in
    mk_elaborated (List.rev list) src tar

  let _check src s tgt =
    let rec expr s tgt =
      match s, Ctx.value tgt with
      | [], [] -> []
      | (_::_,[] |[],_::_) -> raise NotValid
      | (x1,_)::_, (x2,(_,_))::_ when x1 != (var_of_cvar x2) -> raise NotValid
      | (_,t)::s, (_,(u,_))::tgt ->
	 let s = expr s tgt in
         let t = Tm.check src t in
	 let ty = t.ty in
         (* TODO: replace this *)
	 Ty.check_equal src ty (apply_list_Ty s tgt src u);
	 t::s
    in {list = expr (List.rev s) tgt; src = src; tar = tgt}

  let check_to_ps src s tgt =
    let tgt = Ctx.of_ps tgt in
    let rec expr s tgt =
      match s, Ctx.value tgt with
      | [], [] -> []
      | (_::_,[] |[],_::_) -> raise NotValid
      | t::s, (_,(u,_))::tgt ->
	 let s = expr s tgt in
         let t = Tm.check src t in
	 let ty = t.ty in
         (* TODO: replace this *)
	 Ty.check_equal src ty (apply_list_Ty s tgt src u);
	 t::s
    in {list = expr (List.rev s) tgt; src = src; tar = tgt}


  (** Make the expression into a substitution *)
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

  let _forget s = List.map2 (fun (v,_) t -> (var_of_cvar v, Tm._forget t)) s.tar s.list
  let _forget_to_ps s = List.map Tm._forget s.list

  (** Keep only the the maximal elements of a substitution ("unealborate"). *)
  let explicit (s:t) =
    let rec aux s c =
      match s,c with
      |[], c when Ctx.is_empty c -> []
      |(u::s),c -> begin
          match Ctx.head c with
          |(_,(_,true)) -> u::(aux s (Ctx.tail c))
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
  type t = (cvar * (Ty.t * bool)) list

  (* Makers *)
  val empty : unit -> t
  val add : t -> var -> ty -> t
  val make : (var * ty) list -> t
  val of_ps : PS.t -> t

  (* Structural operations *)
  val head : t -> cvar * (Ty.t * bool)
  val tail : t -> t
  val suspend : t -> int -> t
  val functorialize : t -> (CVar.t * (var * var)) list -> t

  (* Syntactic properties *)
  val ty_var : t -> cvar -> Ty.t
  val domain : t -> cvar list
  val explicit_domain : t -> cvar list
  val max_used_var : t -> int
  val value : t -> (cvar * (Ty.t * bool)) list
  val dim : t -> int

  val _forget : t -> Unchecked.ctx
  val _check : Unchecked.ctx -> t
  val _extend : t -> var -> Unchecked.ty -> t


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

  let add_explicit (ctx : Ctx.t) x u =
    let u = Ty.make ctx u in
    let x = CVar.make x in
    try
      ignore (List.assoc x (ctx :> t));
      raise (DoubleDef (CVar.to_string x))
    with Not_found -> (x,(u,true))::(ctx :> t)


  (** Create a context from a list of terms. *)
  let make l =
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

  let explicit_domain ctx = List.map fst (List.filter (fun x -> snd (snd x)) ctx)

  let value (ctx : t) = ctx

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
        | Name _ -> aux n l
        | New k -> aux (max k n) l
        | Db _ -> aux n l
    in aux 0 (domain ctx)

  (** Suspend a context, i.e. rempace types "*" by arrow types (forgets the marking).*)
  let suspend (ctx : t) i =
        (* picking a fresh number for the new variable in context ctx*)
    let n = max_used_var ctx in
    assert (i>=1);
    let rec aux k j c = (*k is the last used var, j the number of time we functorialized*)
      match j with
      | j when j = i -> c,Arr (Var (New (k)), Var (New (k+1)))
      | j ->
	 let k' = k+2 in
	 let ty = Arr (Var (New (k)), Var (New (k+1))) in
         aux (k')
           (j+1)
	   (Ctx.add
	      (Ctx.add c (New (k')) ty)
	      (New (k'+1))
	      ty)
    in
    let ctx' =
      Ctx.add
	(Ctx.add (Ctx.empty ()) (New (n+1)) Obj)
	(New (n+2))
	Obj
    in
    let ctx',ty = aux (n+1) 1 ctx'  in
    let open Ty in
    let rec comp c res = match c with
      | (x,(tx,_))::c when tx.e = Obj-> comp c (Ctx.add res (var_of_cvar x) ty)
      | (x,(tx,_))::c -> comp c (Ctx.add res (var_of_cvar x) (Ty.reinit tx))
      | [] -> res
    in
    comp (List.rev ctx) ctx'

  (** Check whether a context is included in another one. *)
  (* it is just a prefix, to check if we can spare some type checking *)
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

  let functorialize (c:Ctx.t) l =
    let compute (c : Ctx.t) =
      match (c :> (CVar.t * (Ty.t * bool)) list) with
      |[] -> []
      |(x,(tx,false))::_ -> add (Ctx.functorialize (Ctx.tail c) l) (CVar.to_var x) (Ty.reinit tx)
      |(x,(tx,true))::_ ->
        let tx = Ty.reinit tx in
        try let (y,f) = List.assoc x l in
            let x = CVar.to_var x in
            let c = Ctx.add (Ctx.functorialize (Ctx.tail c) l) x tx in
            let c = Ctx.add c y tx in
            add_explicit c f (Arr(Var x,Var y))
        with Not_found -> add (Ctx.functorialize (Ctx.tail c) l) (CVar.to_var x) tx
    in mark (compute c)


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
  val dim : t -> int
  val source : int -> t -> t
  val target : int -> t -> t
  val suspend : t -> int -> t
  val functorialize : t -> cvar -> var -> var -> t

  val _forget : t -> Unchecked.ps
  val check : Unchecked.ps -> t

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
             | Arr (_, {e = CVar fx; _}, {e = CVar fy; _}) ->
                if (y <> fy) then raise Invalid;
                let x,_ = marker ps in
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
        | [_,_] -> raise Invalid
        | [] ->
	   let _,tx = marker ps in close ps tx
      in
      aux (PNil (x0,ty)) l
    in build (List.rev (Ctx.value l))

  let susp (_ps : t) : t = assert false
  let concat (_ps : t list) : t = assert false

  let rec check ps =
    match ps with
    | Unchecked.Br [] -> assert false
    | Unchecked.Br l -> concat (List.map (fun ps -> susp (check ps)) l)

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
      | PNil _ -> PNil g
      | PCons (ps,y,_) -> PCons (ps,y,g)
      | _ -> assert false
    in
    let rec aux = function
      | PNil _ as ps -> ps
      | PCons (ps,_,_) when height ps > i -> aux ps
      | PCons (ps,y,_) when height ps = i -> replace y (aux ps)
      | PCons (ps,y,f) -> PCons (aux ps,y,f)
      | PDrop ps when height ps > i -> aux ps
      | PDrop ps -> PDrop (aux ps)
    in
    aux ps

  (** Suspend a pasting scheme. *)
  (* TODO: implement this more efficiently *)
  let suspend ps i =
    mk (Ctx.suspend (Ctx.of_ps ps) i)

  let functorialize ps v v' al =
    let rec compute_ctx ps =
    match ps with
    |(PNil (x,_) as ps) when x = v ->
      let x = CVar.to_var x in
      let ctx1 = (Ctx.add (Ctx.of_ps ps) v' Obj) in
      Ctx.add ctx1 al (Arr(Var x,Var v'))
    |((PDrop (PCons (_,_,(x,ty)))) as ps) when x = v ->
      let x = CVar.to_var x in
      let ctx1 = Ctx.add (Ctx.of_ps ps) v' (Ty.reinit ty) in
      Ctx.add ctx1 al (Arr(Var x, Var v'))
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
    |PNil (_,_) -> assert(false)
    in
    let newps = compute_ctx ps in
    PS.mk newps

  (* assumes that all ps are completed with enough PDrop in the end *)
  let _forget ps =
    let rec find_previous ps list =
      match ps with
      | PNil x -> (list, PNil x)
      | PCons (ps,_,_) -> (list, ps)
      | PDrop ps ->
         let p,ps = build_till_previous ps in
         find_previous ps (List.append list [p])
    and build_till_previous ps =
      match ps with
      | PNil x -> Unchecked.Br [], PNil x
      | PCons (_,_,_) -> assert false
      | PDrop ps -> let p,ps = find_previous ps [] in Unchecked.Br p,ps
    in
    fst (build_till_previous ps)

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
  type v =
    |Coh of Coh.t
    |Let of Tm.t
  type t = {print : string * int list; value : v}

  val mk_coh : string -> (var * ty) list -> ty-> t
  val mk_let : string -> (var * ty) list -> tm -> t * string
  val mk_let_check : string -> (var * ty) list -> tm -> ty -> t * string

  val dim : t -> int

  val suspend : t -> int -> t
  val functorialize : t -> int list -> var -> t

  val ty :  t -> (Ctx.t * Ty.t)
  val ctx : t -> Ctx.t
  val check_equal : t -> Tm.t -> Sub.t -> t -> Tm.t -> Sub.t -> Ctx.t -> unit
end
=
struct
  type v =
    |Coh of Coh.t
    |Let of Tm.t

  type t = {print : string * int list; value : v}

  let mk_coh nm ps t =
  let ps = PS.mk (Ctx.make ps) in
  let c = Coh.mk ps t in
  {print = (nm,[]); value = Coh c}

  let mk_let nm c u =
  let c = Ctx.make c in
  let u,ty = Tm.make c u in
  let u = Tm.mark_ctx u in
  {print = (nm,[]); value = Let u}, Ty.to_string ty

  let mk_let_check nm c u t =
  let c = Ctx.make c in
  let u,ty = Tm.make c u in
  let t = Ty.make c t in
  Ty.check_equal c t ty;
  let u = Tm.mark_ctx u in
  {print = (nm,[]); value = Let u}, Ty.to_string t

  let dim v =
    match v.value with
    |Coh c -> Coh.dim c
    |Let t -> Tm.dim t

  let suspend v i =
    match v.value with
    |Coh coh -> {print = v.print; value = Coh (Coh.suspend coh i)}
    |Let tm ->
      let newtm = Tm.suspend tm i in
      let newtm = Tm.mark_ctx newtm in
      {print = v.print; value = Let newtm}

  let ty v =
    match v.value with
    |Coh coh -> (Ctx.of_ps (Coh.ps coh), Coh.target coh)
    |Let t -> let open Tm in (t.c, t.ty)

  let ctx v =
    match v.value with
    |Coh c -> (Ctx.of_ps (Coh.ps c))
    |Let t -> let open Tm in t.c

  let to_names ctx func =
    let fresh = Ctx.max_used_var ctx in
    let vars = List.rev (Ctx.explicit_domain ctx) in
    let rec names l fresh =
      match l with
      |[] -> []
      |i::l -> (List.get i vars, (New (fresh), New (fresh + 1)))::(names l (fresh + 2))
    in names (func) (fresh + 1)

  let print_list l =
    let rec aux l =
      match l with
      |[] -> ""
      |i::l -> Printf.sprintf "%d %s" i (aux l)
    in Printf.sprintf "[%s]" (aux l)

  let functorialize v func evar =
    match func with
    |[] -> v
    |_ ->
      let newprint =
        match v.print with
        |nm,[] -> nm,func
        |_,l -> Printf.sprintf "nm_#%s" (print_list l), func
      in
      let ctx = ctx v in
      let func = to_names ctx func in
      let newval =
        match v.value with
        |Coh coh -> Coh (Coh.functorialize coh func evar)
        |Let tm -> Let (Tm.functorialize tm func)
      in {print = newprint; value = newval}

  let check_equal v1 tm1 s1 v2 tm2 s2 src =
    match (v1.value, v2.value) with
    |Coh _, Coh _ -> Sub.check_equal s1 s2
    |Let t1, Let t2 -> Tm.check_equal src (Sub.apply_Tm s1 t1) (Sub.apply_Tm s2 t2)
    |Let t, Coh _ -> Tm.check_equal src (Sub.apply_Tm s1 t) tm2
    |Coh _, Let t -> Tm.check_equal src tm1 (Sub.apply_Tm s2 t)

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
  val _forget : t -> Unchecked.ty
  val _from_unchecked : Ctx.t -> Unchecked.ty -> t
  val apply : t -> Sub.t -> t

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

  let rec _from_unchecked c t =
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
  let make c e =
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
    | Arr(a,_,_) -> 1 + dim a

  (** Expression from a type. *)
  (* TODO: can we remove this? *)
  let reinit t : ty =
    match t.e with
    | Obj -> Obj
    | Arr(_,u,v) -> Arr (Tm.reinit u, Tm.reinit v)

  let rec _forget t =
    match t.e with
    | Obj -> Unchecked.Obj
    | Arr (a,u,v) -> Unchecked.Arr (_forget a, Tm._forget u, Tm._forget v)

  let rec unify (ty1 : t) (ty2 : t) l =
    match ty1.e ,ty2.e with
    | Obj, _ -> l
    | Arr(a,u,v), Arr(a',u',v') ->
       let l = unify a a' l in
       let l = Tm.unify u u' l
       in Tm.unify v v' l
    | _, _ -> raise UnableUnify

  let apply t s =
    _from_unchecked (Sub.src s) (Unchecked.ty_apply_sub (_forget t) (Sub._forget s))

end

(** Operations on terms. *)
and Tm
    :
sig
  type expr =
    | CVar of cvar
    | Sub of evar * EnvVal.t * Sub.t
    | Coh of Coh.t * Sub.t
  and t = {c : Ctx.t; ty : Ty.t; e : expr}

  val free_vars : t -> cvar list
  val to_string : t -> string

  val infer : Ctx.t -> t -> Ty.t
  val check_equal : Ctx.t -> t -> t -> unit
  val check_type : Ctx.t -> t -> Ty.t -> unit
  val make : Ctx.t -> tm -> t * Ty.t
  val check : Ctx.t -> Unchecked.tm -> t
  val dim : t -> int

  val reinit : t -> tm
  val _forget : t -> Unchecked.tm
  val list_expl_vars : t -> var list

  val mark_ctx : t -> t
  val suspend : t -> int -> t
  val functorialize : t -> (cvar * (var * var)) list -> t

  val unify : t -> t -> ((CVar.t * Ty.t) * t option * bool) list -> ((CVar.t * Ty.t) * t option * bool) list

end
  =
struct
  (** An expression. *)
  type expr =
    | CVar of cvar (** a context variable *)
    | Sub of evar * EnvVal.t * Sub.t (** a substituted environment variable *)
    | Coh of Coh.t * Sub.t

  (** A term, i.e. an expression with given type in given context. *)
  and t = {c : Ctx.t; ty : Ty.t; e : expr}

  exception Unknown

  let free_vars tm =
    match tm.e with
    | CVar x -> [x]
    | Sub (_,_,sub) -> Sub.free_vars sub
    | Coh (_,sub) -> Sub.free_vars sub

  let to_string tm =
    match tm.e with
    | CVar x -> CVar.to_string x
    | Sub (_,v,s) ->
       let open EnvVal in
       Printf.sprintf "(%s %s)" (fst(v.print)) (Sub.to_string_func s (snd(v.print)))
    | Coh (_,_) -> assert false

  let check_equal ctx tm1 tm2 =
    (* debug "checking equality between %s and %s" (to_string tm1)(to_string tm2); *)
    match tm1.e, tm2.e with
    | CVar x,CVar y ->
      if not (x = y)
      then
	raise (NotEqual (to_string tm1, to_string tm2))
      else ()
    | Sub(_,v1,s1),Sub(_,v2,s2) ->
       EnvVal.check_equal v1 tm1 s1 v2 tm2 s2 ctx
    | Coh(_,_),Coh(_,_) -> assert false
    | Coh _, Sub _ | Sub _, Coh _ -> assert false
    | CVar _, Sub _ |Sub _, CVar _ | CVar _, Coh _ | Coh _, CVar _ ->
       raise (NotEqual (to_string tm1, to_string tm2))

  (** Infer the type of an expression. *)
  let infer_expr ctx tme =
    match tme with
    | CVar x -> Ctx.ty_var ctx x
    | Sub (_,v,s) ->
       let _,ty = EnvVal.ty v in
       Sub.apply_Ty s ty
    | Coh (_,_) -> assert false

  (** Infer the type of a term. *)
  let infer ctx tm =
    try Ctx.check_sub_ctx tm.c ctx; tm.ty
    with _ -> infer_expr ctx tm.e

  (** Check that term has given type. *)
  let check_type ctx e t  =
    Ty.check_equal ctx (infer ctx e) t

  (* TODO: do we really need this? *)
  let reinit tm =
    match tm.e with
    | CVar v -> Var (CVar.to_var v)
    | Sub (x,_,s) -> Sub (Var (EVar.to_var x), Sub.reinit s,[])
    | Coh(_,_) -> assert false

  let rec _forget tm =
    match tm.e with
    | CVar v -> Unchecked.Var (CVar.to_var v)
    | Coh(c,s) ->
       let ps,t = Coh._forget c in
       let s = Sub._forget_to_ps s in
       Unchecked.Coh (ps,t,s)
    | Sub (x,_,s) ->
       let _,t = Env.val_var x 0 [] in
       match t.value with
       | Coh (ps,ty) -> Unchecked.Coh(PS._forget ps, Ty._forget ty, Sub._forget_to_ps s)
       | Let t -> Unchecked.tm_apply_sub (_forget t) (Sub._forget s)

  let list_expl_vars tm : var list =
    match tm.e with
    | CVar v -> [(CVar.to_var v)]
    | Sub (_,_,s) -> Sub.list_expl_vars s
    | Coh(_,s) -> Sub.list_expl_vars s

  let mark_ctx t =
    {c = Ctx.mark t.c; ty = t.ty; e = t.e}

  let suspend tm i =
    let ct = tm.c in
    let ct = Ctx.suspend ct i in
    let tm = reinit tm in
    fst (Tm.make ct tm)

  let functorialize tm l =
    let c = Ctx.functorialize tm.c l in
    let rec func_expr e =
      match e with
      | CVar v -> begin
          try Var (snd (List.assoc v l))
          with Not_found -> Var (CVar.to_var v)
        end
      | Sub (x,_,s) ->
         let vars = List.map (fun x -> CVar.to_var (fst x)) l in
         let reinit_s = Sub.reinit s in
         let functed_s = List.map (fun t -> func_expr t.e) (Sub.explicit s) in
         let rec func s i =
           match s with
           |[] -> []
           |(a::s) when List.exists (fun v -> List.mem v vars) (list_vars a) -> i::(func s (i+1))
           |(_::s) -> func s (i+1)
         in
         Sub (Var (EVar.to_var x),(functed_s),func (reinit_s) 0)
      | Coh(_,_) -> assert false
    in fst (Tm.make c (func_expr (tm.e)))

  let dim tm =
    Ctx.dim tm.c

  (** Create a term from an expression. *)
  (* TODO: return a value of type t instead of a pair *)
  let make c e =
    let e = remove_let_tm e in
    let already_known = Hashtbl.find_all Hash.tbtm e in
    let rec aux l = match l with
      | [] -> raise Unknown
      | tm::q -> try Ctx.check_sub_ctx tm.c c; (tm, tm.ty) with _ -> aux q
    in
    try aux already_known
    with Unknown ->
      (* debug "building term %s in context %s" (string_of_tm e) (Ctx.to_string c); *)
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
             |Var v -> let v = EVar.make v in Env.val_var v i func
             |(Sub (_,_,_) | Letin_tm(_,_,_)) -> assert false
           in let tar,ty = EnvVal.ty t in
              (* debug "got the context %s" (Ctx.to_string tar); *)
              let s = Sub.mk (List.map fst s) c tar in
              let ty = Sub.apply_Ty s ty in
              ({c = c; ty = ty; e = Sub(v,t,s)}, ty)
        | Letin_tm _ -> assert false
      in Hashtbl.add Hash.tbtm e newtm; newtm,newty

  let check c t =
    match t with
    | Unchecked.Var x ->
       let x = CVar.make x in
       let e, ty  = CVar x, Ctx.ty_var c x in
       ({c; ty; e})
    | Unchecked.Coh (ps,t,s) ->
       let ps = PS.check ps in
       let t = Ty._from_unchecked (Ctx.of_ps ps) t in
       let coh = Coh.check ps t in
       let sub = Sub.check_to_ps c s ps in
       let e, ty = Coh(coh,sub), Ty.apply t sub in
       {c; ty; e}


  let unify (tm1 : t) (tm2 : t) l =
    match tm1.e, tm2.e with
    | CVar u, _ ->
       let rec replace l =
         match l with
         | (((v,ty), None, _)::l) when u = v -> ((v,ty), Some tm2, true)::l
         | ((((v,_), Some _, _)::_) as l) when u = v -> l
         (* TODO : check compatibility between the constraints *)
         | a::l -> a::(replace l)
         | [] -> []
       in
       replace l
    | Sub(_,_,s), Sub (_,_,s') ->
       Sub.unify s s' l
    | _, CVar _ -> raise UnableUnify
    | _,_ -> assert false
end

(* -- Module with a specific type for well-defined coherences
    -- They are different from normal type, they need to be substituted *)
(** A coherence. *)
and Coh
    : sig
  type t = PS.t * Ty.t

  val mk : PS.t -> ty -> t
  val _to_string : t -> string
  val ps : t -> PS.t
  val dim : t -> int
  val target : t -> Ty.t
  val suspend : t -> int -> t
  val functorialize : t -> (cvar * (var * var)) list -> var ->  t
  val _forget : t -> Unchecked.ps * Unchecked.ty
  val check : PS.t -> Ty.t -> t
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

  let _to_string (ps,t) =
    Printf.sprintf "Coh {%s |- %s}"
      (PS.to_string ps)
      (Ty.to_string t)

  let ps (ps,_) = ps

  let target (_,t) = t

  let dim (ps,_) = PS.dim ps

  let suspend (ps,t) i =
    let t = Ty.reinit t in
    let ps = PS.suspend ps i in
    (Coh.mk ps t)

  let functorialize (ps,_) l evar =
    match l with
    |[] -> assert(false)
    |(v,(v',al))::l ->
      let rec funcps l = match l with
        |[] -> let ps = PS.functorialize ps v v' al in
               ps,[CVar.to_var v,v']
        |(v,(v',al))::l -> let ps,repl = funcps l in
                   let newps = PS.functorialize ps v v' al in
                   newps,(CVar.to_var v,v')::repl
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

  let _forget (ps,t) = (PS._forget ps, Ty._forget t)
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

(** Operations on environments. *)
and Env : sig

  val add_let : var -> (var * ty) list -> tm -> string
  val add_let_check : var -> (var * ty) list -> tm -> ty -> string
  val add_coh : var -> (var * ty) list -> ty -> unit
  val init : unit -> unit
  val val_var : EVar.t -> int -> int list -> EVar.t * EnvVal.t
end
  = GAssoc(EVar)(EnvVal)

type kTm = Tm.t
type kTy = Ty.t

let init_env = Env.init

let add_coh_env = Env.add_coh

let add_let_env v c u =
  Env.add_let v c u

let add_let_env_of_ty v c u t =
  Env.add_let_check v c u t


let mk_tm c e =
  let c = Ctx.make c in
  let e,t = Tm.make c e in
  (Tm.to_string e, Ty.to_string t)

let mk_tm_of_ty c e t =
  let c = Ctx.make c in
  let _,t' = Tm.make c e in
  let t = Ty.make c t in
  Ty.check_equal c t' t
