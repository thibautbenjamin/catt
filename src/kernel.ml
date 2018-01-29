open Stdlib
open Settings
open Common
open PShape
open ExtSyntax
		   
		   

(** TODO : write both of them in one go*)       
module EVar
: sig 
    type t
    val to_string : t -> string
    val mk : var -> t
    val to_var : t -> var 
  end
= struct
  type t = var

  let to_string v =
      Var.to_string v
      
  let mk v = v

  let to_var v = v
end


module CVar
: sig 
    type t
    val to_string : t -> string
    val mk : var -> t
    val to_var : t -> var
  end
= struct
    type t = var

    let to_string v =
      Var.to_string v
	       
    let mk v = v

    let to_var v = v 
end

type evar = EVar.t
type cvar = CVar.t

let var_of_cvar = CVar.to_var
	       
(** --Substitutions are lists of terms, they come with 	    
	 - maker
	 - equality decision procedure
	 - application on a term 
*)
module rec Sub 
: sig
  type t = private (Expr.t list)
		     
  (** Structural functions *)
  val mk : Env.t -> expr list -> Ctx.t -> PS.t -> t
  val mk_elaborated : Env.t -> expr list -> Ctx.t -> PS.t -> t
  val to_expr : t -> expr list
						    
  (** Syntactic properties *)		    
  val free_vars : t -> cvar list
  val apply : Env.t -> t -> Ctx.t -> Ctx.t -> Expr.t -> Expr.t
  val dim : Env.t -> Ctx.t -> expr list -> int
					
  (** Equality procedures *)
  val checkEqual : Env.t -> Ctx.t -> t -> t -> unit

  (** Printing *)	
  val to_string : t -> bool -> string
				 
  (** Well-definedness procedure *)
  val check : Env.t -> t  -> Ctx.t -> Ctx.t -> unit
end
= struct
    type t = Expr.t list

		    
    (** --------------------
	Syntactic properties
        --------------------  *) 
    let free_vars s =
      List.concat (List.map Expr.free_vars s)
		  
    let rec apply_var (s:t) (tar:Ctx.t) x =
      match s,tar with
      |_,_ when Ctx.isEmpty tar ->
	raise (UnknownId (CVar.to_string x))
      |t::l, _ ->
	let ((y,_),tar) = (Ctx.head tar, Ctx.tail tar) in
	if y = x
	then t
	else apply_var l tar x
      |[], _ -> assert (false)     

    let rec compose env src tar s s' =
      List.rev (List.map (fun t -> Expr.to_expr (apply env s tar src t)) s')
    and apply env (s:t) tar sour e =
      let open Expr in
      match e with
      |CVar x -> apply_var s tar x
      |Obj -> Obj
      |Arr (a,u,v) -> Arr (apply env s tar sour a, apply env s tar sour u, apply env s tar sour v)
      |Sub (t,s') -> let newtar = Cut.ps t in Sub (t, Sub.mk_elaborated env (compose env sour tar s (s' :> Expr.t list)) sour newtar)

    (** -----------------
	Typing procedures
        -----------------  *) 
    let rec checkEqual env ctx s1 s2 =
      match s1,s2 with
      |[],[] -> ()
      |t1::s1,t2::s2 ->
	Expr.checkEqual env ctx t1 t2;
	checkEqual env ctx s1 s2
      |_,_ -> raise NotValid

    let rec check env s src (tar:Ctx.t) =
      match s,(tar :> (cvar * Expr.t) list)
      with
      |[],[] -> ()
      |(_::_,[] |[],_::_) -> raise NotValid
      |t::s,_ ->
	let ((x,u),tar) = (Ctx.head tar,Ctx.tail tar) in
	check env s src tar;
	Expr.checkT env tar u;
	Expr.checkType env src t (apply env s tar src u)
		       
    (** --------
	Printing
        --------  *)   
    let rec to_string s abbrev =
      match s with
      |[] -> ""
      |u::s ->
	Printf.sprintf "%s (%s)"
		       (to_string s abbrev)
		       (Expr.to_string u abbrev)

		       
    (** --------------------
	Structural functions
        --------------------  *)
    let elaborate env l src tar =
      let rec complete l x a ps =
	match ps with
	|PNil ->
	  [x]
	|PCons ps->
	  let a',x',y' =
	    match (a:Expr.t) with
	    |Arr(a',x',y') -> a',x',y'
	    |_ -> assert(false)
	  in
	  x::y'::(complete l x' a' ps)
	|(PDrop _) as ps -> find_max l ps 
      and find_max l ps =
	match l,ps with
	|x::[], PNil ->
	  let x = Expr.mk env src x in
	  [x]
	|[],_ -> raise NotValid
	| _, PNil -> raise NotValid
	|f::l, PDrop(PCons(ps)) ->
	  let f = Expr.mk env src f in
	  let a,x,y =
	    match (Expr.infer env src f) with
	    |Arr(a,x,y) -> a,x,y
	    |_ -> assert(false)
	  in
	  let s = complete l x a ps in
	  f::y::s
	|s,PDrop ps -> find_max s ps
	|s, PCons _ -> assert(false)
      in
      let s = find_max (List.rev l) (PS.shape tar) in
      let () = check env s src (Ctx.of_ps tar) in
      s

    let mk_elaborated env l src tar =
      let rec aux l (tar : Ctx.t) =
	match l,(tar :> (cvar * Expr.t) list) with
	|[],[] -> []
	|(_::_,[] |[],_::_) -> raise NotValid
	|t::s,_ ->
	  let ((x,u),tar) = (Ctx.head tar,Ctx.tail tar) in
	  let s = aux s tar in
	  let t = Expr.mk env src t in
	  let () = Expr.checkType env src t (apply env s tar src u)
	  in t::s
      in aux (List.rev l) (Ctx.of_ps tar)
        
    let mk env l src tar =
      if !partial_substitutions then
	elaborate env l src tar
      else
        mk_elaborated env l src tar
      
               
    let dim env ctx l =
      let rec max l i =
	match l with
	| [] -> i
	| t::l -> if t > i
		  then max l t
		  else max l i
      in
      let l  = (List.map (fun x -> Expr.dim (Expr.infer env ctx (Expr.mk env ctx x))) l)
      in
      match l with
      |t::l -> max l t
      |[] -> raise EmptySub

    let to_expr s =
      List.rev (List.map Expr.to_expr s)		   
  end

    
(** -- Contexts are association lists of variables and terms in normal form.
   -- They are provided with 	    
	 - maker (normalization and well-definedness)
	 - equality decision procedure
*)
and Ctx
: sig
  type t = private ((cvar * Expr.t) list)

  (** Makers *)
  val empty : unit -> t
  val add : Env.t -> t -> var -> expr -> t
  val add_norm : Env.t -> t -> var -> Expr.t -> t
  val mk : Env.t -> (var * expr) list -> t
  val of_ps : PS.t -> t
					       
  (** Structural operations *)
  val head : t -> cvar * Expr.t
  val tail : t -> t
  val suspend : Env.t -> t -> int -> t
		    
  (** Syntactic properties *)
  val ty_var : t -> cvar -> Expr.t
  val free_vars : t -> cvar list
  val mem : t -> cvar -> bool
  val to_expr : t -> (var * expr) list

  (** Equality procedure *)
  val isEmpty : t -> bool
  val checkEqual : Env.t -> t -> t -> unit

  (** Printing *)
  val to_string : t -> bool -> string
end
= struct
  type t = (cvar * Expr.t) list
                        
  let ty_var ctx x =
    try
      List.assoc x ctx
    with
    | Not_found -> raise (UnknownId (CVar.to_string x))

  (** ------
      Makers
      ------ *)
  let empty _ = []

  let add env (ctx :Ctx.t) x u =
    let u = Expr.mk env ctx u in
    let x = CVar.mk x in
    (ctx :> t)@[(x,u)]


  let add_norm env (ctx :Ctx.t) x u =
    let () = Expr.checkT env ctx u in
    let x = CVar.mk x in
    (ctx :> t)@[(x,u)]

  let rec mk env  l =
    let rec aux l ctx =
      match l with
      |[] -> ctx
      |(x,t)::l ->
	let ctx = Ctx.add env ctx x t in
	aux l ctx
    in aux l (Ctx.empty ()) 

  let rec of_ps ps =
    let open PS in
    match ps with
    |PNil (x,t) ->  [(x,t)]
    |PCons (ps,(x1,t1),(x2,t2)) ->
      (of_ps ps)@[(x1,t1);(x2,t2)]
    |PDrop ps -> of_ps ps

		       
  (** ---------------------
      Structural operations
      --------------------- *)
  let rec head ctx = match ctx with
    |[] -> assert(false)
    |a::[] -> a
    |_::ctx -> head ctx
  	     
  let rec tail ctx = match ctx with 
    |[] -> assert(false)
    |_::[] -> []
    |a::ctx -> a::(tail ctx)


		    
  let suspend env (ctx : t) i =
    let open Var in
    assert (i>=1);
    let rec aux k c ty=
      match k with
      |k when k = i -> c,ty
      |k ->
	let k' = k+1 in
	let ty = Arr (Var (New (2*k-1)), Var (New (2*k)))
	in
	let ty' = Arr (Var (New (2*k'-1)), Var (New (2*k')))
	in aux k'
	     (Ctx.add 
		env
		(Ctx.add env c (New ((2*k')-1)) ty)
		(New (2*k'))
		ty)
	     ty'
    in
    let ctx' = Ctx.add env
		   (Ctx.add_norm env (Ctx.empty ()) (New 1) Expr.Obj)
		   (New 2)
		   Obj    
    in
    let ctx',ty = aux 1 ctx' (Arr (Var (New 1), Var (New 2))) in
    let rec comp c res = match c with
      |(x,Expr.Obj)::c -> comp c (Ctx.add env res (var_of_cvar x) ty)
      |(x,tx)::c -> comp c (Ctx.add env res (var_of_cvar x) (Expr.to_expr tx))
      |[] -> res
    in
    comp ctx ctx'
    

    

  (** --------------------
      Syntactic properties
      -------------------- *)
 let free_vars ctx = List.map fst ctx

 let rec mem c v = match c with
   |[] -> false
   |(x,u)::c when x = v -> true
   |_::c -> mem c v


 let to_expr c =
   List.map
     (fun (v,t) -> (CVar.to_var v, (Expr.to_expr t)))
     c
		
  (** -------------------
      Equality procedures
      ------------------- *)
 let isEmpty c =
    match c with
    |[] -> true
    |_ -> false
		
  let rec checkEqual env ctx1 ctx2 =
    let rec equal c (ctx1 : Ctx.t) (ctx2 : Ctx.t) = 
      match ((ctx1 :> (cvar * Expr.t) list),
	     (ctx2 :> (cvar * Expr.t) list)) with
      |[],[] -> ()
      |_::_, _::_ ->
	let ((v1,x1),t1) = (Ctx.head ctx1, Ctx.tail ctx1) in
	let ((v2,x2),t2) = (Ctx.head ctx2, Ctx.tail ctx2) in
	if not (v1 = v2) then raise NotValid;
	Expr.checkEqual env c x1 x2;
        equal ctx1 t1 t2
      |_,_ -> raise NotValid
    in equal (Ctx.empty ()) ctx1 ctx2
						 
		   
  (** --------
      Printing
      -------- *)	      
 let rec to_string ctx abbrev =
   let to_string = (fun c -> to_string c abbrev) in
   match ctx with
   |[] -> ""
   |(x,t)::c ->
     Printf.sprintf "(%s,%s) %s"
		    (CVar.to_string x)
                    (Expr.to_string t abbrev)
                    (to_string c)
end


(** -- Pasting schemes are specific contexts
    -- They are provided with 	    
	 - makers (normalization and well-definedness)
	 - equality decision procedure
	 - specific operations (height, dimension, source, target)
*)
and PS
: sig
  type t = private
          |PNil of (cvar * Expr.t)
          |PCons of t * (cvar * Expr.t) * (cvar * Expr.t)
          |PDrop of t

  (** Maker *)
  val mk : Ctx.t -> t

  (** Syntactic properties *)
  val free_vars : t -> cvar list
  val to_expr : t -> (var*expr) list

  (** Structural operations *)
  val height : t -> int
  val dim : t -> int
  val source : int -> t -> t
  val target : int -> t -> t
  val shape : t -> pshape
  val suspend : Env.t -> t -> int -> t
			     
  (** Printing *)
  val to_string : t -> bool -> string
end
= struct
  exception Invalid
  
  type t =
    |PNil of (cvar * Expr.t)
    |PCons of PS.t * (cvar * Expr.t) * (cvar * Expr.t)
    |PDrop of PS.t


  (** --------------------
      Syntactic properties
      -------------------- *)
  let free_vars ps = Ctx.free_vars (Ctx.of_ps ps)
		
  (** -----
      Maker
      ----- *)
  (** Dangling variable. *)
  let rec marker ps =
    match ps with
    | PNil (x,t) -> x,t
    | PCons (ps,_,f) -> f
    | PDrop ps ->
       let f,tf = marker ps in
       match tf with
       | Expr.Arr (_,x,Expr.CVar y) ->
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


  let mk (l : Ctx.t) : t =
    let open Expr in 
    let rec close ps tx =
      match tx with
      | Obj -> ps
      | Arr (tx,_,_) -> close (PDrop ps) tx
      | _ -> assert(false)
    in
    let x0,l =
      match (l :> (cvar*Expr.t) list) with
      | (x,Obj)::l -> x,l
      | _ -> raise Invalid
    in
    let rec aux ps = function
      | (y,ty)::(f,tf)::l ->
         begin
           match tf with
           | Arr (_, CVar fx, CVar fy) ->
              if (y <> fy) then raise Invalid;
              let x,tx = marker ps in
              if x = fx then
                let fvps = PS.free_vars ps in
                assert (not (List.mem f fvps));
                assert (not (List.mem y fvps));
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
    aux (PNil(x0,Obj)) l

	
	
  (** ---------------------
      Structural operations
      --------------------- *)
  let rec height = function
    | PNil _ -> 0
    | PCons (ps,_,_) -> height ps + 1
    | PDrop ps -> height ps - 1

  let rec dim = function
    | PNil _ -> 0
    | PCons (ps,_,_) -> max (dim ps) (height ps + 1)
    | PDrop ps -> dim ps

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

  let rec shape ps =
    match ps with
    |PNil _ -> PShape.PNil
    |PCons (ps,_,_) -> PShape.PCons (shape ps)
    |PDrop ps -> PShape.PDrop (shape ps)

  let rec suspend env ps i =
    mk (Ctx.suspend env (Ctx.of_ps ps) i)
			      
  (** --------
      Printing
      -------- *)        
  let to_string ps abbrev =
    if abbrev
    then
      Ctx.to_string (Ctx.of_ps ps) abbrev
    else
      let rec print ps = 
	match ps with
	|PNil (x,t) ->
	  Printf.sprintf "[(%s,%s)]"
			 (CVar.to_string x)
			 (Expr.to_string t abbrev)
	|PCons (ps,(x1,t1),(x2,t2)) ->
	  Printf.sprintf "%s [(%s,%s) (%s,%s)]"
			 (print ps)
			 (CVar.to_string x1)
			 (Expr.to_string t1 abbrev)
			 (CVar.to_string x2)
			 (Expr.to_string t2 abbrev)
	|PDrop ps ->
	  Printf.sprintf " %s ! "
			 (print ps)
      in print ps

  let to_expr ps = Ctx.to_expr (Ctx.of_ps ps)

	
  end

(** -- Environnement is a association list of variable and coherences
    -- It is provided with 	    
	 - maker 
	 - association
*)    
and Env
: sig
  type t = private (evar * Coh.t) list

  (** Makers *)
  val empty : unit -> t
  val add : t -> var -> expr -> t

  (** Structural operation *)
  val val_var : t -> evar -> Coh.t
end
= struct
  type t = (evar * Coh.t) list

  (** ------
      Makers
      ------ *)
  let empty a = []

  let add env x u =
    let u = match u with
    |Coh (ps,u) ->
      let c = PS.mk (Ctx.mk env ps) in
      Coh.mk env c u
    |_ -> assert (false)
    in
    (EVar.mk x,u)::(env :> (evar * Coh.t) list)


  (** --------------------
      Structural operation
      -------------------- *)	     
  let val_var env x =
    try List.assoc x env
    with Not_found -> raise (UnknownCoh (EVar.to_string x))
end

    
and Expr
: sig
  type t = 
    |CVar of cvar
    |Obj
    |Arr of t * t * t
    |Sub of Cut.t * Sub.t
  
  val free_vars : t -> cvar list
  val to_string : t -> bool  -> string

  val checkT : Env.t -> Ctx.t -> t -> unit
  val infer : Env.t -> Ctx.t -> t -> t
  val checkEqual : Env.t -> Ctx.t -> t -> t -> unit
  val checkType : Env.t -> Ctx.t -> t -> t -> unit
  val mk : Env.t -> Ctx.t -> expr -> t

  val dim : t -> int
  val to_expr : t -> expr
  end
= struct
  type  t =
    |CVar of cvar
    |Obj
    |Arr of t * t * t
    |Sub of Cut.t * Sub.t

  let rec free_vars e =
    match e with
    |CVar x -> [x]
    |Obj -> []
    |Arr (t,u,v) -> List.unions [(free_vars t);(free_vars u);(free_vars v)]
    |Sub (_,sub) -> Sub.free_vars sub
  (* to be modified to include Cut.free_vars *)

    
  let rec to_string expr abbrev =
    let to_string  = fun u -> to_string u abbrev in 
    match expr with
    |CVar x -> CVar.to_string x
    |Obj -> "*"
    |Arr (t,u,v) ->
      if abbrev then
        Printf.sprintf "%s -> %s" (to_string u) (to_string v)
      else Printf.sprintf "%s | %s -> %s" (to_string t) (to_string u) (to_string v)
    |Sub (t,s) -> Printf.sprintf "%s.%s" (Sub.to_string s abbrev) (Cut.to_string t abbrev)

  let rec checkEqual env ctx e1 e2 =
    let equal = checkEqual env ctx in
    match e1, e2 with
    |CVar x,CVar y ->
      if not (x = y)
      then
	raise (NotEqual (to_string e1 true, to_string e2 true))
      else ()
    |Obj,Obj -> ()
    |Arr(t1,u1,v1),Arr(t2,u2,v2) ->
      equal t1 t2;
      equal u1 u2;
      equal v1 v2
    |Sub(t1,s1),Sub(t2,s2) ->
      let tar = Cut.checkEqual env t1 t2 in
      Sub.checkEqual env tar s1 s2
    |(CVar _|Obj |Arr _|Sub _),_ ->
      raise (NotEqual (to_string e1 true, to_string e2 true)) 
  (** TODO : prove that infer produces only normal forms 
       that are also valid types *)
  and infer env ctx e =
    match e with
    |CVar x -> Ctx.ty_var ctx x
    |Sub (e,s) ->
      let tar,ty = Cut.infer env e in
      Sub.check env s ctx tar;
      Sub.apply env s tar ctx ty
    |(Obj |Arr _) -> raise (HasNoType (Expr.to_string e true))
  and checkT env ctx e =
    match e with
    |Obj -> ()
    |Arr (t,u,v) ->
      checkT env ctx t;
      checkType env ctx u t;
      checkType env ctx v t
    |(CVar _ |Sub _) ->
      raise (IsNotType (Expr.to_string e true))
  and checkType env ctx e1 e2  =
    checkEqual env ctx (infer env ctx e1) e2 

  let mk env c (e:expr) =
    let rec translate  e = 
      match e with
      |Var v -> CVar (CVar.mk v)
      |Obj -> Obj
      |Arr (u,v) ->
	let u = translate u in
	let v = translate v in 
	let t = infer env c u in
	let t' = infer env c v in
	let () = checkEqual env c t t' in
	Arr (t,u,v)
      |Sub (t,s) ->
	let t,tar = Cut.mk env t (Sub.dim env c s) in
	let s = Sub.mk env s c tar in
	Sub (t,s)
      |Coh _ -> failwith "unsubstituted coherence"
    in
    let check e  =
      match e with
      |(CVar _ |Sub _) ->
	let _ = infer env c e in ()
      |Arr _ -> checkT env c e
      |Obj -> ()
    in
    let e = translate e
    in
    check e;
    e

  let rec dim t =
    match t with
    |Obj -> 0
    |Arr(a,t,u) -> 1 + dim a
    |_ -> assert (false)

  let rec to_expr t : expr=
    match t with
    |Obj -> Obj
    |Arr(_,u,v) -> Arr(to_expr u, to_expr v)
    |CVar v -> Var (CVar.to_var v)
    |Sub (t,s) -> Sub(Cut.to_expr t, Sub.to_expr s)
end
    
and Cut
: sig

  type t =
    |Fold of evar
    |Unfold of Coh.t		 
  val free_vars : t -> cvar list
  val to_string : t -> bool -> string
  val checkEqual : Env.t -> t -> t -> Ctx.t
  val infer : Env.t -> t -> Ctx.t * Expr.t
  val mk : Env.t -> expr -> int -> (t * PS.t)
  val to_expr : t -> expr
  val ps : t -> PS.t
end
= struct
  type t = 
    |Fold of evar
    |Unfold of Coh.t
		 
  let free_vars coh =
    match coh with
     |Fold x -> assert (false) (** Ignore this case for now *)
     |Unfold coh -> Coh.free_vars coh 

  let to_string coh abbrev =
    match coh with
    |Fold x -> EVar.to_string x
    |Unfold coh -> Coh.to_string coh abbrev
				  
  let checkEqual env e1 e2 =
    match e1, e2 with
    |Unfold coh1, Unfold coh2 -> Coh.checkEqual env coh1 coh2
    |(Fold _, _ |_, Fold _) -> assert (false)
    (** allowing cut rule : this case should be
	|Fold x, y -> checkEqual_norm (val_var x) y 
	and its symmetric case*)

  let infer env coh =
    match coh with
    |Fold _ -> assert (false) (** No cut rule yet *)
    |Unfold coh ->
      (Ctx.of_ps (Coh.ps coh), Coh.target coh)

  let ps coh =
    match coh with
    |Fold _ -> assert (false)
    |Unfold coh -> Coh.ps coh
        
  let mk env e i =
    match e with
    |Var v ->
      let coh = Env.val_var env (EVar.mk v) in
      let ps = Coh.ps coh in
      let j = PS.dim ps in
      if (j=i)
      then
	(Unfold coh, ps)
      else if i>j then
	let t = Expr.to_expr (Coh.target coh) in
        let ps = PS.suspend env ps (i-j) in
	(Unfold (Coh.mk env ps t), ps)
      else failwith "substitution not applied enough"
    |Coh (ps,t) ->
      let ps = PS.mk (Ctx.mk env ps) in
      let j = PS.dim ps in
      if (j=i) then
	(Unfold (Coh.mk env ps t), ps)
      else if i>j then
	let ps = PS.suspend env ps (i-j) in 
	(Unfold (Coh.mk env ps t), ps)
      else failwith "substitution not applied enough"

    |(Obj |Arr _|Sub _) -> raise BadUnderSub

  let rec to_expr c =
    match c with
    |Fold v -> Var (EVar.to_var v)
    |Unfold coh -> Coh.to_expr coh

end

(** -- Module with a specific type for well-defined coherences
    -- They are different from normal type, they need to be substituted *)    
and Coh    
: sig
  type t = private (PS.t * Expr.t)   

  val mk : Env.t -> PS.t -> expr -> t
  val free_vars : t -> cvar list
  val to_string : t -> bool -> string
  val checkEqual : Env.t -> t -> t -> Ctx.t
  val ps : t -> PS.t
  val target : t -> Expr.t
  val to_expr : t -> expr
end
= struct
  type t = PS.t * Expr.t
		    
  let check env ps t = 
    if List.included (PS.free_vars ps) (Expr.free_vars t)
    then  (ps,t)
    else
      let open Expr in
      let a,f,g = match t with
        |Arr(a,f,g) -> (a,f,g)  
        |_ -> raise NotAlgebraic
      in
      let i = PS.dim ps in
      let pss = PS.source (i-1) ps
      and pst = PS.target (i-1) ps in
      let ctxs = Ctx.of_ps pss
      and ctxt = Ctx.of_ps pst in
      let fvf = List.union (free_vars f) (free_vars a)
      and fvg = List.union (free_vars g) (free_vars a) in
      try
	let tf = Expr.infer env ctxs f in
	let tg = Expr.infer env ctxt g in
	begin
	  Expr.checkT env ctxs tf;
	  Expr.checkT env ctxt tg;
	  if List.included (PS.free_vars pss)
			    fvf &&
	     List.included (PS.free_vars pst)
			   fvg
	  then (ps,t) 
	  else raise NotAlgebraic
	end;
      with
      |UnknownId _ -> raise NotAlgebraic
			    
  let mk env ps t =
    let t = Expr.mk env (Ctx.of_ps ps) t in
    check env ps t

      
  let free_vars (ps,t) =
    List.union (PS.free_vars ps) (Expr.free_vars t)

  let to_string (ps,t) abbrev =
    Printf.sprintf "Coh {%s |- %s}"
		   (PS.to_string ps abbrev)
		   (Expr.to_string t abbrev)

  let checkEqual env (ps1,t1) (ps2,t2) =
    let c1 = Ctx.of_ps ps1 and c2 = Ctx.of_ps ps2 in
    Ctx.checkEqual env c1 c2;
    Expr.checkEqual env c1 t1 t2; c1

  let ps (ps,t) = ps

  let target (ps,t) = t

  let to_expr (ps,t) = Coh (PS.to_expr ps, Expr.to_expr t)

end    
        
type env = Env.t
type ctx = Ctx.t
type kexpr = Expr.t

             
let empty_env = Env.empty ()
let add_env = Env.add

let checkType = Expr.checkType
let mk_expr = Expr.mk
let mk_ctx = Ctx.mk
