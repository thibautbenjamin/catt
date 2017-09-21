open Stdlib
open Common
open ExtSyntax
		   
		   

(** TODO : write both of them in one go*)       
module EVar
: sig 
    type t
    val to_string : t -> string
    val mk : var -> t
  end
= struct
  type t = var

  let to_string v = Var.to_string v

  let mk v = v
end


module CVar
: sig 
    type t
    val to_string : t -> string
    val mk : var -> t
  end
= struct
  type t = var

  let to_string v = Var.to_string v

  let mk v = v
end

type evar = EVar.t
type cvar = CVar.t
    
    
	       
(** --Substitutions are lists of terms, they come with 	    
	 - maker
	 - equality decision procedure
	 - application on a term 
*)
module rec Sub 
: sig
  type t = private (Expr.t list)
		     
  (** Structural functions *)
  val mk : Env.t -> expr list -> Ctx.t -> Ctx.t -> t

  (** Syntactic properties *)		    
  val free_vars : t -> Var.t list
  val apply : t -> Ctx.t -> Expr.t -> Expr.t

  (** Equality procedures *)
  val checkEqual : Env.t -> Ctx.t -> t -> t -> unit

  (** Printing *)	
  val to_string : t -> bool -> string
				 
  (** Temporary *)
  val check : Env.t -> t  -> Ctx.t -> Ctx.t -> unit
end
= struct
    type t = Expr.t list

		    
    (** --------------------
	Syntactic properties
        --------------------  *) 
    let free_vars s =
      List.concat (List.map Expr.free_vars s)
			   
    let rec apply_var (s:t) (tar:Ctx.t) (x : Var.t) =
      match s,tar with
      |_,_ when Ctx.isEmpty tar ->
	raise (UnknownId (Var.to_string x))
      |t::l, _ ->
	let ((y,_),tar) = (Ctx.head tar, Ctx.tail tar) in
	if y = x
	then t
	else apply_var l tar x
      |[], _ -> assert (false)

    let rec apply (s:t) tar e =
      let open Expr in
      match e with
      |CVar x -> apply_var s tar x
      |Obj -> Obj
      |Arr (a,u,v) ->
	Arr (apply s tar a, apply s tar u, apply s tar v)
      |Sub _ -> assert (false)

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
      match s,(tar :> (Var.t * Expr.t) list)
      with
      |[],[] -> ()
      |(_::_,[] |[],_::_) -> raise NotValid
      |t::s,_ ->
	let ((x,u),tar) = (Ctx.head tar,Ctx.tail tar) in
	check env s src tar;
	Expr.checkT env tar u;
	Expr.checkType env src t (apply s tar u)

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
    let mk env l src tar =
      let rec aux l (tar : Ctx.t) =
	match l,(tar :> (Var.t * Expr.t) list) with
	|[],[] -> []
	|(_::_,[] |[],_::_) -> raise NotValid
	|t::s,_ ->
	  let ((x,u),tar) = (Ctx.head tar,Ctx.tail tar) in
	  let s = aux s tar in
	  let t = Expr.mk env src t in
	  let () = Expr.checkT env tar u in
	  let () = Expr.checkType env src t (apply s tar u)
	  in t::s
      in aux (List.rev l) tar
 			
end

(** -- Contexts are association lists of variables and terms in normal form.
   -- They are provided with 	    
	 - maker (normalization and well-definedness)
	 - equality decision procedure
*)
and Ctx
: sig
  type t = private ((Var.t * Expr.t) list)

  (** Makers *)
  val empty : unit -> t
  val add : Env.t -> t -> Var.t -> expr -> t
  val mk : Env.t -> (var * expr) list -> t
  val of_ps : PS.t -> t
					       
  (** Structural operations *)
  val head : t -> Var.t * Expr.t
  val tail : t -> t

  (** Syntactic properties *)
  val ty_var : t -> Var.t -> Expr.t
  val free_vars : t -> Var.t list
  val mem : t -> Var.t -> bool

  (** Equality procedure *)
  val isEmpty : t -> bool
  val checkEqual : Env.t -> t -> t -> unit

  (** Printing *)
  val to_string : t -> bool -> string
end
= struct
  type t = (Var.t * Expr.t) list
                        
  let ty_var ctx x = try List.assoc x ctx with Not_found -> raise (UnknownId (Var.to_string x))

  (** ------
      Makers
      ------ *)
  let empty _ = []

  let add env (ctx :Ctx.t) x u =
    let u = Expr.mk env ctx u in 
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


  (** --------------------
      Syntactic properties
      -------------------- *)
 let free_vars ctx = List.map fst ctx

 let rec mem c v = match c with
   |[] -> false
   |(x,u)::c when x = v -> true
   |_::c -> mem c v

		    
  (** -------------------
      Equality procedures
      ------------------- *)
 let isEmpty c =
    match c with
    |[] -> true
    |_ -> false
		
  let rec checkEqual env ctx1 ctx2 =
    let rec equal c (ctx1 : Ctx.t) (ctx2 : Ctx.t) = 
      match ((ctx1 :> (Var.t * Expr.t) list),
	     (ctx2 :> (Var.t * Expr.t) list)) with
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
		    (Var.to_string x)
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
          |PNil of (Var.t * Expr.t)
          |PCons of t * (Var.t * Expr.t) * (Var.t * Expr.t)
          |PDrop of t

  (** Maker *)
  val mk : Ctx.t -> t

  (** Syntactic properties *)
  val free_vars : t -> Var.t list

  (** Structural operations *)
  val height : t -> int
  val dim : t -> int
  val source : int -> t -> t
  val target : int -> t -> t

  (** Printing *)
  val to_string : t -> bool -> string
end
= struct
  exception Invalid
  
  type t =
    |PNil of (Var.t * Expr.t)
    |PCons of PS.t * (Var.t * Expr.t) * (Var.t * Expr.t)
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


  let mk l : t =
    let open Expr in 
    let x0,l =
      match l with
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
      | [] -> ps
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

  (** --------
      Printing
      -------- *)        
  let to_string ps abbrev =
    Ctx.to_string (Ctx.of_ps ps) abbrev 
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
  val val_var : t -> EVar.t -> Coh.t
end
= struct
  type t = (EVar.t * Coh.t) list

  (** ------
      Makers
      ------ *)
  let empty a = []

  let add env x u =
    let u = match u with
    |Coh (ps,u) ->
      let c = Ctx.mk env ps in
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
    |CVar of Var.t
    |Obj
    |Arr of t * t * t
    |Sub of Cut.t * Sub.t
  
  val free_vars : t -> Var.t list
  val to_string : t -> bool  -> string

  val checkT : Env.t -> Ctx.t -> t -> unit
  val infer : Env.t -> Ctx.t -> t -> t
  val checkEqual : Env.t -> Ctx.t -> t -> t -> unit
  val checkType : Env.t -> Ctx.t -> t -> t -> unit
  val mk : Env.t -> Ctx.t -> expr -> t
  end
= struct
  type  t =
    |CVar of Var.t
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
    let to_string  = fun u -> Expr.to_string u abbrev in 
    match expr with
    |CVar x -> Var.to_string x
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
      Sub.apply s tar ty
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
      |Var v -> CVar v
      |Obj -> Obj
      |Arr (u,v) ->
	let u = translate u in
	let v = translate v in 
	let t = infer env c u in
	let t' = infer env c v in
	let () = checkEqual env c t t' in
	Arr (t,u,v)
      |Sub (t,s) ->
	let t,tar = Cut.mk env t in
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
end
    
and Cut
: sig

  type t =
    |Fold of EVar.t
    |Unfold of Coh.t		 
  val free_vars : t -> Var.t list
  val to_string : t -> bool -> string
  val checkEqual : Env.t -> t -> t -> Ctx.t
  val infer : Env.t -> t -> Ctx.t * Expr.t
  val mk : Env.t -> expr -> (t * Ctx.t)
end
= struct
  type t = 
    |Fold of EVar.t
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

  let mk env e =
    match e with
    |Var v ->
      let coh = Env.val_var env (EVar.mk v) in
      (Unfold coh, Ctx.of_ps(Coh.ps coh))
    |Coh (ps,t) ->
      let c = Ctx.mk env ps in
      (Unfold (Coh.mk env c t), c)
    |(Obj |Arr _|Sub _) -> failwith "problem"
end

(** -- Module with a specific type for well-defined coherences
    -- They are different from normal type, they need to be substituted *)    
and Coh    
: sig
  type t = private (PS.t * Expr.t)   

  val mk : Env.t -> Ctx.t -> expr -> t
  val free_vars : t -> Var.t list
  val to_string : t -> bool -> string
  val checkEqual : Env.t -> t -> t -> Ctx.t
  val ps : t -> PS.t
  val target : t -> Expr.t
end
= struct
  type t = PS.t * Expr.t
		    
  let mk env ctx t =
    let ps = PS.mk ctx in
    let t = Expr.mk env ctx t in
    if List.included (PS.free_vars ps) (Expr.free_vars t)
    then  (ps,t)
    else
      let open Expr in
      let f,g = match t with
        |Arr(a,f,g) -> (f,g)  
        |_ -> raise NotAlgebraic
      in
      let i = PS.dim ps in
      let pss = PS.source (i-1) ps
      and pst = PS.target (i-1) ps in
      let ctxs = Ctx.of_ps pss
      and ctxt = Ctx.of_ps pst in
      try
	let tf = Expr.infer env ctxs f in
	let tg = Expr.infer env ctxt g in
	begin
	  Expr.checkT env ctxs tf;
	  Expr.checkT env ctxt tg;
	  if List.included (PS.free_vars pss) (free_vars f) && List.included (PS.free_vars pst) (free_vars g)
	  then (ps,t) 
	  else raise NotAlgebraic
	end;
      with
      |UnknownId _ -> raise NotAlgebraic
	
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

end    
        
type env = Env.t

let empty_env = Env.empty ()
let add_env = Env.add

					   
