open Stdlib
open Common

       
			 
module Var = struct
  type t =
  |Name of string

  let to_string v =
  match v with
  |Name s -> s
end


module EVar = struct
  type t =
  |Name of string

  let to_string v =
  match v with
  |Name s -> s
end

	       
(** --Substitutions are lists of terms, they come with 	    
	 - maker
	 - normal form 
	 - equality decision procedure
	 - well-definedness checking procedure 
	 - application on a term 
*)
module rec Sub 
: sig
  type t = private (Expr.t list)
		     
  (** Structural functions *)
  val mk : Env.t ->  Expr.t list -> t

  (** Syntactic properties *)		    
  val free_vars : t -> Var.t list
  val apply : t -> Ctx.t -> Expr.t -> Expr.t

  (** Typing procedures *)
  val normalize : Env.t -> Ctx.t -> t -> t 
  val checkEqual : Env.t -> Ctx.t -> t -> t -> unit
  val check : Env.t -> t -> Ctx.t -> Ctx.t -> unit

  (** Printing *)	
  val to_string : t -> bool -> string
end
= struct
    type t = Expr.t list

		    
    (** --------------------
	Structural functions
        --------------------  *) 
    let mk env (l: Expr.t list) = List.rev l

					   
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
      |PArr(u,v) ->
	PArr (apply s tar u, apply s tar v)
      |Sub _ -> assert (false)

    (** -----------------
	Typing procedures
        -----------------  *) 
    let rec checkEqual env ctx s1 s2 =
      match s1,s2 with
      |[],[] -> ()
      |t1::s1,t2::s2 ->
	Expr.checkEqual_norm env ctx t1 t2;
	checkEqual env ctx s1 s2
      |_,_ -> raise NotValid

    let normalize env ctx sub =
      List.map (Expr.normalize env ctx) sub

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
end

                      
and Ctx
: sig
  type t = private ((Var.t * Expr.t) list)
  val value : t -> ((Var.t * Expr.t) list)      
  val ty_var : t -> Var.t -> Expr.t
  val empty : unit -> t
  val isEmpty : t -> bool
  val add : Env.t -> t -> Var.t -> Expr.t -> t
  val of_ps : PS.t -> t
  val checkEqual : Env.t -> t -> t -> unit
  val head : t -> Var.t * Expr.t
  val tail : t -> t
  val ext : t -> (Var.t * Expr.t) * t
  val free_vars : t -> Var.t list
  val mem : t -> Var.t -> bool
  val to_string : t -> bool -> string
end
= struct
  type t = (Var.t * Expr.t) list
                        
  let ty_var ctx x = try List.assoc x ctx with Not_found -> raise (UnknownId (Var.to_string x))

  let empty _ = []

  let isEmpty c =
    match c with
    |[] -> true
    |_ -> false
		
  let add env (ctx :Ctx.t) x u =
    let u = Expr.normalize env ctx u in
    let () = Expr.checkT env ctx u in
    (ctx :> t)@[(x,u)] 
						 
  let value ctx = ctx
    
  let rec of_ps ps =
    let open PS in
    match ps with
    |PNil (x,t) ->  [(x,t)]
    |PCons (ps,(x1,t1),(x2,t2)) -> (of_ps ps)@[(x1,t1);(x2,t2)]
    |PDrop ps -> of_ps ps


  let rec checkEqual env ctx1 ctx2 =
    let rec equal c ctx1 ctx2 = 
      match ctx1, ctx2 with
      |[],[] -> ()
      |(v1,x1)::ctx1, (v2,x2)::ctx2 -> if not (v1 = v2) then raise NotValid;
                                       Expr.checkEqual_norm env c x1 x2;
                                       equal (Ctx.add env c v1 x1) ctx1 ctx2
      |_,_ -> raise NotValid
    in equal (Ctx.empty ()) ctx1 ctx2

  let rec head ctx = match ctx with
    |[] -> assert(false)
    |a::[] -> a
    |_::ctx -> head ctx
	     
 let rec tail ctx = match ctx with 
   |[] -> assert(false)
   |_::[] -> []
   |a::ctx -> a::(tail ctx)

 let rec ext ctx = match ctx with 
   |[] -> assert(false)
   |a::ctx -> (a,ctx)
		   
 let free_vars ctx = List.map fst ctx

 let rec mem c v = match c with
   |[] -> false
   |(x,u)::c when x = v -> true
   |_::c -> mem c v
			      
 let rec to_string ctx abbrev =
   let to_string = (fun c -> to_string c abbrev) in
   match ctx with
   |[] -> ""
   |(x,t)::c -> Printf.sprintf "(%s,%s) %s" (Var.to_string x)
                                            (Expr.to_string t abbrev)
                                            (to_string c)
end

and PS
: sig
  type t = private
          |PNil of (Var.t * Expr.t)
          |PCons of t * (Var.t * Expr.t) * (Var.t * Expr.t)
          |PDrop of t
                      
  val free_vars : t -> Var.t list
  val mk : Ctx.t -> t
  val height : t -> int
  val dim : t -> int
  val source : int -> t -> t
  val target : int -> t -> t
  val to_string : t -> bool -> string
end
= struct
  exception Invalid
  
  (** --Syntactic properties-- *)
  type t =
    |PNil of (Var.t * Expr.t)
    |PCons of PS.t * (Var.t * Expr.t) * (Var.t * Expr.t)
    |PDrop of PS.t

  let free_vars ps = Ctx.free_vars (Ctx.of_ps ps)
		
  (** --Maker-- *)
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


  (** Create pasting scheme from a context. *)
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

	
  (** --Manipulations-- *)
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

  let rec map f = function
    | PNil x -> PNil (f x)
    | PCons (ps,x,y) ->
       let ps = map f ps in
       let x = f x in
       let y = f y in
       PCons (ps,x,y)
    | PDrop ps -> PDrop (map f ps)
        
  let to_string ps abbrev =
    Ctx.to_string (Ctx.of_ps ps) abbrev 
end

and Env
: sig
  type t = private (EVar.t * Coh.t) list
  (*a function is required here for the safe module condition*)
  val empty : unit -> t
  val val_var : t -> EVar.t -> Coh.t
  val add : t -> EVar.t -> Coh.t -> t 
end
= struct
  type t = (EVar.t * Coh.t) list

  let value env = env

  let empty a = []
                    
  let val_var env x = try List.assoc x env with Not_found -> raise (UnknownCoh (EVar.to_string x))
					
  let add env x u =
    (x,u)::env
end

    
and Expr
: sig
  type t = 
    |CVar of Var.t
    |Obj
    |Arr of t * t * t
    |PArr of t * t
    |Sub of Cut.t * Sub.t
  
  val free_vars : t -> Var.t list
  val to_string : t -> bool  -> string

  val checkT : Env.t -> Ctx.t -> t -> unit
  val infer : Env.t -> Ctx.t -> t -> t
  val checkEqual_norm : Env.t -> Ctx.t -> t -> t -> unit
  val checkEqual : Env.t -> Ctx.t -> t -> t -> unit
  val checkType : Env.t -> Ctx.t -> t -> t -> unit
  val normalize : Env.t -> Ctx.t -> t -> t
  end
= struct
  type  t =
    |CVar of Var.t
    |Obj
    |Arr of t * t * t
    |PArr of t * t
    |Sub of Cut.t * Sub.t

  let rec free_vars e =
    match e with
    |CVar x -> [x]
    |Obj -> []
    |Arr (t,u,v) -> List.unions [(free_vars t);(free_vars u);(free_vars v)]
    |PArr (u,v) -> assert(false)
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
    |PArr (u,v) -> Printf.sprintf "%s -> %s" (to_string u) (to_string v)
    |Sub (t,s) -> Printf.sprintf "%s.%s" (Sub.to_string s abbrev) (Cut.to_string t abbrev)

  let rec normalize env ctx e =
    match e with
    |CVar x -> CVar x
    |Obj -> e
    |Arr (t,u,v) ->
      Arr (normalize env ctx t, normalize env ctx u, normalize env ctx v)
    |PArr (u,v) ->
      let u = normalize env ctx u and v = normalize env ctx v in
      let t = infer env ctx u and t' = infer env ctx v in
      let _ = checkEqual env ctx t t' in
       Arr (normalize env ctx t,u,v)
    |Sub (t,s) ->
      let s = Sub.normalize env ctx s in
      let t = Cut.normalize env t in
      Sub (t,s)
			  
  and checkEqual_norm env ctx e1 e2 =
    let equal = checkEqual_norm env ctx in
    match e1, e2 with
    |CVar x,CVar y -> if not (x = y) then raise (NotEqual (to_string e1 true, to_string e2 true)) else ()
    |Obj,Obj -> ()
    |Arr(t1,u1,v1),Arr(t2,u2,v2) ->
      equal t1 t2;
      equal u1 u2;
      equal v1 v2
    |Sub(t1,s1),Sub(t2,s2) ->
      let tar = Cut.checkEqual env t1 t2 in
      Sub.checkEqual env tar s1 s2
    |(PArr _, _ |_, PArr _) -> assert (false)
    (** Not a normal form*)
    |(CVar _|Obj |Arr _|Sub _),_ ->
      raise (NotEqual (Expr.to_string e1 true, Expr.to_string e2 true)) 
				      
  and checkEqual env ctx e1 e2 =
    checkEqual_norm env ctx
		    (normalize env ctx e1)
		    (normalize env ctx e2)		    
  and infer env ctx e =
    match e with
    |CVar x -> Ctx.ty_var ctx x
    |Sub (e,s) ->
      let tar,ty = Cut.infer env e in
      Sub.check env s ctx tar;
      checkT env tar ty;
      (** Useless? *)
      Sub.apply s tar ty
    |(Obj |Arr _) -> raise (HasNoType (Expr.to_string e true))
    |PArr _ -> assert (false)
  and checkT env ctx e =
    match e with
    |Obj -> ()
    |Arr (t,u,v) -> checkT env ctx t; checkType env ctx u t; checkType env ctx v t
    |(CVar _ |Sub _) -> raise (IsNotType (Expr.to_string e true))
    |PArr _ -> assert (false)
  and checkType env ctx e1 e2  =
    checkEqual env ctx (infer env ctx e1) e2 
  end
    
and Cut
: sig

  type t =
    |Fold of EVar.t
    |Unfold of Coh.t

  val mk_fold : EVar.t -> t
  val mk_unfold : Coh.t -> t
		 
  val free_vars : t -> Var.t list
  val to_string : t -> bool -> string
  val normalize : Env.t -> t -> t
  val checkEqual : Env.t -> t -> t -> Ctx.t
  val infer : Env.t -> t -> Ctx.t * Expr.t
    
end
= struct
  type t = 
    |Fold of EVar.t
    |Unfold of Coh.t

  let mk_fold x =
    Fold x

  let mk_unfold coh =
    Unfold coh
		 
  let free_vars coh =
    match coh with
     |Fold x -> assert (false) (** Ignore this case for now *)
     |Unfold coh -> Coh.free_vars coh 

  let to_string coh abbrev =
    match coh with
    |Fold x -> EVar.to_string x
    |Unfold coh -> Coh.to_string coh abbrev
				  
  let normalize env coh =
    match coh with
    |Fold x -> Unfold (Env.val_var env x)
    |Unfold coh -> Unfold coh

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
end

(** -- Module with a specific type for well-defined coherences
    -- They are different from normal type, they need to be substituted *)    
and Coh    
: sig
  type t = private (PS.t * Expr.t)   

  val mk : Env.t -> PS.t -> Expr.t -> t
  val free_vars : t -> Var.t list
  val to_string : t -> bool -> string
  val checkEqual : Env.t -> t -> t -> Ctx.t
  val ps : t -> PS.t
  val target : t -> Expr.t
end
= struct
  type t = PS.t * Expr.t
		    
  let mk env ps t =
    let ctx = Ctx.of_ps ps in
    let t = Expr.normalize env ctx t in
    Expr.checkT env ctx t;
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
        
type var = Var.t
type evar = EVar.t
type env = Env.t
type ctx = Ctx.t
type sub = Sub.t
type ps = PS.t
type expr = Expr.t
type coh = Coh.t
type cut = Cut.t
     	     
let empty_ctx = Ctx.empty ()
let empty_env = Env.empty ()
let mk_ps = PS.mk
let mk_sub = Sub.mk
let mk_coh = Coh.mk
let mk_fold = Cut.mk_fold
let mk_unfold = Cut.mk_unfold
let add_env = Env.add
let add_ctx = Ctx.add
let in_ctx = Ctx.mem
let expr_to_string = Expr.to_string                  
let coh_to_string = Coh.to_string                  

(** To be removed, for debugging purposes *)
let string_of_ctx = fun x -> Ctx.to_string x false

					   
