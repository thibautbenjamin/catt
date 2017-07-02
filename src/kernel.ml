open Stdlib

exception NotValid
exception NotAlgebraic
module Var = struct
  type t =
  |Name of string
  |New of string * int

  let to_string v abbrev show_instances =
    match v with
    |Name s -> s
    |New (s,i) -> if not(abbrev)&&show_instances then Printf.sprintf "%s.%d" s i else s
                                           
end
exception UnknownId of Var.t

               
module rec Sub 
: sig
  type t = private (Expr.t list * Ctx.t * Ctx.t)
  val list : t -> Expr.t list
  val source : t -> Ctx.t
  val target : t -> Ctx.t
  val assoc_list : t -> ((Var.t * Expr.t) list)
  val normalize : Env.t -> t -> t
  val checkEqual : Env.t -> t -> t -> unit
  val mk : Env.t -> Expr.t list -> Ctx.t -> Ctx.t -> t
  val to_string : t -> bool -> bool -> string
end
= struct
  type t = (Expr.t list * Ctx.t * Ctx.t)

  let list (s:t) =
    match s with 
    |l,_,_ -> l

  let source (s:t) = 
    match s with
    |_,src,_ -> src

  let target (s:t) =
    match s with
    |_,_,targ -> targ
    
  let assoc_list (s:t) = 
    let rec build l ctx =
      match l,ctx with
      |t::l,(x,_)::ctx -> (x,t)::(build l ctx)
      |[],[] -> []
      |_,_ -> assert (false)
    in build (list s) (Ctx.value (target s))

  let normalize env s =
  (List.map (Expr.normalize env) (list s), Ctx.normalize env (source s), Ctx.normalize env (target s))

  let checkEqual env s1 s2 =
    let rec equal_list s1 s2 = 
      match s1,s2 with
      |[],[] -> ()
      |t1::s1,t2::s2 -> Expr.checkEqual env t1 t2; equal_list s1 s2
      |_,_ -> raise NotValid
    in equal_list (list (normalize env s1)) (list (normalize env s2));
       Ctx.checkEqual env (source s1) (source s2);
       Ctx.checkEqual env (target s1) (target s2)
                      
  let rec check_list env s delta gamma =
    match s,(Ctx.value gamma) with
    |([],c) when c = Ctx.value (Ctx.empty) -> ()
    |(t::s, (x,u)::_) -> let gamma = Ctx.tail gamma in
                         Infer.checkT env gamma u;
                         let s = Sub.mk env s delta gamma in
                         Infer.checkType env delta t (Expr.subst u s)
    |_ -> raise NotValid
  and mk env s delta gamma : t =
    check_list env s delta gamma; (s,delta,gamma)            

  let rec string_of_assoc s abbrev show_instances =
    match s with
    |[] -> ""
    |(x,u)::s -> Printf.sprintf "(%s,%s) %s" (Var.to_string x abbrev show_instances)
                                             (Expr.to_string u abbrev show_instances)
                                             (string_of_assoc s abbrev show_instances)

  let rec string_of_list s abbrev show_instances =
    match s with
    |[] -> ""
    |u::s -> Printf.sprintf "%s; %s" (Expr.to_string u abbrev show_instances)
                                     (string_of_list s abbrev show_instances)
                                             
  let to_string s abbrev show_instances =
    if abbrev then Printf.sprintf "[%s]" (string_of_assoc (assoc_list s) abbrev show_instances)
    else Printf.sprintf "(%s |- %s : %s)" (Ctx.to_string (source s) abbrev show_instances)
                                         (string_of_list (list s) abbrev show_instances)
                                         (Ctx.to_string (target s) abbrev show_instances)  
end

                      
and Ctx
: sig
  type t = private ((Var.t * Expr.t) list)
  val value : t -> ((Var.t * Expr.t) list)      
  val ty_var : t -> Var.t -> Expr.t
  val empty : t
  val add : (Env.t * t) -> Var.t -> Expr.t -> (Env.t * t) 
  val of_ps : PS.t -> t
  val normalize : Env.t -> t -> t
  val checkEqual : Env.t -> t -> t -> unit
  val tail : t -> t
  val to_string : t -> bool -> bool -> string
end
= struct
  type t = (Var.t * Expr.t) list
                        
  let ty_var ctx x = try List.assoc x ctx with Not_found -> raise (UnknownId x)

  let empty = []
                                                                  
  let add (env,(ctx :Ctx.t)) x u = Infer.checkT env ctx u;
                          let ctx = (ctx :> t)@[(x,u)] in (Env.add_var env x, ctx)

                                                                  
  let value ctx = ctx
    
  let rec of_ps ps =
    let open PS in
    match ps with
    |PNil (x,t) ->  [(x,t)]
    |PCons (ps,(x1,t1),(x2,t2)) -> (of_ps ps)@[(x1,t1);(x2,t2)]
    |PDrop ps -> of_ps ps

  let normalize env ctx =
    List.map (fun (v,x) -> (v, Expr.normalize env x)) ctx

  let checkEqual env ctx1 ctx2 =
    let rec equal ctx1 ctx2 =
      match ctx1, ctx2 with
      |[],[] -> ()
      |(v1,x1)::ctx1, (v2,x2)::ctx2 -> if not (v1 = v2) then raise NotValid;
                                       Expr.checkEqual env x1 x2;
                                       equal ctx1 ctx2
      |_,_ -> raise NotValid
    in equal (normalize env ctx1) (normalize env ctx2)
             
 let rec tail ctx = match ctx with 
   |[] -> assert(false)
   |_::[] -> []
   |a::ctx -> a::(tail ctx)

 let rec to_string ctx abbrev show_instances =
   let to_string = (fun c -> to_string c abbrev show_instances) in
   match ctx with
   |[] -> ""
   |(x,t)::c -> Printf.sprintf "(%s,%s) %s" (Var.to_string x abbrev show_instances)
                                            (Expr.to_string t abbrev show_instances)
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
  val normalize : Env.t -> t -> t
  val checkEqual : Env.t -> t -> t -> unit
  val to_string : t -> bool -> bool -> string
end
= struct
  exception Invalid
  
  (** --Syntactic properties-- *)
  type t =
    |PNil of (Var.t * Expr.t)
    |PCons of PS.t * (Var.t * Expr.t) * (Var.t * Expr.t)
    |PDrop of PS.t

  let rec free_vars ps =
    match ps with
    |PNil(x,t) -> [x]
    |PCons(ps,(x1,t1),(x2,t2)) -> List.unions [[x1];[x2];(free_vars ps)]
    |PDrop ps -> free_vars ps

  (** --Maker-- *)
  (** Dangling variable. *)
  let rec marker ps =
    match ps with
    | PNil (x,t) -> x,t
    | PCons (ps,_,f) -> f
    | PDrop ps ->
       let f,tf = marker ps in
       match tf with
       | Expr.Arr (_,x,Expr.Var y) ->
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
           | Arr (_, Var fx, Var fy) ->
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
        
  let normalize env c =
    map (fun (x,t) -> (x, Expr.normalize env t)) c

  let checkEqual env ps1 ps2 =
    let rec equal ps1 ps2 = 
      match ps1,ps2 with
      |PNil (x1,t1), PNil (x2,t2) -> if not (x1 = x2) then raise NotValid; Expr.checkEqual env t1 t2
      |PCons (ps1,(x1,t1),(y1,u1)), PCons (ps2,(x2,t2),(y2,u2)) -> if not(x1 = x2 && y1 = y2) then raise NotValid;
                                                                   Expr.checkEqual env t1 t2;
                                                                   Expr.checkEqual env u1 u2;
                                                                   equal ps1 ps2
      |PDrop ps1, PDrop ps2 -> equal ps1 ps2
      |(PNil _|PCons _|PDrop _),_ -> raise NotValid
    in equal (normalize env ps1) (normalize env ps2)


  let to_string ps abbrev show_instances =
    Ctx.to_string (Ctx.of_ps ps) abbrev show_instances
end




and Env
: sig
  type t = private (Var.t * Expr.t) list
  (*a function is required here for the safe module condition*)
  val empty : unit -> t
  val val_var : t -> Var.t -> Expr.t
  val add_var : t -> Var.t -> t
  val add_expr : t -> Var.t -> Expr.t -> t 
end
= struct
  type t = (Var.t * Expr.t) list

  let value env = env

  let empty a = []
                    
  let val_var env x = try List.assoc x env with Not_found -> raise (UnknownId x)

  let add_var env x = (x,Expr.Var x)::env
    
  let add_expr (env : Env.t) x u =
    match u with
    |Expr.Coh(ps,v) -> let _ = Infer.infer env (Ctx.of_ps ps) u in (x,u)::(env :> t)
    |_ -> assert(false)            
end



    
and Expr
: sig
  type t = 
    |Var of Var.t
    |Obj
    |Arr of t * t * t
    |Coh of PS.t * t
    |Sub of t * Sub.t

  val free_vars : t -> Var.t list
  val normalize : Env.t -> t -> t
  val checkEqual : Env.t -> t -> t -> unit
  val to_string : t -> bool -> bool  -> string
  val subst : t -> Sub.t -> t
end
= struct
  type  t =
    |Var of Var.t
    |Obj
    |Arr of t * t * t
    |Coh of PS.t * t
    |Sub of t * Sub.t

    let rec free_vars e =
      match e with
      |Var x -> [x]
      |Obj -> []
      |Arr (t,u,v) -> List.unions [(free_vars t);(free_vars u);(free_vars v)]
      |Coh (ps,t) -> List.union (PS.free_vars ps) (free_vars t)
      |Sub (t,sub) -> List.unions (List.map (fun x -> try (free_vars (List.assoc x (Sub.assoc_list sub)))
                                                      with Not_found -> [x])
                                            (free_vars (t)))                                


(** Performs all possible substitutions *)
  let rec subst t s =
    match t with
    |Var x -> List.assoc x (Sub.assoc_list s)
    |Obj -> Obj
    |Arr (a,u,v) -> Arr (subst a s, subst u s, subst v s)
    |Coh (c,u) -> Sub (t,s)
    |Sub (u,ss) -> assert (false) (** In the minimal system, this case should not be allowed to appear *)

  (** Normalization of an expression *)
  let rec normalize env e =
    match e with
    |Var x -> Env.val_var env x
    |Obj -> e
    |Arr (t,u,v) ->
      Arr (normalize env t, normalize env u, normalize env v)
    |Coh (c,t) ->
      Coh (PS.normalize env c, normalize env t)
    |Sub (t,s) -> let s = Sub.normalize env s in
                  let t = normalize env t in
                  subst t s                          

  (** Checks the equality of two terms *)
  let checkEqual env e1 e2 =
    let rec equal e1 e2 =
      match e2, e2 with
      |Var x,Var y -> if not (x = y) then raise NotValid else ()
      |Obj,Obj -> ()
      |Arr(t1,u1,v1),Arr(t2,u2,v2) -> equal t1 t2; equal u1 u2; equal v1 v2
      |Coh(c1,t1),Coh(c2,t2) -> PS.checkEqual env c1 c2; equal t1 t2
      |Sub(t1,s1),Sub(t2,s2) -> equal t1 t2; Sub.checkEqual env s1 s2
      |(Var _|Obj |Arr _|Coh _|Sub _),_ -> raise NotValid
    in equal (normalize env e1) (normalize env e2) 

  let to_string expr abbrev show_instances =
    let to_string  = fun u -> Expr.to_string u abbrev show_instances in 
    match expr with
    |Var x -> Var.to_string x abbrev show_instances
    |Obj -> "*"
    |Arr (t,u,v) -> if abbrev then
                      Printf.sprintf "%s -> %s" (to_string u) (to_string v)
                    else Printf.sprintf "%s | %s -> %s" (to_string t) (to_string u) (to_string v)
    |Coh (c,t) -> Printf.sprintf "Coh {%s |- %s}" (PS.to_string c abbrev show_instances) (to_string t)
    |Sub (t,s) -> Printf.sprintf "%s.%s" (Sub.to_string s abbrev show_instances) (to_string t)
end


and Infer
: sig
  val checkT : Env.t -> Ctx.t -> Expr.t -> unit
  val infer : Env.t -> Ctx.t -> Expr.t -> Expr.t
  val checkType : Env.t -> Ctx.t -> Expr.t -> Expr.t -> unit
                                            
end
= struct
  let rec infer env ctx e =
    let open Expr in
    match e with
    |Var x -> Ctx.ty_var ctx x
    |Coh (c,u) -> checkT env (Ctx.of_ps c) u;
                  if List.included (PS.free_vars c) (free_vars u) then u
                  else
                    let f,g = match u with
                      |Arr(a,f,g) -> (f,g)  
                      |_ -> raise NotAlgebraic
                    in
                    let i = PS.dim c in
                    let pss = PS.source (i-1) c and pst = PS.target (i-1) c in
                    let tf = infer env ctx f and tg = infer env ctx g in
                    (checkT env (Ctx.of_ps pss) tf; checkT env (Ctx.of_ps pst) tg;
                     if List.included (PS.free_vars pss) (free_vars f) && List.included (PS.free_vars pst) (free_vars g) then u
                     else raise NotAlgebraic)
    |Sub (e,s) -> let c1 = (Sub.source s) in Ctx.checkEqual env ctx c1;
                                             let c2 = (Sub.target s) in
                                             let ty = infer env c2 e in
                                             checkT env c2 ty; (Sub (ty,s))
    |(Obj |Arr _) -> assert (false)
  and checkT env ctx e =
    let open Expr in
    match e with
    |Obj -> ()
    |Arr (t,u,v) -> checkT env ctx t; checkType env ctx u t; checkType env ctx v t
    |_ -> raise NotValid
  and checkType env ctx e1 e2  =
    Expr.checkEqual env (infer env ctx e1) e2 
end

type var = Var.t
type env = Env.t
type ctx = Ctx.t
type sub = Sub.t
type ps = PS.t
type expr = Expr.t
            
let empty_ctx = Ctx.empty
let empty_env = Env.empty ()
let mk_ps = PS.mk
let mk_sub = Sub.mk
let add_env = Env.add_expr
let add_ctx = Ctx.add
let to_string = Expr.to_string                  

(** To be removed, for debugging purposes *)
let string_of_ctx = fun x -> Ctx.to_string x false true
