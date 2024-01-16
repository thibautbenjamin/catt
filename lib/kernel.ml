open Std

exception IsObj
exception IsCoh
exception InvalidSubTarget of string * string
exception NotEqual of string * string
exception DoubledVar of string
exception MetaVariable

(* Internal representation of a functorialisation: each position in
   the list is a locally maximal variable and each integer indicates
   how many time the corresponding position is functorialised *)
type functorialisation_data = int list

module Var =
struct
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
module rec Sub
  : sig
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
    Io.info ~v:5
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
          Ty.check_equal (Tm.typ t) (Ty.apply_sub a sub);
          t::sub.list
      in
      {list = expr s tgt; src; tgt; unchecked = s}
    in
    aux src s tgt

  let check_to_ps src s tgt =
    let tgt = PS.to_ctx tgt in
    let s =
      try List.map2 (fun (x,_) (t,_) -> (x,t)) (Ctx.value tgt) s
      with Invalid_argument _ -> Error.fatal "uncaught wrong number of arguments"
    in
    check src s tgt

  let forget s = s.unchecked
end

(** A context, associating a type to each context variable. *)
and Ctx
  : sig
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
  val to_ctx : t -> Ctx.t
  val dim : t -> int
  val bdry : int -> t -> t
  val source : int -> t -> Sub.t
  val target : int -> t -> Sub.t
  val forget : t -> Unchecked_types.ps
  val check_equal : t -> t -> unit
end
=
struct
  exception Invalid

  (** A pasting scheme. *)
  type ps_derivation =
    | PNil of (Var.t * Ty.t)
    | PCons of ps_derivation * (Var.t * Ty.t) * (Var.t * Ty.t)
    | PDrop of ps_derivation

  type t = { tree : Unchecked_types.ps; ctx : Ctx.t}

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

  (** Dangling variable. *)
  let rec marker (ps : ps_derivation) =
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
    {tree = make_tree oldrep; ctx = l}

  let forget ps = ps.tree

  let to_string ps = Unchecked.ps_to_string (forget ps)

  (** Create a context from a pasting scheme. *)
  let to_ctx ps =
    ps.ctx

  (* let height ps = height_old ps.oldrep *)
  let dim ps = Unchecked.dim_ps (ps.tree)

  let bdry i ps =
    let rec bdry_tree i ps =
      match ps with
      | Unchecked_types.Br [] -> Unchecked_types.Br []
      | Br _ when i <= 0 -> Br []
      | Br l ->  Br (List.map (bdry_tree (i-1)) l)
    in (mk (Ctx.check (Unchecked.ps_to_ctx (bdry_tree i ps.tree))))

  let rec nb_vars ps =
    match ps with
    | Unchecked_types.Br [] -> 1
    | Br l -> List.fold_left (fun nb ps -> nb + (nb_vars ps) + 1) 1 l

  let right_point ps =
    match ps with
    | Unchecked_types.Br [] -> 0
    | Br (_::l) -> nb_vars (Br l)

  let bdry_inclusion ~select_bdry i ps =
    let var i = Unchecked_types.Var (Var.Db i) in
    let rec inclusion i ps next_var =
      match ps with
      | Unchecked_types.Br [] -> [(var next_var),true], next_var + 1
      | Br l when i <= 0 ->
        let m = select_bdry next_var ps in
        [(var m), false], next_var + nb_vars (Br l)
      | Br l ->
        let base = (var next_var) in
        glue i l (next_var + 1) base
    and glue i l next_var base =
      match l with
      | [] -> [base, false], next_var
      | ps::l ->
        let sl, next_var = glue i l next_var base in
        let v = (var next_var) in
        let s, next_var = inclusion (i-1) ps (next_var+1) in
        List.append s ((v,false)::sl), next_var
    in
    Sub.check_to_ps (to_ctx ps) (fst (inclusion i ps.tree 0)) (bdry i ps)

  let source = bdry_inclusion ~select_bdry:(fun n _ -> n)
  let target = bdry_inclusion ~select_bdry:(fun n ps -> n + right_point ps)

  let check_equal ps1 ps2 =
    Unchecked.check_equal_ps ps1.tree ps2.tree
end


and Ty : sig
  type t
  val to_string : t -> string
  val free_vars : t -> Var.t list
  val is_full : t -> bool
  val is_obj : t -> bool
  val check_equal : t -> t -> unit
  val morphism : Tm.t -> Tm.t -> Ty.t
  val forget : t -> Unchecked_types.ty
  val check : Ctx.t -> Unchecked_types.ty -> t
  val apply_sub : t -> Sub.t -> t
  val retrieve_arrow : t -> (t * Tm.t * Tm.t)
  val under_type : t -> t
  val target : t -> Tm.t
  val ctx : t -> Ctx.t

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
    Io.info ~v:5
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
        let u = Tm.check c ~ty:a u in
        let v = Tm.check c ~ty:a v in
        Arr(a,u,v)
      | Meta_ty _ -> raise MetaVariable
    in {c; e; unchecked = t}

  (** Free variables of a type. *)
  let rec free_vars ty =
    match ty.e with
    | Obj -> []
    | Arr (t,u,v) -> List.unions [free_vars t; Tm.free_vars u; Tm.free_vars v]

  let is_full t = List.included (Ctx.domain t.c) (free_vars t)

  let forget t = t.unchecked

  let to_string ty =
    Unchecked.ty_to_string (forget ty)

  (** Test for equality. *)
  let check_equal ty1 ty2 =
    Ctx.check_equal ty1.c ty2.c;
    Unchecked.check_equal_ty (forget ty1) (forget ty2)

  let morphism t1 t2 =
    let a1 = Tm.ty t1 in
    let a2 = Tm.ty t2 in
    check_equal a1 a2;
    {c=a1.c; e=Arr(a1,t1,t2);
      unchecked = Unchecked_types.Arr(forget a1, Tm.forget t1, Tm.forget t2)}

  let apply_sub t s =
    Ctx.check_equal t.c (Sub.tgt s);
    check (Sub.src s) (Unchecked.ty_apply_sub (forget t) (Sub.forget s))

  let ctx t = t.c
end

(** Operations on terms. *)
and Tm : sig
  type t
  val to_var : t -> Var.t
  val typ : t -> Ty.t
  val free_vars : t -> Var.t list
  val is_full : t -> bool
  val forget : t -> Unchecked_types.tm
  val check : Ctx.t -> ?ty:Ty.t -> Unchecked_types.tm -> t
  val apply_sub : t -> Sub.t -> t
  val preimage : t -> Sub.t -> t
  val ty : t -> Ty.t
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
    let fvty = Ty.free_vars tm.ty in
    match tm.e with
    | Var x -> x::fvty
    | Coh (_,sub) -> Sub.free_vars sub

  let is_full tm =
    List.included (Ctx.domain (Ty.ctx tm.ty)) (free_vars tm)

  let forget tm = tm.unchecked
  let _to_string tm = Unchecked.tm_to_string (forget tm)

  let check c ?ty t =
    Io.info ~v:5
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
        let sub = Sub.check_to_ps c s (Coh.ps coh) in
        let e, ty = Coh(coh,sub), Ty.apply_sub (Coh.ty coh) sub in
        {ty; e; unchecked = t}
    in match ty with
    | None -> tm
    | Some ty -> Ty.check_equal ty tm.ty; tm

  let apply_sub t sub =
    Ctx.check_equal (Sub.tgt sub) (Ty.ctx t.ty);
    let c = Sub.src sub in
    let ty = Ty.apply_sub t.ty sub in
    let t = Unchecked.tm_apply_sub (forget t) (Sub.forget sub) in
    check c ~ty t

  let preimage t sub =
    Ctx.check_equal (Sub.src sub) (Ty.ctx t.ty);
    let c = Sub.tgt sub in
    let t = Unchecked.tm_sub_preimage (forget t) (Sub.forget sub) in
    check c t

  let ty t = t.ty
end

(** A coherence. *)
and Coh : sig
  type t
  val ps : t -> PS.t
  val ty : t -> Ty.t
  val check : Unchecked_types.ps -> Unchecked_types.ty -> Unchecked_types.coh_pp_data -> t
  val check_noninv : Unchecked_types.ps -> Unchecked_types.tm -> Unchecked_types.tm -> Unchecked_types.coh_pp_data -> t
  val to_string : t -> string
  (* val data_noninv : t -> PS.t * Tm.t * Tm.t * Sub.t * Sub.t * PS.t *)
  (* val data : t -> PS.t * Ty.t * Unchecked_types.coh_pp_data *)
  val forget : t -> Unchecked_types.ps * Unchecked_types.ty * Unchecked_types.coh_pp_data
  val func_data : t -> functorialisation_data option
  val check_equal : t -> t -> unit
end = struct

  type cohInv = {ps : PS.t; ty : Ty.t}
  type cohNonInv = {ps : PS.t;
                    bdry : PS.t;
                    src : Tm.t;
                    src_inclusion : Sub.t;
                    tgt : Tm.t;
                    tgt_inclusion : Sub.t;
                    total_ty: Ty.t}

  type t =
    | Inv of cohInv * Unchecked_types.coh_pp_data
    | NonInv of cohNonInv * Unchecked_types.coh_pp_data

  exception NotAlgebraic

  let ps = function
    | Inv(data,_) -> data.ps
    | NonInv(data,_) -> data.ps

  let ty = function
    | Inv(data,_) -> data.ty
    | NonInv(data,_) -> data.total_ty

  (* let check_inv ps ty name = *)
  (*   Ctx.check_equal (PS.to_ctx ps) (Ty.ctx ty); *)
  (*   if Ty.is_full ty then *)
  (*     Inv({ps; ty}, name) *)
  (*   else raise NotAlgebraic *)

  let algebraic ps ty name =
    if Ty.is_full ty then
      (Ctx.check_equal (PS.to_ctx ps) (Ty.ctx ty);
       Inv({ps; ty}, name))
    else
      let i = PS.dim ps in
      let _,src,tgt =
        try Ty.retrieve_arrow ty with IsObj -> raise NotAlgebraic
      in
      let bdry = PS.bdry (i-1) ps in
      let src_inclusion = PS.source (i-1) ps in
      let tgt_inclusion = PS.target (i-1) ps in
      let src = Tm.preimage src src_inclusion in
      let tgt = Tm.preimage tgt tgt_inclusion in
      if (Tm.is_full src && Tm.is_full tgt) then
        NonInv
          ({ps; src; tgt; total_ty=ty; src_inclusion; tgt_inclusion; bdry},
           name)
      else raise NotAlgebraic

  let check ps t ((name,_,_) as pp_data) =
    Io.info ~v:5
      (lazy
        (Printf.sprintf "checking coherence (%s,%s)"
           (Unchecked.ps_to_string ps)
           (Unchecked.ty_to_string t)));
    try
      let cps = Ctx.check (Unchecked.ps_to_ctx ps) in
      let ps = PS.mk cps in
      let t = Ty.check cps t in
      algebraic ps t pp_data
    with
    | NotAlgebraic ->
      Error.not_valid_coherence name
        (Printf.sprintf "type %s not algebraic in pasting scheme %s"
           (Unchecked.ty_to_string t)
           (Unchecked.(ctx_to_string (ps_to_ctx ps))))
    | DoubledVar(s) ->
      Error.not_valid_coherence name
        (Printf.sprintf "variable %s appears twice in the context" s)

  let check_noninv ps src tgt name =
    let ps = PS.mk (Ctx.check (Unchecked.ps_to_ctx ps)) in
    let i = PS.dim ps in
    let src_inclusion = PS.source (i-1) ps in
    let tgt_inclusion = PS.target (i-1) ps in
    let bdry = PS.bdry (i-1) ps in
    let cbdry = PS.to_ctx bdry in
    let src = Tm.check cbdry src in
    let tgt = Tm.check cbdry tgt in
    let total_ty =
      Ty.morphism (Tm.apply_sub src src_inclusion)
        (Tm.apply_sub tgt tgt_inclusion)
    in
    if (Tm.is_full src && Tm.is_full tgt) then
      NonInv
        ({ps; src; tgt; total_ty; src_inclusion; tgt_inclusion; bdry},
         name)
    else
      raise NotAlgebraic

  let data c =
    match c with
    | Inv (d,pp_data) -> d.ps, d.ty, pp_data
    | NonInv (d,pp_data) -> d.ps, d.total_ty, pp_data

  let to_string c =
    let ps,ty,pp_data = data c in
    if not (!Settings.unroll_coherences) then
      Unchecked.coh_pp_data_to_string pp_data
    else
      Printf.sprintf "Coh(%s,%s)" (PS.to_string ps) (Ty.to_string ty)

  let _data_noninv c =
    match c with
    | Inv (_,_) -> Error.fatal "non-invertible data of an invertible coh"
    | NonInv (d,_) -> d.ps, d.src, d.tgt, d.src_inclusion, d.tgt_inclusion, d.bdry

  let func_data = function
    | Inv(_,(_,_,func)) |NonInv(_,(_,_,func)) -> func

  let forget c =
    let ps,ty,pp_data = data c in
    PS.forget ps, Ty.forget ty, pp_data

  let check_equal coh1 coh2 =
    match coh1, coh2 with
    | Inv(d1,_) , Inv(d2,_) ->
      PS.check_equal d1.ps d2.ps;
      Ty.check_equal d1.ty d2.ty
    | NonInv (d1,_),  NonInv(d2,_) ->
      PS.check_equal d1.ps d2.ps;
      Ty.check_equal d1.total_ty d2.total_ty
    | Inv _, NonInv _ | NonInv _, Inv _ ->
      raise (NotEqual (to_string coh1, to_string coh2))
end


and Unchecked_types : sig
  type coh_pp_data = string * int * functorialisation_data option
  type ps = Br of ps list

  type ty =
    | Meta_ty of int
    | Obj
    | Arr of ty * tm * tm
  and tm =
    | Var of Var.t
    | Meta_tm of int
    | Coh of Coh.t * sub_ps
  and sub_ps = (tm * bool) list
  type ctx = (Var.t * (ty * bool)) list
  type sub = (Var.t * tm) list
  type meta_ctx = ((int * ty) list)
end = struct
  type coh_pp_data = string * int * functorialisation_data option

  type ps = Br of ps list

  type ty =
    | Meta_ty of int
    | Obj
    | Arr of ty * tm * tm
  and tm =
    | Var of Var.t
    | Meta_tm of int
    | Coh of Coh.t * sub_ps

  and sub_ps = (tm * bool) list

  type ctx = (Var.t * (ty * bool)) list

  type sub = (Var.t * tm) list

  type meta_ctx = ((int * ty) list)
end
and Unchecked : sig
  exception NotInImage
  val ps_to_string : Unchecked_types.ps -> string
  val ty_to_string : Unchecked_types.ty -> string
  val tm_to_string : Unchecked_types.tm -> string
  val sub_ps_to_string : ?func : functorialisation_data -> Unchecked_types.sub_ps -> string
  val ctx_to_string : Unchecked_types.ctx -> string
  val sub_to_string : Unchecked_types.sub -> string
  val coh_pp_data_to_string : ?print_func:bool -> Unchecked_types.coh_pp_data -> string
  val meta_ctx_to_string : Unchecked_types.meta_ctx -> string
  val check_equal_ty : Unchecked_types.ty -> Unchecked_types.ty -> unit
  val check_equal_ctx : Unchecked_types.ctx -> Unchecked_types.ctx -> unit
  val check_equal_ps : Unchecked_types.ps -> Unchecked_types.ps -> unit
  val tm_apply_sub : Unchecked_types.tm -> Unchecked_types.sub -> Unchecked_types.tm
  val ty_apply_sub : Unchecked_types.ty -> Unchecked_types.sub -> Unchecked_types.ty
  val tm_sub_preimage : Unchecked_types.tm -> Unchecked_types.sub -> Unchecked_types.tm
  val rename_ty : Unchecked_types.ty -> (Var.t * int) list -> Unchecked_types.ty
  val db_levels : Unchecked_types.ctx -> Unchecked_types.ctx * (Var.t * int) list * int
  val ps_to_ctx : Unchecked_types.ps -> Unchecked_types.ctx
  val sub_ps_to_sub : Unchecked_types.sub_ps -> Unchecked_types.ps -> Unchecked_types.sub * Unchecked_types.ctx
  val two_fresh_vars : Unchecked_types.ctx -> Var.t * Var.t
  val identity_ps : Unchecked_types.ctx -> Unchecked_types.sub_ps
  val tm_contains_var : Unchecked_types.tm -> Var.t -> bool
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
  exception NotInImage

  let rec func_to_string = function
    | [] -> ""
    | i::func -> Printf.sprintf "%s%d" (func_to_string func) i

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
      if !Settings.verbosity >= 3 then
        Printf.sprintf "%s | %s -> %s"
          (ty_to_string a)
          (tm_to_string u)
          (tm_to_string v)
      else
        Printf.sprintf "%s -> %s"
          (tm_to_string u)
          (tm_to_string v)
  and tm_to_string = function
    | Unchecked_types.Var v -> Var.to_string v
    | Unchecked_types.Meta_tm i -> Printf.sprintf "_tm%i" i
    | Unchecked_types.Coh (c,s) ->
      if not (!Settings.unroll_coherences) then
        let func = Coh.func_data c in
        Printf.sprintf "(%s%s)"
          (Coh.to_string c)
          (sub_ps_to_string ?func s)
      else
        Printf.sprintf "%s[%s]"
          (Coh.to_string c)
          (sub_ps_to_string s)
  and sub_ps_to_string ?func s =
    match func with
    | None ->
      begin
        match s with
        | [] -> ""
        | (t,expl)::s ->
          if(expl || !Settings.print_explicit_substitutions) then
            Printf.sprintf "%s %s" (sub_ps_to_string s)  (tm_to_string t)
          else sub_ps_to_string s
      end
    | Some func ->
      match s,func with
      | [],[] -> ""
      | (t,true)::s, i::func ->
        Printf.sprintf "%s %s" (sub_ps_to_string ~func s)  (bracket i (tm_to_string t))
      | (t,false)::s, func ->
        if(!Settings.print_explicit_substitutions) then
          Printf.sprintf "%s %s" (sub_ps_to_string ~func s) (tm_to_string t)
        else sub_ps_to_string ~func s
      | _::_,[] | [], _::_ -> Error.fatal "Wrong number of functorialisation arguments"
  and coh_pp_data_to_string ?(print_func=false) (name, susp, func) =
    let susp_name =
      if susp > 0 then Printf.sprintf "!%i%s" susp name else name
    in
    if print_func
    then
      match func with
      | None -> susp_name
      | Some func -> let func = func_to_string func in susp_name^"/"^func
    else susp_name
  and bracket i s = if i <= 0 then s else Printf.sprintf "[%s]" (bracket (i-1) s)

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
      Coh.check_equal coh1 coh2;
      check_equal_sub_ps s1 s2
    | Var _, Coh _ | Coh _, Var _
    | Meta_tm _, Var _| Meta_tm _, Coh _
    | Var _, Meta_tm _ | Coh _, Meta_tm _ ->
      raise (NotEqual (tm_to_string tm1, tm_to_string tm2))
  and check_equal_sub_ps s1 s2 =
    List.iter2 (fun (t1,_) (t2,_) -> check_equal_tm t1 t2) s1 s2

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
  and sub_ps_do_on_variables s f = List.map (fun (t,expl) -> tm_do_on_variables t f, expl) s

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

  let rec var_sub_preimage v s =
    match s with
    | [] -> raise NotInImage
    | (w, Unchecked_types.Var v')::_ when v = v' -> Unchecked_types.Var w
    | _::s -> var_sub_preimage v s
  let tm_sub_preimage tm s = tm_do_on_variables tm
      (fun v -> var_sub_preimage v s)

  (* rename is applying a variable to de Bruijn levels substitutions *)
  let rename_ty ty l = ty_do_on_variables ty
      (fun v -> Unchecked_types.Var (Db (List.assoc v l)))

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
  and suspend_coh c =
    let p,t,(name,susp,f) = Coh.forget c in
    Coh.check (suspend_ps p) (suspend_ty t) (name, susp+1, f)
  and suspend_sub_ps = function
    | [] -> [Var (Var.Db 1), false; Var (Var.Db 0), false]
    | (t,expl)::s -> (suspend_tm t, expl) :: (suspend_sub_ps s)

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
    try List.map2 (fun (t,_) (x,_) -> (x,t)) s ps, ps
    with Invalid_argument _ -> Error.fatal "uncaught wrong number of arguments"

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
    | (x,(_,expl))::c -> (Unchecked_types.Var x,expl) :: (identity_ps c)

  let rec tm_contains_var t x =
    match t with
    | Unchecked_types.Var v -> v = x
    | Coh(_,s) -> List.exists (fun (t,_) -> tm_contains_var t x) s
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

let check check_fn name =
  let v = 2 in
  let fname = if !Settings.verbosity >= v then Lazy.force name else "" in
  Io.info ~v (lazy ("checking "^fname));
  try check_fn() with
  | NotEqual(s1,s2) ->
    Error.untypable
      (if !Settings.verbosity >= v then fname else Lazy.force name)
      (Printf.sprintf "%s and %s are not equal" s1 s2)
  | InvalidSubTarget (s,tgt) ->
    Error.untypable
      (if !Settings.verbosity >= v then fname else Lazy.force name)
      (Printf.sprintf "substitution %s does not apply from context %s" s tgt)
  | Error.UnknownId (s) ->
    Error.untypable
      (if !Settings.verbosity >= v then fname else Lazy.force name)
      (Printf.sprintf "unknown identifier :%s" s)
  | MetaVariable ->
    Error.incomplete_constraints (if !Settings.verbosity >= v then fname else Lazy.force name)

let check_type ctx a =
  let ty = lazy ("type: "^Unchecked.ty_to_string a) in
  check (fun () -> Ty.check ctx a) ty

let check_term ctx ?ty t =
  let ty = Option.map (check_type ctx) ty in
  let tm = lazy ("term: " ^ (Unchecked.tm_to_string t)) in
  check (fun () -> Tm.check ctx ?ty t) tm

let check_coh ps ty pp_data =
  let c = lazy ("coherence: "^(Unchecked.coh_pp_data_to_string pp_data)) in
  check (fun () -> Coh.check ps ty pp_data) c
