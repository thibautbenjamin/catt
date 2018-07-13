open Kernel
open Settings
open Common


(** A command. *)
type cmd =
  | Coh of Var.t * (Var.t * ty) list * ty (** a coherence *)
  | Check of ((Var.t * ty) list) * tm * ty option (** check that a term is well-typed in a context *)
  | Decl of Var.t * (Var.t * ty) list * tm * ty option (** let declarations *)

(** A program. *)
type prog = cmd list

let rec print l =
  match l with
  | ((x,_),true)::l -> Printf.sprintf "(%s) %s" (Var.to_string x) (print l);
  | ((x,_),false)::l -> Printf.sprintf "{%s} %s" (Var.to_string x) (print l);
  | [] -> ""

let rec print_vars l =
  match l with
  | x::l -> Printf.sprintf "(%s) %s" (Var.to_string x) (print_vars l);
  | [] -> ""
           
let exec_cmd cmd =
  match cmd with
  | Coh (x,ps,e) ->
     command "let %s = %s" (Var.to_string x) (string_of_ty e);
     let ps = Ctx.make ps in
     let env =
       if !debug_mode then 
	 Kernel.add_coh_env x ps e
       else
	 try Kernel.add_coh_env x ps e
	 with
	 | UnknownId s  -> error "unknown identifier %s" s
	 | UnknownCoh s  -> error "unknown coherence name %s" s
	 | IsNotType s -> error "got %s, but a type was expected" s
	 | HasNoType s -> error "the term %s has no type" s
	 | NotEqual (s1,s2) -> error "got %s, but %s was expected" s1 s2
     in 
     info "defined";
     env
  | Check (l, e, t) ->
     let c = Kernel.Ctx.make l in
     begin
       match t with
       | Some t ->
          command "check %s : %s" (string_of_tm e) (string_of_ty t);
          Kernel.mk_tm_of_ty c e t;
          info "checked"
       | None ->
          command "check %s " (string_of_tm e);
          let e,t = Kernel.mk_tm c e in
          info "checked term %s type %s" e t
     end

  | Decl (v,l,e,t) ->
     let c = Kernel.Ctx.make l in
     let t = match t with
       | Some t ->
          command "let %s = %s : %s" (Var.to_string v) (string_of_tm e) (string_of_ty t);
          let t = Kernel.add_let_env_of_ty v c e t in t
       | None ->
          command "let %s = %s" (Var.to_string v) (string_of_tm e);
          let t = Kernel.add_let_env v c e in t
     in
     info "defined term of type %s" t
     
     
let rec exec prog =
  let rec aux = function
    | [] -> ()
    | (t::l)  -> exec_cmd t; aux l
  in
  Kernel.init_env ();
  aux prog




                        
