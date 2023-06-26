open Settings
open Common
open Syntax


(** A command. *)
type cmd =
  | Coh of var * (var * ty) list * ty (** a coherence *)
  | Check of ((var * ty) list) * tm * ty option (** check that a term is well-typed in a context *)
  | Decl of var * (var * ty) list * tm * ty option (** let declarations *)

(** A program. *)
type prog = cmd list

let rec print l =
  match l with
  | ((x,_),true)::l -> Printf.sprintf "(%s) %s" (string_of_var x) (print l);
  | ((x,_),false)::l -> Printf.sprintf "{%s} %s" (string_of_var x) (print l);
  | [] -> ""

let rec print_vars l =
  match l with
  | x::l -> Printf.sprintf "(%s) %s" (string_of_var x) (print_vars l);
  | [] -> ""

let exec_cmd cmd =
  match cmd with
  | Coh (x,ps,e) ->
     command "let %s = %s" (string_of_var x) (string_of_ty e);
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
     begin
       match t with
       | Some t ->
          command "check %s : %s" (string_of_tm e) (string_of_ty t);
          Kernel.mk_tm_of_ty l e t;
          info "checked"
       | None ->
          command "check %s " (string_of_tm e);
          let e,t = Kernel.mk_tm l e in
          info "checked term %s type %s" e t
     end
  | Decl (v,l,e,t) ->
     let t = match t with
       | Some t ->
          command "let %s = %s : %s" (string_of_var v) (string_of_tm e) (string_of_ty t);
          let t = Kernel.add_let_env_of_ty v l e t in t
       | None ->
          command "let %s = %s" (string_of_var v) (string_of_tm e);
          let t = Kernel.add_let_env v l e in t
     in
     info "defined term of type %s" t


let exec prog =
  let rec aux = function
    | [] -> ()
    | (t::l)  -> exec_cmd t; aux l
  in
  aux prog
