open Common
open Variables
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

let exec_coh v ps ty =
  let ty = Elaborate.ty_in_ps ps ty in
  let ps = Elaborate.ps ps in
  Environment.add_coh v ps ty

let exec_decl v l e t =
  let c = Elaborate.ctx l in
  let e = Elaborate.tm c e in
  match t with
  | None -> Environment.add_let v c e
  | Some _ -> assert false

let exec_cmd cmd =
  match cmd with
  | Coh (x,ps,e) ->
     command "let %s = %s" (string_of_var x) (string_of_ty e);
     exec_coh x ps e;
     info "defined";
  | Check (_l, _e, _t) -> assert false
     (* begin *)
     (*   match t with *)
     (*   | Some t -> *)
     (*      command "check %s : %s" (string_of_tm e) (string_of_ty t); *)
     (*      Kernel.mk_tm_of_ty l e t; *)
     (*      info "checked" *)
     (*   | None -> *)
     (*      command "check %s " (string_of_tm e); *)
     (*      let e,t = Kernel.mk_tm l e in *)
     (*      info "checked term %s type %s" e t *)
     (* end *)
  | Decl (v,l,e,t) ->
     exec_decl v l e t;
     info "defined term"


let exec prog =
  let rec aux = function
    | [] -> ()
    | (t::l)  -> exec_cmd t; aux l
  in
  aux prog
