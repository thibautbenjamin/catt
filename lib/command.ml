open Common
open Syntax

(**toplevel commands. *)
type cmd =
  | Coh of Var.t * (Var.t * ty) list * ty
  | Check of ((Var.t * ty) list) * tm * ty option
  | Decl of Var.t * (Var.t * ty) list * tm * ty option

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

let exec_coh v ps ty =
  let ty = Elaborate.ty_in_ps ps ty in
  let ps = Elaborate.ps ps in
  Environment.add_coh v ps ty

let exec_decl v l e t =
  let c = Elaborate.ctx l in
  let e = Elaborate.tm c e in
  match t with
  | None -> Environment.add_let v c e
  | Some ty ->
     let ty = Elaborate.ty c ty in
     Environment.add_let_check v c e ty

let check l e t =
  let c = Elaborate.ctx l in
  let e = Elaborate.tm c e in
  let ty =
    match t with
    | None -> None
    | Some ty -> Some (Elaborate.ty c ty)
  in
  let c = Kernel.Ctx.check c in
  ignore(Kernel.Tm.check c ?ty e)

let exec_cmd cmd =
  match cmd with
  | Coh (x,ps,e) ->
     command "coh %s = %s" (Var.to_string x) (string_of_ty e);
     exec_coh x ps e
  | Check (l, e, t) ->
    command "check %s" (string_of_tm e);
    check l e t;
    info "valid term %s" (string_of_tm e);
  | Decl (v,l,e,t) ->
    command "let %s = %s" (Var.to_string v) (string_of_tm e);
    exec_decl v l e t

let exec prog =
  let rec aux = function
    | [] -> ()
    | (t::l)  -> exec_cmd t; aux l
  in
  aux prog
