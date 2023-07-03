open Common

(**toplevel commands. *)
type cmd =
  | Coh of Var.t * (Var.t * Syntax.ty) list * Syntax.ty
  | Check of ((Var.t * Syntax.ty) list) * Syntax.tm * Syntax.ty option
  | Decl of Var.t * (Var.t * Syntax.ty) list * Syntax.tm * Syntax.ty option

type prog = cmd list

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
     Io.command "coh %s = %s" (Var.to_string x) (Syntax.string_of_ty e);
     exec_coh x ps e
  | Check (l, e, t) ->
    Io.command "check %s" (Syntax.string_of_tm e);
    check l e t;
    Io.info "valid term %s" (Syntax.string_of_tm e);
  | Decl (v,l,e,t) ->
    Io.command "let %s = %s" (Var.to_string v) (Syntax.string_of_tm e);
    exec_decl v l e t

let exec prog =
  let rec aux = function
    | [] -> ()
    | (t::l)  -> exec_cmd t; aux l
  in
  aux prog
