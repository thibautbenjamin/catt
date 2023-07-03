open Common

(**toplevel commands. *)
type cmd =
  | Coh of Var.t * (Var.t * Syntax.ty) list * Syntax.ty
  | Check of ((Var.t * Syntax.ty) list) * Syntax.tm * Syntax.ty option
  | Decl of Var.t * (Var.t * Syntax.ty) list * Syntax.tm * Syntax.ty option
  | Set of string * string

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

let exec_set o v =
  let parse_bool v =
    match v with
    | _ when String.equal v "t" -> true
    | _ when String.equal v "true" -> true
    | _ when String.equal v "1" -> true
    | _ when String.equal v "f" -> false
    | _ when String.equal v "false" -> false
    | _ when String.equal v "0" -> false
    | _ -> raise (Error.NotABoolean v)
  in
  let parse_int v =
    match int_of_string_opt v with
    | Some s -> s
    | None -> raise (Error.NotAnInt v)
  in
  match o with
  | _ when String.equal o "explicit_substitutions" ->
    let v = parse_bool v in
    Settings.explicit_substitutions := v
  | _ when String.equal o "verbosity" ->
    let v = parse_int v in
    Settings.verbosity := v
  | _ -> raise (Error.UnknownOption o)

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
  | Set (o,v) -> exec_set o v

let exec prog =
  let rec aux = function
    | [] -> ()
    | (t::l)  -> exec_cmd t; aux l
  in
  aux prog
