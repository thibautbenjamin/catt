open Kernel
open Raw_types

(**toplevel commands. *)
type cmd =
  | Coh of Var.t * (Var.t * tyR) list * tyR
  | Check of ((Var.t * tyR) list) * tmR * tyR option
  | Decl of Var.t * (Var.t * tyR) list * tmR * tyR option
  | Set of string * string

type prog = cmd list

let exec_coh v ps ty =
  let ps,ty = Elaborate.ty_in_ps ps ty in
  Environment.add_coh v ps ty

let exec_decl v l e t =
  let c,e = Elaborate.tm l e in
  match t with
  | None -> Environment.add_let v c e
  | Some ty ->
     let _,ty = Elaborate.ty l ty in
     Environment.add_let v c ~ty e

let check l e t =
  let c,e = Elaborate.tm l e in
  let ty =
    match t with
    | None -> None
    | Some ty -> let _,ty = Elaborate.ty l ty in Some ty
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
  | _ when String.equal o "implicit_suspension" ->
    let v = parse_bool v in
    Settings.implicit_suspension := v
  | _ when String.equal o "verbosity" ->
    let v = parse_int v in
    Settings.verbosity := v
  | _ -> raise (Error.UnknownOption o)

let exec_cmd cmd =
  match cmd with
  | Coh (x,ps,e) ->
     Io.command "coh %s = %s" (Var.to_string x) (Raw.string_of_ty e);
     exec_coh x ps e
  | Check (l, e, t) ->
    Io.command "check %s" (Raw.string_of_tm e);
    check l e t;
    Io.info (lazy (Printf.sprintf "valid term %s" (Raw.string_of_tm e)));
  | Decl (v,l,e,t) ->
    Io.command "let %s = %s" (Var.to_string v) (Raw.string_of_tm e);
    exec_decl v l e t
  | Set (o,v) -> exec_set o v

let exec prog =
  let rec aux = function
    | [] -> ()
    | (t::l)  -> exec_cmd t; aux l
  in
  aux prog
