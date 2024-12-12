open Common
open Kernel
open Raw_types
open Unchecked_types.Unchecked_types (Coh) (Tm)

exception UnknownOption of string
exception NotAnInt of string
exception NotABoolean of string

(**toplevel commands. *)
type cmd =
  | Coh of Var.t * (Var.t * tyR) list * tyR
  | Check of (Var.t * tyR) list * tmR * tyR option
  | Decl of Var.t * (Var.t * tyR) list * tmR * tyR option
  | Set of string * string

type prog = cmd list

let postprocess_fn : (ctx -> tm -> ctx * tm) ref = ref (fun c e -> (c, e))

let () =
  postprocess_fn :=
    fun ctx tm ->
      Io.debug "conectx 1: %s" (Unchecked.ctx_to_string (Cones.Cone.ctx 1));
      Io.debug "conectx 2: %s" (Unchecked.ctx_to_string (Cones.Cone.ctx 2));
      Io.debug "conectx 3: %s" (Unchecked.ctx_to_string (Cones.Cone.ctx 3));
      Io.debug "conectx 4: %s" (Unchecked.ctx_to_string (Cones.Cone.ctx 4));
      Io.debug "conectx 5: %s" (Unchecked.ctx_to_string (Cones.Cone.ctx 5));
      Io.debug "conecomp 2: %s"
        (Unchecked.tm_to_string (Tm.develop (Cones.compose 2 2 1)));
      Io.debug "conecomp 3: %s"
        (Unchecked.tm_to_string (Tm.develop (Cones.compose 3 3 1)));
      Io.debug "conecomp 3*_2*3: %s \n\t of type %s"
        (Unchecked.tm_to_string (Tm.develop (Cones.compose 3 3 2)))
        (Unchecked.ty_to_string (Tm.ty (Cones.compose 3 3 2)));
      Io.debug "conecomp 4*_2*4: %s \n\t of type %s"
        (Unchecked.tm_to_string (Tm.develop (Cones.compose 4 4 2)))
        (Unchecked.ty_to_string (Tm.ty (Cones.compose 4 4 2)));
      Io.debug "conecomp 4*_3*4: %s \n\t of type %s"
        (Unchecked.tm_to_string (Tm.develop (Cones.compose 4 4 3)))
        (Unchecked.ty_to_string (Tm.ty (Cones.compose 4 4 3)));
      (* Io.debug "conecomp 3*2: %s" (Tm.name (Cones.compose 3 2 1)); *)
      (* Io.debug "conecomp 4*2: %s" (Tm.name (Cones.compose 4 2 1)); *)
      (* Io.debug "conecomp 4*3: %s" (Tm.name (Cones.compose 4 3 1)); *)
      (* Io.debug "conecomp 2*4: %s" (Tm.name (Cones.compose 2 4 1)); *)
      (* Io.debug "conecomp 3*4: %s" *)
      (*   (Unchecked.tm_to_string (Tm.develop (Cones.compose 3 4 1))); *)
      (* Io.debug "conecomp 5: %s" (Tm.name (Cones.compose 5 5 1)); *)
      (* Io.debug "conecomp 6: %s" (Tm.name (Cones.compose 6 6 1)); *)
      (ctx, tm)

let exec_coh v ps ty =
  let ps, ty = Elaborate.ty_in_ps ps ty in
  Environment.add_coh v ps ty

let exec_decl v l e t =
  let c, e = Elaborate.tm l e in
  let c, e = if !Settings.postprocess then !postprocess_fn c e else (c, e) in
  match t with
  | None -> Environment.add_let v c e
  | Some ty ->
      let _, ty = Elaborate.ty l ty in
      Environment.add_let v c ~ty e

let check l e t =
  let c, e = Elaborate.tm l e in
  let ty =
    match t with
    | None -> None
    | Some ty ->
        let _, ty = Elaborate.ty l ty in
        Some ty
  in
  let c = Kernel.Ctx.check c in
  let tm = Kernel.check_unnamed_term c ?ty e in
  let ty = Kernel.UnnamedTm.ty tm in
  (e, ty)

let exec_set o v =
  let parse_bool v =
    match v with
    | _ when String.equal v "t" -> true
    | _ when String.equal v "true" -> true
    | _ when String.equal v "1" -> true
    | _ when String.equal v "f" -> false
    | _ when String.equal v "false" -> false
    | _ when String.equal v "0" -> false
    | _ -> raise (NotABoolean v)
  in
  let parse_int v =
    match int_of_string_opt v with Some s -> s | None -> raise (NotAnInt v)
  in
  match o with
  | _ when String.equal o "explicit_substitutions" ->
      let v = parse_bool v in
      Settings.explicit_substitutions := v
  | _ when String.equal o "print_explicit_substitutions" ->
      let v = parse_bool v in
      Settings.print_explicit_substitutions := v
  | _ when String.equal o "postprocess" ->
      let v = parse_bool v in
      Settings.postprocess := v
  | _ when String.equal o "unroll_coherences" ->
      let v = parse_bool v in
      Settings.unroll_coherences := v
  | _ when String.equal o "implicit_suspension" ->
      let v = parse_bool v in
      Settings.implicit_suspension := v
  | _ when String.equal o "verbosity" ->
      let v = parse_int v in
      Settings.verbosity := v
  | _ -> raise (UnknownOption o)

let exec_cmd cmd =
  match cmd with
  | Coh (x, ps, e) ->
      Io.command "coh %s = %s" (Var.to_string x) (Raw.string_of_ty e);
      let coh = exec_coh x ps e in
      Io.info
        (lazy (Printf.sprintf "successfully defined %s" (Coh.to_string coh)))
  | Check (l, e, t) ->
      Io.command "check %s" (Raw.string_of_tm e);
      let e, ty = check l e t in
      Io.info
        (lazy
          (Printf.sprintf "valid term %s of type %s" (Unchecked.tm_to_string e)
             (Unchecked.ty_to_string ty)))
  | Decl (v, l, e, t) ->
      Io.command "let %s = %s" (Var.to_string v) (Raw.string_of_tm e);
      let tm, ty = exec_decl v l e t in
      Io.info
        (lazy
          (Printf.sprintf "successfully defined term %s of type %s"
             (Unchecked.tm_to_string tm)
             (Unchecked.ty_to_string ty)))
  | Set (o, v) -> (
      try exec_set o v with
      | UnknownOption o -> Error.unknown_option o
      | NotAnInt v -> Error.wrong_option_argument ~expected:"int" o v
      | NotABoolean v -> Error.wrong_option_argument ~expected:"boolean" o v)

type next = Abort | KeepGoing | Interactive

let show_menu () =
  Io.eprintf
    "Chose an option: \n\
     \t [x/SPC]: ignore and keep going; \n\
     \t [i]: drop in interactive mode; \n\
     \t [q/RET]: quit\n\
     %!";
  let rec decision () =
    let c = read_line () in
    if c = "x" || c = " " then KeepGoing
    else if c = "q" || c = "" then Abort
    else if c = "i" then Interactive
    else (
      Io.printf "Please chose a valid option";
      decision ())
  in
  decision ()

let initialise () = Cubical_composite.init ()

let exec ~loop_fn prog =
  initialise ();
  let rec aux = function
    | [] -> ()
    | t :: l -> (
        let next =
          try
            exec_cmd t;
            KeepGoing
          with
          | Error.InvalidEntry ->
              if !Settings.keep_going then KeepGoing
              else if !Settings.debug then show_menu ()
              else (
                Io.printf "Aborting...";
                Abort)
          | Error.OptionsError -> KeepGoing
        in
        match next with
        | KeepGoing -> aux l
        | Abort -> exit 1
        | Interactive -> loop_fn ())
  in
  aux prog
