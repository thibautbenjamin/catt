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
  | Check_builtin of builtin
  | Decl of Var.t * (Var.t * tyR) list * tmR * tyR option
  | Decl_builtin of Var.t * builtin
  | Set of string * string
  | Benchmark of (Var.t * tyR) list * tmR
  | Benchmark_builtin of builtin

type prog = cmd list

let postprocess_fn : (ctx -> tm -> ctx * tm) ref = ref (fun c e -> (c, e))

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

let exec_decl_builtin v b =
  let value = Environment.builtin_to_value b in
  Environment.add_value v value

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

let exec_check_builtin b =
  let e = Environment.builtin_to_value b in
  let ty = Environment.value_ty e in
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
          (Printf.sprintf "valid term %s of type %s" (Printing.tm_to_string e)
             (Printing.ty_to_string ty)))
  | Decl (v, l, e, t) ->
      Io.command "let %s = %s" (Var.to_string v) (Raw.string_of_tm e);
      let tm, ty = exec_decl v l e t in
      Io.info
        (lazy
          (Printf.sprintf "successfully defined term %s of type %s"
             (Printing.tm_to_string tm) (Printing.ty_to_string ty)))
  | Set (o, v) -> (
      try exec_set o v with
      | UnknownOption o -> Error.unknown_option o
      | NotAnInt v -> Error.wrong_option_argument ~expected:"int" o v
      | NotABoolean v -> Error.wrong_option_argument ~expected:"boolean" o v)
  | Check_builtin b ->
      Io.command "check %s" (Raw.string_of_builtin b);
      let e, ty = exec_check_builtin b in
      Io.info
        (lazy
          (Printf.sprintf "valid term %s of type %s"
             (Environment.value_to_string e)
             (Printing.ty_to_string ty)))
  | Decl_builtin (v, b) ->
      Io.command "let %s = %s" (Var.to_string v) (Raw.string_of_builtin b);
      let e, ty = exec_decl_builtin v b in
      Io.info
        (lazy
          (Printf.sprintf "successfully defined term %s of type %s"
             (Environment.value_to_string e)
             (Printing.ty_to_string ty)))
  | Benchmark (l, e) ->
      let e, _ = check l e None in
      Io.info
        (lazy
          (Printf.sprintf "term computes to:\n %s"
             (Printing.print_kolmogorov e)))
  | Benchmark_builtin b ->
      let e, _ = exec_check_builtin b in
      let e =
        match e with
        | Environment.Coh _ ->
            Error.fatal "bechmarking a builtin resolving to a coherence"
        | Environment.Tm e -> Tm.develop e
      in
      Io.info
        (lazy
          (Printf.sprintf "term computes to:\n %s"
             (Printing.print_kolmogorov e)))

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
