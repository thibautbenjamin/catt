(** Parse a string. *)
let parse s =
  let lexbuf = Lexing.from_string s in
  try Ok (Parser.prog Lexer.token lexbuf) with
  | Failure s when s = "lexing: empty token" ->
      let pos = Lexing.lexeme_end_p lexbuf in
      Error
        (Io.error "lexing error in file %s at line %d, character %d"
           pos.Lexing.pos_fname pos.Lexing.pos_lnum
           (pos.Lexing.pos_cnum - pos.Lexing.pos_bol))
  | Parser.Error ->
      let pos = Lexing.lexeme_end_p lexbuf in
      Error
        (Io.error
           "parsing error in file %s at word \"%s\", line %d, character %d"
           pos.Lexing.pos_fname (Lexing.lexeme lexbuf) pos.Lexing.pos_lnum
           (pos.Lexing.pos_cnum - pos.Lexing.pos_bol - 1))
  | Error.ReservedName x ->
      Error
        (Io.error
           "Could not parse the input because the name %s is a built-in.\n\
            You can change the name of the term or coherence, or add the \
            option '--no-builtins' to deactivate the use of built-ins"
           x)

(** Initialize the prover. *)
let init () = Printf.printf "=^.^= "

(** Execute a command. *)
let rec exec s parse_error_fn =
  if s = "exit" then exit 0
  else
    match parse s with
    | Ok cmd -> Command.exec ~loop_fn:loop cmd
    | Error _ -> parse_error_fn ()

(** Interactive loop. *)
and loop () =
  while true do
    init ();
    let s = read_line () in
    exec s (fun () -> ())
  done
