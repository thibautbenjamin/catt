(** Interaction with user. *)
open Common
       

(** Parse a string. *)
let parse s =
  let lexbuf = Lexing.from_string s in
  try
    Parser.prog Lexer.token lexbuf
  with
  | Failure s when s = "lexing: empty token" ->
     let pos = Lexing.lexeme_end_p lexbuf in
     error "lexing error in file %s at line %d, character %d"
     pos.Lexing.pos_fname
     pos.Lexing.pos_lnum
     (pos.Lexing.pos_cnum - pos.Lexing.pos_bol) 
  | Parsing.Parse_error ->
     let pos = (Lexing.lexeme_end_p lexbuf) in
     failwith (Printf.sprintf "parsing error in file %s at word \"%s\", line %d, character %d"
              (*error "parsing error in file %s at word \"%s\", line %d, character %d"*)
       pos.Lexing.pos_fname
       (Lexing.lexeme lexbuf)
       pos.Lexing.pos_lnum
       (pos.Lexing.pos_cnum - pos.Lexing.pos_bol - 1))


(** Initialize the prover. *)
let init () =
  print_string "=^.^= "

(** Execute a command. *)
let exec s =
  if s = "exit" then
    exit 0
  else
Command.exec (parse s)

(** Interactive loop. *)
let loop () =
  while true do
    init ();
    let s = read_line () in
    exec s
  done
