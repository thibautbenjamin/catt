{
  open Parser
}

let space = ' ' | '\t' | '\r'

rule token = parse
  | "coh" { COH }
  | "check" { CHECK }
  | "let" { LET }
  | "in" { IN }
  | "(" { LPAR }
  | ")" { RPAR }
  | ":" { COL }
  | "->" { MOR }
  | "*" { OBJ }
  | "[" { LBRA }
  | "]" { RBRA }
  | "=" { EQUAL }
  | "set" { SET }
  | (['a'-'z''A'-'Z''0'-'9']['-''+''a'-'z''A'-'Z''0'-'9''_''@''{''}''/'',''\'']* as str) { IDENT str }
  | space+ { token lexbuf }
  | "#"[^'\n']* { token lexbuf }
  | "\n" { Lexing.new_line lexbuf; token lexbuf }
| eof { EOF }
