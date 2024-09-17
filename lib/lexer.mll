{
  open Parser
}

let space = ' ' | '\t' | '\r'

rule token = parse
  | "coh" { COH }
  | "check" { CHECK }
  | "let" { LET }
  | "in" { IN }
  | "comp" as str { BUILTIN str }
  | "id" as str { BUILTIN str }
  | "I" { INV }
  | "U" { UNIT }
  | "(" { LPAR }
  | ")" { RPAR }
  | ":" { COL }
  | "->" { MOR }
  | "*" { OBJ }
  | "[" { LBRA }
  | "]" { RBRA }
  | "{" { LCUR }
  | "}" { RCUR }
  | "=" { EQUAL }
  | "_" { WILD }
  | "set" { SET }
  | "!" { BANG }
  | "," { COMA }
  | "op" { OP }
  | "@" { AT }
  | "" { IGNORE }
  | ['0'-'9']* as str { INT str }
  | (['a'-'z''A'-'Z''0'-'9']['-''+''a'-'z''A'-'Z''0'-'9''_''@''>''{''}''/'',''\'']* as str) { IDENT str }
  | space+ { token lexbuf }
  | "#"[^'\n']* { token lexbuf }
  | "\n" { Lexing.new_line lexbuf; token lexbuf }
| eof { EOF }
