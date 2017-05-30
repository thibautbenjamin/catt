{
  open Parser
}


let space = ' ' | '\t' | '\r'

rule token = parse
  | "coh" { COH }
  | "functoriality" { FUNCTY }
  | "let" { LET }
  | "hyp" { HYP }
  | "check" { CHECK }
  | "eval" { EVAL }
  | "env" { ENV }
  | "Type" { TYPE }
  | "HomType" { HOMTYPE }
  | "Cat" { CAT }
  | "(" { LPAR }
  | ")" { RPAR }
  | ":" { COL }
  | "->" { ARR }
  | "=>" { ARROW }
  | "→" { MOR }
  | "⇒" { FUNCT }
  | "." { FS }
  | "*" { OBJ }
  | "=" { EQ }
  | "|" { PIPE }
  | "," { COMMA }
  | "[" { LBRA }
  | "]" { RBRA }
  | "fun" { FUN }
  | "ap" { APTOR }
  | "forall" { FORALL }
  | (['_''a'-'z''A'-'Z''0'-'9']['-''+''a'-'z''A'-'Z''0'-'9''_']* as str) { IDENT str }
  | space+ { token lexbuf }
  | "#"[^'\n']* { token lexbuf }
  | '"'([^'"']* as str)'"' { STRING str }
  | "\n" { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }