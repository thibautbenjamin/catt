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
  | "conecomp(" (['0'-'9']* as n) "," (['0'-'9']* as k) "," (['0'-'9']* as m)")" {
                                                                            let n = int_of_string n in
                                                                            let k = int_of_string k in
                                                                            let m = int_of_string m in
                                                                            CONECOMP(n,k,m) }
  | "cylcomp(" (['0'-'9']* as n) "," (['0'-'9']* as k) "," (['0'-'9']* as m)")" {
                                                                            let n = int_of_string n in
                                                                            let k = int_of_string k in
                                                                            let m = int_of_string m in
                                                                            CYLCOMP(n,k,m) }
  | "cylstack(" (['0'-'9']* as n) ")" {
                                      let n = int_of_string n in
                                      CYLSTACK(n) }
  | "EH(" (['0'-'9']* as n) "," (['0'-'9']* as k) "," (['0'-'9']* as l)")" {
                                                                            let n = int_of_string n in
                                                                            let k = int_of_string k in
                                                                            let l = int_of_string l in
                                                                            EH_FULL(n,k,l) }
  | "eh(" (['0'-'9']* as n) "," (['0'-'9']* as k) "," (['0'-'9']* as l)")" {
                                                                            let n = int_of_string n in
                                                                            let k = int_of_string k in
                                                                            let l = int_of_string l in
                                                                            EH_HALF(n,k,l) }                                                                        
  | "declare" { DECLARE }
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
  | "op" { OP }
  | "@" { AT }
  | "" { IGNORE }
  | ['0'-'9']* as str { INT str }
  | (['a'-'z''A'-'Z''0'-'9'](['-''+''a'-'z''A'-'Z''0'-'9''_''@''>''<''{''}''/''\'']*) as str) { IDENT str }
  | space+ { token lexbuf }
  | "#"[^'\n']* { token lexbuf }
  | "\n" { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
