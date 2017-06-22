%{
    open Common
    open Syntax
    open Command

    let hide e =
      mk ~pos:e.pos ~show:false (e.desc)
%}

%token COH OBJ
%token PIPE MOR
%token LPAR RPAR COL FS RBRA LBRA
%token <string> IDENT STRING
%token CHECK EVAL HYP ENV
%token EOF

%left PIPE
%right MOR

%start prog
%type <Command.prog> prog
%%

prog:
    | cmd prog { let t = $1 in debug "ok"; t::$2 }
    | EOF { debug "EOF"; [] }

cmd:
    | HYP IDENT COL expr FS { Hyp (Name $2, $4) }
    | COH IDENT args COL expr FS { Decl (Name $2, mk (Coh ($3, hide $5))) } 
    | CHECK expr FS { Check $2 }
    | EVAL expr FS { Eval $2 }
    | ENV FS { Env }

args:
    | LPAR IDENT COL expr RPAR args { (Name $2,hide $4)::$6 }
    | { [] }


simple_expr :
    | LPAR expr RPAR { $2 }
    | OBJ { mk Obj }
    | IDENT { mk (Var (Name $1)) }

subst_expr :
    |simple_expr { $1 }
    |subst_expr LBRA args RBRA { mk (Sub ($1,$3)) } 

expr :
    | subst_expr { $1 }
    | expr PIPE expr MOR expr { mk (Arr ($1,$3,$5)) }
    | COH STRING args COL simple_expr { mk (Coh ($3,$5)) }
