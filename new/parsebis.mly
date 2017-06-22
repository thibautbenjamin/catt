%{
    open Common
    open Syntax
    open Command

%}

%token COH OBJ PIPE MOR
%token LPAR RPAB LBRA RBRA COL FS
%token <string> IDENT STRING
%token CHECK EVAL HYP ENV
%token EOF

%left PIPE
%right MOR

%start prog
%type <Command.prog> prog
%%

prog:
    |cmd prog { $1::$2 }
    |EOF { [] }

cmd:
    |HYP IDENT COL expr FS { Hyp(Name $2, $4) }
    |COH IDENT args COL expr { Decl(Name $2, mk coh($3,$5)) }
    |CHECK expr FS { Check $2 }
    |EVAL expr FS { Eval $2 }
    |ENV { Env }

args:
    |LPAR IDENT COL expr RPAR args { (Name $2,$4)::$6 }
    |{ [] }

simple_expr:
    |LPAR expr RPAR { $2 }
    |OBJ { mk Obj}
    |IDENT { mk (Var (Name $1)) }

subst_expr:
    |simple_expr { $1 }
    |subst_expr LBRA args RBRA { mk Sub ($1,$3) }

expr:
    |subst_expr { $1 }
    |expr PIPE expr MOR expr { mk (Arr ($1,$3,$5)) }
    |COH STRING args COL simple_expr { mk (Coh ($3,$5)) }