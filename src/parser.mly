%{
    open Common
    open Command
    open ExtSyntax
%}

%token COH OBJ PIPE MOR
%token LPAR RPAR LBRA RBRA COL FS
%token <string> IDENT STRING
%token CHECK EVAL HYP ENV EQUAL LET
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
    |COH IDENT args COL expr FS { DeclCoh (Var.mk $2, Coh($3,$5)) }
    |CHECK args COL expr EQUAL expr FS { Check ($2,$6, Some $4) }
    |CHECK args EQUAL expr FS { Check ($2,$4,None) }
    |LET IDENT args COL expr EQUAL expr FS { Decl (Var.mk $2,$3,$7, Some $5) }
    |LET IDENT args EQUAL expr FS { Decl (Var.mk $2,$3,$5, None) }


args:
    |LPAR IDENT COL expr RPAR args { (Var.mk $2, $4)::$6 }
    |{ [] }

sub:
    |simple_expr sub { $1::$2 }	
    |{ [] }

simple_expr:
    |LPAR expr RPAR { $2 }
    |OBJ { Obj }
    |IDENT { Var (Var.mk $1) }

subst_expr:
    |simple_expr { $1 }
    |subst_expr LBRA sub RBRA { Sub ($1,$3) }

expr:
    |subst_expr { $1 }
    |expr MOR expr { Arr ($1,$3) }
    |COH args COL simple_expr { Coh ($2,$4) }