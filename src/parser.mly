%{
    open Common
    open Command
    open Kernel.Expr

    module Var = Kernel.Var
%}

%token COH OBJ PIPE MOR
%token LPAR RPAR LBRA RBRA COL
%token <string> IDENT STRING
%token CHECK EVAL HYP ENV EQUAL LET IN
%token EOF

%left PIPE
%right MOR

%start prog
%type <Command.prog> prog
%%

prog:
    | cmd prog { $1::$2 }
    | EOF { [] }

cmd:
    | COH IDENT args COL tyexpr { Coh (Var.make $2,$3,$5) }
    | CHECK args COL tyexpr EQUAL tmexpr { Check ($2,$6, Some $4) }
    | CHECK args EQUAL tmexpr { Check ($2,$4,None) }
    | LET IDENT args COL tyexpr EQUAL list_replace tmexpr { Decl (Var.make $2,$3,$7,$8,Some $5) }
    | LET IDENT args EQUAL list_replace tmexpr { Decl (Var.make $2,$3,$5,$6, None) }
    

args:
    | LPAR IDENT COL tyexpr RPAR args { (Var.make $2, $4)::$6 }
    | { [] }

list_replace:
    | LET IDENT EQUAL tmexpr IN list_replace { (Var.make $2, $4)::$6 }
    | { [] }

sub:
    | simple_tmexpr sub { $1::$2 }	
    | { [] }

simple_tmexpr:
    | LPAR tmexpr RPAR { $2 }
    | IDENT { Var (Var.make $1) }

simple_tyexpr:
    | LPAR tyexpr RPAR { $2 }
    | OBJ { Obj }

subst_tmexpr:
    | simple_tmexpr { $1 }	
    | simple_tmexpr simple_tmexpr sub { Sub ($1,$2::$3) }

tmexpr:
    | subst_tmexpr { $1 }

tyexpr:
    | simple_tyexpr { $1 } 
    | subst_tmexpr MOR subst_tmexpr { Arr ($1,$3) }
