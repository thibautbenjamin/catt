%{
    open Common
    open Command
    open Syntax

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
    | COH IDENT args COL tyexpr { Coh (make_var $2,$3,$5) }
    | CHECK args COL tyexpr EQUAL tmexpr { Check ($2,$6, Some $4) }
    | CHECK args EQUAL tmexpr { Check ($2,$4,None) }
    | LET IDENT args COL tyexpr EQUAL tmexpr { Decl (make_var $2,$3,$7,Some $5) }
    | LET IDENT args EQUAL tmexpr { Decl (make_var $2,$3,$5, None) }
    

args:
    | LPAR IDENT COL tyexpr RPAR args { (make_var $2, $4)::$6 }
    | { [] }

list_replace:
    | LET IDENT EQUAL tmexpr IN list_replace { (make_var $2, $4)::$6 }
    | { [] }

sub:
    | simple_tmexpr sub { $1::$2 }	
    | { [] }

simple_tmexpr:
    | LPAR tmexpr RPAR { $2 }
    | IDENT { Var (make_var $1) }

simple_tyexpr:
    | LPAR tyexpr RPAR { $2 }
    | OBJ { Obj }

subst_tmexpr:
    | simple_tmexpr { $1 }	
    | simple_tmexpr simple_tmexpr sub { Sub ($1,$2::$3) }

tmexpr:
    | LET IDENT EQUAL tmexpr IN tmexpr { Letin_tm (make_var $2, $4, $6) }
    | subst_tmexpr { $1 }

tyexpr:
    | LET IDENT EQUAL tmexpr IN tyexpr { Letin_ty (make_var $2, $4, $6) }
    | simple_tyexpr { $1 } 
    | subst_tmexpr MOR subst_tmexpr { Arr ($1,$3) }
