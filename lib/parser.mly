%{
    open Command
    open Common
    open Syntax

    let add_suspension = function
      | Sub (x,s,None) -> Sub (x,s,Some 1)
      | Sub (x,s,Some n) -> Sub (x,s,Some (n+1))
      | _ -> assert false
%}

%token COH OBJ MOR WILD
%token LPAR RPAR LBRA RBRA COL BANG
%token <string> IDENT
%token CHECK EQUAL LET IN SET
%token EOF

%start prog
%type <Command.prog> prog
%%


prog:
    | cmd prog { $1::$2 }
    | EOF { [] }

cmd:
    | COH IDENT args COL tyexpr { Coh (Var.make_var $2,$3,$5) }
    | CHECK args COL tyexpr EQUAL tmexpr { Check ($2,$6, Some $4) }
    | CHECK args EQUAL tmexpr { Check ($2,$4,None) }
    | LET IDENT args COL tyexpr EQUAL tmexpr { Decl (Var.make_var $2,$3,$7,Some $5) }
    | LET IDENT args EQUAL tmexpr { Decl (Var.make_var $2,$3,$5, None) }
    | SET IDENT EQUAL IDENT { Set ($2,$4) }

args:
    | args LPAR IDENT COL tyexpr RPAR { (Var.make_var $3, $5)::$1 }
    | { [] }

nonempty_sub:
    | sub simple_tmexpr { ($2,false)::$1 }
    | sub functed_tmexpr { ($2,true)::$1 }

sub:
    | nonempty_sub { $1 }
    | { [] }

simple_tmexpr:
    | LPAR tmexpr RPAR { $2 }
    | WILD { Meta }
    | IDENT { Var (Var.make_var $1) }

functed_tmexpr:
    | LBRA tmexpr RBRA { $2 }

simple_tyexpr:
    | LPAR tyexpr RPAR { $2 }
    | OBJ { Obj }

subst_tmexpr:
    | simple_tmexpr { $1 }
    | simple_tmexpr nonempty_sub {  Sub ($1,$2,None) }
    | BANG subst_tmexpr { add_suspension $2 }

tmexpr:
    | LET IDENT EQUAL tmexpr IN tmexpr { Letin_tm (Var.make_var $2, $4, $6) }
    | subst_tmexpr { $1 }

tyexpr:
    | LET IDENT EQUAL tmexpr IN tyexpr { Letin_ty (Var.make_var $2, $4, $6) }
    | simple_tyexpr { $1 }
    | subst_tmexpr MOR subst_tmexpr { Arr ($1,$3) }
