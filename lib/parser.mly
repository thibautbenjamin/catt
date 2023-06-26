%{
    open Command
    open Syntax

    let generate_functorialize l =
    	let rec aux l i = match l with
	|[] -> [],[]
	|(x,true)::l -> let (res,func) = aux l (i+1)
		        in x::res,i::func
	|(x,false)::l -> let (res,func) = aux l (i+1)
		      	 in x::res,func
	in aux l 0
%}

%token COH OBJ MOR
%token LPAR RPAR LBRA RBRA COL
%token <string> IDENT
%token CHECK EQUAL LET IN
%token EOF

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

sub:
    | simple_tmexpr sub { ($1,false)::$2 }
    | functed_tmexpr sub { ($1,true)::$2 }
    | { [] }

simple_tmexpr:
    | LPAR tmexpr RPAR { $2 }
    | IDENT { Var (make_var $1) }

functed_tmexpr:
    | LBRA tmexpr RBRA { $2 }

simple_tyexpr:
    | LPAR tyexpr RPAR { $2 }
    | OBJ { Obj }

subst_tmexpr:
    | simple_tmexpr { $1 }
    | simple_tmexpr simple_tmexpr sub { let sub,func = generate_functorialize (($2,false)::$3)
      		    		      	in Sub ($1,sub,func) }
    | simple_tmexpr functed_tmexpr sub { let sub,func = generate_functorialize (($2,true)::$3)
      		    		      	 in Sub ($1,sub,func) }

tmexpr:
    | LET IDENT EQUAL tmexpr IN tmexpr { Letin_tm (make_var $2, $4, $6) }
    | subst_tmexpr { $1 }

tyexpr:
    | LET IDENT EQUAL tmexpr IN tyexpr { Letin_ty (make_var $2, $4, $6) }
    | simple_tyexpr { $1 }
    | subst_tmexpr MOR subst_tmexpr { Arr ($1,$3) }
