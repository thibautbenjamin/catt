%{
    open Common
    open Syntax
    open Command


   let defpos () = Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()

    let mk ?pos ?show e =
      let pos = match pos with
      | None -> defpos ()
      | Some pos -> pos
      in
      let show = match show with
      | None -> false
      | Some show -> show
      in
      mk ~pos ~show e

    let hide e =
      mk ~pos:e.pos ~show:false (e.desc)
      

%}

%token COH OBJ PIPE MOR
%token LPAR RPAR LBRA RBRA COL FS
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
    |HYP IDENT COL expr FS { Hyp (Name $2, $4) }
    |COH IDENT args COL expr FS { Decl (Name $2, mk (Coh($3, hide $5))) }
    |CHECK expr FS { Check $2 }
    |EVAL expr FS { Eval $2 }
    |ENV FS { Env }

args:
    |LPAR IDENT COL expr RPAR args { (Name $2, hide $4)::$6 }
    |{ [] }

vars:
    |IDENT vars { (Name $1):: $2 }	
    |{ [] }

simple_expr:
    |LPAR expr RPAR { $2 }
    |OBJ { mk Obj}
    |IDENT { mk (Var (Name $1)) }

subst_expr:
    |simple_expr { $1 }
    |subst_expr LBRA vars RBRA { mk (Badsub ($1,$3)) }

expr:
    |subst_expr { $1 }
    |expr PIPE expr MOR expr { mk (Arr ($1,$3,$5)) }
    |COH STRING args COL simple_expr { mk (Coh ($3,$5)) }