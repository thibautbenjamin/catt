%{
    open Common
    open Syntax
    open Command
    open Ps

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
      

    let rec abstract ?pos (l : (var * expr) list) (e : expr) =
      match l with
      | [] -> e
      | (x,t)::l -> mk ?pos (Lambda (x,t, abstract l e))

    let rec find_cat (t : expr) =
      match t.desc with
      | Arr (c,_,_,_) -> c
      | Obj c -> c
      | _ -> error "only objects and morphisms are allowed"
%}

%token COH LET OBJ TYPE HOMTYPE FUN FORALL CAT FCOH
%token PIPE MOR ARR ARROW COMMA FUNCT APTOR
%token LPAR RPAR COL EQ FS RBRA LBRA
%token <string> IDENT STRING
%token CHECK EVAL HYP ENV
%token EOF

%left PIPE
%right MOR ARR ARROW FUNCT

%start prog
%type <Command.prog> prog
%%

prog:
    | cmd prog { $1::$2 }
    | EOF { [] }

cmd:
    | LET IDENT args EQ expr FS { Decl (Name $2, abstract $3 $5)}
    | HYP IDENT COL expr FS { Hyp (Name $2, $4) }
    | COH IDENT IDENT args COL expr FS { Decl (Name $2, mk (Coh ($2, Name $3, PS.make $4,hide $6))) }
    | FCOH IDENT IDENT IDENT IDENT args COL expr FS { Decl (Name $2, mk (Fcoh ($2, Name $5, (Name $3, Name $4), PS.make $6,hide $8))) }
    | CHECK expr FS { Check $2 }
    | EVAL expr FS { Eval $2 }
    | ENV FS { Env }

args:
    | LPAR IDENT COL expr RPAR args { (Name $2,hide $4)::$6 }
    | { [] }


simple_expr :
    | LPAR expr RPAR { $2 }
    | OBJ IDENT { mk (Obj  (mk (Var (Name $2)))) }
    | IDENT { mk (Var (Name $1)) }
    | TYPE { mk Type }
    | HOMTYPE IDENT { mk (HomType (mk (Var (Name $2)))) }
    | CAT { mk (Cat) }
    | APTOR LPAR expr COMMA expr RPAR { mk (Aptor ($3,$5)) }

app_expr:
    | app_expr simple_expr { mk (App ($1,$2)) }
    | simple_expr { $1 }
    
expr:
    | app_expr { $1 }
    | expr PIPE expr MOR expr { mk (Arr (find_cat $1,$1,$3,$5)) }
    | expr FUNCT expr { mk (Functor ($1,$3)) }
    | COH STRING IDENT args COL simple_expr { mk (Coh ($2,(Name $3),PS.make $4,$6)) }
