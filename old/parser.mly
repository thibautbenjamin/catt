%{
    open Lang

    let defpos () = Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()

    let mk ?pos e =
      let pos = match pos with
      | None -> defpos ()
      | Some pos -> pos
      in
      mk ~pos e

    let rec abstract ?pos (l : (var * expr) list) (e : expr) =
      match l with
      | [] -> e
      | (x,t)::l -> mk ?pos (Lambda (x,t, abstract l e))
%}

%token COH LET OBJ TYPE HOMTYPE FUN FORALL CAT FUNCTY
%token PIPE MOR ARR ARROW COMMA FUNCT APTOR
%token LPAR RPAR COL EQ FS RBRA LBRA
%token <string> IDENT STRING
%token CHECK EVAL HYP ENV
%token EOF

%left PIPE
%right MOR ARR ARROW FUNCT

%start prog
%type <Lang.prog> prog
%%

prog:
    | cmd prog { $1::$2 }
    | EOF { [] }

cmd:
    | LET IDENT args EQ expr FS { Decl (Name $2, abstract $3 $5)}
    | HYP IDENT COL expr FS { Hyp (Name $2, $4) }
    | COH IDENT args COL expr FS { Decl (Name $2, mk (Coh ($2, PS.make $3,$5))) }
    | CHECK expr FS { Check $2 }
    | EVAL expr FS { Eval $2 }
    | ENV FS { Env }
    | FUNCTY IDENT IDENT args COL expr FS  { Decl (Name $2, mk (Functorial ($2, PS.make $4, (mk (Var (Name $3))), $6))) } 

args:
    | LPAR IDENT COL expr RPAR args { (Name $2,$4)::$6 }
    | { [] }


simple_expr :
    | LPAR expr RPAR { $2 }
    | OBJ { mk Obj  }
    | IDENT { mk (Var (Name $1)) }
    | TYPE { mk Type }
    | HOMTYPE { mk HomType  }
    | CAT { mk (Cat) }
    | APTOR LPAR expr COMMA expr RPAR { mk (Aptor ($3,$5))}

app_expr:
    | app_expr simple_expr { mk (App ($1,$2)) }
    | simple_expr { $1 }
    
expr:
    | app_expr { $1 }
    | expr PIPE expr MOR expr { mk (Arr ($1,$3,$5)) }
    | expr FUNCT expr { mk (Functor ($1,$3)) }
    | COH STRING args COL simple_expr { mk (Coh ($2,PS.make $3,$5)) }