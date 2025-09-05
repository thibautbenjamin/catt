%{
    open Common
    open Command
    open Raw_types

    type annotated_ps =
      | Br of (Var.t * annotated_ps) list * Var.t

    let add_suspension = function
      | Sub (x,s,None,b) -> Sub (x,s,Some 1,b)
      | Sub (x,s,Some n,b) -> Sub (x,s,Some (n+1),b)
      | Letin_tm _ | VarR _ |Op _ | Meta | Inverse _ | Unit _ | BuiltinR _
        -> Error.fatal "trying to generate an invalid suspension"

    let mark_explicit = function
      | Sub(x,s,i,_) -> Sub(x,s,i,true)
      | Letin_tm _ | VarR _ |Op _ | Meta | Inverse _ | Unit _ | BuiltinR _
        -> Error.fatal "only substitution can be marked explicit"

    let context_of_annotated_ps ps =
      let rec context_ending_to x ty l =
        match l with
        | [] -> [(x, ty)]
        | (y,ps)::l ->
           List.append
             (context_over (ArrR (VarR y, VarR x)) ps)
             ((x, ty)::(context_ending_to y ty l))
      and context_over ty p =
        match p with
        | Br(l,x) -> context_ending_to x ty l
      in
      context_over ObjR ps
%}

%token COH OBJ MOR WILD IGNORE
%token LPAR RPAR LBRA RBRA LCUR RCUR COL BANG OP AT
%token <string> BUILTIN
%token <int*int*int> CONECOMP
%token <int*int*int> CYLCOMP
%token <int*int*int> EH_FULL
%token <int*int*int> EH_HALF
%token <int> CYLSTACK
%token <string> IDENT
%token <string> INT
%token CHECK EQUAL LET IN SET INV UNIT DECLARE
%token EOF

%start prog
%type <Command.prog> prog
%%

prog:
  | cmd prog { $1::$2 }
  | IGNORE prog { $2 }
  | EOF { [] }

cmd:
  | COH IDENT args_or_ps COL tyexpr { Coh (Var.make_var $2,$3,$5) }
  | COH BUILTIN args_or_ps COL tyexpr
    { if !Settings.use_builtins then raise (Error.ReservedName $2)
      else Coh (Var.make_var $2,$3,$5) }
  | CHECK args_or_ps COL tyexpr EQUAL tmexpr { Check ($2,$6, Some $4) }
  | CHECK args_or_ps EQUAL tmexpr { Check ($2,$4,None) }
  | CHECK builtin { Check_builtin ($2) }
  | LET IDENT args_or_ps COL tyexpr EQUAL tmexpr
    { Decl (Var.make_var $2,$3,$7,Some $5) }
  | LET IDENT args_or_ps EQUAL tmexpr
    { Decl (Var.make_var $2,$3,$5, None) }
  | LET BUILTIN args_or_ps COL tyexpr EQUAL tmexpr
    {
      if !Settings.use_builtins then raise (Error.ReservedName $2)
      else Decl (Var.make_var $2,$3,$7,Some $5)
    }
  | LET BUILTIN args_or_ps EQUAL tmexpr
    { if !Settings.use_builtins then raise (Error.ReservedName $2)
      else Decl (Var.make_var $2,$3,$5, None) }
  | SET IDENT EQUAL IDENT { Set ($2,$4) }
  | SET IDENT EQUAL INT { Set ($2,$4) }
  | DECLARE IDENT EQUAL builtin { Decl_builtin (Var.make_var $2,$4) }

args_of_same_ty :
  | IDENT COL tyexpr { [Var.make_var $1, $3], $3 }
  | IDENT args_of_same_ty { (Var.make_var $1, snd $2)::(fst $2), snd $2 }

nonempty_args :
  | LPAR args_of_same_ty RPAR args { List.append (fst $2) $4 }

args:
  | nonempty_args { $1 }
  | { [] }

args_or_ps :
  | args { List.rev $1 }
  | ps { $1 }

nonempty_sub:
  | sub simple_tmexpr { ($2,0)::$1 }
  | sub functed_tmexpr { $2::$1 }

sub:
  | nonempty_sub { $1 }
  | { [] }

builtin_tm :
  | builtin {
            if !Settings.use_builtins
            then BuiltinR $1
            else VarR (Var.make_var (Raw.string_of_builtin $1)) }

builtin:
  | BUILTIN {
    match $1 with
    | s when String.equal s "comp" -> Comp
    | s when String.equal s "id" -> Id
    | _ -> assert false }
 | CONECOMP { let (n,k,m) = $1 in Conecomp(n,k,m) }
 | CYLCOMP { let (n,k,m) = $1 in Cylcomp(n,k,m) }
 | CYLSTACK { let n = $1 in Cylstack(n) }
 | EH_HALF { let (n,k,l) = $1 in Eh_half(n,k,l)}
 | EH_FULL { let (n,k,l) = $1 in Eh_full(n,k,l)}

simple_tmexpr:
  | LPAR tmexpr RPAR { $2 }
  | WILD { Meta }
  | INV LPAR tmexpr RPAR { Inverse $3 }
  | UNIT LPAR tmexpr RPAR { Unit $3 }
  | IDENT { VarR (Var.make_var $1) }
  | builtin_tm { $1 }

functed_tmexpr:
  | LBRA maybe_functed_tmexpr RBRA { let t,n = $2 in t,n+1 }

maybe_functed_tmexpr:
  | tmexpr { ($1,0) }
  | LBRA maybe_functed_tmexpr RBRA { let t,n = $2 in t,n+1 }

simple_tyexpr:
  | LPAR tyexpr RPAR { $2 }
  | OBJ { ObjR }

susp_tmexpr:
  | simple_tmexpr { $1 }
  | simple_tmexpr nonempty_sub {  Sub ($1,$2,None,false) }
  | BANG susp_tmexpr { add_suspension $2 }

subst_tmexpr:
  | susp_tmexpr { $1 }
  | AT susp_tmexpr { mark_explicit $2 }

tmexpr:
  | LET IDENT EQUAL tmexpr IN tmexpr { Letin_tm (Var.make_var $2, $4, $6) }
  | subst_tmexpr { $1 }
  | OP LCUR int_list RCUR LPAR tmexpr RPAR { Op($3, $6) }

tyexpr:
  | LET IDENT EQUAL tmexpr IN tyexpr { Letin_ty (Var.make_var $2, $4, $6) }
  | simple_tyexpr { $1 }
  | subst_tmexpr MOR subst_tmexpr { ArrR ($1,$3) }

ps :
  | LPAR IDENT RPAR { context_of_annotated_ps (Br ([], Var.make_var $2)) }
  | LPAR IDENT simpl_ps ps_list IDENT RPAR
    {
      context_of_annotated_ps
        (Br (List.append $4 [(Var.make_var $2, $3)], Var.make_var $5))
    }

simpl_ps :
  | LPAR ps_list IDENT RPAR { Br ($2,Var.make_var $3) }

nonempty_ps_list :
  | ps_list IDENT simpl_ps { (Var.make_var $2,$3)::$1 }

ps_list :
  | nonempty_ps_list { $1 }
  | { [] }

int_list :
  | INT int_list { (int_of_string $1)::$2 }
  | { [] }
