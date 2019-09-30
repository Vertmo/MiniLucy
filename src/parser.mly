%{

  open Asttypes
  open PMinils

  let mk_expr e startp endp = { pexpr_desc = e; pexpr_loc = (startp, endp) }
  let mk_patt p startp endp = { ppatt_desc = p; ppatt_loc = (startp, endp) }

%}

%token AND
%token ARROW
%token BOOL
%token COLON
%token COMMA
%token <Asttypes.op> COMP
%token <bool> CONST_BOOL
%token <int> CONST_INT
%token <float> CONST_REAL
%token DIV
%token ELSE
%token EOF
%token EQUAL
%token EVERY
%token FBY
%token NEQ
%token REAL
%token <string> IDENT
%token IF
%token INT
%token LET
%token LPAREN
%token MERGE
%token MINUS
%token MOD
%token NODE
%token NOT
%token OR
%token PLUS
(* %token PRE *)
%token RETURNS
%token RPAREN
%token SEMICOL
%token SLASH
%token STAR
%token TEL
%token THEN
%token TYPE
%token VAR
%token WHEN
%token XOR


%nonassoc ELSE
(* %right ARROW *)
%left OR
%left XOR
%left AND
%left COMP EQUAL NEQ                          /* < <= > >= <> = <> */
%left PLUS MINUS                              /* + -  */
%left STAR SLASH DIV MOD                      /* * /  mod */
%nonassoc NOT (* PRE *)                             /* not pre */

/* Point d'entrée */

%start file
%type <PMinils.p_file> file

%%

file: clock_decs node_decs EOF
  { { pf_clocks = $1; pf_nodes = $2; } }
;

clock_decs:
| /* empty */ { [] }
| clock clock_decs { $1 :: $2 }
;

clock:
| TYPE IDENT EQUAL constr_list SEMICOL
  { ($2, $4) }
;

constr_list:
| IDENT
  { [$1] }
| IDENT PLUS constr_list
{ $1 :: $3 }
;

node_decs:
| /* empty */       { [] }
| node node_decs    { $1 :: $2 }
;


node:
| NODE IDENT LPAREN in_params RPAREN
  RETURNS LPAREN out_params RPAREN SEMICOL
  local_params
  LET eq_list TEL semi_opt
    { { pn_name = $2;
	pn_input = $4;
	pn_output = $8;
	pn_local = $11;
	pn_equs = $13;
	pn_loc = ($startpos, $endpos) } }
;

in_params:
| /* empty */
    { [] }
| param_list
    { $1 }
;


out_params:
| param_list
    { $1 }
;

local_params:
| /* empty */
    { [] }
| VAR param_list_semicol
    { $2 }
;

param_list:
| param
    { $1 }
| param SEMICOL param_list
    { $1 @ $3 }
;

param_list_semicol:
| param  SEMICOL
    { $1 }
| param SEMICOL param_list_semicol
    { $1 @ $3 }
;


param:
  | ident_comma_list COLON typ
      { let typ = $3 in
        List.map (fun id -> (id, typ)) $1 }
;

eq_list:
| eq
    { [$1] }
| eq eq_list
    { $1 :: $2 }
;

eq:
| pattern EQUAL expr SEMICOL
    { { peq_patt = $1; peq_expr = $3; } }
;

pattern:
| IDENT
    { mk_patt (PP_ident $1) $startpos $endpos }
| LPAREN IDENT COMMA ident_comma_list RPAREN
    { mk_patt (PP_tuple($2::$4)) $startpos $endpos }
;

expr:
| LPAREN expr RPAREN
    { $2 }
| const
    { mk_expr (PE_const $1) $startpos $endpos }
| IDENT
    { mk_expr (PE_ident $1) $startpos $endpos }
| IDENT LPAREN expr_comma_list_empty RPAREN
    { mk_expr (PE_app ($1, $3,
                       { pexpr_desc = PE_const (Cbool false);
                         pexpr_loc = ($startpos, $endpos)})) $startpos $endpos }
| IDENT LPAREN expr_comma_list_empty RPAREN EVERY expr
    { mk_expr (PE_app ($1, $3, $6)) $startpos $endpos }
| IF expr THEN expr ELSE expr
    { mk_expr (PE_op (Op_if, [$2; $4; $6])) $startpos $endpos }
| expr PLUS expr
    { mk_expr (PE_op (Op_add, [$1; $3])) $startpos $endpos }
| expr MINUS expr
    { mk_expr (PE_op (Op_sub, [$1; $3])) $startpos $endpos }
| expr STAR expr
    { mk_expr (PE_op (Op_mul, [$1; $3])) $startpos $endpos }
| expr SLASH expr
    { mk_expr (PE_op (Op_div, [$1; $3])) $startpos $endpos }
| expr DIV expr
    { mk_expr (PE_op (Op_div, [$1; $3])) $startpos $endpos }
| expr MOD expr
    { mk_expr (PE_op (Op_mod, [$1; $3])) $startpos $endpos }
| expr COMP expr
    { mk_expr (PE_op ($2, [$1; $3])) $startpos $endpos }
| expr EQUAL expr
    { mk_expr (PE_op (Op_eq, [$1; $3])) $startpos $endpos }
| expr NEQ expr
    { mk_expr (PE_op (Op_neq, [$1; $3])) $startpos $endpos }
| expr AND expr
    { mk_expr (PE_op (Op_and, [$1; $3])) $startpos $endpos }
| expr OR expr
    { mk_expr (PE_op (Op_or, [$1; $3])) $startpos $endpos }
| expr XOR expr
    { mk_expr (PE_op (Op_xor, [$1; $3])) $startpos $endpos }
(* | expr ARROW expr
 *     { mk_expr (PE_arrow ($1, $3)) $startpos $endpos } *)
| const FBY expr
    { mk_expr (PE_fby ($1, $3)) $startpos $endpos }
| MINUS expr
    { mk_expr (PE_op (Op_sub, [$2])) $startpos $endpos }
| NOT expr
    { mk_expr (PE_op (Op_not, [$2])) $startpos $endpos }
(* | PRE expr
 *     { mk_expr (PE_pre ($2)) $startpos $endpos } *)
| LPAREN expr COMMA expr_comma_list RPAREN
    { mk_expr (PE_tuple ($2::$4)) $startpos $endpos }
| expr WHEN IDENT LPAREN IDENT RPAREN
    { mk_expr (PE_when ($1, $3, $5)) $startpos $endpos }
| MERGE IDENT branch_list
    { mk_expr (PE_merge ($2, $3)) $startpos $endpos }
;

const:
| CONST_BOOL
    { Cbool $1 }
| CONST_INT
    { Cint $1 }
| CONST_REAL
    { Creal $1 }
;

ident_comma_list:
| IDENT COMMA ident_comma_list
    { $1 :: $3 }
| IDENT { [$1] }
;

expr_comma_list_empty:
    { [] }
| expr_comma_list { $1 }
;

expr_comma_list:
| expr COMMA expr_comma_list
    { $1 :: $3 }
| expr { [$1] }
;

branch_list:
| branch { [$1] }
| branch branch_list { $1::$2 }
;

branch:
| LPAREN IDENT ARROW expr RPAREN { ($2, $4) }
;

btyp:
| BOOL   { Tbool }
| INT    { Tint }
| REAL   { Treal }
| IDENT { Tclock ($1) }
;

typ:
  | btyp { Base $1 }
  | typ WHEN IDENT LPAREN IDENT RPAREN { Clocked ($1, $3, $5) }
;

semi_opt:
    { () }
| SEMICOL
    { () }
;
