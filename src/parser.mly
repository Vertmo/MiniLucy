%{

  open Asttypes
  open PMinils.PMinils

  let mk_expr e startp endp = { kexpr_desc = e; kexpr_loc = (startp, endp); kexpr_annot = [] }
  let mk_eq p e startp endp = { keq_patt = p; keq_expr = e; keq_loc = (startp, endp) }

%}

%token AND
%token ARROW
%token AUTOMATON
%token BOOL
%token COLON
%token COMMA
%token <Asttypes.op> COMP
%token <bool> CONST_BOOL
%token <int> CONST_INT
%token <float> CONST_REAL
%token DIV
%token ELSE
%token END
%token EOF
%token EQUAL
%token EVERY
%token FBY
%token NEQ
%token REAL
%token <string> IDENT
%token IF
%token IN
%token INT
%token LET
%token LPAREN
%token MERGE
%token MINUS
%token MOD
%token NODE
%token NOT
%token OR
%token PIPE
%token PLUS
%token PRE
%token RETURNS
%token RESET
%token RPAREN
%token SEMICOL
%token SLASH
%token STAR
%token SWITCH
%token TEL
%token THEN
%token TYPE
%token UNTIL
%token VAR
%token WHEN
%token XOR


%nonassoc ELSE
%right ARROW
%left OR
%left XOR
%left AND
%left COMP EQUAL NEQ                          /* < <= > >= <> = <> */
%left PLUS MINUS                              /* + -  */
%left STAR SLASH DIV MOD                      /* * /  mod */
%nonassoc NOT (* PRE *)                             /* not pre */

/* Point d'entrée */

%start file
%type <PMinils.PMinils.p_file> file

%%

file: clock_decs node_decs EOF
  { { pf_clocks = $1; pf_nodes = $2; } }
;

clock_decs:
| /* empty */ { [] }
| clock_dec clock_decs { $1 :: $2 }
;

clock_dec:
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
  LET instr_list TEL semi_opt
    { { pn_name = $2;
	pn_input = $4;
	pn_output = $8;
	pn_local = $11;
	pn_instrs = $13;
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
  | ident_comma_list COLON annot
      { let typ = $3 in
        List.map (fun id -> (id, typ)) $1 }
;

instr_list:
| /* empty */ { [] }
| instr instr_list
    { $1 :: $2 }
;

instr:
| eq
    { Eq $1 }
| RESET instr_list EVERY expr SEMICOL
    { Reset ($2, $4) }
| AUTOMATON auto_branch_list END SEMICOL
    { Automaton $2 }
;

auto_branch_list:
| auto_branch { [$1] }
| auto_branch auto_branch_list { $1::$2 }
;

auto_branch:
| PIPE IDENT ARROW let_list instr_list until_list { ($2, $4, $5, $6) }
;

let_list:
| /* empty */ { [] }
| LET IDENT COLON typ EQUAL expr IN let_list
  { ($2, $4, $6)::$8 }
;

until_list:
| /* empty */ { [] }
| UNTIL expr THEN IDENT SEMICOL until_list { ($2, $4, false)::$6 }
| UNTIL expr THEN IDENT AND RESET SEMICOL until_list { ($2, $4, true)::$8 }
;

eq:
| pattern EQUAL expr_list SEMICOL
    { mk_eq $1 $3 $startpos $endpos }
;

pattern:
| IDENT
    { [$1] }
| LPAREN ident_comma_list RPAREN
    { $2 }
;

expr:
| LPAREN expr RPAREN
    { $2 }
| const
    { mk_expr (KE_const $1) $startpos $endpos }
| IDENT
    { mk_expr (KE_ident $1) $startpos $endpos }
| IDENT LPAREN expr_comma_list_empty RPAREN
    { mk_expr (KE_app ($1, $3, mk_expr (KE_const (Cbool false)) $startpos $endpos))
      $startpos $endpos }
| IDENT LPAREN expr_comma_list_empty RPAREN EVERY expr
    { mk_expr (KE_app ($1, $3, $6)) $startpos $endpos }
| expr PLUS expr
    { mk_expr (KE_binop (Op_add, $1, $3)) $startpos $endpos }
| expr MINUS expr
    { mk_expr (KE_binop (Op_sub, $1, $3)) $startpos $endpos }
| expr STAR expr
    { mk_expr (KE_binop (Op_mul, $1, $3)) $startpos $endpos }
| expr SLASH expr
    { mk_expr (KE_binop (Op_div, $1, $3)) $startpos $endpos }
| expr DIV expr
    { mk_expr (KE_binop (Op_div, $1, $3)) $startpos $endpos }
| expr MOD expr
    { mk_expr (KE_binop (Op_mod, $1, $3)) $startpos $endpos }
| expr COMP expr
    { mk_expr (KE_binop ($2, $1, $3)) $startpos $endpos }
| expr EQUAL expr
    { mk_expr (KE_binop (Op_eq, $1, $3)) $startpos $endpos }
| expr NEQ expr
    { mk_expr (KE_binop (Op_neq, $1, $3)) $startpos $endpos }
| expr AND expr
    { mk_expr (KE_binop (Op_and, $1, $3)) $startpos $endpos }
| expr OR expr
    { mk_expr (KE_binop (Op_or, $1, $3)) $startpos $endpos }
| expr XOR expr
    { mk_expr (KE_binop (Op_xor, $1, $3)) $startpos $endpos }
| MINUS expr
    { mk_expr (KE_unop (Op_sub, $2)) $startpos $endpos }
| NOT expr
    { mk_expr (KE_unop (Op_not, $2)) $startpos $endpos }
| expr_list ARROW expr_list
    { mk_expr (KE_arrow ($1, $3)) $startpos $endpos }
| expr_list FBY expr_list
    { mk_expr (KE_fby ($1, $3)) $startpos $endpos }
(* | PRE expr
 *     { mk_expr (KE_pre ($2)) $startpos $endpos } *)
(* | LPAREN expr COMMA expr_comma_list RPAREN
 *     { mk_expr (KE_tuple ($2::$4)) $startpos $endpos } *)
| expr_list WHEN IDENT LPAREN IDENT RPAREN
    { mk_expr (KE_when ($1, $3, $5)) $startpos $endpos }
| MERGE IDENT branch_list
    { mk_expr (KE_merge ($2, $3)) $startpos $endpos }
| SWITCH expr branch_list
    { mk_expr (KE_switch ($2, $3)) $startpos $endpos }
| IF expr THEN expr ELSE expr
    { mk_expr (KE_switch ($2, [("True", [$4]); ("False", [$6])])) $startpos $endpos }
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

expr_list:
| LPAREN expr_comma_list RPAREN { $2 }
| expr { [$1] }

branch_list:
| branch { [$1] }
| branch branch_list { $1::$2 }
;

branch:
| LPAREN IDENT ARROW expr_list RPAREN { ($2, $4) }
;

typ:
| BOOL   { Tbool }
| INT    { Tint }
| REAL   { Treal }
| IDENT  { Tclock ($1) }
;

clock:
| IDENT LPAREN IDENT RPAREN { Con ($1, $3, Cbase) }
| clock WHEN IDENT LPAREN IDENT RPAREN { Con ($3, $5, $1) }
;


annot:
| typ { ($1, Cbase) }
| typ WHEN clock { ($1, $3) }
;

semi_opt:
    { () }
| SEMICOL
    { () }
;
