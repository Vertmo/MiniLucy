%{

  open Asttypes
  open PMinils.PMinils

  let mk_expr e startp endp = { kexpr_desc = e; kexpr_loc = (startp, endp); kexpr_annot = [] }
  let mk_eq p e startp endp = { keq_patt = p; keq_expr = e; keq_loc = (startp, endp) }
  let mk_instr e startp endp = { pinstr_desc = e; pinstr_loc = (startp, endp) }

%}

%token AND
%token ARROW
%token AUTOMATON
%token BOOL
%token COLON
%token COMMA
%token <Asttypes.op> COMP
%token TRUE FALSE
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
%token MATCH
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
%token WITH
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
| NODE IDENT LPAREN in_params RPAREN SEMICOL?
  RETURNS LPAREN out_params RPAREN SEMICOL?
  local_params
  LET instr+ TEL SEMICOL?
    { { pn_name = $2;
	pn_input = $4;
	pn_output = $9;
	pn_local = $12;
	pn_instrs = $14;
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
| VAR param_list_semicol SEMICOL?
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

instr:
| eq
    { mk_instr (Eq $1) $startpos $endpos }
| RESET instr+ EVERY expr SEMICOL
    { mk_instr (Reset ($2, $4)) $startpos $endpos }
| AUTOMATON auto_branch+ END SEMICOL
    { mk_instr (Automaton $2) $startpos $endpos }
| SWITCH expr instr_branch+ END SEMICOL
    { mk_instr (Switch ($2, $3)) $startpos $endpos }
| LET LPAREN IDENT COLON annot RPAREN EQUAL expr IN instr+ END SEMICOL
    { mk_instr (Let ($3, $5, $8, $10)) $startpos $endpos }
;

auto_branch:
| PIPE IDENT ARROW instr+ until_list { ($2, $4, $5) }
;

instr_branch:
| PIPE IDENT ARROW instr+ { ($2, $4) }
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
| LPAREN? ident_comma_list RPAREN?
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
| expr_list WHEN constr_ckid
    { let (constr, ckid) = $3 in
      mk_expr (KE_when ($1, constr, ckid)) $startpos $endpos }
| MERGE IDENT branch+
    { mk_expr (KE_merge ($2, $3)) $startpos $endpos }
| MATCH expr WITH branch+
    { mk_expr (KE_match ($2, $4)) $startpos $endpos }
| IF expr THEN expr_list ELSE expr_list
    { mk_expr (KE_match ($2, [("True", $4); ("False", $6)])) $startpos $endpos }
;

const:
| TRUE { Cbool true }
| FALSE { Cbool false }
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

branch:
| LPAREN IDENT ARROW expr_list RPAREN { ($2, $4) }
| LPAREN TRUE ARROW expr_list RPAREN { ("True", $4) }
| LPAREN FALSE ARROW expr_list RPAREN { ("False", $4) }
;

typ:
| BOOL   { Tbool }
| INT    { Tint }
| REAL   { Treal }
| IDENT  { Tclock ($1) }
;

constr_ckid:
| IDENT LPAREN IDENT RPAREN { ($1, $3) }
| IDENT { ("True", $1) }
| NOT IDENT { ("False", $2) }
;

clock:
| constr_ckid { let (constr, ckid) = $1 in Con (constr, ckid, Cbase) }
| clock WHEN constr_ckid { let (constr, ckid) = $3 in Con (constr, ckid, $1) }
;


annot:
| typ { ($1, Cbase) }
| typ WHEN clock { ($1, $3) }
;
