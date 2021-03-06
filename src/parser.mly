%{

  open Common
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
%token <Common.op> COMP
%token TRUE FALSE
%token <int> CONST_INT
%token <float> CONST_REAL
%token DIV
%token DO
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
%token LAST
%token LET
%token LPAREN
%token MATCH
%token MERGE
%token MINUS
%token MOD
%token NODE
%token NOT
%token ON
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
%token STATE
%token SWITCH
%token TEL
%token THEN CONTINUE
%token TYPE
%token UNTIL UNLESS
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

/* Point d'entr�e */

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
| TYPE IDENT EQUAL constr_list SEMICOL?
  { ($2, $4) }
;

constr_list:
| IDENT
  { [$1] }
| IDENT PLUS constr_list
{ $1 :: $3 }
(* Heptagon syntax *)
| IDENT PIPE constr_list
{ $1 :: $3 }
;

node_decs:
| /* empty */       { [] }
| node node_decs    { $1 :: $2 }
;


node:
| NODE IDENT LPAREN param_list? RPAREN SEMICOL?
  RETURNS LPAREN param_list RPAREN SEMICOL?
  block
  { { pn_name = $2;
	    pn_input = (match $4 with Some l -> l | None -> []);
	    pn_output = $9;
	    pn_body = $12;
	    pn_loc = ($startpos, $endpos) } }
;

block:
| local_params LET instr+ TEL SEMICOL?
  { { pb_local = $1; pb_instrs = $3; pb_loc = ($startpos, $endpos) } }
;

param_list:
| param
    { $1 }
| param SEMICOL param_list
    { $1 @ $3 }
;

param:
| ident_comma_list COLON annot
    { let typ = $3 in
      List.map (fun id -> (id, typ)) $1 }
;

local_params:
| /* empty */
    { [] }
| VAR local_param_list
    { $2 }
;

local_param_list:
| local_param SEMICOL
    { $1 }
| local_param SEMICOL local_param_list
    { $1 @ $3 }
;

local_param:
| param
    { List.map (fun (a, b) -> (a, b, None)) $1 }
| LAST IDENT COLON annot EQUAL const
    { [($2, $4, Some $6)] }
;

instr:
| eq
    { mk_instr (Eq $1) $startpos $endpos }
| RESET instr+ EVERY expr SEMICOL?
    { mk_instr (Reset ($2, $4)) $startpos $endpos }
| AUTOMATON auto_branch+ END SEMICOL?
    { mk_instr (Automaton ($2, (None, None, []))) $startpos $endpos }
| SWITCH expr instr_branch+ END SEMICOL?
    { mk_instr (Switch ($2, $3, (None, []))) $startpos $endpos }
| block
    { mk_instr (Block $1) $startpos $endpos }
;

auto_branch:
| PIPE IDENT ARROW unless* instr+ until* { ($2, $4, $5, $6) }
(* Heptagon syntax *)
| STATE IDENT DO instr+ unless* until* { ($2, $5, $4, $6) }
;

instr_branch:
| PIPE IDENT ARROW instr+ { ($2, $4) }
(* Heptagon syntax *)
| PIPE IDENT DO instr+ { ($2, $4) }
;

until:
| UNTIL expr THEN IDENT SEMICOL? { ($2, $4, true) }
| UNTIL expr CONTINUE IDENT SEMICOL? { ($2, $4, false) }
;

unless:
| UNLESS expr THEN IDENT SEMICOL? { ($2, $4, true) }
| UNLESS expr CONTINUE IDENT SEMICOL? { ($2, $4, false) }
;


eq:
| pattern EQUAL expr_list SEMICOL?
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
    { mk_expr (KE_arrow ($1, $3, mk_expr (KE_const (Cbool false)) $startpos $endpos))
      $startpos $endpos }
| expr_list FBY expr_list
    { mk_expr (KE_fby ($1, $3, mk_expr (KE_const (Cbool false)) $startpos $endpos))
      $startpos $endpos }
(* | PRE expr
 *     { mk_expr (KE_pre ($2)) $startpos $endpos } *)
| expr_list WHEN constr_ckid
    { let (constr, ckid) = $3 in
      mk_expr (KE_when ($1, constr, ckid)) $startpos $endpos }
| MERGE IDENT branch+
    { mk_expr (KE_merge ($2, $3)) $startpos $endpos }
| MERGE IDENT expr expr
    { mk_expr (KE_merge ($2, [("True", [$3]); ("False", [$4])])) $startpos $endpos }
| MATCH expr WITH branch+
    { mk_expr (KE_match ($2, $4)) $startpos $endpos }
| IF expr THEN expr_list ELSE expr_list
    { mk_expr (KE_match ($2, [("True", $4); ("False", $6)])) $startpos $endpos }
| LAST IDENT
    { mk_expr (KE_last $2) $startpos $endpos }
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

(* clock:
 * | constr_ckid { let (constr, ckid) = $1 in Con (constr, ckid, Cbase) }
 * | clock ON constr_ckid { let (constr, ckid) = $3 in Con (constr, ckid, $1) }
 * ; *)

annot:
| typ { ($1, Cbase) }
| typ WHEN constr_ckid
    { let (constr, ckid) = $3 in ($1, Con (constr, ckid, Cbase)) }
;
