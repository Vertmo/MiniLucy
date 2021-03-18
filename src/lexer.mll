{
  open Lexing
  open Parser
  open Common

  exception Lexical_error of string

  let id_or_keyword =
    let h = Hashtbl.create 17 in
    List.iter (fun (s,k) -> Hashtbl.add h s k)
      [
	"and", AND;
  "automaton", AUTOMATON;
	"bool", BOOL;
  "continue", CONTINUE;
  "div", DIV;
  "do", DO;
  "end", END;
	"else", ELSE;
  "every", EVERY;
  "fby", FBY;
	"false", FALSE;
	"if", IF;
  "in", IN;
	"int", INT;
  "last", LAST;
	"let", LET;
  "match", MATCH;
  "merge", MERGE;
	"mod", MOD;
	"node", NODE;
	"not", NOT;
  "on", ON;
	"or", OR;
  "pre", PRE;
	"real", REAL;
	"returns", RETURNS;
  "reset", RESET;
  "switch", SWITCH;
  "state", STATE;
	"tel", TEL;
	"then", THEN;
  "type", TYPE;
	"true", TRUE;
  "unless", UNLESS;
  "until", UNTIL;
	"var", VAR;
  "when", WHEN;
  "with", WITH;
  "xor", XOR;
      ];
    fun s ->
      try Hashtbl.find h s with Not_found -> IDENT s
}

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let exponent = ('e' | 'E') ('+' | '-')? digit+
let float = digit+ '.' digit* exponent?
          | digit* '.'digit+ exponent?
	  | digit+ exponent
let ident = alpha (alpha | '_' | digit)*

rule token = parse
  | '\n'
      { new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r']+
      { token lexbuf }
  | "--" [^ '\n']* ['\n']
      { new_line lexbuf; token lexbuf }
  | "/*"
      { comment lexbuf; token lexbuf }
  | "(*"
      { comment lexbuf; token lexbuf }
  | ident
      { id_or_keyword (lexeme lexbuf) }
  | digit+
      { CONST_INT (int_of_string (lexeme lexbuf)) }
  | float
      { CONST_REAL (float_of_string (lexeme lexbuf)) }
  | "-"
      { MINUS }
  | "+"
      { PLUS }
  | "*"
      { STAR }
  | "/"
      { SLASH }
  | ">"
      { COMP Op_gt }
  | ">="
      { COMP Op_ge }
  | "<"
      { COMP Op_lt }
  | "<="
      { COMP Op_le }
  | "<>"
      { NEQ }
  | "->"
      { ARROW }
  | "("
      { LPAREN }
  | ")"
      { RPAREN }
  | ":"
      { COLON }
  | ";"
      { SEMICOL }
  | "="
      { EQUAL }
  | ","
      { COMMA }
  | "|"
      { PIPE }
  | _
      { raise (Lexical_error (lexeme lexbuf)) }
  | eof
      { EOF }

and comment = parse
  | "*/" { () }
  | "*)" { () }
  | '\n' { new_line lexbuf; comment lexbuf }
  | _    { comment lexbuf }
  | eof  { raise (Lexical_error "unterminated comment") }
