{
  open Lexing
  open Parser
  open Asttypes

  exception Lexical_error of string

  let id_or_keyword =
    let h = Hashtbl.create 17 in
    List.iter (fun (s,k) -> Hashtbl.add h s k)
      [
	"and", AND;
	"bool", BOOL;
  "div", DIV;
	"else", ELSE;
  "every", EVERY;
	"false", CONST_BOOL(false);
	"if", IF;
	"int", INT;
	"let", LET;
  "merge", MERGE;
	"mod", MOD;
	"node", NODE;
	"not", NOT;
	"or", OR;
  "pre", PRE;
	"real", REAL;
	"returns", RETURNS;
	"tel", TEL;
	"then", THEN;
	"true", CONST_BOOL(true);
	"var", VAR;
  "when", WHEN;
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
  | "=>"
      { IMPL }
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
  | _
      { raise (Lexical_error (lexeme lexbuf)) }
  | eof
      { EOF }

and comment = parse
  | "*/" { () }
  | '\n' { new_line lexbuf; comment lexbuf }
  | _    { comment lexbuf }
  | eof  { raise (Lexical_error "unterminated comment") }
