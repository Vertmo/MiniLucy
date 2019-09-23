open Lexing

let usage = "usage: " ^ Sys.argv.(0) ^ " [-parse] [-check] <input_file>"

type step = Parse | Check

let step = ref Check

let speclist = [
  ("-parse", Arg.Unit (fun () -> step := Parse), ": only parse the program");
  ("-check", Arg.Unit (fun () -> step := Check), ": parse and check the program");
]

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.file Lexer.token lexbuf with
  | Parser.Error ->
    Printf.fprintf stderr "Syntax error in program at %a\n" print_position lexbuf;
    exit (-1)

let lex_and_parse ic =
  let lexbuf = Lexing.from_channel ic in
  parse_with_error lexbuf

let main filename step =
  let ic = open_in filename in
  let file = lex_and_parse ic in
  if (step = Parse) then (
    print_endline (Minils.string_of_file file);
    exit 0
  );
  Typechecker.check_file file;
  let cfile = Clockchecker.clock_file file in
  if (step = Check) then (
    print_endline (CMinils.string_of_file cfile);
    exit 0
  )

let _ = Arg.parse speclist (fun x -> main x !step) usage

