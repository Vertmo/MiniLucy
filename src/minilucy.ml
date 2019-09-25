open Lexing

let usage = "usage: " ^ Sys.argv.(0) ^ " [-parse] [-check] [-norm] [-asserts] <input_file>"

type step = Parse | Check | Norm
let asserts = ref false

let step = ref Norm

let speclist = [
  ("-parse", Arg.Unit (fun () -> step := Parse),
   ": only parse the program");
  ("-check", Arg.Unit (fun () -> step := Check),
   ": parse and check the program");
  ("-norm", Arg.Unit (fun () -> step := Norm),
   ": parse, check and normalize the program");
  ("-asserts", Arg.Unit (fun () -> asserts := true),
   ": turns on assertions")
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

  (* Parse *)
  if (step = Parse) then (
    print_endline (Minils.string_of_file file);
    exit 0
  );

  (* Check *)
  let tfile = Typechecker.check_file file in
  let cfile = Clockchecker.clock_file tfile in
  if !asserts then assert (Clockchecker.equiv_parse_clock_file tfile cfile);
  Causalitychecker.check_file cfile;
  let cfile = Scheduler.schedule_file cfile in
  if (step = Check) then (
    print_endline (CMinils.string_of_file cfile);
    exit 0
  );

  (* Normalize *)
  let nfile = Normalizer.norm_file cfile in
  if (step = Norm) then (
    print_endline (NMinils.string_of_file nfile);
    exit 0
  )

let _ = Arg.parse speclist (fun x -> main x !step) usage

