open Lexing

let usage = "usage: " ^ Sys.argv.(0) ^
            " [-parse] [-check] [-norm] [-translate] [-generate] [-asserts]\
             [-o <output_file]\
             <input_file>"

type step = Parse | Check | Norm | Translate | Generate
let asserts = ref false

let step = ref Generate
let output = ref None

let speclist = [
  ("-o", Arg.String (fun s -> output := Some s),
  ": set output file for c code");
  ("-parse", Arg.Unit (fun () -> step := Parse),
   ": parse and print the program");
  ("-check", Arg.Unit (fun () -> step := Check),
   ":check the program, and print it with annotated clocks");
  ("-norm", Arg.Unit (fun () -> step := Norm),
   ": print the normalized program");
  ("-translate", Arg.Unit (fun () -> step := Translate),
   ": print the program translated to the Obc language");
  ("-generate", Arg.Unit (fun () -> step := Generate),
   ": print the generated C code");
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
  if (step = Check) then (
    print_endline (CMinils.string_of_file cfile);
    exit 0
  );

  (* Normalize *)
  let nfile = Normalizer.norm_file cfile in
  let nfile = Scheduler.schedule_file nfile in
  if (step = Norm) then (
    print_endline (NMinils.string_of_file nfile);
    exit 0
  );

  (* Translate *)
  let mfile = Translator.translate_file nfile in
  if (step = Translate) then (
    print_endline (Obc.string_of_file mfile);
    exit 0
  );

  (* Generate *)
  let ccode = Generator.generate_file mfile in
  match !output with
  | None -> print_endline (MicroC.string_of_file ccode);
  | Some s ->
    let outc = open_out s in
    output_string outc (MicroC.string_of_file ccode);
    close_out outc

let _ = Arg.parse speclist (fun x -> main x !step) usage
