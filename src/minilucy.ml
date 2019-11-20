open Lexing
open PMinils

let usage = "usage: " ^ Sys.argv.(0) ^
            " [-parse] [-desugar] [-check] [-norm] [-translate] [-generate]\
             [-asserts] [-avr] [-o <output_file>]\
             [-interpret <name> <k>]\
             <input_file>"

type step = Parse | Desugar | Check | Norm | Translate | Generate
let asserts = ref false
let targetAvr = ref false

let step = ref Generate
let output = ref None
let interpret_name = ref None
let interpret_k = ref 0

let speclist = [
  ("-o", Arg.String (fun s -> output := Some s),
  ": set output file for c code");
  ("-parse", Arg.Unit (fun () -> step := Parse),
   ": parse and print the program");
  ("-desugar", Arg.Unit (fun () -> step := Desugar),
   ": parse, desugar and print the program");
  ("-check", Arg.Unit (fun () -> step := Check),
   ":check the program, and print it with annotated clocks");
  ("-norm", Arg.Unit (fun () -> step := Norm),
   ": print the normalized program");
  ("-translate", Arg.Unit (fun () -> step := Translate),
   ": print the program translated to the Obc language");
  ("-generate", Arg.Unit (fun () -> step := Generate),
   ": print the generated C code");
  ("-avr", Arg.Unit (fun () -> targetAvr := true),
   ": generate avr-compatible C and compile it");
  ("-asserts", Arg.Unit (fun () -> asserts := true),
   ": turns on assertions");
  ("-interpret",
   Arg.Tuple [Arg.String (fun s -> interpret_name := Some s);
              Arg.Int (fun k -> interpret_k := k)],
   ": run <k> step for the node <name>, with random inputs")
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

let filenames = ref []

let _ =
  Arg.parse_expand speclist (fun x -> filenames := !filenames@[x]) usage;
  let step = !step and filenames = !filenames in

  let p_file = List.fold_left (fun f filename ->
      let ic = open_in filename in
      let f' = lex_and_parse ic in
      close_in ic;
      { pf_clocks = f.pf_clocks@f'.pf_clocks;
        pf_nodes = f.pf_nodes@f'.pf_nodes })
      { pf_clocks = []; pf_nodes = [] } filenames in

  (* Parse *)
  if (step = Parse) then (
    print_endline (PMinils.string_of_file p_file);
    exit 0
  );

  (* Desugar *)
  let file = Desugarizer.desugar_file p_file in

  (* Run the nodes from both files, checking they give the same result *)
  if !asserts then Pinterpr.run_files p_file file;

  if (step = Desugar) then (
    print_endline (Minils.string_of_file file);
    exit 0
  );

  (* Let's interpr this a bit ! *)
  match (!interpret_name) with
  | Some name ->
    (* Interpr.run_file file; *)
    Interpr.run_node file name !interpret_k;
    exit 0; (* TEMP *)
  | None -> ();

  (* Check *)
  let tfile = Typechecker.check_file file in
  if !asserts then assert (Typechecker.equiv_typed_file file tfile);
  let cfile = Clockchecker.clock_file tfile in
  if !asserts then assert (Clockchecker.equiv_clock_file tfile cfile);
  Causalitychecker.check_file cfile;
  if (step = Check) then (
    print_endline (CMinils.string_of_file cfile);
    exit 0
  );

  (* Normalize *)
  let nfile = Normalizer.norm_file cfile in
  if !asserts then assert (Normalizer.equiv_norm_file cfile nfile);
  let nfile = Scheduler.schedule_file nfile in
  if !asserts then assert (Scheduler.schedule_is_correct_file nfile);
  if (step = Norm) then (
    print_endline (NMinils.string_of_file nfile);
    exit 0
  );

  (* Translate *)
  let mfile = Translator.translate_file nfile in
  if !asserts then assert (Translator.equiv_translate_file nfile mfile);
  if (step = Translate) then (
    print_endline (Obc.string_of_file mfile);
    exit 0
  );

  if(not !targetAvr) then (
    (* Generate for GCC *)
    let ccode = Generator.generate_file mfile in
    match !output with
    | None -> print_endline (MicroC.string_of_file ccode);
    | Some s ->
      let outc = open_out s in
      output_string outc (MicroC.string_of_file ccode);
      close_out outc
  ) else (
    (* Generate for AVR *)
    match !output with
    | None ->
      Printf.eprintf "Generating for AVR should always specify an output file";
      exit 1
    | Some hexfile ->
      let prefix = Filename.remove_extension hexfile in
      let ccode = AvrGenerator.generate_file prefix mfile in
      let cfile = prefix^".c" in
      let avrfile = prefix^".avr" in

      let outc = open_out cfile in
      output_string outc (MicroC.string_of_file ccode);
      close_out outc;

      let libdir = "../src/" (* TODO*) in
      ignore (Sys.command
                (Printf.sprintf
                   "avr-g++ -g -fno-exceptions -Wall -std=c++11 \
                    -O2 -Wnarrowing\ -Wl,-Os -fdata-sections \
                    -ffunction-sections -Wl,-gc-sections \
                    -mmcu=atmega328p -DF_CPU=16000000 \
                    -I %s %s -o %s" libdir cfile avrfile));
      ignore (Sys.command
                (Printf.sprintf
                   "avr-objcopy -O ihex -R .eeprom %s %s"
                   avrfile hexfile))
  )

