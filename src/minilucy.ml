open Common
open Lexing
open PMinils.PMinils

let usage = "usage: " ^ Sys.argv.(0) ^
            " [-parse] [-desugar] [-check] [-norm] [-translate] [-generate]\
             [-asserts] [-avr] [-o <output_file>]\
             [-interpret <name> <k>]\
             <input_file>"
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
   ": stop after parsing and print the program");
  ("-check", Arg.Unit (fun () -> step := Check),
   ": stop after type and clock checks and print the program");
  ("-last", Arg.Unit (fun () -> step := Last),
   ": stop after last removal and print the program");
  ("-automaton", Arg.Unit (fun () -> step := Automaton),
   ": stop after automaton removal and print the program");
  ("-reset", Arg.Unit (fun () -> step := Reset),
   ": stop after reset removal and print the program");
  ("-switch", Arg.Unit (fun () -> step := Switch),
   ": stop after switch removal and print the program");
  ("-block", Arg.Unit (fun () -> step := Block),
   ": stop after block removal and print the program");
  ("-norm", Arg.Unit (fun () -> step := Norm),
   ": print the normalized program");
  ("-sched", Arg.Unit (fun () -> step := Sched),
  ": stop after scheduling and print the program");
  ("-translate", Arg.Unit (fun () -> step := Translate),
   ": stop after Obc translation and print the program");
  ("-generate", Arg.Unit (fun () -> step := Generate),
   ": generate C code and print it");
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

let compile step filenames =
  (* Parse *)
  let pfile = List.fold_left (fun f filename ->
      let ic = open_in filename in
      let f' = lex_and_parse ic in
      close_in ic;
      { pf_clocks = f.pf_clocks@f'.pf_clocks;
        pf_nodes = f.pf_nodes@f'.pf_nodes })
      { pf_clocks = []; pf_nodes = [] } filenames in

  if (step = Parse) then (
    print_file Format.std_formatter pfile;
    exit 0
  );

  (* Type and clock check *)
  let tfile = Typechecker.type_file pfile in
  let cfile = Clockchecker.elab_file tfile in

  if (step = Check) then (
    Clockchecker.CPMinils.print_file Format.std_formatter cfile;
    exit 0
  );

  (* Let's interpr this a bit ! *)
  match (!interpret_name) with
  | Some name ->
    (* Interpr.run_file file; *)
    Pinterpr.run_node cfile name !interpret_k;
    exit 0;
  | None -> ();

  (* Kernelize *)
    let file =
      try
        Kernelizer.kernelize_file step cfile
      with Done -> exit 0 in

  (* Run the nodes from both files, checking they give the same result *)
  if !asserts then Pinterpr.compare_files cfile file;

  (* Normalize *)
  let nfile = Normalizer.norm_file file in

  if (step = Norm) then (
    NMinils.print_file Format.std_formatter nfile;
    exit 0
  );

  Causalitychecker.check_file nfile;
  let nfile = Scheduler.schedule_file nfile in
  if !asserts then assert (Scheduler.schedule_is_correct_file nfile);

  if (step = Sched) then (
    NMinils.print_file Format.std_formatter nfile;
    exit 0
  );

  (* Translate *)
  let mfile = Translator.translate_file nfile in

  (* We can check the translation against the original node *)
  if !asserts then Obcinterpr.compare_files cfile mfile;

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
      let filename = Filename.basename prefix
      and filedir = Filename.dirname prefix in
      let ccode = AvrGenerator.generate_file filename mfile in
      let cfile = prefix^".c" in
      let avrfile = prefix^".avr" in

      let outc = open_out cfile in
      output_string outc (MicroC.string_of_file ccode);
      close_out outc;

      let libdir = Config.libdir in
      ignore (Sys.command
                (Printf.sprintf
                   "avr-gcc -g -fno-exceptions \
                    -O2 -Wnarrowing\ -Wl,-Os -fdata-sections \
                    -ffunction-sections -Wl,-gc-sections \
                    -mmcu=atmega328p -DF_CPU=16000000 \
                    -I %s %s/avrlib.o %s/liquidCrystal.o -I %s %s -o %s"
                   libdir libdir libdir filedir cfile avrfile));
      ignore (Sys.command
                (Printf.sprintf
                   "avr-objcopy -O ihex -R .eeprom %s %s"
                   avrfile hexfile))
  )

(** Compile the program while catching exceptions *)
let compile_and_catch step filenames =
  try compile step filenames with
  | Typechecker.UnexpectedEquationError (id, loc) ->
    Printf.eprintf "Type checking error : UnexpectedEquation for %s at %s\n"
      id (string_of_loc loc); exit 1
  | Typechecker.TypeError (msg, loc) ->
    Printf.eprintf "Type checking error : %s at %s\n"
      msg (string_of_loc loc); exit 1
  | Clockchecker.ClockError (msg, loc) ->
    Printf.eprintf "Clock checking error : %s at %s\n"
      msg (string_of_loc loc); exit 1
  | Causalitychecker.CausalityError (msg, nodeid, loc) ->
    Printf.printf "Causality error : %s in node %s at %s\n"
      msg nodeid (string_of_loc loc); exit 1

let _ =
  Arg.parse_expand speclist (fun x -> filenames := !filenames@[x]) usage;
  let step = !step and filenames = !filenames in

  compile_and_catch step filenames
