open Lexing
open PMinils.PMinils

let usage = "usage: " ^ Sys.argv.(0) ^
            " [-parse] [-desugar] [-check] [-norm] [-translate] [-generate]\
             [-asserts] [-avr] [-o <output_file>]\
             [-interpret <name> <k>]\
             <input_file>"

type step = Parse | Kernelize | Check | Norm | Sched | Translate | Generate
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
  ("-kernelize", Arg.Unit (fun () -> step := Kernelize),
   ": parse, kernelize and print the program");
  ("-check", Arg.Unit (fun () -> step := Check),
   ":check the program, and print it with annotated clocks");
  ("-norm", Arg.Unit (fun () -> step := Norm),
   ": print the normalized program");
  ("-sched", Arg.Unit (fun () -> step := Sched),
  ": print the scheduled program");
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

  let pfile = List.fold_left (fun f filename ->
      let ic = open_in filename in
      let f' = lex_and_parse ic in
      close_in ic;
      { pf_clocks = f.pf_clocks@f'.pf_clocks;
        pf_nodes = f.pf_nodes@f'.pf_nodes })
      { pf_clocks = []; pf_nodes = [] } filenames in

  (* Parse *)
  if (step = Parse) then (
    print_endline (string_of_file pfile);
    exit 0
  );

  (* Type and clock check *)
  let tfile = Typechecker.type_file pfile in
  let cfile = Clockchecker.elab_file tfile in

  if (step = Check) then (
    print_endline (Clockchecker.CPMinils.string_of_file cfile);
    exit 0
  );

  (* Kernelize *)
  let file = Kernelizer.kernelize_file cfile in

  (* Run the nodes from both files, checking they give the same result *)
  (* if !asserts then Pinterpr.run_files p_file file; *)

  if (step = Kernelize) then (
    print_endline (Kernelizer.CMinils.string_of_file file);
    exit 0
  );

  (* Let's interpr this a bit ! *)
  match (!interpret_name) with
  | Some name ->
    (* Interpr.run_file file; *)
    Interpr.run_node file name !interpret_k;
    exit 0;
  | None -> ();

  (* Normalize *)
  let nfile = Normalizer.norm_file file in

  if (step = Norm) then (
    print_endline (NMinils.string_of_file nfile);
    exit 0
  );

  Causalitychecker.check_file nfile;
  let nfile = Scheduler.schedule_file nfile in
  if !asserts then assert (Scheduler.schedule_is_correct_file nfile);

  if (step = Sched) then (
    print_endline (NMinils.string_of_file nfile);
    exit 0
  );

  (* Translate *)
  let mfile = Translator.translate_file nfile in
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

