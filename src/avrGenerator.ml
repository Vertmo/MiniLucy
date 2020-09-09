(** Code generator for AVR targets *)

open Asttypes
open Obc
open MicroC
open Generator

(** Input reads *)
let generate_input_reads pins =
  List.map (fun (p, _) ->
        Assign (Ident p,
                Call ("io_read_"^p, []))) pins

(** Output writes *)
let generate_output_writes pins =
  List.map (fun (p, _) ->
      Call ("io_write_"^p, [Field (Ident "out", p)])) pins

(** Generate code for a whole file *)
let generate_file filename (f : Obc.file) : MicroC.file =
  let defs =
    (List.map generate_clockdec f.clocks)@
    (List.concat (List.map generate_machine
                    (List.filter (fun m -> m.m_name <> "main") f.machines))) in

  let main = try List.find (fun m -> m.m_name = "main") f.machines
    with _ -> failwith "A program compiled for Avr should have a 'main' node" in

  let (ins, outs, _, _) = main.m_step in
  let mainDefs = generate_machine main in

  let mainFun = Fun {
      fun_name = "main";
      fun_ret = Tint;
      fun_args = [];
      fun_body = [
        (* Initialization code *)
        Call ("io_init", []);
        VarDec (Tident "main_mem", "mem"); VarDec (Tident "main_out", "out");
        Call ("main_reset", [Ref (Ident "mem")])]@
        (List.map (fun (p, ty) ->
             VarDec (ty_of_ty ty, p)) ins)@

        (* Main loop *)
        [ While (Const (Int 1),
                 (generate_input_reads ins)@
                 [Call ("main_step",
                        (List.map (fun (p, _) -> Ident p) ins)@
                        [Ref (Ident "mem"); (Ref (Ident "out"))])]@
                 (generate_output_writes outs)@
                 [Call ("avr_delay", [Ident "CLOCK_PERIOD"])])
        ]
    } in
  (Include "avrlib.h")::(Include (filename^"_io.c"))::defs@mainDefs@[mainFun]
