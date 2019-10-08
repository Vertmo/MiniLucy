(** Code generator for AVR targets *)

open Asttypes
open Obc
open MicroC
open Generator

type pin = PIN0 | PIN1 | PIN2 | PIN3 | PIN4 | PIN5 | PIN6 | PIN7
         | PIN8 | PIN9 | PIN10 | PIN11 | PIN12 | PIN13
         | PINA0 | PINA1 | PINA2 | PINA3 | PINA4 | PINA5

let pin_of_string = function
  | "pin0" -> PIN0
  | "pin1" -> PIN1
  | "pin2" -> PIN2
  | "pin3" -> PIN3
  | "pin4" -> PIN4
  | "pin5" -> PIN5
  | "pin6" -> PIN6
  | "pin7" -> PIN7
  | "pin8" -> PIN8
  | "pin9" -> PIN9
  | "pin10" -> PIN10
  | "pin11" -> PIN11
  | "pin12" -> PIN12
  | "pin13" -> PIN13
  | "pinA0" -> PINA0
  | "pinA1" -> PINA1
  | "pinA2" -> PINA2
  | "pinA3" -> PINA3
  | "pinA4" -> PINA4
  | "pinA5" -> PINA5
  | s -> failwith (Printf.sprintf "%s is not a valid pin id" s)

let int_of_pin = function
  | PIN0 -> 0
  | PIN1 -> 1
  | PIN2 -> 2
  | PIN3 -> 3
  | PIN4 -> 4
  | PIN5 -> 5
  | PIN6 -> 6
  | PIN7 -> 7
  | PIN8 -> 8
  | PIN9 -> 9
  | PIN10 -> 10
  | PIN11 -> 11
  | PIN12 -> 12
  | PIN13 -> 13
  | PINA0 -> 14
  | PINA1 -> 15
  | PINA2 -> 16
  | PINA3 -> 17
  | PINA4 -> 18
  | PINA5 -> 19

let string_of_pin = function
  | PIN0 -> "pin0"
  | PIN1 -> "pin1"
  | PIN2 -> "pin2"
  | PIN3 -> "pin3"
  | PIN4 -> "pin4"
  | PIN5 -> "pin5"
  | PIN6 -> "pin6"
  | PIN7 -> "pin7"
  | PIN8 -> "pin8"
  | PIN9 -> "pin9"
  | PIN10 -> "pin10"
  | PIN11 -> "pin11"
  | PIN12 -> "pin12"
  | PIN13 -> "pin13"
  | PINA0 -> "pinA0"
  | PINA1 -> "pinA1"
  | PINA2 -> "pinA2"
  | PINA3 -> "pinA3"
  | PINA4 -> "pinA4"
  | PINA5 -> "pinA5"

(** IO initialization for inputs *)
let generate_input_inits pins =
  List.map (fun p ->
      Call ("avr_pin_mode", [Const (Int (int_of_pin p));Const (Int 0)])) pins

(** IO initialization for outputs *)
let generate_output_inits pins =
  List.map (fun p ->
      Call ("avr_pin_mode", [Const (Int (int_of_pin p));Const (Int 1)])) pins

(** Check that a pin does support analog read *)
let can_analog_read pin =
  pin = PINA0 || pin = PINA1 || pin = PINA2 ||
  pin = PINA3 || pin = PINA4 || pin = PINA5

(** Check that a pin does support pwm write *)
let can_analog_write pin =
  pin = PIN3 || pin = PIN5 || pin = PIN6 ||
  pin = PIN9 || pin = PIN10 || pin = PIN11

(** Input reads *)
let generate_input_reads pins =
  List.map (fun (p, ty) ->
      match ty with
      | Tbool ->
        Assign (Ident (string_of_pin p),
                Call ("avr_digital_read", [Const (Int (int_of_pin p))]))
      | Tint ->
        if (not (can_analog_read p))
        then failwith (Printf.sprintf
                         "%s does not support analog input" (string_of_pin p));
        Assign (Ident (string_of_pin p),
                Call ("avr_analog_read", [Const (Int (int_of_pin p))]))
      | t -> failwith (Printf.sprintf "Type %s is not supported on a pin"
                         (string_of_base_ty t))) pins

(** Output writes *)
let generate_output_writes pins =
  List.map (fun (p, ty) ->
      match ty with
      | Tbool ->
        Call ("avr_digital_write", [Const (Int (int_of_pin p));
                                    Field (Ident "out", (string_of_pin p))])
      | Tint ->
        if (not (can_analog_write p))
        then failwith (Printf.sprintf
                         "%s does not support analog output" (string_of_pin p));
        Call ("avr_analog_write", [Const (Int (int_of_pin p));
                                   Field (Ident "out", (string_of_pin p))])
      | t -> failwith (Printf.sprintf "Type %s is not supported on a pin"
                      (string_of_base_ty t))) pins

(** Generate code for a whole file *)
let generate_file (f : Obc.file) : MicroC.file =
  let defs =
    (List.map generate_clockdec f.clocks)@
    (List.concat (List.map generate_machine
                    (List.filter (fun m -> m.m_name <> "main") f.machines))) in

  let main = try List.find (fun m -> m.m_name = "main") f.machines
    with _ -> failwith "A program compiled for Avr should have a 'main' node" in

  let (ins, outs, _, _) = main.m_step in
  let ins = List.map (fun (id, ty) -> pin_of_string id, ty) ins
  and outs = List.map (fun (id, ty) -> pin_of_string id, ty) outs in
  let mainDefs = generate_machine main in

  let mainFun = Fun {
      fun_name = "main";
      fun_ret = Tint;
      fun_args = [];
      fun_body = [
        (* Initialization code *)
        VarDec (Tident "main_mem", "mem"); VarDec (Tident "main_out", "out");
        Call ("main_reset", [Ref (Ident "mem")])]@
        (List.map (fun (p, ty) ->
             VarDec (ty_of_base_ty ty, string_of_pin p)) ins)@
        (generate_input_inits (List.map fst ins))@
        (generate_output_inits (List.map fst outs))@

        (* Main loop *)
        [ While (Const (Int 1),
                 (generate_input_reads ins)@
                 [Call ("main_step",
                        (List.map (fun (p, _) -> Ident (string_of_pin p)) ins)@
                        [Ref (Ident "mem"); (Ref (Ident "out"))])]@
                 (generate_output_writes outs)@
                 [Call ("avr_delay", [Const (Int 10)])])
        ]
    } in
  (Include "avrlib.c")::defs@mainDefs@[mainFun]
