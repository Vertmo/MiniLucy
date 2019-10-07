(** Code generator for AVR targets *)

open Asttypes
open Obc
open MicroC
open Generator

(** Generate code for a whole file *)
let generate_file (f : Obc.file) : MicroC.file =
  let defs =
    (List.map generate_clockdec f.clocks)@
    (List.concat (List.map generate_machine
                    (List.filter (fun m -> m.m_name <> "main") f.machines))) in
  (* TODO generate main machine *)
  defs
