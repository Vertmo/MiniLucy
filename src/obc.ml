(* Object code AST *)

open Asttypes

type expr =
  | Const of const
  | Ident of ident
  | StIdent of ident
  | Op of op * expr list

let rec string_of_expr = function
  | Const c -> string_of_const c
  | Ident id -> id
  | StIdent id -> Printf.sprintf "state(%s)" id
  | Op (op, es) -> Printf.sprintf "(%s [%s])"
                     (string_of_op op)
                     (String.concat "; " (List.map string_of_expr es))

type instr =
  | Assign of (ident * expr)
  | StAssign of (ident * expr)
  | Reset of ident
  | StepAssign of (ident list * ident * expr list)
  | Case of ident * instr list * instr list

let rec string_of_instr = function
  | Assign (id, e) ->
    Printf.sprintf "%s := %s"
      id (string_of_expr e)
  | StAssign (id, e) ->
    Printf.sprintf "state(%s) := %s"
      id (string_of_expr e)
  | Reset id ->
    Printf.sprintf "%s.reset" id
  | StepAssign (ids, fid, es) ->
    Printf.sprintf "(%s) := %s.step(%s)"
      (String.concat ", " ids) fid
      (String.concat ", " (List.map string_of_expr es))
  | Case (id, instrCl, instrNCl) ->
    Printf.sprintf "case(%s) {\nTrue -> %s\nFalse -> %s\n}"
      id (string_of_instrs instrCl) (string_of_instrs instrNCl)

and string_of_instrs instrs =
  String.concat "\n" (List.map string_of_instr instrs)

type p = (ident * base_ty) list

(** Check if the instruction assigns the state *)
let rec assign_state = function
  | Assign _ -> false
  | StAssign _ -> true
  | Reset _ -> false
  | StepAssign _ -> false
  | Case (_, i1, i2) ->
    List.exists assign_state i1 || List.exists assign_state i2

let string_of_p p =
  String.concat "; " (List.map (fun (id, t) ->
      Printf.sprintf "%s:%s" id (string_of_base_ty t)) p)

type machine = {
  m_name: ident;
  m_memory: p;
  m_instances: (ident * (ident * (ident list))) list;
  m_reset: instr list;
  (* input, output, locals, body *)
  m_step : p * p * p * instr list;
}

let string_of_machine m =
  let (input, output, vars, instrs) = m.m_step in
  Printf.sprintf "machine %s =\n\
                   memory %s\n\
                   instances %s\n\
                   reset () =\n\
                   %s\n\
                   step(%s) returns(%s) = var %s in\n\
                   %s\n\n"
    m.m_name (string_of_p m.m_memory)
    (String.concat "\n" (List.map (fun (o, (f, _)) -> o^" : "^f) m.m_instances))
    (string_of_instrs m.m_reset)
    (string_of_p input) (string_of_p output) (string_of_p vars)
    (string_of_instrs instrs)

type file = machine list

let string_of_file f =
  String.concat "\n" (List.map string_of_machine f)
