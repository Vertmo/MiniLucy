(* Object code AST *)

open Common

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
  | Case of expr * ty * (constr * instr list) list

let rec string_of_instr level ins =
  let indent = String.make (level*2) ' ' in
  match ins with
  | Assign (id, e) ->
    Printf.sprintf "%s%s := %s;"
      indent id (string_of_expr e)
  | StAssign (id, e) ->
    Printf.sprintf "%sstate(%s) := %s;"
      indent id (string_of_expr e)
  | Reset id ->
    Printf.sprintf "%s%s.reset;" indent id
  | StepAssign (ids, fid, es) ->
    Printf.sprintf "%s(%s) := %s.step(%s);"
      indent
      (String.concat ", " ids) fid
      (String.concat ", " (List.map string_of_expr es))
  | Case (e, _, instrs) ->
    Printf.sprintf "%scase(%s) {\n%s\n%s}\n"
      indent (string_of_expr e)
      (String.concat "\n" (List.map (fun (c, ins) ->
           Printf.sprintf "%s%s:\n%s" indent c (string_of_instrs (level+1) ins)) instrs))
      indent

and string_of_instrs level instrs =
  String.concat "\n" (List.map (string_of_instr level) instrs)

type p = (ident * ty) list

(** Check if the instruction assigns the state *)
let rec updates_state = function
  | Assign _ -> false
  | StAssign (_, Const _) -> false
  | StAssign _ -> true
  | Reset _ -> false
  | StepAssign _ -> false
  | Case (_, _, instrs) ->
    List.exists (fun (_, ins) -> List.exists updates_state ins) instrs

let string_of_p p =
  String.concat "; " (List.map (fun (id, t) ->
      Printf.sprintf "%s:%s" id (string_of_ty t)) p)

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
                  step(%s) returns(%s) =\nvar %s in\n\
                  %s\n\n"
    m.m_name (string_of_p m.m_memory)
    (String.concat "\n" (List.map (fun (o, (f, _)) -> o^" : "^f) m.m_instances))
    (string_of_instrs 1 m.m_reset)
    (string_of_p input) (string_of_p output) (string_of_p vars)
    (string_of_instrs 1 instrs)

type file =
  { clocks : clockdec list;
    machines : machine list }

let string_of_file f =
  Printf.sprintf "%s\n%s"
    (String.concat "\n" (List.map string_of_clockdec f.clocks))
    (String.concat "\n" (List.map string_of_machine f.machines))
