(** Parsed AST *)

open Asttypes
open Minils.KMinils

let indent level = String.make (level*2) ' '

type p_let = ident * ty * k_expr

let string_of_let level (id, ty, e) =
  Printf.sprintf "%slet %s : %s = %s in"
    (indent level) id (string_of_ty ty) (string_of_expr e)

type p_until = k_expr * constr * bool

let string_of_until level (e, c, r) =
  if r then Printf.sprintf "%suntil %s then %s and reset;" (indent level) (string_of_expr e) c
  else Printf.sprintf "%suntil %s then %s;" (indent level) (string_of_expr e) c

type p_instr =
  | Eq of k_equation
  | Automaton of (constr * p_let list * p_instr list * p_until list) list
  | Reset of (p_instr list * k_expr)

let rec string_of_instr level = function
  | Eq eq -> Printf.sprintf "%s%s;" (indent level) (string_of_equation eq)
  | Automaton branches ->
    Printf.sprintf "%sautomaton\n%s" (indent level)
      (String.concat "\n" (List.map (fun (c, lets, ins, untils) ->
           Printf.sprintf "%s| %s ->\n%s\n%s\n%s" (indent level) c
             (String.concat "\n" (List.map (string_of_let (level+1)) lets))
             (String.concat "\n" (List.map (string_of_instr (level+1)) ins))
             (String.concat "\n" (List.map (string_of_until (level+1)) untils)))
          branches))
  | Reset (ins, er) ->
    Printf.sprintf "%sreset\n%s\n%severy %s;" (indent level)
      (String.concat "\n" (List.map (string_of_instr (level + 1)) ins))
      (indent level) (string_of_expr er)

(** Variables defined by an instruction *)
let rec defined_of_instr = function
  | Eq eq -> defined_of_equation eq
  | Automaton brs ->
    (* If the program is well typed, all the branches
       define the same equations left-hand-sides *)
    let (_, _, is, _) = List.hd brs in
    List.concat (List.map defined_of_instr is)
  | Reset (is, _) ->
    List.concat (List.map defined_of_instr is)

type p_node =
    { pn_name: ident;
      pn_input: (ident * ann) list;
      pn_output: (ident * ann) list;
      pn_local: (ident * ann) list;
      pn_instrs: p_instr list;
      pn_loc: location; }

let string_of_node n =
  Printf.sprintf "node %s(%s) returns (%s);\n\
                 var %s;\n\
                 let\n\
                 %s\n\
                 tel\n"
    n.pn_name
    (string_of_ident_ann_list n.pn_input)
    (string_of_ident_ann_list n.pn_output)
    (string_of_ident_ann_list n.pn_local)
    (String.concat "\n" (List.map (string_of_instr 1) n.pn_instrs))

type p_file =
  { pf_clocks: clockdec list;
    pf_nodes: p_node list; }

let string_of_file f =
  Printf.sprintf "%s\n%s"
    (String.concat "\n" (List.map string_of_clockdec f.pf_clocks))
    (String.concat "\n" (List.map string_of_node f.pf_nodes))
