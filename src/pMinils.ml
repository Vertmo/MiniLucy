(** Parsed AST *)

open Asttypes
open Minils

module PMINILS(A : Annotations) = struct
  include MINILS(A)

  let indent level = String.make (level*2) ' '

  type p_let = ident * ty * k_expr

  let string_of_let ?(print_anns=false) level (id, ty, e) =
    Printf.sprintf "%slet %s : %s = %s in"
      (indent level) id (string_of_ty ty) (string_of_expr ~print_anns e)

  type p_unless = k_expr * constr * bool
  type p_until = k_expr * constr * bool

  let string_of_unless ?(print_anns=false) level (e, c, r) =
    Printf.sprintf "%sunless %s %s %s;"
      (indent level) (string_of_expr ~print_anns e)
      (if r then "then" else "continue") c

  let string_of_until ?(print_anns=false) level (e, c, r) =
    Printf.sprintf "%suntil %s %s %s;"
      (indent level) (string_of_expr ~print_anns e)
      (if r then "then" else "continue") c

  type p_instr =
    { pinstr_desc: p_instr_desc;
      pinstr_loc: location }

  and p_instr_desc =
    | Eq of k_equation
    | Let of (ident * ann * k_expr * p_instr list)
    | Switch of (k_expr * (constr * p_instr list) list * (ident option * ident list))
    | Reset of (p_instr list * k_expr)
    | Automaton of ((constr * p_unless list * p_instr list * p_until list) list * (ident option * clock option * ident list))

  let rec string_of_instr ?(print_anns=false) level i =
    match i.pinstr_desc with
    | Eq eq -> Printf.sprintf "%s%s;" (indent level) (string_of_equation ~print_anns eq)
    | Let (id, ann, e, ins) ->
      Printf.sprintf "%slet (%s : %s) = %s in\n%s\n%send;" (indent level)
        id (string_of_ann ann) (string_of_expr ~print_anns e)
        (string_of_instrs ~print_anns (level+1) ins)
        (indent level)
    | Automaton (branches, _) ->
      Printf.sprintf "%sautomaton\n%s" (indent level)
        (String.concat "\n" (List.map (fun (c, unlesss, ins, untils) ->
             Printf.sprintf "%s| %s ->\n%s\n%s\n%s" (indent level) c
               (String.concat "\n" (List.map (string_of_unless ~print_anns (level+1)) unlesss))
               (string_of_instrs ~print_anns (level+1) ins)
               (String.concat "\n" (List.map (string_of_until ~print_anns (level+1)) untils)))
             branches))
    | Reset (ins, er) ->
      Printf.sprintf "%sreset\n%s\n%severy %s;" (indent level)
        (string_of_instrs ~print_anns (level + 1) ins)
        (indent level) (string_of_expr er)
    | Switch (e, branches, (ckid, _)) ->
      Printf.sprintf "%sswitch%s %s\n%s\n%send;" (indent level)
        (match ckid with Some ckid -> Printf.sprintf "(%s)" ckid | None -> "")
        (string_of_expr e)
        (String.concat "\n" (List.map (fun (c, ins) ->
             Printf.sprintf "%s| %s -> \n%s" (indent level) c
               (string_of_instrs ~print_anns (level+1) ins))
             branches))
        (indent level)
  and string_of_instrs ?(print_anns=false) level ins =
    String.concat "\n" (List.map (string_of_instr ~print_anns level) ins)

  type p_node =
    { pn_name: ident;
      pn_input: (ident * ann) list;
      pn_output: (ident * ann) list;
      pn_local: (ident * ann * const option) list;
      pn_instrs: p_instr list;
      pn_loc: location; }

  let string_of_local (id, ann, init) =
    match init with
    | Some init -> Printf.sprintf "last %s:%s = %s"
                     id (string_of_ann ann) (string_of_const init)
    | None -> Printf.sprintf "%s:%s" id (string_of_ann ann)

  let string_of_node ?(print_anns=false) n =
    Printf.sprintf "node %s(%s) returns (%s);\n\
                    var %s;\n\
                    let\n\
                    %s\n\
                    tel\n"
      n.pn_name
      (string_of_ident_ann_list n.pn_input)
      (string_of_ident_ann_list n.pn_output)
      (String.concat "; " (List.map string_of_local n.pn_local))
      (String.concat "\n" (List.map (string_of_instr ~print_anns 1) n.pn_instrs))

  type p_file =
    { pf_clocks: clockdec list;
      pf_nodes: p_node list; }

  let string_of_file ?(print_anns=false) f =
    Printf.sprintf "%s\n%s"
      (String.concat "\n" (List.map string_of_clockdec f.pf_clocks))
      (String.concat "\n" (List.map (string_of_node ~print_anns) f.pf_nodes))
end

module PMinils = PMINILS(NoAnnot)
