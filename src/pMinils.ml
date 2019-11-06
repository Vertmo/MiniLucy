(** Parsed AST *)

open Asttypes

type p_expr =
  { pexpr_desc: p_expr_desc;
    pexpr_loc: location; }

and p_expr_desc =
  | PE_const of const
  | PE_ident of ident
  | PE_op of op * p_expr list
  | PE_app of ident * p_expr list * p_expr
  | PE_fby of const * p_expr
  | PE_arrow of p_expr * p_expr
  | PE_pre of p_expr
  | PE_tuple of p_expr list
  | PE_when of p_expr * constr * ident
  | PE_merge of ident * (constr * p_expr) list

let rec string_of_expr e =
  string_of_expr_desc e.pexpr_desc

and string_of_expr_desc = function
  | PE_const c -> string_of_const c
  | PE_ident i -> i
  | PE_op (op, es) -> Printf.sprintf "(%s [%s])"
                        (string_of_op op)
                        (String.concat "; " (List.map string_of_expr es))
  | PE_app (id, es, ever) -> Printf.sprintf "(%s [%s] every %s)" id
                         (String.concat "; " (List.map string_of_expr es))
                         (string_of_expr ever)
  | PE_fby (c, e) -> Printf.sprintf "(%s fby %s)"
                       (string_of_const c) (string_of_expr e)
  | PE_arrow (e1, e2) -> Printf.sprintf "(%s -> %s)"
                           (string_of_expr e1) (string_of_expr e2)
  | PE_pre e -> Printf.sprintf "(pre %s)" (string_of_expr e)
  | PE_tuple es -> Printf.sprintf "(%s)"
                     (String.concat ", " (List.map string_of_expr es))
  | PE_when (e, constr, clid) ->
    Printf.sprintf "%s when %s(%s)"
      (string_of_expr e) constr clid
  | PE_merge (id, es) ->
    Printf.sprintf "merge %s %s"
      id (String.concat " "
            (List.map
               (fun (constr, e) -> Printf.sprintf "(%s -> %s)"
                   constr (string_of_expr e)) es))

type p_patt =
  { ppatt_desc: p_patt_desc;
    ppatt_loc: location; }

and p_patt_desc =
  | PP_ident of ident
  | PP_tuple of ident list

let rec string_of_patt p =
  string_of_pat_desc p.ppatt_desc

and string_of_pat_desc = function
  | PP_ident id -> id
  | PP_tuple ids -> Printf.sprintf "(%s)" (String.concat ", " ids)

type p_equation =
    { peq_patt: p_patt;
      peq_expr: p_expr; }

let string_of_equation eq =
  Printf.sprintf "%s = %s"
    (string_of_patt eq.peq_patt)
    (string_of_expr eq.peq_expr)

(** Variables defined by an equation *)
let defined_of_equation eq =
  match eq.peq_patt.ppatt_desc with
  | PP_ident id -> [id]
  | PP_tuple ids -> ids

type p_let = ident * ty * p_expr

let string_of_let (id, ty, e) =
  Printf.sprintf "let %s : %s = %s in"
    id (string_of_ty ty) (string_of_expr e)

type p_until = p_expr * constr

let string_of_until (e, c) =
  Printf.sprintf "until %s then %s;" (string_of_expr e) c

type p_instr =
  | Eq of p_equation
  | Automaton of (constr * p_let list * p_instr list * p_until list) list

let rec string_of_instr = function
  | Eq eq -> Printf.sprintf "%s;" (string_of_equation eq)
  | Automaton branches ->
    Printf.sprintf "automaton\n%s"
      (String.concat "\n" (List.map (fun (c, lets, ins, untils) ->
           Printf.sprintf "| %s ->\n%s\n%s\n%s" c
             (String.concat "\n" (List.map string_of_let lets))
             (String.concat "\n" (List.map string_of_instr ins))
             (String.concat "\n" (List.map string_of_until untils)))
          branches))

(** Variables defined by an instruction *)
let rec defined_of_instr = function
  | Eq eq -> defined_of_equation eq
  | Automaton brs ->
    (* If the program is well typed, all the branches
       define the same equations left-hand-sides *)
    let (_, _, is, _) = List.hd brs in
    List.flatten (List.map defined_of_instr is)

type p_node =
    { pn_name: ident;
      pn_input: (ident * ty) list;
      pn_output: (ident * ty) list;
      pn_local: (ident * ty) list;
      pn_instrs: p_instr list;
      pn_loc: location; }

let string_of_node n =
  Printf.sprintf "node %s(%s) returns (%s);\n\
                 var %s;\n\
                 let\n\
                 %s\
                 tel\n"
    n.pn_name
    (string_of_ident_type_list n.pn_input)
    (string_of_ident_type_list n.pn_output)
    (string_of_ident_type_list n.pn_local)
    (String.concat "" (List.map (fun i ->
         Printf.sprintf "  %s\n" (string_of_instr i)) n.pn_instrs))

type p_file =
  { pf_clocks: clockdec list;
    pf_nodes: p_node list; }

let string_of_file f =
  Printf.sprintf "%s\n%s"
    (String.concat "\n" (List.map string_of_clockdec f.pf_clocks))
    (String.concat "\n" (List.map string_of_node f.pf_nodes))
