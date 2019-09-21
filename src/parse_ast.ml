(* Arbres de syntaxe abstraite *)

open Asttypes

type ident = string

type p_expr =
  { pexpr_desc: p_expr_desc;
    pexpr_loc: location; }

and p_expr_desc =
  | PE_const of const
  | PE_ident of ident
  | PE_op of op * p_expr list
  | PE_app of ident * p_expr list
  | PE_arrow of p_expr * p_expr
  | PE_pre of p_expr
  | PE_tuple of p_expr list

let rec string_of_expr p =
  string_of_expr_desc p.pexpr_desc

and string_of_expr_desc = function
  | PE_const c -> string_of_const c
  | PE_ident i -> i
  | PE_op (op, es) -> Printf.sprintf "(%s [%s])"
                        (string_of_op op)
                        (String.concat "; " (List.map string_of_expr es))
  | PE_app (id, es) -> Printf.sprintf "(%s [%s])" id
                         (String.concat "; " (List.map string_of_expr es))
  | PE_arrow (e1, e2) -> Printf.sprintf "(%s -> %s)"
                           (string_of_expr e1) (string_of_expr e2)
  | PE_pre e -> Printf.sprintf "(pre %s)" (string_of_expr e)
  | PE_tuple es -> Printf.sprintf "(%s)"
                     (String.concat ", " (List.map string_of_expr es))

type p_patt =
  { ppatt_desc: p_patt_desc;
    ppatt_loc: location; }

and p_patt_desc =
  | PP_ident of ident
  | PP_tuple of ident list

let rec string_of_pat p =
  string_of_pat_desc p.ppatt_desc

and string_of_pat_desc = function
  | PP_ident id -> id
  | PP_tuple ids -> Printf.sprintf "(%s)" (String.concat ", " ids)

type p_equation =
    { peq_patt: p_patt;
      peq_expr: p_expr; }

let string_of_equation eq =
  Printf.sprintf "%s = %s"
    (string_of_pat eq.peq_patt)
    (string_of_expr eq.peq_expr)

type p_node =
    { pn_name: ident;
      pn_input: (ident * base_ty) list;
      pn_output: (ident * base_ty) list;
      pn_local: (ident * base_ty) list;
      pn_equs: p_equation list;
      pn_loc: location; }

let string_of_ident_type_list l =
  String.concat "; " (List.map (fun (id, t) ->
      Printf.sprintf "%s:%s" id (string_of_base_ty t)) l)

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
    (String.concat "" (List.map (fun eq ->
         Printf.sprintf "  %s;\n" (string_of_equation eq)) n.pn_equs))

type p_file = p_node list

let string_of_file f =
  String.concat "\n" (List.map string_of_node f)
