(* Abstract syntax tree *)

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
  (* | PE_arrow of p_expr * p_expr
   * | PE_pre of p_expr *)
  | PE_tuple of p_expr list
  | PE_when of p_expr * ident * bool
  (* the last parameters indicates if the clock is negated *)
  | PE_merge of ident * p_expr * p_expr

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
  (* | PE_arrow (e1, e2) -> Printf.sprintf "(%s -> %s)"
   *                          (string_of_expr e1) (string_of_expr e2)
   * | PE_pre e -> Printf.sprintf "(pre %s)" (string_of_expr e) *)
  | PE_tuple es -> Printf.sprintf "(%s)"
                     (String.concat ", " (List.map string_of_expr es))
  | PE_when (e, id, neg) ->
    Printf.sprintf (if neg then "%s when not %s" else "%s when %s")
      (string_of_expr e) id
  | PE_merge (id, e1, e2) -> Printf.sprintf "merge %s (%s) (%s)"
                               id (string_of_expr e1) (string_of_expr e2)

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
      pn_input: (ident * ty) list;
      pn_output: (ident * ty) list;
      pn_local: (ident * ty) list;
      pn_equs: p_equation list;
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
    (String.concat "" (List.map (fun eq ->
         Printf.sprintf "  %s;\n" (string_of_equation eq)) n.pn_equs))

type p_file = p_node list

let string_of_file f =
  String.concat "\n" (List.map string_of_node f)
