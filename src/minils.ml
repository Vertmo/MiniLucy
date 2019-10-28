(** Kernel AST *)

open Asttypes

type k_expr =
  { kexpr_desc: k_expr_desc;
    kexpr_loc: location; }

and k_expr_desc =
  | KE_const of const
  | KE_ident of ident
  | KE_op of op * k_expr list
  | KE_app of ident * k_expr list * k_expr
  | KE_fby of const * k_expr
  | KE_tuple of k_expr list
  | KE_when of k_expr * constr * ident
  | KE_merge of ident * (constr * k_expr) list

let rec string_of_expr e =
  string_of_expr_desc e.kexpr_desc

and string_of_expr_desc = function
  | KE_const c -> string_of_const c
  | KE_ident i -> i
  | KE_op (op, es) -> Printf.sprintf "(%s [%s])"
                        (string_of_op op)
                        (String.concat "; " (List.map string_of_expr es))
  | KE_app (id, es, ever) -> Printf.sprintf "(%s [%s] every %s)" id
                         (String.concat "; " (List.map string_of_expr es))
                         (string_of_expr ever)
  | KE_fby (c, e) -> Printf.sprintf "(%s fby %s)"
                       (string_of_const c) (string_of_expr e)
  | KE_tuple es -> Printf.sprintf "(%s)"
                     (String.concat ", " (List.map string_of_expr es))
  | KE_when (e, constr, clid) ->
    Printf.sprintf "%s when %s(%s)"
      (string_of_expr e) constr clid
  | KE_merge (id, es) ->
    Printf.sprintf "merge %s %s"
      id (String.concat " "
            (List.map
               (fun (constr, e) -> Printf.sprintf "(%s -> %s)"
                   constr (string_of_expr e)) es))

type k_patt =
  { kpatt_desc: k_patt_desc;
    kpatt_loc: location; }

and k_patt_desc =
  | KP_ident of ident
  | KP_tuple of ident list

let rec string_of_patt p =
  string_of_patt_desc p.kpatt_desc

and string_of_patt_desc = function
  | KP_ident id -> id
  | KP_tuple ids -> Printf.sprintf "(%s)" (String.concat ", " ids)

type k_equation =
    { keq_patt: k_patt;
      keq_expr: k_expr; }

let string_of_equation eq =
  Printf.sprintf "%s = %s"
    (string_of_patt eq.keq_patt)
    (string_of_expr eq.keq_expr)

(** Variables defined by an equation *)
let defined_of_equation eq =
  match eq.keq_patt.kpatt_desc with
  | KP_ident id -> [id]
  | KP_tuple ids -> ids

type k_node =
    { kn_name: ident;
      kn_input: (ident * ty) list;
      kn_output: (ident * ty) list;
      kn_local: (ident * ty) list;
      kn_equs: k_equation list;
      kn_loc: location; }

let string_of_node n =
  Printf.sprintf "node %s(%s) returns (%s);\n\
                 var %s;\n\
                 let\n\
                 %s\
                 tel\n"
    n.kn_name
    (string_of_ident_type_list n.kn_input)
    (string_of_ident_type_list n.kn_output)
    (string_of_ident_type_list n.kn_local)
    (String.concat "" (List.map (fun eq ->
         Printf.sprintf "  %s;\n" (string_of_equation eq)) n.kn_equs))

type k_file =
  { kf_clocks: clockdec list;
    kf_nodes: k_node list; }

let string_of_file f =
  Printf.sprintf "%s\n%s"
    (String.concat "\n" (List.map string_of_clockdec f.kf_clocks))
    (String.concat "\n" (List.map string_of_node f.kf_nodes))
