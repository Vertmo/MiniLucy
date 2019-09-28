(** Type-annotated AST *)

open Asttypes

type t_expr =
  { texpr_desc: t_expr_desc;
    texpr_ty: base_ty;
    texpr_loc: location; }

and t_expr_desc =
  | TE_const of const
  | TE_ident of ident
  | TE_op of op * t_expr list
  | TE_app of ident * t_expr list * t_expr
  | TE_fby of const * t_expr
  | TE_tuple of t_expr list
  | TE_when of t_expr * ident * bool
  | TE_merge of ident * t_expr * t_expr

type t_patt = Minils.k_patt
type t_patt_desc = Minils.k_patt_desc

let string_of_patt = Minils.string_of_patt
let string_of_patt_desc = Minils.string_of_patt_desc

let rec string_of_expr e =
  string_of_expr_desc e.texpr_desc

and string_of_expr_desc = function
  | TE_const c -> string_of_const c
  | TE_ident i -> i
  | TE_op (op, es) -> Printf.sprintf "(%s [%s])"
                        (string_of_op op)
                        (String.concat "; " (List.map string_of_expr es))
  | TE_app (id, es, ever) -> Printf.sprintf "(%s [%s] every %s)" id
                         (String.concat "; " (List.map string_of_expr es))
                         (string_of_expr ever)
  | TE_fby (c, e) -> Printf.sprintf "(%s fby %s)"
                       (string_of_const c) (string_of_expr e)
  | TE_tuple es -> Printf.sprintf "(%s)"
                     (String.concat ", " (List.map string_of_expr es))
  | TE_when (e, id, b) ->
    Printf.sprintf (if b then "%s when %s" else "%s when not %s")
      (string_of_expr e) id
  | TE_merge (id, e1, e2) -> Printf.sprintf "merge %s (%s) (%s)"
                               id (string_of_expr e1) (string_of_expr e2)

type t_equation =
    { teq_patt: t_patt;
      teq_expr: t_expr; }

let string_of_equation eq =
  Printf.sprintf "%s = %s"
    (string_of_patt eq.teq_patt)
    (string_of_expr eq.teq_expr)

type t_node =
    { tn_name: ident;
      tn_input: (ident * ty) list;
      tn_output: (ident * ty) list;
      tn_local: (ident * ty) list;
      tn_equs: t_equation list;
      tn_loc: location; }

let string_of_node n =
  Printf.sprintf "node %s(%s) returns (%s);\n\
                 var %s;\n\
                 let\n\
                 %s\
                 tel\n"
    n.tn_name
    (string_of_ident_type_list n.tn_input)
    (string_of_ident_type_list n.tn_output)
    (string_of_ident_type_list n.tn_local)
    (String.concat "" (List.map (fun eq ->
         Printf.sprintf "  %s;\n" (string_of_equation eq)) n.tn_equs))

type t_file = t_node list

let string_of_file f =
  String.concat "\n" (List.map string_of_node f)
