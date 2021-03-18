(** Normalized abstract syntax tree *)

open Common

type n_expr =
  { nexpr_desc: n_expr_desc;
    nexpr_ty: ty;
    nexpr_clock: clock; }

and n_expr_desc =
  | NE_const of const
  | NE_ident of ident
  | NE_op of op * n_expr list
  | NE_when of n_expr * constr * ident

let rec string_of_expr e =
  Printf.sprintf "%s"
    (string_of_expr_desc e.nexpr_desc)

and string_of_expr_desc = function
  | NE_const c -> string_of_const c
  | NE_ident i -> i
  | NE_op (op, es) -> Printf.sprintf "(%s [%s])"
                        (string_of_op op)
                        (String.concat "; " (List.map string_of_expr es))
  | NE_when (e, c, id) ->
    Printf.sprintf "%s when %s(%s)"
      (string_of_expr e) c id

type n_cexpr =
  { ncexpr_desc: n_cexpr_desc;
    ncexpr_ty: ty;
    ncexpr_clock: clock; }

and n_cexpr_desc =
  | NCE_match of n_expr * (constr * n_cexpr) list
  | NCE_merge of ident * (constr * n_cexpr) list
  | NCE_expr of n_expr_desc

let rec string_of_cexpr e =
  Printf.sprintf "%s"
    (string_of_cexpr_desc e.ncexpr_desc)

and string_of_cexpr_desc = function
  | NCE_match (e, es) ->
    Printf.sprintf "match %s %s"
      (string_of_expr e)
      (String.concat " "
         (List.map
            (fun (constr, e) -> Printf.sprintf "(%s -> %s)"
                constr (string_of_cexpr e)) es))
  | NCE_merge (id, es) ->
    Printf.sprintf "merge %s %s"
      id (String.concat " "
            (List.map
               (fun (constr, e) -> Printf.sprintf "(%s -> %s)"
                   constr (string_of_cexpr e)) es))
  | NCE_expr e -> string_of_expr_desc e

type n_equation =
  | NQ_ident of ident * n_cexpr
  | NQ_fby of ident * const * n_expr * ident * clock
  | NQ_app of ident list * ident * n_expr list * ident * clock * clock

let string_of_equation = function
  | NQ_ident (id, e) ->
    Printf.sprintf "%s = %s" id (string_of_cexpr e)
  | NQ_fby (id, c, e, r, _) ->
    Printf.sprintf "%s = %s fby %s every %s"
      id (string_of_const c) (string_of_expr e) r
  | NQ_app (ids, f, es, ever, _, _) ->
    Printf.sprintf "(%s) = %s(%s) every %s"
      (String.concat ", " ids) f
      (String.concat ", " (List.map string_of_expr es))
      ever

type n_node =
  { nn_name: ident;
    nn_input: (ident * ann) list;
    nn_output: (ident * ann) list;
    nn_local: (ident * ann) list;
    nn_equs: n_equation list;
    nn_loc: location }

let string_of_node n =
  Printf.sprintf "node %s(%s) returns (%s);\n\
                  var %s;\n\
                  let\n\
                  %s\
                  tel\n"
    n.nn_name
    (string_of_ident_ann_list n.nn_input)
    (string_of_ident_ann_list n.nn_output)
    (string_of_ident_ann_list n.nn_local)
    (String.concat "" (List.map (fun eq ->
         Printf.sprintf "  %s;\n" (string_of_equation eq)) n.nn_equs))

type n_file =
  { nf_clocks: clockdec list;
    nf_nodes : n_node list; }

let string_of_file f =
  Printf.sprintf "%s\n%s"
    (String.concat "\n" (List.map string_of_clockdec f.nf_clocks))
    (String.concat "\n" (List.map string_of_node f.nf_nodes))
