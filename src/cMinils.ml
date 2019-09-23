(* Abstract syntax tree annotated with clocks *)

open Asttypes

type clock =
  | Base
  | Cl of clock * ident (* Clock *)
  | NotCl of clock * ident (* Negated clock *)
  | Ctuple of clock list

let clock_of_ty : ty -> clock = function
  | Base _ -> Base
  | Clocked (_, cl, neg) ->
    if neg then NotCl (Base, cl) else Cl (Base, cl)

let rec string_of_clock = function
  | Base -> "base"
  | Cl (base, cl) ->
    Printf.sprintf "(%s on %s)" (string_of_clock base) cl
  | NotCl (base, cl) ->
    Printf.sprintf "(%s on not %s)" (string_of_clock base) cl
  | Ctuple cls ->
    Printf.sprintf "(%s)" (String.concat "," (List.map string_of_clock cls))

type c_expr =
  { cexpr_desc: c_expr_desc;
    cexpr_clock: clock;
    cexpr_loc: location; }

and c_expr_desc =
  | CE_const of const
  | CE_ident of ident
  | CE_op of op * c_expr list
  | CE_app of ident * c_expr list * c_expr
  | CE_fby of const * c_expr
  | CE_tuple of c_expr list
  | CE_when of c_expr * ident * bool
  (* the last parameters indicates if the clock is negated *)
  | CE_merge of ident * c_expr * c_expr

let rec string_of_expr e =
  Printf.sprintf "(%s {%s})"
    (string_of_expr_desc e.cexpr_desc)
    (string_of_clock e.cexpr_clock)

and string_of_expr_desc = function
  | CE_const c -> string_of_const c
  | CE_ident i -> i
  | CE_op (op, es) -> Printf.sprintf "(%s [%s])"
                        (string_of_op op)
                        (String.concat "; " (List.map string_of_expr es))
  | CE_app (id, es, ever) -> Printf.sprintf "(%s [%s] every %s)" id
                         (String.concat "; " (List.map string_of_expr es))
                         (string_of_expr ever)
  | CE_fby (c, e) -> Printf.sprintf "(%s fby %s)"
                       (string_of_const c) (string_of_expr e)
  | CE_tuple es -> Printf.sprintf "(%s)"
                     (String.concat ", " (List.map string_of_expr es))
  | CE_when (e, id, neg) ->
    Printf.sprintf (if neg then "%s when not %s" else "%s when %s")
      (string_of_expr e) id
  | CE_merge (id, e1, e2) -> Printf.sprintf "merge %s (%s) (%s)"
                               id (string_of_expr e1) (string_of_expr e2)

type c_patt =
  { cpatt_desc: c_patt_desc;
    cpatt_loc: location; }

and c_patt_desc =
  | CP_ident of ident
  | CP_tuple of ident list

let rec string_of_pat p =
  string_of_pat_desc p.cpatt_desc

and string_of_pat_desc = function
  | CP_ident id -> id
  | CP_tuple ids -> Printf.sprintf "(%s)" (String.concat ", " ids)

type c_equation =
  { ceq_patt : c_patt;
    ceq_expr : c_expr }

let string_of_equation eq =
  Printf.sprintf "%s = %s"
    (string_of_pat eq.ceq_patt)
    (string_of_expr eq.ceq_expr)

type c_node =
  { cn_name: ident;
    cn_input: (ident * ty) list;
    cn_output: (ident * ty) list;
    cn_local: (ident * ty) list;
    cn_equs: c_equation list;
    cn_loc: location; }

let string_of_node n =
  Printf.sprintf "node %s(%s) returns (%s);\n\
                  var %s;\n\
                  let\n\
                  %s\
                  tel\n"
    n.cn_name
    (string_of_ident_type_list n.cn_input)
    (string_of_ident_type_list n.cn_output)
    (string_of_ident_type_list n.cn_local)
    (String.concat "" (List.map (fun eq ->
         Printf.sprintf "  %s;\n" (string_of_equation eq)) n.cn_equs))

type c_file = c_node list

let string_of_file f =
  String.concat "\n" (List.map string_of_node f)
