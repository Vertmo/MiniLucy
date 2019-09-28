(** Desugarizer from parsed AST to kernel AST *)

open PMinils
open Minils

let desugar_patt (p : p_patt) : k_patt =
  let desc = match p.ppatt_desc with
    | PP_ident id -> KP_ident id
    | PP_tuple ids -> KP_tuple ids in
  { kpatt_desc = desc; kpatt_loc = p.ppatt_loc; }

let rec desugar_expr (e : p_expr) : k_expr =
  let desc = match e.pexpr_desc with
    | PE_const c -> KE_const c
    | PE_ident id -> KE_ident id
    | PE_op (op, es) -> KE_op (op, List.map desugar_expr es)
    | PE_app (id, es, e) ->
      KE_app (id, List.map desugar_expr es, desugar_expr e)
    | PE_fby (c, e) -> KE_fby (c, desugar_expr e)
    | PE_tuple es -> KE_tuple (List.map desugar_expr es)
    | PE_when (e, id, b) -> KE_when (desugar_expr e, id, b)
    | PE_merge (id, e1, e2) ->
      KE_merge (id, desugar_expr e1, desugar_expr e2) in
  { kexpr_desc = desc; kexpr_loc = e.pexpr_loc; }

let desugar_equation (eq : p_equation) : k_equation =
  { keq_patt = desugar_patt eq.peq_patt;
    keq_expr = desugar_expr eq.peq_expr; }

let desugar_node (n : p_node) : k_node =
  { kn_name = n.pn_name;
    kn_input = n.pn_input;
    kn_output = n.pn_output;
    kn_local = n.pn_local;
    kn_equs = List.map desugar_equation n.pn_equs;
    kn_loc = n.pn_loc }

let desugar_file (f : p_file) : k_file =
  List.map desugar_node f
