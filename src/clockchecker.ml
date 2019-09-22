open Asttypes
open Parse_ast
open Clocked_ast

exception ClockError of (string * location)

(** Get the clocks(s) expected for a pattern [pat],
    as well as the translated pattern *)
let get_pattern_clock (streams : (ident * clock) list) (pat : p_patt) =
  match pat.ppatt_desc with
  | PP_ident id ->
    (try (List.assoc id streams)
     with _ -> failwith "Should not happen (typing)"),
    { cpatt_desc = CP_ident id; cpatt_loc = pat.ppatt_loc }
  | PP_tuple ids ->
    (Ctuple (List.map (fun id ->
         try (List.assoc id streams)
         with _ -> failwith "Should not happen (typing)"
       ) ids)),
     { cpatt_desc = CP_tuple ids; cpatt_loc = pat.ppatt_loc }

(** Check and get the clocked version of expression [e] *)
let rec clock_expr nodes streams (e : p_expr) =
  let loc = e.pexpr_loc in
  match e.pexpr_desc with
  | PE_const c ->
    { cexpr_desc = CE_const c; cexpr_clock = Base; cexpr_loc = loc }
  | PE_ident id ->
    let cl = (try (List.assoc id streams)
              with _ -> failwith "Should no happen (typing)") in
    { cexpr_desc = CE_ident id; cexpr_clock = cl; cexpr_loc = loc }
  | PE_op (op, es) ->
    let ces = List.map (clock_expr nodes streams) es in
    let cl = (List.hd ces).cexpr_clock in
    if (not (List.for_all (fun ce -> ce.cexpr_clock = cl) ces))
    then raise (ClockError
                  (Printf.sprintf
                     "All the operands of %s should be on the same clock"
                   (string_of_op op), loc));
    { cexpr_desc = CE_op (op, ces); cexpr_clock = cl; cexpr_loc = loc}
  | PE_tuple es ->
    let ces = List.map (clock_expr nodes streams) es in
    let cls = List.map (fun ce -> ce.cexpr_clock) ces in
    { cexpr_desc = CE_tuple ces; cexpr_clock = Ctuple cls; cexpr_loc = loc}
  | PE_when (ew, clid, neg) ->
    let cew = clock_expr nodes streams ew in
    let cl = if neg
      then NotCl (cew.cexpr_clock, clid)
      else Cl (cew.cexpr_clock, clid) in
    { cexpr_desc = CE_when (cew, clid, neg); cexpr_clock = cl; cexpr_loc = loc }

(** Check the clocks for the equation [eq] *)
let clock_equation nodes streams (eq : p_equation) =
  let (expected, pat) = get_pattern_clock streams eq.peq_patt
  and ce = clock_expr nodes streams eq.peq_expr in
  if (ce.cexpr_clock <> expected)
  then raise (ClockError
                (Printf.sprintf
                   "Wrong clock for equation %s; expected %s, found %s"
                   (Parse_ast.string_of_equation eq)
                   (string_of_clock expected)
                   (string_of_clock ce.cexpr_clock), eq.peq_expr.pexpr_loc));
  { ceq_patt = pat ; ceq_expr = ce }

(** Check the clocks for the node [f] *)
let clock_node (nodes : (ident * c_node) list) (n : p_node) : c_node =
  let streams = List.map (fun (id, ty) -> (id, clock_of_ty ty))
      (n.pn_input@n.pn_local@n.pn_output) in
  { cn_name = n.pn_name;
    cn_input = n.pn_input;
    cn_output = n.pn_output;
    cn_local = n.pn_local;
    cn_equs = List.map (clock_equation nodes streams) n.pn_equs;
    cn_loc = n.pn_loc }

(** Check the clocks for the file [f] *)
let clock_file (f : p_file) : c_file =
  try
    List.map snd
      (List.fold_left (fun env n ->
           (n.pn_name, (clock_node env n))::env) [] f)
  with
  | ClockError (msg, loc) ->
    Printf.printf "Type checking error : %s at %s\n"
      msg (string_of_loc loc); exit 1
