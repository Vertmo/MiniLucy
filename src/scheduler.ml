(** Equation scheduler *)

open Asttypes
open NMinils

(** Get the variables defined by an equation *)
let def_vars = function
  | NQ_ident (id, _) -> [id]
  | NQ_fby (id, _, _) -> [id]
  | NQ_app (ids, _, _, _, _) -> ids

(** Get the variables used by an expression *)
let rec expr_vars (e : n_expr) =
  (match e.nexpr_desc with
   | NE_const _ -> []
   | NE_ident id -> [id]
   | NE_op (_, es) -> List.flatten (List.map expr_vars es)
   | NE_when (e, _, clid) -> clid::(expr_vars e)
  )@(clock_vars e.nexpr_clock)

let rec cexpr_vars (e : n_cexpr) =
  (match e.ncexpr_desc with
   | NCE_switch (e, es) ->
     (expr_vars e)@(List.flatten (List.map (fun (_, e) -> cexpr_vars e) es))
   | NCE_merge (id, es) ->
     id::(List.flatten (List.map (fun (_, e) -> cexpr_vars e) es))
   | NCE_expr e' ->
     (expr_vars { nexpr_desc = e';
                  nexpr_ty = e.ncexpr_ty; nexpr_clock = e.ncexpr_clock })
  )@(clock_vars e.ncexpr_clock)

(** Get the variables used by an equation *)
let used_vars = function
  | NQ_ident (_, e) -> (cexpr_vars e)
  | NQ_fby (_, _, e) -> clock_vars (e.nexpr_clock)
  | NQ_app (_, _, es, evid, cl) ->
    evid::(clock_vars cl)@(List.flatten (List.map expr_vars es))

(** Schedule a node *)
let schedule_node (n : n_node) =
  let rec top_sort defs equs =
    let (equs, rest) = List.partition (fun eq ->
        let used = used_vars eq in
        List.for_all (fun u -> List.mem u defs) used) equs in
    if (List.length rest = 0) then equs
    else equs@(top_sort ((List.flatten (List.map def_vars equs))@defs) rest) in
  let sorted_equs = top_sort (List.map fst n.nn_input) n.nn_equs in
  { n with nn_equs = sorted_equs; }

let schedule_file (f : n_file) =
  { f with nf_nodes = List.map schedule_node f.nf_nodes }

(*                      Check that the scheduling is correct                  *)

let schedule_is_correct_node n =
  let defined =
    List.fold_left (fun defs eq ->
        let used = List.sort_uniq String.compare (used_vars eq) in
        if not (List.for_all (fun v -> List.mem v defs) used)
        then failwith (String.concat "," used);
        (def_vars eq)@defs) (List.map fst n.nn_input) n.nn_equs in
  List.for_all (fun v -> List.mem v defined)
    (List.map fst (n.nn_local@n.nn_output))

let schedule_is_correct_file f =
    List.for_all schedule_is_correct_node f.nf_nodes
