(** Causality checking *)

open Asttypes
open CMinils

exception CausalityError of (string * ident * location)

(** Get the "variables" of a clock *)
let rec clock_vars = function
  | Base -> []
  | Cl (cl, id) -> id::(clock_vars cl)
  | NotCl (cl, id) -> id::(clock_vars cl)
  | Ctuple cls ->
    List.concat (List.map clock_vars cls)

(** Get the "free variables" of the expression [e] *)
let rec expr_vars (e : c_expr) =
  (match e.cexpr_desc with
  | CE_const _ -> []
  | CE_ident id -> [id]
  | CE_op (_, es) -> List.concat (List.map expr_vars es)
  | CE_app (_, es, ev) ->
    List.concat ((expr_vars ev)::(List.map expr_vars es))
  | CE_fby (_, _) -> []
  | CE_tuple es -> List.concat (List.map expr_vars es)
  | CE_when (e, id, _) -> id::(expr_vars e)
  | CE_merge (id, e1, e2) -> id::(expr_vars e1)@(expr_vars e2)
  )@(clock_vars e.cexpr_clock)

(** Get the variables bound by the pattern [p] *)
let pat_vars (p : c_patt) =
  match p.cpatt_desc with
  | CP_ident id -> [id]
  | CP_tuple ids -> ids

module IdentMap = Map.Make(String)

(** Dependency graph, represented as a quite inneficient structure *)
type dep_graph = (ident list) IdentMap.t

(** Compute the dependencies introduced by the equation [eq] *)
let eq_dependencies (eq : c_equation) : dep_graph =
  let defined = pat_vars eq.ceq_patt and used = expr_vars eq.ceq_expr in
  IdentMap.of_seq (List.to_seq (List.map (fun l -> (l, used)) defined))

(** Check if there is a self-dependency for one of the ident in the graph *)
let has_self_dependency (n : ident) (graph : dep_graph) =
  let rec depth_first (visited : ident list) (current : ident) =
    let next =
      try IdentMap.find current graph
      with Not_found -> [] in
    List.fold_left (fun vis n' ->
        if List.mem n' vis then vis else depth_first (n'::vis) n')
      visited next in
  if (List.mem n (depth_first [] n)) then true else false

(** Check the node [n] for causality errors
    Return the dependency graph of the node *)
let check_node (n : c_node) =
  let graph = List.fold_left
      (fun graph eq -> IdentMap.union
          (fun _ l1 l2 -> failwith "Should not happen (typing)")
          graph (eq_dependencies eq))
      IdentMap.empty n.cn_equs in
  IdentMap.iter (fun id _ ->
      if has_self_dependency id graph
      then raise
          (CausalityError
             (Printf.sprintf "%s depends on itself" id,
              n.cn_name, n.cn_loc))) graph

(** Check the file [f] for causality errors
    Return the dependency graphs *)
let check_file (f : c_file) =
  try
    List.iter check_node f
  with
  | CausalityError (msg, nodeid, loc) ->
    Printf.printf "Causality error : %s in node %s at %s"
      msg nodeid (string_of_loc loc); exit 1
