(** Causality checking *)

open Asttypes
open CMinils

exception CausalityError of (string * ident * location)

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
   | CE_when (e, _, id) -> id::(expr_vars e)
   | CE_merge (id, es) ->
     id::(List.flatten (List.map (fun (_, e) -> expr_vars e) es))
  )@(clock_vars e.cexpr_clock)

(** Get the variables bound by the pattern [p] *)
let pat_vars (p : c_patt) =
  match p.cpatt_desc with
  | CP_ident id -> [id]
  | CP_tuple ids -> ids

module IdentMap = Map.Make(String)

(** Dependency graph *)
type dep_graph = (ident list) IdentMap.t

(** Compute the dependencies introduced by the equation [eq] *)
let eq_dependencies (eq : c_equation) : dep_graph =
  let defined = pat_vars eq.ceq_patt and used = expr_vars eq.ceq_expr in
  IdentMap.of_seq (List.to_seq (List.map (fun l -> (l, used)) defined))

(** Get all the streams [x] depends on *)
let get_dependencies (x : ident) (graph : dep_graph) =
  let rec depth_first (visited : ident list) (current : ident) =
    let next =
      try IdentMap.find current graph
      with Not_found -> [] in
    List.fold_left (fun vis n' ->
        if List.mem n' vis then vis else depth_first (n'::vis) n')
      visited next in
  depth_first [] x

(** Check if [x] has a self-dependency *)
let has_self_dependency (x : ident) (graph : dep_graph) =
  List.mem x (get_dependencies x graph)

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
    List.iter check_node f.cf_nodes
  with
  | CausalityError (msg, nodeid, loc) ->
    Printf.printf "Causality error : %s in node %s at %s"
      msg nodeid (string_of_loc loc); exit 1
