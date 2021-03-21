(** Causality checking *)

open Common
open NMinils

exception CausalityError of (string * ident * location)

(** Get the variables defined by an equation *)
let def_vars = function
  | NQ_ident (id, _) -> [id]
  | NQ_fby (id, _, _, _, _) -> [id]
  | NQ_app (ids, _, _, _, _, _) -> ids

(** Get the variables used by an expression *)
let rec expr_vars (e : n_expr) =
  match e.nexpr_desc with
  | NE_const _ -> []
  | NE_ident id -> [id]
  | NE_op (_, es) -> List.flatten (List.map expr_vars es)
  | NE_when (e, _, clid) -> clid::(expr_vars e)

let rec cexpr_vars (e : n_cexpr) =
  match e.ncexpr_desc with
  | NCE_match (e, es) ->
    (expr_vars e)@(List.flatten (List.map (fun (_, e) -> cexpr_vars e) es))
  | NCE_merge (id, es) ->
    id::(List.flatten (List.map (fun (_, e) -> cexpr_vars e) es))
  | NCE_expr e' ->
    (expr_vars { nexpr_desc = e';
                 nexpr_ty = e.ncexpr_ty; nexpr_clock = e.ncexpr_clock })

(** Get the variables used by an equation *)
let used_vars = function
  | NQ_ident (_, e) -> (clock_vars e.ncexpr_clock)@(cexpr_vars e)
  | NQ_fby (_, _, e, r, ckr) -> r::(clock_vars (e.nexpr_clock))@(clock_vars ckr)
  | NQ_app (_, _, es, evid, bck, ckr) ->
    evid::(clock_vars bck)@(clock_vars ckr)@(List.flatten (List.map expr_vars es))

module IdentMap = Map.Make(String)

(** Dependency graph *)
type dep_graph = (ident list) IdentMap.t

(** Compute the dependencies introduced by the equation [eq] *)
let eq_dependencies (eq : n_equation) : dep_graph =
  let defined = def_vars eq and used = used_vars eq in
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
let check_node (n : n_node) =
  let graph = List.fold_left
      (fun graph eq -> IdentMap.union
          (fun k l1 l2 -> failwith
              (Printf.sprintf "Should not happen %s [%s] [%s]"
                 k (String.concat "," l1) (String.concat "," l2)))
          graph (eq_dependencies eq))
      IdentMap.empty n.nn_equs in
  IdentMap.iter (fun id _ ->
      if has_self_dependency id graph
      then raise
          (CausalityError
             (Printf.sprintf "%s depends on itself" id,
              n.nn_name, n.nn_loc))) graph

(** Check the file [f] for causality errors
    Return the dependency graphs *)
let check_file (f : n_file) =
  List.iter check_node f.nf_nodes
