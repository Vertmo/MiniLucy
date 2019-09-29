(** Equation scheduler *)

open Asttypes
open NMinils

module IdentMap = Map.Make(String)

(** Dependency graph *)
type dep_graph = (ident list) IdentMap.t

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
   | NE_when (e, clid, _) -> clid::(expr_vars e)
  )@(clock_vars e.nexpr_clock)

let rec cexpr_vars (e : n_cexpr) =
  (match e.ncexpr_desc with
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

(** Compute the dependencies introduced by the equation [eq] *)
let eq_dependencies (eq : n_equation) : dep_graph =
  let defined = def_vars eq
  and used = List.sort_uniq String.compare (used_vars eq) in
  IdentMap.of_seq (List.to_seq (List.map (fun l -> (l, used)) defined))

(** Gets all the streams [x] depends on *)
let get_dependencies (x : ident) (graph : dep_graph) =
  let rec depth_first (visited : ident list) (current : ident) =
    let next =
      try IdentMap.find current graph
      with Not_found -> [] in
    List.fold_left (fun vis n' ->
        if List.mem n' vis then vis else depth_first (n'::vis) n')
      visited next in
  depth_first [] x

let schedule_node (n : n_node) =
  let graph = List.fold_left
      (fun graph eq -> IdentMap.union
          (fun _ l1 l2 -> failwith "Should not happen (typing)")
              graph (eq_dependencies eq))
      IdentMap.empty n.nn_equs in
  let sorted_equs = List.sort (fun eq1 eq2 ->
      let defs1 = def_vars eq1 and defs2 = def_vars eq2 in
      if List.exists
          (fun df1 ->
             List.exists (fun df2 ->
                 List.mem df2 (get_dependencies df1 graph)) defs2) defs1
      then 1 else -1) n.nn_equs in
  { n with nn_equs = sorted_equs; }

let schedule_file (f : n_file) =
  { f with nf_nodes = List.map schedule_node f.nf_nodes }
