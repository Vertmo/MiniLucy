(** Causality checking *)

open Asttypes
open Kernelizer.CMinils

exception CausalityError of (string * ident * location)


let clocks_of (es : k_expr list) =
  List.concat (List.map (fun e -> List.map snd e.kexpr_annot) es)

(** Get the "free variables" of the expression [e] *)
let rec expr_vars (e : k_expr) =
  (match e.kexpr_desc with
   | KE_const _ -> []
   | KE_ident id -> [id]
   | KE_unop (_, e1) -> expr_vars e1
   | KE_binop (_, e1, e2) -> (expr_vars e1)@(expr_vars e2)
   | KE_app (_, es, ev) ->
     (expr_vars ev)@(exprs_vars es)
   | KE_fby (e0, _) -> (exprs_vars e0)
   | KE_arrow (e0, e) -> (exprs_vars e0)@(exprs_vars e)
   | KE_switch (e, es) ->
     List.concat ((expr_vars e)::(List.map (fun (_, e) -> exprs_vars e) es))
   | KE_when (e, _, id) -> id::(exprs_vars e)
   | KE_merge (id, es) ->
     id::(List.concat (List.map (fun (_, e) -> exprs_vars e) es))
  )@(List.concat (List.map (fun (_, (ck, _)) -> clock_vars ck) e.kexpr_annot))
and exprs_vars es = List.concat (List.map expr_vars es)

module IdentMap = Map.Make(String)

(** Dependency graph *)
type dep_graph = (ident list) IdentMap.t

(** Compute the dependencies introduced by the equation [eq] *)
let eq_dependencies (eq : k_equation) : dep_graph =
  let defined = eq.keq_patt and used = exprs_vars eq.keq_expr in
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
let check_node (n : k_node) =
  let graph = List.fold_left
      (fun graph eq -> IdentMap.union
          (fun _ l1 l2 -> failwith "Should not happen (typing)")
          graph (eq_dependencies eq))
      IdentMap.empty n.kn_equs in
  IdentMap.iter (fun id _ ->
      if has_self_dependency id graph
      then raise
          (CausalityError
             (Printf.sprintf "%s depends on itself" id,
              n.kn_name, n.kn_loc))) graph

(** Check the file [f] for causality errors
    Return the dependency graphs *)
let check_file (f : k_file) =
  try
    List.iter check_node f.kf_nodes
  with
  | CausalityError (msg, nodeid, loc) ->
    Printf.printf "Causality error : %s in node %s at %s"
      msg nodeid (string_of_loc loc); exit 1
