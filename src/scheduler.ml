(** Equation scheduler *)

open Common
open NMinils
open Causalitychecker

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
