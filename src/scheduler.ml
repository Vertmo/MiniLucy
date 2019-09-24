(** Equation scheduler *)

open CMinils
open Causalitychecker

(** Schedule the equations inside a node *)
let schedule_node (n : c_node) =
  let eqs = n.cn_equs in
  let eqs = List.sort (fun eq1 eq2 ->
      let def = List.hd (pat_vars eq1.ceq_patt)
      and used = expr_vars eq2.ceq_expr in
      if (List.mem def used) then -1 else 1
    ) eqs in
  { n with cn_equs = eqs }

(** Schedule the equations inside a file *)
let schedule_file (f : c_file) =
  List.map schedule_node f
