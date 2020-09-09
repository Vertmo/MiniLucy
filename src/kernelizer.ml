(** Desugarizer from parsed AST to kernel AST *)

open Asttypes
open PMinils
open Minils.KMinils

(* Sort fields                                                                 *)

let rec sort_expr (e : k_expr) : k_expr =
  let desc = match e.kexpr_desc with
    | KE_const c -> KE_const c
    | KE_ident id -> KE_ident id
    | KE_op (op, es) -> KE_op (op, List.map sort_expr es)
    | KE_app (id, es, e) ->
      KE_app (id, List.map sort_expr es, sort_expr e)
    | KE_fby (e0, e) -> KE_fby (sort_expr e0, sort_expr e)
    | KE_arrow (e0, e) -> KE_arrow (sort_expr e0, sort_expr e)
    (* | KE_pre e -> KE_fby (Cnil, sort_expr e) *)
    | KE_tuple es -> KE_tuple (List.map sort_expr es)
    | KE_when (e, constr, clid) -> KE_when (sort_expr e, constr, clid)
    | KE_switch (e, es) ->
      KE_switch (sort_expr e,
                 List.sort (fun (c1, e1) (c2, e2) -> String.compare c1 c2)
                   (List.map (fun (c, e) -> (c, sort_expr e)) es))
    | KE_merge (id, es) ->
      KE_merge (id,
                List.sort (fun (c1, e1) (c2, e2) -> String.compare c1 c2)
                  (List.map (fun (c, e) -> (c, sort_expr e)) es)) in
  { e with kexpr_desc = desc }

let sort_equation (eq : k_equation) : k_equation =
  { eq with keq_expr = sort_expr eq.keq_expr; }

let sort_instr : p_instr -> p_instr = function
  | Eq eq -> Eq (sort_equation eq)
  | _ -> failwith "TODO sort_instr"

let sort_node (n : p_node) : p_node =
  { n with pn_instrs = List.map sort_instr n.pn_instrs }

let sort_file (f : p_file) : p_file =
    { pf_clocks =
        (List.map
           (fun (c, constrs) -> (c, List.sort String.compare constrs))
           f.pf_clocks);
      pf_nodes = List.map sort_node f.pf_nodes }

(* Transcription                                                              *)

let tr_instr : p_instr -> k_equation = function
  | Eq eq -> eq
  | _ -> invalid_arg "tr_instr"

let tr_node (n : p_node) : k_node =
  { kn_name = n.pn_name;
    kn_input = n.pn_input;
    kn_output = n.pn_output;
    kn_local = n.pn_local;
    kn_equs = List.map tr_instr n.pn_instrs;
    kn_loc = n.pn_loc }

let tr_file (f : p_file) : k_file =
  { kf_clocks = f.pf_clocks;
    kf_nodes = List.map tr_node f.pf_nodes }

(* Conclusion                                                                 *)

let kernelize_file (f : p_file) : k_file =
  f |> sort_file |> tr_file
