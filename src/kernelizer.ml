(** Desugarizer from parsed AST to kernel AST *)

open Asttypes
open PMinils
open Minils
open Clockchecker
open Clockchecker.CPMinils

module CMinils = MINILS(TypeClockAnnot)

(* Sort fields                                                                 *)

let rec sort_expr (e : k_expr) : k_expr =
  let desc = match e.kexpr_desc with
    | KE_const c -> KE_const c
    | KE_ident id -> KE_ident id
    | KE_op (op, es) -> KE_op (op, List.map sort_expr es)
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
                  (List.map (fun (c, e) -> (c, sort_expr e)) es))
    | KE_app (id, es, e) ->
      KE_app (id, List.map sort_expr es, sort_expr e)
  in { e with kexpr_desc = desc }

let sort_equation (eq : k_equation) : k_equation =
  { eq with keq_expr = sort_expr eq.keq_expr; }

let rec sort_instr : p_instr -> p_instr = function
  | Eq eq -> Eq (sort_equation eq)
  | Reset (ins, er) ->
    Reset (List.map sort_instr ins, sort_expr er)
  | _ -> failwith "TODO sort_instr"

let sort_node (n : p_node) : p_node =
  { n with pn_instrs = List.map sort_instr n.pn_instrs }

let sort_file (f : p_file) : p_file =
    { pf_clocks =
        (List.map
           (fun (c, constrs) -> (c, List.sort String.compare constrs))
           f.pf_clocks);
      pf_nodes = List.map sort_node f.pf_nodes }

(* Eliminate reset blocks                                                     *)

let rec reset_expr (x : ident) (e : k_expr) =
  let desc = match e.kexpr_desc with
    | KE_const c -> KE_const c
    | KE_ident id -> KE_ident id
    | KE_op (op, es) -> KE_op (op, List.map (reset_expr x) es)
    | KE_tuple es -> KE_tuple (List.map (reset_expr x) es)
    | KE_when (e, constr, ckid) -> KE_when (reset_expr x e, constr, ckid)
    | KE_switch (e, es) ->
      KE_switch (reset_expr x e,
                 List.map (fun (c, e) -> (c, reset_expr x e)) es)
    | KE_merge (ckid, es) ->
      KE_merge (ckid,
                List.map (fun (c, e) -> (c, reset_expr x e)) es)
    | KE_fby (e0, e1) ->
      KE_switch ({ kexpr_desc = KE_ident x; (* TODO *)
                   kexpr_annot = e.kexpr_annot;
                   kexpr_loc = dummy_loc },
                 [("True", e0); ("False", e)])
    | KE_arrow (e0, e1) ->
      KE_switch ({ kexpr_desc = KE_ident x; (* TODO *)
                   kexpr_annot = e.kexpr_annot;
                   kexpr_loc = dummy_loc },
                 [("True", e0); ("False", e)])
    | KE_app (f, es, er) ->
      KE_app (f, es, { kexpr_desc =
                         KE_op (Op_or, [er;
                                        { kexpr_desc = KE_ident x;
                                          kexpr_annot = er.kexpr_annot;
                                          kexpr_loc = dummy_loc }]);
                       kexpr_annot = e.kexpr_annot;
                       kexpr_loc = dummy_loc })
  in { e with kexpr_desc = desc }

let reset_eq (x : ident) (eq : k_equation) : k_equation =
  { eq with keq_expr = reset_expr x eq.keq_expr }

let rec reset_instr (eq : p_instr) : (p_instr list * ident list) =
  let rec reset_instr' (x : ident) : p_instr -> p_instr = function
    | Eq eq -> Eq (reset_eq x eq)
    | _ -> invalid_arg "reset_instr'" in
  match eq with
  | Eq eq -> ([Eq eq], [])
  | Reset (ins, er) ->
     let (ins', ys) = reset_instrs ins in
     let y = Atom.fresh "$" in
     let ins' = List.map (reset_instr' y) ins' in
     (Eq { keq_patt = { kpatt_desc = KP_ident y; kpatt_loc = dummy_loc };
           keq_expr = er })::ins',
     y::ys
  | _ -> invalid_arg "reset_instr"

and reset_instrs (eqs : p_instr list) =
  List.fold_left (fun (inss1, ys1) ins ->
      let (inss2, ys2) = reset_instr ins in (inss1@inss2, ys1@ys2))
    ([], []) eqs

let reset_node (n : p_node) : p_node =
  let (ins, names) = reset_instrs n.pn_instrs in
  { n with pn_instrs = ins;
           pn_local =
             n.pn_local @ List.map (fun id -> (id, (Tbool, Cbase (* TODO *)))) names }

let reset_file (f : p_file) : p_file =
  { f with pf_nodes = List.map reset_node f.pf_nodes }

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
  f |> reset_file |> sort_file |> tr_file
