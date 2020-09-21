(** Desugarizer from parsed AST to kernel AST *)

open Asttypes
open PMinils
open Minils
open Clockchecker
open Clockchecker.CPMinils

module CMinils = MINILS(TypeClockAnnot)

(** Eliminate reset blocks                                                    *)

let rec reset_expr (x : ident) (ck : clock) (e : k_expr) =
  let desc = match e.kexpr_desc with
    | KE_const c -> KE_const c
    | KE_ident id -> KE_ident id
    | KE_unop (op, e1) -> KE_unop (op, reset_expr x ck e1)
    | KE_binop (op, e1, e2) -> KE_binop (op, reset_expr x ck e1, reset_expr x ck e2)
    | KE_when (e, constr, ckid) -> KE_when (reset_exprs x ck e, constr, ckid)
    | KE_match (e, es) ->
      KE_match (reset_expr x ck e, reset_branches x ck es)
    | KE_merge (ckid, es) ->
      KE_merge (ckid, reset_branches x ck es)
    | KE_fby (e0, e1) ->
      let e0' = reset_exprs x ck e0 and e1' = reset_exprs x ck e1 in
      let fby' = { kexpr_desc = KE_fby (e0', e1' );
                   kexpr_annot = e.kexpr_annot;
                   kexpr_loc = e.kexpr_loc } in
      KE_match ({ kexpr_desc = KE_ident x; (* TODO *)
                  kexpr_annot = e.kexpr_annot;
                  kexpr_loc = dummy_loc },
                [("True", e0'); ("False", [fby'])])
    | KE_arrow (e0, e1) ->
      let e0' = reset_exprs x ck e0 and e1' = reset_exprs x ck e1 in
      let arrow' = { kexpr_desc = KE_arrow (e0', e1' );
                     kexpr_annot = e.kexpr_annot;
                     kexpr_loc = e.kexpr_loc } in
      KE_match ({ kexpr_desc = KE_ident x; (* TODO *)
                  kexpr_annot = e.kexpr_annot;
                  kexpr_loc = dummy_loc },
                [("True", e0); ("False", [arrow'])])
    | KE_app (f, es, er) ->
      let es' = reset_exprs x ck es and er' = reset_expr x ck er in
      KE_app (f, es', { kexpr_desc =
                          KE_binop (Op_or, er',
                                    { kexpr_desc = KE_ident x;
                                      kexpr_annot = er.kexpr_annot;
                                      kexpr_loc = dummy_loc });
                        kexpr_annot = e.kexpr_annot;
                        kexpr_loc = dummy_loc })
  in { e with kexpr_desc = desc }
and reset_exprs (x : ident) (ck : clock) es = List.map (reset_expr x ck) es
and reset_branches (x : ident) (ck : clock) brs =
  List.map (fun (constr, es) -> (constr, reset_exprs x ck es)) brs

let reset_eq (x : ident) (ck : clock) (eq : k_equation) : k_equation =
  { eq with keq_expr = reset_exprs x ck eq.keq_expr }

let rec reset_instr (eq : p_instr) : (p_instr list * (ident * clock) list) =
  let rec reset_instr' (x : ident) (ck : clock) : p_instr -> p_instr = function
    | Eq eq -> Eq (reset_eq x ck eq)
    | _ -> invalid_arg "reset_instr'" in
  match eq with
  | Eq eq -> ([Eq eq], [])
  | Reset (ins, er) ->
    let (ins', ys) = reset_instrs ins in
    let y = Atom.fresh "$" and (_, (ckr, _)) = List.hd er.kexpr_annot in
    let ins' = List.map (reset_instr' y ckr) ins' in
    (Eq { keq_patt = [y]; keq_expr = [er]; keq_loc = dummy_loc })::ins',
    (y, ckr)::ys
  | _ -> invalid_arg "reset_instr"

and reset_instrs (eqs : p_instr list) =
  List.fold_left (fun (inss1, ys1) ins ->
      let (inss2, ys2) = reset_instr ins in (inss1@inss2, ys1@ys2))
    ([], []) eqs

let reset_node (n : p_node) : p_node =
  let (ins, names) = reset_instrs n.pn_instrs in
  { n with pn_instrs = ins;
           pn_local =
             n.pn_local @ List.map (fun (id, ck) -> (id, (Tbool, ck))) names }

let reset_file (f : p_file) : p_file =
  { f with pf_nodes = List.map reset_node f.pf_nodes }

(** Transcription                                                             *)

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

(** Conclusion                                                                *)

let kernelize_file (f : p_file) : k_file =
  f |> reset_file |> tr_file
