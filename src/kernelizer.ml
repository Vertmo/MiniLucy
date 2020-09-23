(** Desugarizer from parsed AST to kernel AST *)

open Asttypes
open PMinils
open Minils
open Clockchecker
open Clockchecker.CPMinils

module CMinils = MINILS(TypeClockAnnot)


(** alpha-conversion, needed for switch and let compilation                   *)

let alpha_conv id id' x =
  if x = id then id' else x

let rec alpha_conv_ck id id' = function
  | Cbase -> Cbase
  | Con (constr, ckid, ck) ->
    Con (constr, alpha_conv id id' ckid, alpha_conv_ck id id' ck)

let alpha_conv_annot id id' (ty, ck) =
  (ty, alpha_conv_ck id id' ck)

let alpha_conv_nannot id id' (ty, (ck, name)) =
  (ty, (alpha_conv_ck id id' ck,
        match name with
        | None -> None
        | Some x -> Some (alpha_conv id id' x)))

let rec alpha_conv_expr id id' e =
  let desc =
    match e.kexpr_desc with
    | KE_const c -> KE_const c
    | KE_ident x -> KE_ident (alpha_conv id id' x)
    | KE_unop (op, e1) ->
      KE_unop (op, alpha_conv_expr id id' e1)
    | KE_binop (op, e1, e2) ->
      KE_binop (op, alpha_conv_expr id id' e1, alpha_conv_expr id id' e2)
    | KE_fby (e0s, es) ->
      KE_fby (alpha_conv_exprs id id' e0s, alpha_conv_exprs id id' es)
    | KE_arrow (e0s, es) ->
      KE_arrow (alpha_conv_exprs id id' e0s, alpha_conv_exprs id id' es)
    | KE_match (e, brs) ->
      KE_match (alpha_conv_expr id id' e, alpha_conv_branches id id' brs)
    | KE_when (es, constr, x) ->
      KE_when (alpha_conv_exprs id id' es, constr, alpha_conv id id' x)
    | KE_merge (x, brs) ->
      KE_merge (alpha_conv id id' x, alpha_conv_branches id id' brs)
    | KE_app (f, es, er) ->
      KE_app (f, alpha_conv_exprs id id' es, alpha_conv_expr id id' er)
  in { e with kexpr_desc = desc;
              kexpr_annot = List.map (alpha_conv_nannot id id') e.kexpr_annot }
and alpha_conv_exprs id id' =
  List.map (alpha_conv_expr id id')
and alpha_conv_branches id id' =
  List.map (fun (c, es) -> (c, alpha_conv_exprs id id' es))

let alpha_conv_eq id id' eq =
  { eq with keq_patt = List.map (alpha_conv id id') eq.keq_patt;
            keq_expr = alpha_conv_exprs id id' eq.keq_expr }

let rec alpha_conv_instr id id' ins =
  let desc =
    match ins.pinstr_desc with
    | Eq eq -> Eq (alpha_conv_eq id id' eq)
    | Let (x, ann, e, instrs) ->
      Let (alpha_conv id id' x, alpha_conv_annot id id' ann,
           alpha_conv_expr id id' e, alpha_conv_instrs id id' instrs)
    | _ -> invalid_arg "alpha_conv_instr"
  in { ins with pinstr_desc = desc }
and alpha_conv_instrs id id' = List.map (alpha_conv_instr id id')

(** Eliminate reset blocks                                                    *)

let rec reset_expr (x : ident) (ck : clock) (e : k_expr) =
  let desc = match e.kexpr_desc with
    | KE_const c -> KE_const c
    | KE_ident id -> KE_ident id
    | KE_unop (op, e1) -> KE_unop (op, reset_expr x ck e1)
    | KE_binop (op, e1, e2) -> KE_binop (op, reset_expr x ck e1, reset_expr x ck e2)
    | KE_match (e, es) ->
      KE_match (reset_expr x ck e, reset_branches x ck es)
    | KE_when (e, constr, ckid) -> KE_when (reset_exprs x ck e, constr, ckid)
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

let rec reset_instr (ins : p_instr) : p_instr =
  let rec reset_instr' (x : ident) (ck : clock) (ins : p_instr) : p_instr =
    let desc =
      match ins.pinstr_desc with
      | Eq eq -> Eq (reset_eq x ck eq)
      | Let (id, ann, e, instrs) ->
        Let (id, ann, reset_expr x ck e, reset_instrs' x ck instrs)
      | Switch (e, brs, ckid) ->
        Switch (reset_expr x ck e,
                List.map (fun (c, ins) -> (c, List.map (reset_instr' x ck) ins)) brs,
                ckid)
      | _ -> invalid_arg "reset_instr'"
    in { ins with pinstr_desc = desc }
  and reset_instrs' (x : ident) (ck : clock) =
    List.map (reset_instr' x ck) in
  let desc =
    match ins.pinstr_desc with
    | Eq eq -> Eq eq
    | Let (id, ann, e, instrs) ->
      Let (id, ann, e, reset_instrs instrs)
    | Switch (e, brs, ckid) ->
      Switch (e, reset_branches brs, ckid)
    | Reset (instrs, er) ->
      let instrs' = reset_instrs instrs in
      let y = Atom.fresh "$" and (ty, (ckr, _)) = List.hd er.kexpr_annot in
      let instrs' = List.map (reset_instr' y ckr) instrs' in
      Let (y, (ty, ckr), er, instrs')
    | _ -> invalid_arg "reset_instr"
  in { ins with pinstr_desc = desc }
and reset_instrs instrs = List.map reset_instr instrs
and reset_branches brs = List.map (fun (c, ins) -> (c, reset_instrs ins)) brs

let reset_node (n : p_node) : p_node =
  { n with pn_instrs = reset_instrs n.pn_instrs }

let reset_file (f : p_file) : p_file =
  { f with pf_nodes = List.map reset_node f.pf_nodes }

(** Eliminate switch                                                          *)


let rec add_lets ins (lets : (ident * ann * k_expr) list) =
  match lets with
  | [] -> ins
  | (id, ann, e)::tl ->
    let ins' = [{ pinstr_desc = Let (id, ann, e, ins);
                  pinstr_loc = dummy_loc }] in
    add_lets ins' tl

(** Generates the let-bindings necessary to project vars used and defined in a switch block.
    Does not add let-bindings for names defined by the instrs.
    Returns both the new let-binding instr, and a substitution for the vars defined inside *)
let switch_proj (vars : (ident * ann) list) (ck : clock) constr ckid (ins : p_instr list) =
  let vars = List.filter (fun (_, (ty, ck')) -> ck' = ck) vars in
  let nvars = List.map (fun (id, ann) -> (id, (Atom.fresh "$", ann))) vars in
  let defs = defined_of_instrs ins in
  let ndefs = List.map (fun (id, (id', (ty, ck))) -> (id, (id', (ty, (Con (constr, ckid, ck))))))
      (List.filter (fun (id, _) -> List.mem id defs) nvars)
  and tolet = List.filter (fun (id, _) -> not (List.mem id defs)) nvars in
  let ins' = List.fold_left (fun ins (id, (id', _)) -> alpha_conv_instrs id id' ins) ins nvars in
  let ins' = add_lets ins'
      (List.map (fun (id, (id', ((ty, ck) as ann))) ->
           (id', ann, { kexpr_desc = KE_when ([{ kexpr_desc = KE_ident id;
                                                 kexpr_annot = [(ty, (ck, Some id))];
                                                 kexpr_loc = dummy_loc }], constr, ckid);
                        kexpr_annot = [(ty, (Con (constr, ckid, ck), None))];
                        kexpr_loc = dummy_loc })) tolet) in
  ins', ndefs

let mk_merge ty ck ckid (cvars : (constr * ident) list) =
  { kexpr_desc = KE_merge (ckid,
                           List.map (fun (constr, id) ->
                               (constr, [{ kexpr_desc = KE_ident id;
                                           kexpr_annot = [(ty, (Con (constr, ckid, ck), Some id))];
                                           kexpr_loc = dummy_loc }])) cvars);
    kexpr_annot = [(ty, (ck, None))];
    kexpr_loc = dummy_loc }

let rec switch_instr vars (ins : p_instr) : (p_instr list * (ident * ann) list) =
  match ins.pinstr_desc with
  | Eq eq -> [ins], []
  | Let (id, ann, e, instrs) ->
    let (instrs', ys) = switch_instrs vars instrs in
    [{ ins with pinstr_desc = Let (id, ann, e, instrs')}], ys
  | Switch (e, brs, ckid) ->
    let (ty, (ck, _)) = List.hd e.kexpr_annot in
    let ckid = match ckid with Some ckid -> ckid | None -> failwith "Should not happen" in
    let (brs', ys) = switch_branches vars ckid brs in
    let brs' = List.map (fun (c, ins) -> (c, switch_proj vars ck c ckid ins)) brs' in
    let (_, (_, ndefs)) = List.hd brs' in
    let mergeeqs =
      List.map (fun (id, _) ->
          let cvars = List.map (fun (c, (_, ndefs)) -> (c, fst (List.assoc id ndefs))) brs' in
          { pinstr_desc = Eq { keq_patt = [id];
                               keq_expr = [mk_merge ty ck ckid cvars];
                               keq_loc = dummy_loc; };
            pinstr_loc = dummy_loc }
        ) ndefs in
    { pinstr_desc = Eq { keq_patt = [ckid];
                         keq_expr = [e];
                         keq_loc = dummy_loc };
      pinstr_loc = dummy_loc }::mergeeqs@(List.concat (List.map (fun (_, (ins, _)) -> ins) brs')),
    (ckid, (ty, ck))::ys@(List.map snd (List.concat (List.map (fun (_, (_, ndefs)) -> ndefs) brs')))
  | _ -> invalid_arg "switch_instr"
and switch_instrs vars ins =
  let (ins, ys) =
    List.fold_left (fun (inss1, ys1) ins ->
        let (ins', ys2) = switch_instr vars ins in (ins'::inss1, ys1@ys2))
      ([], []) ins in List.concat (List.rev ins), ys
and switch_branches vars ckid brs =
  let (brs, ys) =
    List.fold_left (fun (brss1, ys1) (c, ins) ->
        let (ins', ys2) = switch_instrs
            (List.map (fun (id, (ty, ck)) -> (id, (ty, Con (c, ckid, ck)))) vars) ins
        in ((c, ins')::brss1, ys1@ys2))
      ([], []) brs in List.rev brs, ys


let switch_node (n : p_node) : p_node =
  let (ins, names) = switch_instrs (n.pn_input@n.pn_output@n.pn_local) n.pn_instrs in
  { n with pn_instrs = ins; pn_local = n.pn_local@names }

let switch_file (f : p_file) : p_file =
  { f with pf_nodes = List.map switch_node f.pf_nodes }

(** Eliminate let blocks                                                      *)

(** check if ident appears in expr, eq, instr *)
let rec free_in_expr id e =
  match e.kexpr_desc with
  | KE_const _ -> false
  | KE_ident x -> id = x
  | KE_unop (_, e1) -> free_in_expr id e1
  | KE_binop (_, e1, e2) -> free_in_expr id e1 || free_in_expr id e2
  | KE_fby (e0s, es) -> free_in_exprs id e0s || free_in_exprs id es
  | KE_arrow (e0s, es) -> free_in_exprs id e0s || free_in_exprs id es
  | KE_match (e, brs) -> free_in_expr id e || free_in_branches id brs
  | KE_when (es, _, x) -> free_in_exprs id es || id = x
  | KE_merge (x, brs) -> id = x || free_in_branches id brs
  | KE_app (_, es, er) -> free_in_exprs id es || free_in_expr id er
and free_in_exprs id = List.exists (free_in_expr id)
and free_in_branches id = List.exists (fun (_, es) -> free_in_exprs id es)

let free_in_eq id eq =
  free_in_exprs id eq.keq_expr

let rec free_in_instr id ins =
  match ins.pinstr_desc with
  | Eq eq -> free_in_eq id eq
  | _ -> invalid_arg "free_in_instr"
and free_in_instrs id =
  List.exists (free_in_instr id)

let rec let_instr (ins : p_instr) : (p_instr list * (ident * ann) list) =
  match ins.pinstr_desc with
  | Eq eq -> ([ins], [])
  | Let (id, ann, e, instrs) ->
    let (instrs', ys) = let_instrs instrs in
    if free_in_instrs id instrs' then
      let id' = Atom.fresh "$" in
      ({ pinstr_desc = Eq { keq_patt = [id'];
                            keq_expr = [e];
                            keq_loc = dummy_loc };
         pinstr_loc = dummy_loc}::List.map (alpha_conv_instr id id') instrs',
       (id', ann)::ys)
    else (instrs', ys)
  | _ -> invalid_arg "let_instr"
and let_instrs (ins : p_instr list) =
  List.fold_left (fun (inss1, ys1) ins ->
      let (inss2, ys2) = let_instr ins in (inss1@inss2, ys1@ys2))
    ([], []) ins

let let_node (n : p_node) : p_node =
  let (instrs', names) = let_instrs n.pn_instrs in
  { n with pn_instrs = instrs';
           pn_local = n.pn_local@names }

let let_file (f : p_file) : p_file =
  { f with pf_nodes = List.map let_node f.pf_nodes }

(** Transcription                                                             *)

let tr_instr (ins : p_instr) : k_equation =
  match ins.pinstr_desc with
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
  f |> reset_file |> switch_file |> let_file |> tr_file
