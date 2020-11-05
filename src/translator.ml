(** Translate Normalized AST to Object representation *)

open Asttypes
open NMinils
open Obc

type compil_env =
  { m : p; (* memory *)
    si : instr list; (* reset *)
    j : (ident * ident) list; (* instances *)
    d : p; (* local variables *)
    s : instr list; (* step *) }

let translate_ident env id =
  if List.mem_assoc id env.m then StIdent id else Ident id

(** Translate an expression *)
let rec translate_expr env (e : n_expr) : expr =
  match e.nexpr_desc with
  | NE_const c -> Const c
  | NE_ident id -> translate_ident env id
  | NE_op (op, es) ->
    Op (op, List.map (translate_expr env) es)
  | NE_when (e, _, _) -> translate_expr env e

(** Translate a c-expression *)
let rec translate_cexpr tys env (x : ident) (e : n_cexpr) : instr =
  match e.ncexpr_desc with
  | NCE_expr e' ->
    let e'' =
      translate_expr env
        { nexpr_desc = e';
          nexpr_ty = e.ncexpr_ty; nexpr_clock = e.ncexpr_clock } in
    Assign (x, e'')
  | NCE_match (e, es) ->
    Case (translate_expr env e, e.nexpr_ty,
          List.map (fun (c, e) -> c, [translate_cexpr tys env x e]) es)
  | NCE_merge (id, es) ->
    Case (translate_ident env id,
          List.assoc id tys,
          List.map (fun (c, e) -> c, [translate_cexpr tys env x e]) es)

(** Protects the execution of an instruction with a clock *)
let control tys env (ck : clock) (ins : instr) : instr =
  let rec aux ck ins = match ck with
    | Cbase -> ins
    | Con (constr, ckid, ck') ->
      aux ck' (Case (translate_ident env ckid,
                     List.assoc ckid tys, [(constr, [ins])]))
  in aux ck ins

(* Fusion of control structures *)
let fusion clocks instrs =
  let sort = List.sort (fun (c1, _) (c2, _) -> String.compare c1 c2) in

  let rec complete_list constrs brs =
    match constrs, brs with
    | [], [] -> []
    | l1, [] -> List.map (fun c1 -> c1, []) l1
    | [], l2 -> failwith "Should not happen"
    | c1::tl1, (c2, i2)::tl2 when c1 = c2 ->
      (c2, i2)::complete_list tl1 tl2
    | c1::tl1, l2 ->
      (c1, [])::(complete_list tl1 l2)

  and fusion i1 i2 =
    match rec_fusion i1, rec_fusion i2 with
    | Case (x1, ty, is1), Case (x2, _, is2) when x1 = x2 ->
      let constrs = List.sort String.compare (Typechecker.constrs_of_clock clocks dummy_loc ty) in
      let is1 = complete_list constrs (sort is1)
      and is2 = complete_list constrs (sort is2) in
      [Case (x1, ty, List.map2 (fun (c1, i1) (_, i2) ->
           (c1, fusion_list (i1@i2))) is1 is2)]
    | _, _ -> [i1;i2]

  and rec_fusion i =
    (match i with
     | Case (x, ty, is) ->
       Case (x, ty, (List.map (fun (c, ins) -> (c, fusion_list ins)) is))
     | _ -> i)

  and fusion_list instrs =
    match instrs with
    | [] -> []
    | i1::is ->
      (match fusion_list is with
       | [] -> [i1]
       | i2::is -> (fusion i1 i2)@is)
  in fusion_list instrs

(** Translate an equation *)
let translate_eq tys env = function
  | NQ_ident (id, e) ->
    { env with s = env.s@[control tys env e.ncexpr_clock (translate_cexpr tys env id e)]; }
  | NQ_fby (x, c, e, r, ckr) ->
    let e' = translate_expr env e in
    { env with si = (StAssign (x, Const c))::env.si;
               s = env.s@
                   [control tys env ckr
                      (Case
                         (translate_ident env r,
                          List.assoc r tys,
                          [("True"), [StAssign (x, Const c)]]));
                     control tys env e.nexpr_clock (StAssign (x, e'))] }
  | NQ_app (ids, fid, es, r, bck, ckr) ->
    let es' = List.map (translate_expr env) es in
    let o = Atom.fresh ("_"^fid) in
    { env with si = (Reset o)::env.si;
               j = (o, fid)::env.j;
               s = env.s@
                   [control tys env ckr
                      (Case
                         (translate_ident env r,
                          List.assoc r tys,
                          [("True", [Reset o])]));
                    control tys env bck (StepAssign (ids, o, es'))] }

(** Collect the list of variables that need to be stored into memory
    They are the one declared using fby equations *)
let collect_mem env = function
  | NQ_ident _ -> env
  | NQ_fby (x, _, e, _, _) ->
    { env with m = (x, e.nexpr_ty)::env.m;
               d = List.remove_assoc x env.d }
  | NQ_app _ -> env

(** Translate a node *)
let translate_node clocks outputs (n : n_node) : machine =
  let input = List.map (fun (id, (ty, _)) -> (id, ty)) n.nn_input
  and local = List.map (fun (id, (ty, _)) -> (id, ty)) n.nn_local
  and output = List.map (fun (id, (ty, _)) -> (id, ty)) n.nn_output in
  let env = { m = []; si = []; j = []; d = local; s = [] } in
  let env = List.fold_left collect_mem env n.nn_equs in
  let env = List.fold_left (translate_eq (input@local@output)) env n.nn_equs in
  { m_name = n.nn_name;
    m_memory = env.m;
    m_instances = List.map
        (fun (iid, fid) -> (iid, (fid, (List.assoc fid outputs)))) env.j;
    m_reset = env.si;
    m_step = input, output,
             List.sort_uniq (fun (v1, _) (v2, _) -> String.compare v1 v2) env.d,
             fusion clocks
               (List.stable_sort (fun i1 i2 ->
                   let b1 = updates_state i1 and b2 = updates_state i2 in
                   if b1 && not b2 then 1
                   else if not b1 && b2 then -1 else 0) env.s); }

(** Translate the full file *)
let translate_file (f : n_file) =
  let clocks = f.nf_clocks in
  { clocks = clocks;
    machines = List.map
        (translate_node clocks
           (List.map (fun n ->
                (n.nn_name, List.map fst n.nn_output)) f.nf_nodes)) f.nf_nodes }
