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

(** Translate an expression *)
let rec translate_expr env (e : n_expr) : expr =
  match e.nexpr_desc with
  | NE_const c -> Const c
  | NE_ident id ->
    if List.mem_assoc id env.m then StIdent id else Ident id
  | NE_op (op, es) ->
    Op (op, List.map (translate_expr env) es)
  | NE_when (e, _, _) -> translate_expr env e

(** Translate a c-expression, and adds some local variables *)
let rec translate_cexpr env (x : ident) (e : n_cexpr) : instr =
  match e.ncexpr_desc with
  | NCE_expr e' ->
    let e'' =
      translate_expr env
        { nexpr_desc = e';
          nexpr_ty = e.ncexpr_ty; nexpr_clock = e.ncexpr_clock } in
    Assign (x, e'')
  | NCE_merge (id, es) ->
    Case (id, List.map (fun (c, e) -> c, [translate_cexpr env x e]) es)

(** Protects the execution of an instruction with a clock *)
let rec control (cl : clock) (ins : instr) : instr =
  match cl with
  | Base -> ins
  | Cl (cl', constr, clid) ->
    Case (clid, [constr, [control cl' ins]])
  | Ctuple _ -> invalid_arg "control"

(* Join the control structures *)
let rec join i1 i2 =
  let rec align_lists l1 l2 =
    match l1, l2 with
    | [], [] -> [], []
    | l1, [] -> l1, List.map (fun (c1, _) -> c1, []) l1
    | [], l2 -> List.map (fun (c2, _) -> c2, []) l2, l2
    | (c1, i1)::tl1, (c2, i2)::tl2 ->
      if c1 = c2 then let (l1, l2) = align_lists tl1 tl2 in
        (c1, i1)::l1, (c2, i2)::l2
      else if c1 < c2 then let (l1, l2) = align_lists tl1 ((c2, i2)::tl2) in
        (c1, i1)::l1, (c1, [])::l2
      else let (l1, l2) = align_lists ((c1, i1)::tl1) tl2 in
        (c2, [])::l1, (c2, i2)::l2 in
  match i1, i2 with
  | Case (x1, is1), Case (x2, is2) when x1 = x2 ->
    let is1, is2 = align_lists is1 is2 in
    [Case (x1, List.map2 (fun (c1, i1) (_, i2) ->
         (c1, join_list i1@i2)) is1 is2)]
  | _, _ -> [i1;i2]
and join_list instrs =
  match instrs with
  | [] -> []
  | i1::is ->
    (match join_list is with
     | [] -> [i1]
     | i2::is -> (join i1 i2)@is)

(** Translate an equation *)
let translate_eq env = function
  | NQ_ident (id, e) ->
    { env with s = (control e.ncexpr_clock (translate_cexpr env id e))::env.s; }
  | NQ_fby (x, c, e) ->
    let e' = translate_expr env e in
    { env with m = (x, e.nexpr_ty)::env.m;
               d = List.remove_assoc x env.d;
               si = (StAssign (x, Const c))::env.si;
               s = (control e.nexpr_clock (StAssign (x, e')))::env.s}
  | NQ_app (ids, fid, es, everid, cl) ->
    let es' = List.map (translate_expr env) es in
    let o = Atom.fresh ("_"^fid) in
    { env with si = (Reset o)::env.si;
               j = (o, fid)::env.j;
               s = (control cl (StepAssign (ids, o, es')))::
                   (control cl (Case (everid, [("True", [Reset o])])))::env.s }

(** Translate a node *)
let translate_node outputs (n : n_node) : machine =
  let input = List.map (fun (id, ty) -> id, base_ty_of_ty ty) n.nn_input
  and local = List.map (fun (id, ty) -> id, base_ty_of_ty ty) n.nn_local
  and output = List.map (fun (id, ty) -> id, base_ty_of_ty ty) n.nn_output in
  let env = List.fold_left translate_eq {
      m = []; si = []; j = [];
      d = local;
      s = []
    } n.nn_equs in
  { m_name = n.nn_name;
    m_memory = env.m;
    m_instances = List.map
        (fun (iid, fid) -> (iid, (fid, (List.assoc fid outputs)))) env.j;
    m_reset = env.si;
    m_step = input, output,
             List.sort_uniq (fun (v1, _) (v2, _) -> String.compare v1 v2) env.d,
             join_list
               (List.stable_sort (fun i1 i2 ->
                   let b1 = assign_state i1 and b2 = assign_state i2 in
                   if b1 && not b2 then 1
                   else if not b1 && b2 then -1 else 0) (List.rev env.s)); }

(** Translate the full file *)
let translate_file (f : n_file) =
  let clocks = f.nf_clocks in
  { clocks = clocks;
    machines = List.map
        (translate_node
           (List.map (fun n ->
                (n.nn_name, List.map fst n.nn_output)) f.nf_nodes)) f.nf_nodes }

(*                           Check equivalence between ASTs                    *)
(* TODO *)
