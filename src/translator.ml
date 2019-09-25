(** Translate Normalized AST to Object representation *)

open Asttypes
open NMinils
open Obc

type compil_env =
  { m : p;
    si : instr list; (* reset *)
    j : (ident * ident) list;
    d : p;
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
  | NCE_merge (id, e1, e2) ->
    Case (id, [translate_cexpr env x e1], [translate_cexpr env x e2])

(** Protects the execution of an instruction with a clock *)
let rec control (cl : clock) (ins : instr) : instr =
  match cl with
  | Base -> ins
  | Cl (cl', clid) -> Case (clid, [control cl' ins], [])
  | NotCl (cl', clid) -> Case (clid, [], [control cl' ins])
  | Ctuple _ -> invalid_arg "control"

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
                   (control cl (Case (everid, [Reset o], [])))::env.s }

(** Translate a node *)
let translate_node (n : n_node) : machine =
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
    m_instances = env.j;
    m_reset = env.si;
    m_step = input, output,
             List.sort_uniq (fun (v1, _) (v2, _) -> String.compare v1 v2) env.d,
             List.rev env.s; }

(** Translate the full file *)
let translate_file (f : n_file) =
  List.map translate_node f

(*                           Check equivalence between ASTs                    *)
(* TODO *)
