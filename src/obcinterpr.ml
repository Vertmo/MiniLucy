(* An interpreter for Obc *)

open Common
open Obc
open Interpr

type memory = value Env.t

type instance =
  { st : memory;
    inst : instance Env.t }

type env =
  { inst : instance;
    loc : memory }

type ctx =
  { ms : (ident * machine) list;
    instances : (ident * (ident * ident list)) list }

let env_of_list l = Env.of_seq (List.to_seq l)

let env_add_opt (x : ident) (v : value option) env =
  match v with
  | None -> env
  | Some v -> Env.add x v env

let env_adds_opt (xs : ident list) (vals : value option list) env =
  List.fold_left (fun env (x, v) -> env_add_opt x v env)
    env (List.combine xs vals)

let get_constr = function
  | Constr c -> c
  | Bool true -> ctrue
  | Bool false -> cfalse
  | _ -> invalid_arg "get_constr"

let rec interp_exp env = function
  | Const c -> Some (value_of_const c)
  | Ident id -> Env.find_opt id env.loc
  | StIdent id -> Env.find_opt id env.inst.st
  | Op (op, exps) ->
    let vs = List.map (interp_exp env) exps in
    match vs with
    | [v1] -> Some (apply_unary op (Option.get v1))
    | [v1;v2] -> Some (apply_binary op (Option.get v1) (Option.get v2))
    | _ -> invalid_arg "interp_exp"

let rec interp_instr ctx env = function
  | Assign (id, e) ->
    let v = interp_exp env e in
    { env with loc = env_add_opt id v env.loc }
  | StAssign (id, e) ->
    let v = interp_exp env e in
    { env with inst = { env.inst with st = env_add_opt id v env.inst.st } }
  | Reset id ->
    let (mid, _) = List.assoc id ctx.instances in
    let m = List.assoc mid ctx.ms in
    let inst = Env.find id env.inst.inst in
    let inst' = reset_machine ctx.ms m inst in
    { env with inst = { env.inst with inst = Env.add id inst' env.inst.inst }}
  | StepAssign (idouts, id, es) ->
    let vs = List.map (interp_exp env) es in
    let (mid, _) = List.assoc id ctx.instances in
    let m = List.assoc mid ctx.ms in
    let inst = Env.find id env.inst.inst in
    let (outs, inst') = step_machine ctx.ms m vs inst in
    let loc = env_adds_opt idouts outs env.loc in
    { loc; inst = { env.inst with inst = Env.add id inst' env.inst.inst }}
  | Case (e, _, brs) ->
    let v = Option.get (interp_exp env e) in
    match (List.assoc_opt (get_constr v) brs) with
    | Some instrs -> interp_instrs ctx env instrs
    | None -> env

and interp_instrs ctx env =
  List.fold_left (interp_instr ctx) env

and step_machine ms m (ins : value option list) (inst : instance) =
  let (inp, outp, _, instrs) = m.m_step in
  let ctx = { ms; instances = m.m_instances } in
  let loc = env_adds_opt (List.map fst inp) ins Env.empty in
  let env = { loc; inst } in
  let env' = interp_instrs ctx env instrs in
  let outs = List.map (fun (id, _) -> Env.find_opt id env'.loc) outp in
  outs, env'.inst

and reset_machine ms m (inst : instance) =
  let ctx = { ms; instances = m.m_instances } in
  let env = { loc = Env.empty; inst } in
  (interp_instrs ctx env m.m_reset).inst

let rec init_machine ms (m : machine) : instance =
  let inst = { st = Env.empty;
               inst = env_of_list
                   (List.map (fun (id, (fid, _)) -> (id, init_machine ms (List.assoc fid ms)))
                      m.m_instances)
             } in
  reset_machine ms m inst

(*                          Comparing nodes                                   *)
(* We can compare the execution of our new node with the one from the
   Pinterpreter *)

open Clockchecker.CPMinils
open Pinterpr

let bot_or_value_to_opt = function
  | Val (Present v) -> Some v
  | _ -> None

let opt_value_to_sync_value = function
  | Some v -> Val (Present v)
  | None -> Val Absent

(** Run the p_node and the machine, and compare their outputs and local streams *)
let compare_nodes (fp : p_file) (f : file) (name : ident) k =
  Random.self_init ();
  let nps = List.map (fun n -> (n.pn_name, n)) fp.pf_nodes
  and ms = List.map (fun n -> (n.m_name, n)) f.machines in
  let np = List.assoc name nps and m = List.assoc name ms in
  let initp = node_init_state nps np
  and initm = init_machine ms m in
  let rec aux n (sp, sk) =
    match n with
    | 0 -> ()
    | n ->
      let ins = generate_rd_input fp.pf_clocks np.pn_input in
      let ins' = List.map bot_or_value_to_opt ins in
      let (pouts, sp') = interp_node ins sp
      and (kouts, sk') =
        try step_machine ms m ins' sk
        with e -> (Printf.eprintf "Exception occured during step of machine %s : %s\n"
                     name (Printexc.to_string e);
                  exit 1) in
      let kouts' = List.map opt_value_to_sync_value kouts in
      if pouts <> kouts'
      then (Printf.eprintf "Error in bisimulation of machine %s:\npnode:%s\nmachine:%s\n"
              name (string_of_ins_outs ins pouts) (string_of_ins_outs ins kouts');
            exit 1)
      else aux (n-1) (sp', sk')
  in aux k (initp, initm)

(** Compare all the nodes in p_file and file *)
let compare_files (fp : p_file) (fk : file) =
  List.iter (fun n -> compare_nodes fp fk n.pn_name 50) fp.pf_nodes
