(*                  Coiterative semantics based interpreter                   *)

open Asttypes
open Kernelizer.CMinils

exception InterpreterError of string
exception NotYetCalculated of ident
exception CausalityError of ident

(** Value of the interpreter *)
type value =
  | Int of int | Bool of bool | Real of float
  | Constr of ident

type sync_value =
  | Present of value
  | Absent

let string_of_value = function
  | Int i -> string_of_int i
  | Bool b -> if b then "true" else "false"
  | Real f -> string_of_float f
  | Constr id -> id

let string_of_sync_value = function
  | Absent -> "."
  | Present v -> string_of_value v

(** Association from name to value (inputs and outputs) *)
module IdentMap = Map.Make(String)
type env = sync_value IdentMap.t

(** Node state *)
type state =
  | NoSt
  | StTuple of state * state
  | StFby of (value option) list * state list * state list
  | StArrow of bool list * state list * state list
  | StMatch of state * state list list
  | StWhen of state list
  | StMerge of state list list
  | StApp of node_state * state list * state

and eq_state =
  state list

and node_state =
  eq_state list

(** Instance of a node *)
and instance = ((ident * location) * state)

let value_of_const = function
  | Cbool b -> Bool b
  | Cint i -> Int i
  | Creal r -> Real r
  | Cconstr (c, _) -> Constr c

(** Apply a unary operator *)
let apply_unary op v =
  match (op, v) with
  | Op_not, Bool b -> Bool (not b)
  | Op_not, Int i -> Int (lnot i)
  | Op_sub, Int i -> Int (-i)
  | Op_sub, Real r -> Real (-.r)
  | _,_ -> failwith "Invalid unary op"

let lift_unary op v =
  match v with
  | Absent -> Absent
  | Present v -> Present (apply_unary op v)

(** Apply comparator *)
let apply_comp comp vl vr =
  match comp with
  | Op_eq -> vl = vr
  | Op_neq -> vl <> vr
  | Op_lt -> vl < vr
  | Op_le -> vl <= vr
  | Op_gt -> vl > vr
  | Op_ge -> vl >= vr
  | _ -> invalid_arg "apply_comp"

(** Apply arithmetic operator *)
let apply_arith fint ffloat el er =
  match el, er with
  | Int il, Int ir -> Int (fint il ir)
  | Real fl, Real fr -> Real (ffloat fl fr)
  | _, _ -> invalid_arg "apply_arith"

(** Apply logic operator *)
let apply_logic fbool fint el er =
  match el, er with
  | Bool bl, Bool br -> Bool (fbool bl br)
  | Int il, Int ir -> Int (fint il ir)
  | _, _ -> invalid_arg "apply_logic"

(** Apply a binary operator *)
let apply_binary op v1 v2 =
  match op with
  | Op_add -> apply_arith (+) (+.) v1 v2
  | Op_sub -> apply_arith (-) (-.) v1 v2
  | Op_mul -> apply_arith ( * ) ( *. ) v1 v2
  | Op_div -> apply_arith (/) (/.) v1 v2
  | Op_mod -> apply_arith (mod) (mod_float) v1 v2
  | Op_and -> apply_logic (&&) (land) v1 v2
  | Op_or -> apply_logic (||) (lor) v1 v2
  | Op_xor ->
    apply_logic (fun b1 b2 -> (b1 && not b2 || not b1 && b2)) (lxor) v1 v2
  | Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge ->
    (match v1, v2 with
     | Bool b1, Bool b2 -> Bool (apply_comp op b1 b2)
     | Int i1, Int i2 -> Bool (apply_comp op i1 i2)
     | Real f1, Real f2 -> Bool (apply_comp op f1 f2)
     | _, _ -> invalid_arg "apply_binary")
  | _ -> invalid_arg "apply_binary"

let lift_binary op v1 v2 =
  match (v1, v2) with
  | (Absent, Absent) -> Absent
  | (Present v1, Present v2) ->
    Present (apply_binary op v1 v2)
  | _ -> invalid_arg
           (Printf.sprintf "lift_binary: %s %s %s"
              (string_of_op op) (string_of_sync_value v1) (string_of_sync_value v2))

(** Get the initial state for an expression *)
let rec expr_init_state nodes (e : k_expr) : state =
  let numstreams = List.length e.kexpr_annot in
  match e.kexpr_desc with
  | KE_const c -> NoSt
  | KE_ident x -> NoSt
  | KE_unop (_, e1) -> expr_init_state nodes e1
  | KE_binop (_, e1, e2) ->
    StTuple (expr_init_state nodes e1, expr_init_state nodes e2)
  | KE_fby (e0s, es) ->
    let st0 = exprs_init_state nodes e0s
    and st = exprs_init_state nodes es in
    StFby (List.init numstreams (fun _ -> None), st0, st)
  | KE_arrow (e0s, es) ->
    let st0 = exprs_init_state nodes e0s
    and st = exprs_init_state nodes es in
    StArrow (List.init numstreams (fun _ -> true), st0, st)
  | KE_match (e, brs) ->
    StMatch (expr_init_state nodes e, brs_init_state nodes brs)
  | KE_when (es, _, _) ->
    let sts = exprs_init_state nodes es in
    StWhen sts
  | KE_merge (_, brs) ->
    StMerge (brs_init_state nodes brs)
  | KE_app (f, es, er) ->
    StApp (node_init_state nodes (List.assoc f nodes),
           exprs_init_state nodes es, expr_init_state nodes er)
  | KE_last _ -> invalid_arg "expr_init_state"
and exprs_init_state nodes = List.map (expr_init_state nodes)
and brs_init_state nodes = List.map (fun (_, es) -> exprs_init_state nodes es)

(** Get the initial states for an equation *)
and eq_init_state nodes (e : k_equation) : eq_state =
  exprs_init_state nodes e.keq_expr

(** Get the initial state for a node *)
and node_init_state nodes n : node_state =
  List.map (eq_init_state nodes) n.kn_equs

(** Transition function for nodes (input, st) -> (st, output) *)
type node_trans = sync_value list -> node_state -> (sync_value list * node_state)

let get_val_in_env env id =
  try IdentMap.find id env
  with _ -> raise (NotYetCalculated id)

let get_st_tuple = function
  | StTuple (st1, st2) -> (st1, st2)
  | _ -> invalid_arg "get_st_tuple"

let get_st_fby = function
  | StFby (v0s, st0, st) -> (v0s, st0, st)
  | _ -> invalid_arg "get_st_fby"

let get_st_arrow = function
  | StArrow (bs, st0, st) -> (bs, st0, st)
  | _ -> invalid_arg "get_st_arrow"

let get_st_match = function
  | StMatch (st, stss) -> (st, stss)
  | _ -> invalid_arg "get_st_match"

let get_st_when = function
  | StWhen sts -> sts
  | _ -> invalid_arg "get_st_when"

let get_st_merge = function
  | StMerge stss -> stss
  | _ -> invalid_arg "get_st_merge"

let get_st_app = function
  | StApp (st, sts, str) -> (st, sts, str)
  | _ -> invalid_arg "get_st_app"

let check_constr constr = function
  | Absent -> false
  | Present (Constr c) -> constr = c
  | Present (Bool true) -> constr = "True"
  | Present (Bool false) -> constr = "False"
  | _ -> invalid_arg "check_constr"

let find_branch v n vs =
  let rec aux = function
    | [] -> invalid_arg "find_branch"
    | (c, vs)::tl ->
      if check_constr c v then vs else aux tl
  in match v with
  | Absent -> List.init n (fun _ -> Absent) (* If v is absent, all the values are also absent *)
  | _ -> aux vs

(** Get the values for an expression *)
let rec interp_expr nodes (e : k_expr) : env -> state -> (sync_value list * state) =
  let numstreams = List.length e.kexpr_annot in
  match e.kexpr_desc with
  | KE_const c -> fun _ st -> [Present (value_of_const c)], st
  | KE_ident id -> fun env st -> [get_val_in_env env id], st
  | KE_unop (op, e1) ->
    let tr1 = interp_expr nodes e1 in
    fun env st ->
      let (v1, st') = tr1 env st in
      [lift_unary op (List.hd v1)], st'
  | KE_binop (op, e1, e2) ->
    let tr1 = interp_expr nodes e1
    and tr2 = interp_expr nodes e2 in
    fun env st ->
      let (st1, st2) = get_st_tuple st in
      let (v1, st1') = tr1 env st1 and (v2, st2') = tr2 env st2 in
      [lift_binary op (List.hd v1) (List.hd v2)], StTuple (st1', st2')
  | KE_fby (e0s, es) ->
    let tr0s = interp_exprs nodes e0s in
    fun env st ->
      let (v0s, st0, st) = get_st_fby st in
      let (v0s', st0') = do_interp_exprs env tr0s st0 in
      List.map2 (fun v v0 -> match (v, v0) with
          | Absent, _ -> Absent
          | Present _, Some v -> Present v
          | Present v, _ -> Present v) v0s' v0s,
      StFby (v0s, st0', st)
  | KE_arrow (e0s, es) ->
    let tr0s = interp_exprs nodes e0s
    and trs = interp_exprs nodes es in
    fun env st ->
      let (bs, st0, st) = get_st_arrow st in
      let (v0s', st0') = do_interp_exprs env tr0s st0
      and (vs', st') = do_interp_exprs env trs st in
      List.map2 (fun b (v0, v) -> if b then v0 else v) bs (List.combine v0s' vs'),
      let bs' = List.map2 (fun b v -> match v with Present _ -> false | Absent -> b) bs v0s' in
      StArrow (bs', st0', st')
  | KE_match (e, brs) ->
    let tr = interp_expr nodes e in
    let trs = interp_branches nodes brs in
    fun env st ->
      let (st, stss) = get_st_match st in
      let (v, st') = tr env st
      and (vss', stss') = do_interp_brs env trs stss in
      find_branch (List.hd v) numstreams vss', StMatch (st', stss')
  | KE_when (es, cstr, ckid) ->
    let trs = interp_exprs nodes es in
    fun env st ->
      let sts = get_st_when st in
      let (vs', sts') = do_interp_exprs env trs sts in
      let b = get_val_in_env env ckid in
      List.map (fun v -> if check_constr cstr b then v else Absent) vs', StWhen sts'
  | KE_merge (ckid, brs) ->
    let trs = interp_branches nodes brs in
    fun env st ->
      let stss = get_st_merge st in
      let v = get_val_in_env env ckid
      and (vss', stss') = do_interp_brs env trs stss in
      find_branch v numstreams vss', StMerge stss'
  | KE_app (f, es, er) ->
    let n = List.assoc f nodes in
    let trs = interp_exprs nodes es
    and trr = interp_expr nodes er in
    fun env st ->
      let (st, sts, str) = get_st_app st in
      let (vs, sts') = do_interp_exprs env trs sts
      and (vr, str') = trr env str in
      (* Treat reset *)
      let st = (match vr with
        | [Present (Bool true)] -> node_init_state nodes n
        | _ -> st) in
      (* Only execute the node when at least one input is present *)
      let b = List.exists (fun v -> match v with Present _ -> true | Absent -> false) vs in
      let (vs, st') =
        if b then (interp_node nodes n vs st)
        else (List.map (fun _ -> Absent) e.kexpr_annot, st) in
      vs, StApp (st', sts', str')
  | KE_last _ -> invalid_arg "interp_expr"
and interp_exprs nodes = List.map (interp_expr nodes)
and interp_branches nodes =
  List.map (fun (c, es) -> (c, interp_exprs nodes es))
and do_interp_exprs env trs sts =
  let res = List.map2 (fun tr st -> tr env st) trs sts in
  (List.concat (List.map fst res), List.map snd res)
and do_interp_brs env trs sts =
  let res = List.map2 (fun (c, tr) st ->
      let (vs, st) = do_interp_exprs env tr st in ((c, vs), st)) trs sts in
  (List.map fst res, List.map snd res)

(** Get the values for an equation *)
and interp_eq nodes (e : k_equation) : env -> eq_state -> (env * eq_state) =
  let trans = interp_exprs nodes e.keq_expr in
  fun env st ->
    let (vals, st') = do_interp_exprs env trans st in
    let env' = List.fold_left (fun env (id, v) -> IdentMap.add id v env) env (List.combine e.keq_patt vals) in
    env', st'

(** Update the delays for an expression *)
and next_for_expr nodes (e : k_expr) : env -> state -> state =
  match e.kexpr_desc with
  | KE_const _ -> fun _ st -> st
  | KE_ident _ -> fun _ st -> st
  | KE_unop (_, e1) ->
    next_for_expr nodes e1
  | KE_binop (_, e1, e2) ->
    let n1 = next_for_expr nodes e1
    and n2 = next_for_expr nodes e2 in
    fun env st ->
      let (st1, st2) = get_st_tuple st in
      StTuple (n1 env st1, n2 env st2)
  | KE_fby (e0s, es) ->
    let trs = interp_exprs nodes es
    and n0 = next_for_exprs nodes e0s
    and n = next_for_exprs nodes es in
    fun env st ->
      let (v0s, st0, st) = get_st_fby st in
      let (vs, st') = do_interp_exprs env trs st in
      let st0' = do_next_for_exprs env n0 st0
      and st' = do_next_for_exprs env n st' in
      let v0s' =
        List.map2 (fun v0 v -> match v with
            | Absent -> v0
            | Present v -> Some v) v0s vs in
      StFby (v0s', st0', st')
  | KE_arrow (e0s, es) ->
    let n0 = next_for_exprs nodes e0s
    and n = next_for_exprs nodes es in
    fun env st ->
      let (bs, st0, st) = get_st_arrow st in
      let st0' = do_next_for_exprs env n0 st0
      and st' = do_next_for_exprs env n st in
      StArrow (bs, st0', st')
  | KE_match (e, brs) ->
    let n = next_for_expr nodes e in
    let ns = next_for_branches nodes brs in
    fun env st ->
      let (st, stss) = get_st_match st in
      let st' = n env st
      and stss' = do_next_for_brs env ns stss in
      StMatch (st', stss')
  | KE_when (es, _, _) ->
    let n = next_for_exprs nodes es in
    fun env st ->
      let sts = get_st_when st in
      let sts' = do_next_for_exprs env n sts in
      StWhen sts'
  | KE_merge (ckid, brs) ->
    let ns = next_for_branches nodes brs in
    fun env st ->
      let stss = get_st_merge st in
      let stss' = do_next_for_brs env ns stss in
      StMerge stss'
  | KE_app (_, es, er) ->
    let ns = next_for_exprs nodes es
    and nr = next_for_expr nodes er in
    fun env st ->
      let (st, sts, str) = get_st_app st in
      let sts' = do_next_for_exprs env ns sts
      and str' = nr env str in
      StApp (st, sts', str')
  | KE_last _ -> invalid_arg "next_for_expr"
and next_for_exprs nodes = List.map (next_for_expr nodes)
and next_for_branches nodes = List.map (fun (_, es) -> next_for_exprs nodes es)
and do_next_for_exprs env = List.map2 (fun n st -> n env st)
and do_next_for_brs env = List.map2 (fun n st -> do_next_for_exprs env n st)

(** Update the delays for an equation *)
and next_for_eq nodes (eq : k_equation) : env -> eq_state -> eq_state =
  let nextfuns = List.map (next_for_expr nodes) eq.keq_expr in
  fun env st ->
    List.map2 (fun f st -> f env st) nextfuns st

(** Get the delays for a node *)
and interp_node nodes (n : k_node) : node_trans =
  (* Transition functions for all the equations *)
  let interpfuns = List.map (interp_eq nodes) n.kn_equs
  and nextfuns = List.map (next_for_eq nodes) n.kn_equs in

  fun inputs st ->
    (* Add the inputs to the env *)
    let env = List.fold_left (fun env ((id, _), v) -> IdentMap.add id v env)
        IdentMap.empty (List.combine n.kn_input inputs) in

    (* Give the states to the equations *)
    let interpfuns = List.combine interpfuns st in

    (* Turn the crank until all eqs have been computed.
       Not efficient !
       And incomplete because of the bad causality notion *)
    let rec compute_eqs env =
      let (env', st) =
        List.fold_left (fun (env, sts) (tr, st) ->
            try
              let (env', st') = tr env st in
              env', st'::sts
            with NotYetCalculated _ -> (env, sts)
          ) (env, []) interpfuns
      in if IdentMap.cardinal env' = List.length (n.kn_input@n.kn_local@n.kn_output)
      then (env', List.rev st)
      else if env' = env
      then raise (CausalityError n.kn_name)
      else compute_eqs env'
    in
    let (env, st') = compute_eqs env in
    let nextfuns = List.combine nextfuns st' in
    let st' = List.map (fun (tr, st) -> tr env st) nextfuns in
    List.map (fun (id, _) -> IdentMap.find id env) n.kn_output, st'

(*                          Running the interpreter                          *)

(** Create random inputs of the right type for a node
    TODO : correctly generate clocked inputs *)
let generate_rd_input (cls : Asttypes.clockdec list) (n : k_node) =
  List.map (fun (_, (ty, _)) ->
      match ty with
      | Tint -> Present (Int (Random.int 100))
      | Treal -> Present (Real (Random.float 100.))
      | Tbool -> Present(Bool (Random.bool ()))
      | Tclock id ->
        let constrs = List.assoc id cls in
        let n = List.length constrs in
        Present (Constr (List.nth constrs (Random.int n)))
    ) n.kn_input

(** Run a node, for testing purposes *)
let run_node (f : k_file) (name : ident) k =
  Random.self_init ();
  let ns = List.map (fun n -> (n.kn_name, n)) f.kf_nodes in
  let node = List.assoc name ns in
  let init = node_init_state ns node in
  let trans = interp_node ns node in
  let rec aux n st vs =
    match n with
    | 0 -> vs
    | n ->
      let ins = generate_rd_input f.kf_clocks node in
      let (outs, st') = trans ins st in
      let vs' = List.fold_left
          (fun vs ((id, _), v) ->
             IdentMap.update id (fun vs -> match vs with
                 | None -> Some [v]
                 | Some vs -> Some (v::vs)) vs)
          vs (List.combine (node.kn_input@node.kn_output) (ins@outs)) in
      aux (n-1) st' vs'
  in
  let vs = (aux k init (IdentMap.empty)) in
  print_endline (Printf.sprintf "First %d iterations:" k);
  IdentMap.iter (fun id vs ->
      print_endline (Printf.sprintf "(%s, [%s])"
                       id (String.concat ";"
                             (List.map string_of_sync_value (List.rev vs))))) vs

let run_file (f : k_file) =
  List.iter (fun n -> run_node f n.kn_name 10) f.kf_nodes
