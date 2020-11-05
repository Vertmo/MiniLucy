(*                  Coiterative semantics based interpreter                   *)

open Asttypes
open Interpr
open Clockchecker.CPMinils

(** Node state *)
type exp_st =
  | StConst of const
  | StIdent of ident
  | StUnop of op * exp_st
  | StBinop of op * exp_st * exp_st
  | StFby of exp_st list * exp_st list * exp_st * (value option) list
  | StArrow of exp_st list * exp_st list * exp_st * bool list
  | StMatch of exp_st * (ident * exp_st list) list
  | StWhen of exp_st list * constr * ident
  | StMerge of ident * (ident * exp_st list) list
  | StApp of node_st * exp_st list * exp_st * node_st

and eq_st =
  ident list * exp_st list

and instr_st =
  | StEq of eq_st
  | StLet of (ident * exp_st * instr_st list)
  | StReset of (instr_st list * exp_st)
  (* TODO *)

and node_st =
  ident list * ident list * ident list * instr_st list

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
  | Val v ->
    Val (match v with
        | Absent -> Absent
        | Present v -> Present (apply_unary op v))
  | _ -> Bottom

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
  | Val v1, Val v2 ->
    Val (match (v1, v2) with
        | (Absent, Absent) -> Absent
        | (Present v1, Present v2) ->
          Present (apply_binary op v1 v2)
        | _ -> invalid_arg
                 (Printf.sprintf "lift_binary: %s %s %s"
                    (string_of_op op) (string_of_sync_value v1) (string_of_sync_value v2)))
  | _ -> Bottom

(** Get the initial state for an expression *)
let rec expr_init_state nodes (e : k_expr) : exp_st =
  let numstreams = List.length e.kexpr_annot in
  match e.kexpr_desc with
  | KE_const c -> StConst c
  | KE_ident x -> StIdent x
  | KE_unop (op, e1) -> StUnop (op, expr_init_state nodes e1)
  | KE_binop (op, e1, e2) ->
    StBinop (op, expr_init_state nodes e1, expr_init_state nodes e2)
  | KE_fby (e0s, es, er) ->
    let st0 = exprs_init_state nodes e0s
    and st = exprs_init_state nodes es
    and str = expr_init_state nodes er in
    StFby (st0, st, str, List.init numstreams (fun _ -> None))
  | KE_arrow (e0s, es, er) ->
    let st0 = exprs_init_state nodes e0s
    and st = exprs_init_state nodes es
    and str = expr_init_state nodes er in
    StArrow (st0, st, str, List.init numstreams (fun _ -> true))
  | KE_match (e, brs) ->
    StMatch (expr_init_state nodes e, brs_init_state nodes brs)
  | KE_when (es, cons, id) ->
    let sts = exprs_init_state nodes es in
    StWhen (sts, cons, id)
  | KE_merge (id, brs) ->
    StMerge (id, brs_init_state nodes brs)
  | KE_app (f, es, er) ->
    let init = node_init_state nodes (List.assoc f nodes) in
    StApp (init,
           exprs_init_state nodes es, expr_init_state nodes er,
           init)
  | KE_last _ -> invalid_arg "expr_init_state"
and exprs_init_state nodes = List.map (expr_init_state nodes)
and brs_init_state nodes = List.map (fun (id, es) -> (id, exprs_init_state nodes es))

(** Get the initial states for an equation *)
and eq_init_state nodes (e : k_equation) : eq_st =
  (e.keq_patt, exprs_init_state nodes e.keq_expr)

and instr_init_state nodes (ins : p_instr) : instr_st =
  match ins.pinstr_desc with
  | Eq eq -> StEq (eq_init_state nodes eq)
  | Let (id, _, e, instrs) ->
    StLet (id, expr_init_state nodes e, instrs_init_state nodes instrs)
  | Reset (instrs, e) ->
    StReset (instrs_init_state nodes instrs, expr_init_state nodes e)
  | _ -> failwith "TODO"
and instrs_init_state nodes =
  List.map (instr_init_state nodes)

(** Get the initial state for a node *)
and node_init_state nodes (n : p_node) : node_st =
  let ins = instrs_init_state nodes n.pn_instrs in
  (List.map fst n.pn_input, List.map fst n.pn_output, List.map (fun (id, _, _) -> id) n.pn_local, ins)

let check_constr constr = function
  | Absent -> false
  | Present (Constr c) -> constr = c
  | Present (Bool true) -> constr = "True"
  | Present (Bool false) -> constr = "False"
  | _ -> invalid_arg "check_constr"

let find_branch v n vs =
  match v with
  | Bottom -> List.init n (fun _ -> Bottom)
  | Val v ->
    let rec aux = function
      | [] -> invalid_arg "find_branch"
      | (c, vs)::tl ->
        if check_constr c v then vs else aux tl
    in match v with
    | Absent -> List.init n (fun _ -> Val Absent) (* If v is absent, all the values are also absent *)
    | _ -> aux vs

let rec extract_vals vs =
  match vs with
  | [] -> Some []
  | Val v::tl ->
    Option.bind (extract_vals tl) (fun vs -> Some (v::vs))
  | Bottom::_ -> None

let hd l =
  match l with
  | hd::_ -> hd
  | _ -> Bottom

(** Get the values for an expression *)
let rec interp_expr env rst st : (bottom_or_value list * exp_st) =
  let interp_expr = interp_expr env rst
  and interp_exprs = interp_exprs env rst
  and interp_branches = interp_branches env rst in
  match st with
  | StConst c -> [Val (Present (value_of_const c))], StConst c
  | StIdent id -> [get_val_in_env env id], st
  | StUnop (op, e1) ->
    let (v1, e1') = interp_expr e1 in
    [lift_unary op (hd v1)], StUnop (op, e1')
  | StBinop (op, e1, e2) ->
    let (v1, e1') = interp_expr e1
    and (v2, e2') = interp_expr e2 in
    [lift_binary op (hd v1) (hd v2)], StBinop (op, e1', e2')
  | StFby (e0s, e1s, er, vps) ->
    let (v0s, e0s') = interp_exprs e0s
    and (v1s, e1s') = interp_exprs e1s
    and (r, er') = interp_expr er in
    (match (bot_or_value_to_bool (hd r)) with
     | None -> List.map (fun _ -> Bottom) vps, StFby (e0s', e1s', er', vps)
     | Some r ->
       (* reset fbys *)
       let vps = List.map (fun v -> if r || rst then None else v) vps in
       let vs =
         List.map2 (fun v0 vp -> match (v0, vp) with
             | Bottom, _ -> Bottom
             | Val Absent, _ -> Val Absent
             | Val Present _, Some v -> Val (Present v)
             | Val Present v, _ -> Val (Present v)) v0s vps
       and vps' =
         List.map2 (fun v1 vp -> match v1 with
             | Bottom | Val Absent -> vp
            | Val Present v -> Some v) v1s vps in
       vs, StFby (e0s', e1s', er', vps'))
  | StArrow (e0s, e1s, er, bs) ->
    let (v0s, e0s') = interp_exprs e0s
    and (v1s, e1s') = interp_exprs e1s
    and (r, er') = interp_expr er in
    (match (bot_or_value_to_bool (hd r)) with
     | None -> List.map (fun _ -> Bottom) bs, StArrow (e0s', e1s', er', bs)
     | Some r ->
       let bs = List.map (fun v -> if r || rst then true else v) bs in
       let vs = List.map2 (fun b (v0, v) -> if b then v0 else v) bs (List.combine v0s v1s)
       and bs' = List.map2 (fun b v -> match v with | Val (Present _) -> false | _ -> b) bs v0s in
       vs, StArrow (e0s', e1s', er', bs'))
  | StMatch (e, brs) ->
    let (v, e') = interp_expr e
    and (vss, brs') = interp_branches brs in
    let numstreams = List.length (snd (List.hd vss)) in
    find_branch (List.hd v) numstreams vss, StMatch (e', brs')
  | StWhen (es, cstr, ckid) ->
    let (vs, es') = interp_exprs es in
    let b = get_val_in_env env ckid in
    List.map (fun v ->
        match b with
        | Bottom -> Bottom
        | Val b -> if check_constr cstr b then v else Val Absent) vs, StWhen (es', cstr, ckid)
  | StMerge (ckid, brs) ->
    let v = get_val_in_env env ckid
    and (vss, brs') = interp_branches brs in
    let numstreams = List.length (snd (List.hd vss)) in
    find_branch v numstreams vss, StMerge (ckid, brs')
  | StApp (init_st, es, er, st) ->
    let (xs, es') = interp_exprs es
    and (r, er') = interp_expr er in
    let numstreams = List.length (match st with (_, outs, _, _) -> outs) in
    match (bot_or_value_to_bool (hd r)) with (* reset must be calculated for us to compute the node *)
    | None -> (List.init numstreams (fun _ -> Bottom), StApp (init_st, es', er', st))
    | Some b ->
      (* Treat reset *)
      let st' = if b || rst then init_st else st in
      (* Only execute the node when at least one input is present *)
      let b = List.exists (fun v -> match v with Val (Present _) -> true | _ -> false) xs in
      let (ys, st'') =
        if b then (interp_node xs st')
        else (List.init numstreams (fun _ -> Val Absent), st') in
      ys, StApp (init_st, es', er', st'')
and interp_exprs env rst es =
  let vst = List.map (interp_expr env rst) es in
  List.concat (List.map fst vst), List.map snd vst
and interp_branches env rst brs =
  let brs = List.map (fun (c, es) ->
      let (vs, es') = interp_exprs env rst es in
      (c, vs), (c, es')) brs in
  List.map fst brs, List.map snd brs

(** Get the values for an equation *)
and interp_eq env rst (xs, es) : (env * eq_st) =
  let (vals, es') = interp_exprs env rst es in
  let env' = adds_in_env xs vals env in
  env', (xs, es')

and interp_instr env rst ins : (env * instr_st) =
  match ins with
  | StEq eq ->
    let (env', eq') = interp_eq env rst eq in
    env', StEq eq'
  | StLet (id, e, instrs) ->
    let (v, e') = interp_expr env rst e in
    let env' = adds_in_env [id] [hd v] env in
    let (env'', instrs') = interp_instrs env' rst instrs in
    (* The bound variable should be removed from the env afterwards.
       Typing should garantee that there is no issue (hopefully) *)
    let env''' = Env.remove id env'' in
    (env''', StLet (id, e', instrs'))
  | StReset (instrs, e) ->
    let (v, e') = interp_expr env rst e in
    match hd v with
    | Val Absent | Val (Present (Bool false)) ->
      let (env', instrs') = interp_instrs env rst instrs in
      env', StReset (instrs', e')
    | Val (Present (Bool true)) ->
      let (env', instrs') = interp_instrs env true instrs in
      env', StReset (instrs', e')
    | _ -> env, StReset (instrs, e) (* propagation of bottom or type error *)

and interp_instrs env rst eqs : (env * instr_st list) =
  let (env', instrs') =
    List.fold_left (fun (env, sts) st ->
        let (env', st') = interp_instr env rst st in
        (env', st'::sts)
      ) (env, []) eqs
  in (env', List.rev instrs')

(** Get the delays for a node *)
and interp_node xs (st : node_st) : (bottom_or_value list * node_st) =
  let (ins, outs, locs, instrs) = st in
  (* Add the inputs to the env *)
  let env = adds_in_env ins xs Env.empty in

  (* Turn the crank until the env is filled, or we cant progress anymore
     Not efficient ! *)
  let rec compute_instrs env =
    let (env', instrs') = interp_instrs env false instrs in
    if Env.cardinal env' = List.length (ins@locs@outs)
    then interp_instrs env' false instrs
    else if env' = env
    then (env', instrs')
    else compute_instrs env'
  in
  let (env, eqs') = compute_instrs env in
  List.map (fun id -> get_val_in_env env id) outs,
  (ins, outs, locs, eqs')

(*                          Running the interpreter                          *)

(** Run a node, for testing purposes *)
let run_node (f : p_file) (name : ident) k =
  Random.self_init ();
  let ns = List.map (fun n -> (n.pn_name, n)) f.pf_nodes in
  let node = List.assoc name ns in
  let init = node_init_state ns node in
  let rec aux n st vs =
    match n with
    | 0 -> vs
    | n ->
      let ins = generate_rd_input f.pf_clocks node.pn_input in
      let (outs, st') = interp_node ins st in
      let vs' = List.fold_left
          (fun vs ((id, _), v) ->
             Env.update id (fun vs -> match vs with
                 | None -> Some [v]
                 | Some vs -> Some (v::vs)) vs)
          vs (List.combine (node.pn_input@node.pn_output) (ins@outs)) in
      aux (n-1) st' vs'
  in
  let vs = (aux k init (Env.empty)) in
  print_endline (Printf.sprintf "First %d iterations:" k);
  Env.iter (fun id vs ->
      print_endline (Printf.sprintf "(%s, [%s])"
                       id (String.concat ";"
                             (List.map string_of_bottom_or_value (List.rev vs))))) vs

(*                          Comparing nodes                                   *)

open Kernelizer.CMinils

(** Run the p_node and the k_node, and compare their outputs and local streams *)
let compare_nodes (fp : p_file) (fk : k_file) (name : ident) k =
  Random.self_init ();
  let nps = List.map (fun n -> (n.pn_name, n)) fp.pf_nodes
  and nks = List.map (fun n -> (n.kn_name, n)) fk.kf_nodes in
  let np = List.assoc name nps and nk = List.assoc name nks in
  let initp = node_init_state nps np
  and initk = Interpr.node_init_state nks nk in
  let rec aux n (sp, sk) =
    match n with
    | 0 -> ()
    | n ->
      let ins = generate_rd_input fp.pf_clocks np.pn_input in
      let (pouts, sp') = interp_node ins sp
      and (kouts, sk') = Interpr.interp_node ins sk in
      if pouts <> kouts
      then (Printf.eprintf "Error in bisimulation of node %s\n" name; exit 1)
      else aux (n-1) (sp', sk')
  in aux k (initp, initk)

(** Compare all the nodes in p_file and k_file *)
let compare_files (fp : p_file) (fk : k_file) =
  List.iter (fun n -> compare_nodes fp fk n.pn_name 20) fp.pf_nodes
