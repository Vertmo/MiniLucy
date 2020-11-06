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

and unless_st = exp_st * constr * bool
and until_st = exp_st * constr * bool

and instr_st =
  | StEq of eq_st
  | StLet of (ident * exp_st * instr_st list)
  | StReset of (instr_st list * exp_st)
  | StSwitch of (exp_st * (constr * instr_st list) list * ident)
  | StAutomaton of (ident * (unless_st list * instr_st list * until_st list) Env.t * ident * (ident * bool))

and node_st =
  ident list * ident list * ident list * instr_st list

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
  | Switch (e, brs, (ckid, _)) ->
    StSwitch (expr_init_state nodes e,
              insbrs_init_state nodes brs,
              Option.get ckid)
  | Automaton (brs, (ckid, _, _)) ->
    let (initid, _ ,_ ,_) = List.hd brs in
    StAutomaton
      (initid,
       env_of_list
         (List.map (fun (c, unl, ins, unt) ->
              (c,
               (un_init_state nodes unl,
                instrs_init_state nodes ins,
                un_init_state nodes unt))) brs),
       Option.get ckid,
       (initid, false))
and instrs_init_state nodes =
  List.map (instr_init_state nodes)
and insbrs_init_state nodes =
  List.map (fun (c, instrs) -> (c, instrs_init_state nodes instrs))
and un_init_state nodes = List.map (fun (e, c, b) -> (expr_init_state nodes e, c, b))

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
    let (v, _) = interp_expr env rst e in
    let env' = adds_in_env [id] [hd v] env in
    let (v, e') = interp_expr env' rst e in (* needed because a def could be recursive *)
    let (env'', instrs') = interp_instrs env' rst instrs in
    (* The bound variable should be removed from the env afterwards.
       Typing should garantee that there is no issue (hopefully) *)
    let env''' = Env.remove id env'' in
    (env''', StLet (id, e', instrs'))
  | StReset (instrs, e) ->
    let (v, e') = interp_expr env rst e in
    (match hd v with
     | Val Absent | Val (Present (Bool false)) ->
       let (env', instrs') = interp_instrs env rst instrs in
       env', StReset (instrs', e')
     | Val (Present (Bool true)) ->
       let (env', instrs') = interp_instrs env true instrs in
       env', StReset (instrs', e')
     | _ -> env, StReset (instrs, e)) (* propagation of bottom or type error *)
  | StSwitch (e, brs, ckid) ->
    let (v, e') = interp_expr env rst e in
    (match (hd v) with
     | Val (Present v) when is_constr v ->
       let (env', brs') = interp_brs (Env.add ckid (Present v) env) rst brs v in
       env', StSwitch (e', brs', ckid)
     | v -> env, StSwitch (e', brs, ckid))
  | StAutomaton (initid, brs, autid, (brid, doreset)) ->
    (* Maybe the automaton itself is reset *)
    let (brid, doreset) =
      if rst
      then (initid, true)
      else (brid, doreset) in

    (* First, interpret unless to see if there is a strong preemption *)
    let (unl, ins, unt) = Env.find brid brs in
    let env = Env.add autid (Present (Constr brid)) env in
    let (newbr, unl') = interp_un env (rst||doreset) (brid, doreset) unl in
    let brs = Env.add brid (unl', ins, unt) brs in

    match newbr with
    | None ->
      env, StAutomaton (initid, brs, autid, (brid, doreset))
    | Some (brid, doreset) ->
      (* Now, actually interpret the branch *)
      let (unl, ins, unt) = Env.find brid brs in
      let env = Env.add autid (Present (Constr brid)) env in
      let env, ins' = interp_instrs env (rst||doreset) ins in

      (* Weak preemptions *)
      let (newbr, unt') = interp_un env (rst||doreset) (brid, false) unt in
      let brs = Env.add brid (unl, ins', unt') brs in
      let env = Env.remove autid env in
      match newbr with
      | None -> env, StAutomaton (initid, brs, autid, (brid, doreset))
      | Some (brid, doreset) ->
        env, StAutomaton (initid, brs, autid, (brid, doreset))

and interp_instrs env rst eqs : (env * instr_st list) =
  let (env', instrs') =
    List.fold_left (fun (env, sts) st ->
        let (env', st') = interp_instr env rst st in
        (env', st'::sts)
      ) (env, []) eqs
  in (env', List.rev instrs')

and interp_brs env rst brs constr : (env * (constr * instr_st list) list) =
  let rec aux (env, brs') = function
    | [] -> env, List.rev brs'
    | (c, ins)::tl ->
      if check_constr c (Present constr) then
        let (env', ins') = interp_instrs env rst ins in
        aux (env', (c, ins')::brs') tl
      else aux (env, (c, ins)::brs') tl
  in aux (env, []) brs

and interp_un env rst def un =
  let rec aux = function
    | [] -> (Some def, [])
    | (e, c, b)::tl ->
      let (res, tl') = aux tl in
      let (v, e') = interp_expr env rst e in
      let un' = (e', c, b)::tl' in
      match (bot_or_value_to_bool (hd v)) with
      | None -> (None, un')
      | Some true -> (Some (c, b), un')
      | Some false -> (res, un')
  in aux un

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

let string_of_ins ins =
  Printf.sprintf "(%s)"
    (String.concat ", " (List.map string_of_bottom_or_value ins))

let string_of_ins_outs ins outs =
  Printf.sprintf "%s -> %s"
    (string_of_ins ins) (string_of_ins outs)

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
      then (Printf.eprintf "Error in bisimulation of machine %s:\npnode:%s\nknode:%s\n"
              name (string_of_ins_outs ins pouts) (string_of_ins_outs ins kouts);
            exit 1)
      else aux (n-1) (sp', sk')
  in aux k (initp, initk)

(** Compare all the nodes in p_file and k_file *)
let compare_files (fp : p_file) (fk : k_file) =
  List.iter (fun n -> compare_nodes fp fk n.pn_name 50) fp.pf_nodes
