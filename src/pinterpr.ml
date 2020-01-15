(*             Stream based interpreter for automata language                *)

open Asttypes
open Minils.KMinils
open PMinils
open Interpr

exception InterpreterError of string
exception CausalityError of ident
exception StreamError of ident * string

(** Used to store the state of automatons
    current state, should reset, (state id, local bindings, recursive trees) for every state *)
type auto_state =
  Node of (constr * (bool * ((constr * (assoc_str * auto_state)) list))) list

(** Node state *)
type state = St of assoc_str * instance list * auto_state

(** Instance of a node *)
and instance = ((ident * location) * state)

(** Get the initial state for an instances in an expression *)
let rec expr_init_instances nodes (e : p_expr) : instance list =
  match e.pexpr_desc with
  | PE_const c -> [] | PE_ident x -> []
  | PE_op (op, es) ->
    let is = List.map (expr_init_instances nodes) es in
    List.flatten is
  | PE_app (fid, es, e) ->
    let is = List.map (expr_init_instances nodes) es
    and ie = expr_init_instances nodes e in
    let n = List.assoc fid nodes in
    let st = get_node_init nodes n in
    (((fid, e.pexpr_loc), st)::ie@(List.concat is))
  | PE_fby (_, e) -> expr_init_instances nodes e
  | PE_arrow (e1, e2) ->
    (expr_init_instances nodes e1)@(expr_init_instances nodes e2)
  | PE_pre e -> expr_init_instances nodes e
  | PE_tuple es ->
    let is = List.map (expr_init_instances nodes) es in
    List.flatten is
  | PE_when (e, _, _) -> expr_init_instances nodes e
  | PE_merge (clid, brs) ->
    List.flatten (List.map (fun (_, e) -> expr_init_instances nodes e) brs)

(** Get the initial states for an equation *)
and get_eq_init nodes (e : p_equation) : (assoc_str * instance list) =
  let is = expr_init_instances nodes e.peq_expr in
  match e.peq_patt.ppatt_desc with
  | PP_ident id -> [(id, [])], is
  | PP_tuple ids -> List.map (fun id -> (id, [])) ids, is

(** Get the initial state for an instruction *)
and get_instr_init nodes i : (assoc_str * instance list * auto_state) =
  match i with
  | Eq eq ->
    let (strs, is) = get_eq_init nodes eq in (strs, is, Node [])
  | Automaton brs ->
    let brs' = List.map (fun (id, lets, instrs, untils) ->
        let vis = List.map (get_instr_init nodes) instrs in
        let vs = List.flatten (List.map (fun (v, _, _) -> v) vis)
        and is = List.flatten (List.map (fun (_, i, _) -> i) vis)
        and ils = List.flatten
            (List.map (fun (_, _, e) -> expr_init_instances nodes e) lets)
        and ius = List.flatten
            (List.map (fun (e, _, _) -> expr_init_instances nodes e) untils)
        and sts = Node (List.flatten
                         (List.map (fun (_, _, Node brs) -> brs) vis)) in
        vs, is@ils@ius, (id, (List.map (fun (id, _, _) -> (id, [])) lets, sts))
      ) brs in
    let strs = List.flatten (List.map (fun (strs, _, _) -> strs) brs')
    and is = List.flatten (List.map (fun (_, is, _) -> is) brs')
    and auts = List.map (fun (_, _, aut) -> aut) brs' in
    strs, is, Node [List.hd (List.map fst auts), (true, auts)]

(** Get the initial state for a node *)
and get_node_init nodes n : state =
  let vis = List.map (get_instr_init nodes) n.pn_instrs in
  let vs = List.sort_uniq (fun (id1, _) (id2, _) -> String.compare id1 id2)
      (List.flatten (List.map (fun (v, _, _) -> v) vis))
  and is = List.flatten (List.map (fun (_, i, _) -> i) vis)
  and st = Node (List.flatten (List.map (fun (_, _, Node brs) -> brs) vis)) in
  St (vs, is, st)

(** Get the instances used in an expression *)
let rec get_instances insts (e : p_expr) =
  match e.pexpr_desc with
  | PE_const _ -> []
  | PE_ident _ -> []
  | PE_op (op, es) ->
    List.flatten (List.map (get_instances insts) es)
  | PE_app (fid, es, e) ->
    let is = List.flatten (List.map (get_instances insts) es)
    and i = get_instances insts e in
    ((fid, e.pexpr_loc),
     (List.assoc (fid, e.pexpr_loc) insts))::i@is
  | PE_fby (_, e) -> get_instances insts e
  | PE_arrow (e1, e2) ->
    (get_instances insts e1)@(get_instances insts e2)
  | PE_pre e -> get_instances insts e
  | PE_tuple es ->
    List.flatten (List.map (get_instances insts) es)
  | PE_when (e, _, _) -> get_instances insts e
  | PE_merge (_, brs) ->
    List.flatten (List.map (fun (_, e) -> get_instances insts e) brs)

type trans_expr = state -> int -> (value * instance list)
type trans_node = (assoc * state) -> (state * assoc)

(** Replace a term with another one in an association list *)
let replace_assoc k l r = (k, r)::(List.remove_assoc k l)

(** Get the transition function for an expression *)
let rec get_expr_trans nodes fbys (e : p_expr) : trans_expr =
  match e.pexpr_desc with
  | PE_const c -> fun _ _ -> value_of_const c, []
  | PE_ident id ->
    (fun (St (strs, _, _)) _ ->
       let str = List.assoc id strs in
       match try List.nth str fbys with _ -> List.hd str with
       | Bottom -> raise (NotYetCalculated id)
       | v -> v, [])
  | PE_op (op, es) ->
    let ts = List.map (get_expr_trans nodes fbys) es in
    fun cont tocalc ->
      let vis = List.map (fun t -> t cont tocalc) ts in
      let vs = List.map fst vis and is = List.map snd vis in
      apply_op op vs, (List.flatten is)
  | PE_app (fid, es, e) ->
    let ts = List.map (get_expr_trans nodes fbys) es in
    let te = get_expr_trans nodes fbys e in
    let n = List.assoc fid nodes in
    fun st tocalc ->
      let vis = List.map (fun t -> t st tocalc) ts
      and (ve, ie) = te st tocalc in
      let vs = List.map fst vis and is = List.map snd vis in
      let inputs = List.map2 (fun (id, _) v -> id, v) n.pn_input vs in
      let (st, outs) = (match ve with
          | Bool true ->
            let init = get_node_init nodes n in
            get_node_trans nodes n (inputs, init)
          | _ ->
            let st = List.assoc (fid, e.pexpr_loc)
                (match st with St (_, ins, _) -> ins) in
            get_node_trans nodes n (inputs, st)) in
      let St (strs, _, _) = st in
      (match outs with
       | [(_, v)] -> v
       | vs -> (Tuple (List.map snd vs))),
      (((fid, e.pexpr_loc), st)::ie@(List.concat is))
  | PE_fby (c, e) ->
    let t = get_expr_trans nodes (fbys+1) e in
    fun st tocalc -> if tocalc <= fbys
      then (value_of_const c), get_instances (match st with St (_, i, _) -> i) e
      else t st tocalc
  | PE_arrow (e1, e2) ->
    let t1 = get_expr_trans nodes fbys e1
    and t2 = get_expr_trans nodes fbys e2 in
    fun st tocalc -> if tocalc <= fbys
      then let (strs, i) = (t1 st tocalc) in
        (strs, i@(get_instances (match st with St (_, i, _) -> i) e2))
      else let (strs, i) = (t2 st tocalc) in
        (strs, i@(get_instances (match st with St (_, i, _) -> i) e1))
  | PE_pre e ->
    let t = get_expr_trans nodes (fbys+1) e in
    fun st tocalc -> if tocalc <= fbys
      then Nil, get_instances (match st with St (_, i, _) -> i) e
      else t st tocalc
  | PE_tuple es ->
    let ts = List.map (get_expr_trans nodes fbys) es in
    fun st tocalc ->
      let vis = List.map (fun t -> t st tocalc) ts in
      let vs = List.map fst vis and is = List.map snd vis in
      Tuple vs, (List.flatten is)
  | PE_when (e, constr, clid) -> get_expr_trans nodes fbys e
  | PE_merge (clid, brs) ->
    fun st tocalc ->
      let St (strs, insts, _) = st in
      let c = (match List.nth (List.assoc clid strs) fbys with
          | Bottom -> raise (NotYetCalculated clid)
          | c -> c) in
      let c = (match c with
          | Bool true -> "True" | Bool false -> "False"
          | Constr c -> c
          | _ -> failwith "merge expects either bool or constr") in
      let e = (match (List.assoc_opt c brs) with
          | None -> failwith "constructor not found in merge branches"
          | Some e -> e) in
      let insts = (match st with St (_, i, _) -> i) in
      let (v, ins) = get_expr_trans nodes fbys e st tocalc in
      v, ins@(List.flatten (List.map (fun (_, e) -> get_instances insts e)
                              (List.remove_assoc c brs)))

(** Get the transitions for an equation *)
and get_eq_trans nodes (e : p_equation) types =
  let trans = get_expr_trans nodes 0 e.peq_expr in
  let defs = defined_of_equation e in
  let tys = List.map (fun d -> d, List.assoc d types) defs in
  fun st ->
    let St (strs, insts, aut) = st in
    (match e.peq_patt.ppatt_desc with
     | PP_ident id ->
       let cl = clock_of_ty (List.assoc id types) in
       if check_clock_value strs cl
       then
         let (v, is) =
           trans st (List.length (List.assoc (List.hd defs) strs)-1) in
         St (fill_val tys strs id v, is@insts, aut)
       else St (fill_val tys strs id Bottom, insts, aut)
     | PP_tuple ids ->
       let cls = List.map (fun id ->
           clock_of_ty (List.assoc id types)) ids in
       if (List.exists (check_clock_value strs) cls) then
         let (v, is) =
           trans st (List.length (List.assoc (List.hd defs) strs)-1) in
         (match v with
          | Tuple vs ->
            St(List.fold_left2 (fill_val tys) strs ids vs, is@insts, aut)
          | _ -> failwith "Should not happen")
       else St (List.fold_left (fun strs id ->
           fill_val tys strs id Bottom) strs ids, insts, aut))

(** Get the transitions for an instruction *)
and get_instr_trans nodes types (i : p_instr) =
  match i with
  | Eq eq -> get_eq_trans nodes eq types
  | Automaton brs ->
    (fun (St (strs, is, (Node autos))) ->
       let (current, (should_be_reset, stbrs)) = List.find (fun (id, (_, _)) ->
             List.exists (fun (id', _, _, _) -> id = id') brs) autos in

       (* Reset if necessary *)
       let (strs', is', stbrs) =
         if (should_be_reset) then
           let (strs', is', Node autos) = get_instr_init nodes i in
           List.map (fun (id, _) -> id, Bottom::[]) strs',
           is', snd (snd (List.hd autos))
         else ([], [], stbrs) in
       let prev_strs = (List.map (fun (id, l) -> id, List.tl l) strs) in
       let strs = List.fold_left (fun strs (id, str) ->
           replace_assoc id strs str) strs strs' in
       let is = List.fold_left (fun is (id, i) ->
           replace_assoc id is i) is is' in

       (* Current active branch (we'll evaluate it) *)
       let (locals, stbr) = List.assoc current stbrs
       and (_, lets, instrs, untils) =
         List.find (fun (id', _, _, _) -> current = id') brs in

       (* Remove the state we're going to modify *)
       let autos = List.remove_assoc current autos
       and stbrs = List.remove_assoc current stbrs in

       (* Calculate local values, and save them *)
       let locals = List.map (fun (id, str) -> id, Bottom::str) locals in
       let strs = locals@strs in
       let lets_ty = List.map (fun (id, ty, _) -> (id, ty)) lets in
       let types = types@lets_ty in
       let let_equs = List.map (fun (id, ty, e) ->
           { peq_patt = { ppatt_desc = PP_ident id; ppatt_loc = dummy_loc };
             peq_expr = e }) lets in
       let St (strs, is, stbr) =
         List.fold_left (fun st eq -> get_eq_trans nodes eq types st)
           (St (strs, is, stbr)) let_equs in
       let locals = List.filter (fun (id, _) ->
           List.mem_assoc id locals) strs in

       (* Update state according to inner instructions *)
       let funs = List.map (fun i ->
           defined_of_instr i,
           get_instr_trans nodes types i) instrs in
       let St (strs, is, stbr) = dynamic_schedule funs (St (strs, is, stbr)) in

       (* Handle state change *)
       let (untils, is) =
         List.fold_left (fun (us, is) (e, constr, reset) ->
           let (v, is') = get_expr_trans nodes 0 e (St (strs, is, stbr)) 0 in
           (v, constr, reset)::us, is'@is) ([], is) untils in
       let strs = List.fold_left (fun strs (id, _) -> List.remove_assoc id strs)
           strs locals in

       (* After the reset, we need to put some of the streams back *)
       let strs = if should_be_reset then
           List.fold_left (fun strs (id, str) ->
               match (List.assoc id strs) with
               | [v] -> replace_assoc id strs (v::str)
               | _ -> strs) strs prev_strs
         else strs in
       let newcurrent, should_be_reset =
         match (List.find_opt (fun (c, _, _) -> c = Bool true) untils) with
         | Some (_, c, reset) -> c, reset | None -> current, false in
       let stbrs = (current, (locals, stbr))::stbrs in
       St (strs, is, Node ((newcurrent, (should_be_reset, stbrs))::autos)))

(** Evaluation with dynamic scheduling of a set of instructions *)
and dynamic_schedule instrs st : state =
  let rec dyn_aux instrs stack st =
    if (instrs = [] && stack = []) then st
    else (match stack with
        | [] -> dyn_aux (List.tl instrs) [List.hd instrs] st
        | hd::tl ->
          (* Try to compute an equation *)
          (try dyn_aux instrs tl ((snd hd) st)
           (* If we're missing something, we need to add
              it to the compute stack *)
           with NotYetCalculated id ->
             let eqmis =
               (try List.find (fun (decs, _) -> List.mem id decs) instrs
                with _ -> raise (CausalityError id)) in
             dyn_aux (List.remove_assoc (fst eqmis) instrs)
               (eqmis::stack) st)) in
  dyn_aux instrs [] st

(** Get transition functions for a node *)
and get_node_trans nodes (n : p_node) : trans_node =
  (* Transition functions for all the equations *)
  let transfuns = List.map (fun i ->
      defined_of_instr i,
      get_instr_trans nodes (n.pn_local@n.pn_output) i) n.pn_instrs in
  fun (inputs, St (strs, insts, aut)) ->
    (* Add the new inputs to the relevant streams *)
    let strs = List.fold_left (fun strs (x, v) ->
        add_val strs x v) strs inputs in
  (* Add Bottom in front of everything to calculate *)
    let locouts = List.map (fun (id, _) -> id) (n.pn_local@n.pn_output) in
    let strs = List.fold_left
        (fun strs x -> add_val strs x Bottom) strs locouts in
    let St (strs, insts, aut) =
      dynamic_schedule transfuns (St (strs, insts, aut)) in
    St (strs, insts, aut),
    List.map (fun (id, l) -> id, try List.hd l with _ -> Nil)
      (List.filter (fun (id, _) -> List.mem_assoc id n.pn_output) strs)

(*                          Running the interpreter                          *)

(** Create random inputs of the right type for a node *)
let generate_rd_input (cls : Asttypes.clockdec list) (n : p_node) =
  List.map (fun (id, ty) ->
      id, match (base_ty_of_ty ty) with
      | Tint -> Int (Random.int 100)
      | Treal -> Real (Random.float 100.)
      | Tbool -> Bool (Random.bool ())
      | Tclock id ->
        let constrs = List.assoc id cls in
        let n = List.length constrs in
        Constr (List.nth constrs (Random.int n))
      | Ttuple _ -> invalid_arg "generate_rd_input"
    ) n.pn_input

(*                          Comparing nodes                                   *)

(** Run the p_node and the k_node, and compare their outputs and local streams *)
let run_nodes (fp : p_file) (fk : k_file) (name : ident) k =
  Random.self_init ();
  let nps = List.map (fun n -> (n.pn_name, n)) fp.pf_nodes
  and nks = List.map (fun n -> (n.kn_name, n)) fk.kf_nodes in
  let np = List.assoc name nps and nk = List.assoc name nks in
  let initp = get_node_init nps np
  and initk = Interpr.get_node_init nks nk in
  let transp = get_node_trans nps np
  and transk = Interpr.get_node_trans nks nk in
  let rec aux n (sp, sk) =
    match n with
    | 0 -> sp, sk
    | n ->
      let inputs = generate_rd_input fp.pf_clocks np in
      aux (n-1)
             (fst (transp (inputs, sp)),
              fst (transk (inputs, sk)))
  in
  let (St (sp, _, _), St (sk, _)) = (aux k (initp, initk)) in
  List.iter (fun (id, strp) ->
      let strk = List.assoc id sk in
      if (strp <> strk) then (
        Printf.printf "Error in bisimulation of node %s, stream %s:\n" name id;
        List.iter (fun (id, strp) ->
            let strk = List.assoc id sk in
            print_endline (Printf.sprintf "(%s, p:[%s], k:[%s])" id
                             (String.concat ";"
                                   (List.map string_of_value (List.rev strp)))
                             (String.concat ";"
                                (List.map string_of_value (List.rev strk)))))
          sp;
        exit 1;
      )) sp

(** Run all the nodes in p_file and k_file *)
let run_files (fp : p_file) (fk : k_file) =
  List.iter (fun n -> run_nodes fp fk n.pn_name 20) fp.pf_nodes
