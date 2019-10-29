(*                  Denotational semantics based interpreter                  *)

open Asttypes
open Minils

exception InterpreterError of string
exception NotYetCalculated of ident
exception CausalityError of ident
exception StreamError of ident * string

(** Value of the interpreter *)
type value = Bottom
           | Nil
           | Int of int | Bool of bool | Real of float
           | Constr of ident
           | Tuple of value list

(** Stream of values. Latest value is at head of the stream *)
type stream = (ident * value list)

(** Association from name to value (inputs and outputs) *)
type assoc = (ident * value) list

(** Association from name to stream of values (states) *)
type assoc_str = (ident * value list) list

(** Add a value in front of the correct stream *)
let add_val strs x v : assoc_str =
  let str = try List.assoc x strs
    with Not_found -> [] in
  (x, v::str)::(List.remove_assoc x strs)

(** ``Fills`` the Bottom at the beginning of the stream.
    If the calculated value is nil, simply remove the head of the stream
    If the head of the stream is not bottom, exception *)
let fill_val strs x v : assoc_str =
  let str = try List.assoc x strs
    with Not_found -> raise (StreamError (x, "stream not found")) in
  match str with
  | Bottom::tl ->
    let str = if (v = Nil) then tl else v::tl in
    (x, str)::(List.remove_assoc x strs)
  | _ -> raise (StreamError (x, "does not begin with bottom"))

(** Node state *)
type state = St of assoc_str * instance list

(** Instance of a node *)
and instance = ((ident * location) * state)

let rec string_of_value = function
  | Bottom -> "bottom"
  | Nil -> "nil"
  | Int i -> string_of_int i
  | Bool b -> if b then "true" else "false"
  | Real f -> string_of_float f
  | Constr id -> id
  | Tuple vs -> Printf.sprintf "(%s)" (String.concat ","
                                         (List.map string_of_value vs))

let value_of_const = function
  | Cbool b -> Bool b
  | Cint i -> Int i
  | Creal r -> Real r
  | Cconstr (c, _) -> Constr c

(** Apply a unary operator *)
let apply_unary op e =
  match (op, e) with
  | Op_not, Bool b -> Bool (not b)
  | Op_not, Int i -> Int (lnot i)
  | Op_sub, Int i -> Int (-i)
  | Op_sub, Real r -> Real (-.r)
  | _,_ -> failwith "Invalid unary op"

(** Apply comparator *)
let apply_comp comp vl vr =
  match comp with
  | Op_eq -> vl = vr
  | Op_neq -> vl <> vr
  | Op_lt -> vl < vr
  | Op_le -> vl <= vr
  | Op_gt -> vl > vr
  | Op_ge -> vl >= vr
  | _ -> failwith "Invalid comparator"

(** Apply arithmetic operator *)
let apply_arith fint ffloat el er =
  match el, er with
  | Int il, Int ir -> Int (fint il ir)
  | Real fl, Real fr -> Real (ffloat fl fr)
  | _, _ -> failwith "Invalid args for arith op"

(** Apply logic operator *)
let apply_logic fbool fint el er =
  match el, er with
  | Bool bl, Bool br -> Bool (fbool bl br)
  | Int il, Int ir -> Int (fint il ir)
  | _, _ -> failwith "Invalid args for bool op"

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
     | _, _ -> failwith "Invalid operands for comparator")
  | _ -> failwith "Invalid binary operator"

(** Apply an if operator *)
let apply_if cond th el =
  match cond with
  | Bool true -> th
  | Bool false -> el
  | _ -> raise (InterpreterError "Condition of if should be a bool")

(** Apply an operator *)
let apply_op op vs =
  if (List.mem Nil vs) then Nil
  else
    match (List.length vs) with
    | 1 -> apply_unary op (List.nth vs 0)
    | 2 -> apply_binary op (List.nth vs 0) (List.nth vs 1)
    | 3 -> apply_if (List.nth vs 0) (List.nth vs 1) (List.nth vs 2)
    | _ -> raise (InterpreterError "Wrong number of arguments for an op")

(** Get the initial state for an instances in an expression *)
let rec expr_init_instances nodes (e : k_expr) : instance list =
  match e.kexpr_desc with
  | KE_const c -> [] | KE_ident x -> []
  | KE_op (op, es) ->
    let is = List.map (expr_init_instances nodes) es in
    List.flatten is
  | KE_app (fid, es, e) ->
    let is = List.map (expr_init_instances nodes) es
    and ie = expr_init_instances nodes e in
    let n = List.assoc fid nodes in
    let st = get_node_init nodes n in
    (((fid, e.kexpr_loc), st)::ie@(List.concat is))
  | KE_fby (_, e) -> expr_init_instances nodes e
  | KE_tuple es ->
    let is = List.map (expr_init_instances nodes) es in
    List.flatten is
  | KE_when (e, _, _) -> expr_init_instances nodes e
  | KE_merge (clid, brs) ->
    List.flatten (List.map (fun (_, e) -> expr_init_instances nodes e) brs)

(** Get the initial states for an equation *)
and get_eq_init nodes (e : k_equation) : (assoc_str * instance list) =
  let is = expr_init_instances nodes e.keq_expr in
  match e.keq_patt.kpatt_desc with
  | KP_ident id -> [(id, [])], is
  | KP_tuple ids -> List.map (fun id -> (id, [])) ids, is

(** Get the initial state for a node *)
and get_node_init nodes n : state =
  let vis = List.map (get_eq_init nodes) n.kn_equs in
  let vs = List.flatten (List.map fst vis)
  and is = List.flatten (List.map snd vis) in
  St (vs, is)

(** Transition function for expressions.
    The second parameter indicated the index of the value we're trying to
    calculate (used to know when to use consts in fby) *)
type trans_expr = state -> int -> (value * instance list)

(** Transition function for nodes (input, st) -> (st, output) *)
type trans_node = (assoc * state) -> (state * assoc)

(** Get the instances used in an expression *)
let rec get_instances insts (e : k_expr) =
  match e.kexpr_desc with
  | KE_const _ -> []
  | KE_ident _ -> []
  | KE_op (op, es) ->
    List.flatten (List.map (get_instances insts) es)
  | KE_app (fid, es, e) ->
    let is = List.flatten (List.map (get_instances insts) es)
    and i = get_instances insts e in
    ((fid, e.kexpr_loc),
     (List.assoc (fid, e.kexpr_loc) insts))::i@is
  | KE_fby (_, e) -> get_instances insts e
  | KE_tuple es ->
    List.flatten (List.map (get_instances insts) es)
  | KE_when (e, _, _) -> get_instances insts e
  | KE_merge (_, brs) ->
    List.flatten (List.map (fun (_, e) -> get_instances insts e) brs)

(** Get the transition function for an expression *)
let rec get_expr_trans nodes fbys (e : k_expr) : trans_expr =
  match e.kexpr_desc with
  | KE_const c -> fun _ _ -> value_of_const c, []
  | KE_ident id ->
    (fun (St (strs, _)) _ ->
       let str = List.assoc id strs in
       match try List.nth str fbys with _ -> List.nth str (fbys-1) with
       | Bottom -> raise (NotYetCalculated id)
       | v -> v, [])
  | KE_op (op, es) ->
    let ts = List.map (get_expr_trans nodes fbys) es in
    fun cont tocalc ->
      let vis = List.map (fun t -> t cont tocalc) ts in
      let vs = List.map fst vis and is = List.map snd vis in
      apply_op op vs, (List.flatten is)
  | KE_app (fid, es, e) ->
    let ts = List.map (get_expr_trans nodes fbys) es in
    let te = get_expr_trans nodes fbys e in
    let n = List.assoc fid nodes in
    fun st tocalc ->
      let vis = List.map (fun t -> t st tocalc) ts
      and (ve, ie)= te st tocalc in
      let vs = List.map fst vis and is = List.map snd vis in
      let ins = List.map2 (fun (id, _) v -> id, v) n.kn_input vs in
      let (st, outs) = (match ve with
          | Bool true ->
            let init = get_node_init nodes n in
            get_node_trans nodes n (ins, init)
        | _ ->
          let st = List.assoc (fid, e.kexpr_loc)
              (match st with St (_, ins) -> ins) in
          get_node_trans nodes n (ins, st)) in
      (match outs with
       | [(id, v)] -> v
       | vs -> (Tuple (List.map snd vs))),
      (((fid, e.kexpr_loc), st)::ie@(List.concat is))
  | KE_fby (c, e) ->
    let t = get_expr_trans nodes (fbys+1) e in
    fun st tocalc -> if tocalc <= fbys
      then (value_of_const c), get_instances (match st with St (_, i) -> i) e
      else t st tocalc
  | KE_tuple es ->
    let ts = List.map (get_expr_trans nodes fbys) es in
    fun st tocalc ->
      let vis = List.map (fun t -> t st tocalc) ts in
      let vs = List.map fst vis and is = List.map snd vis in
      Tuple vs, (List.flatten is)
  | KE_when (e, constr, clid) ->
    let t = get_expr_trans nodes fbys e in
    fun st tocalc ->
      let (St (strs, _)) = st in
      let c = (match List.nth (List.assoc clid strs) fbys with
        | Bottom -> raise (NotYetCalculated clid)
        | c -> c) in
      if (match c with
          | Bool true -> constr = "True"
          | Bool false -> constr = "False"
          | Constr constr' -> constr = constr'
          | _ -> failwith "when expects either bool or constr")
      then t st tocalc
      else Nil, (get_instances (match st with St (_, i) -> i) e)
  | KE_merge (clid, brs) ->
    fun st tocalc ->
      let St (strs, insts) = st in
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
      let insts = (match st with St (_, i) -> i) in
      let (v, ins) = get_expr_trans nodes fbys e st tocalc in
      v, ins@(List.flatten (List.map (fun (_, e) -> get_instances insts e)
                              (List.remove_assoc c brs)))

(** Get the transitions for an equation *)
and get_eq_trans nodes (e : k_equation) =
  let trans = get_expr_trans nodes 0 e.keq_expr in
  let defs = defined_of_equation e in
  fun st ->
    let St (strs, insts) = st in
    let (v, is) = trans st (List.length (List.assoc (List.hd defs) strs)-1) in
    St ((match e.keq_patt.kpatt_desc with
        | KP_ident id -> fill_val strs id v
        | KP_tuple ids ->
          (match v with
           | Tuple vs -> List.fold_left2 fill_val strs ids vs
           | _ -> [])), insts@is)

(** Get transition functions for a node *)
and get_node_trans nodes (n : k_node) : trans_node =
  (* Transition functions for all the equations *)
  let transfuns = List.map (fun eq ->
      defined_of_equation eq, get_eq_trans nodes eq) n.kn_equs in
  fun (inputs, St (strs, insts)) ->
  (* Add the new inputs to the relevant streams *)
  let strs = List.fold_left (fun strs (x, v) ->
      add_val strs x v) strs inputs in
  (* Add Bottom in front of everything to calculate *)
  let locouts = List.map (fun (id, _) -> id) (n.kn_local@n.kn_output) in
  let strs = List.fold_left (fun strs x -> add_val strs x Bottom) strs locouts in
    let rec gnt_aux eqs stack st : state =
      if (eqs = [] && stack = []) then st
      else (match stack with
        | [] -> gnt_aux (List.tl eqs) [List.hd eqs] st
        | hd::tl ->
          (* Try to compute an equation *)
          (try gnt_aux eqs tl ((snd hd) st)
             (* If we're missing something, we need to add
                it to the compute stack *)
             with NotYetCalculated id ->
               let eqmis =
                 (try List.find (fun (decs, _) -> List.mem id decs) eqs
                  with _ -> raise (CausalityError id)) in
               gnt_aux (List.remove_assoc (fst eqmis) eqs)
                 (eqmis::stack) st))
  in let St (strs, insts) = gnt_aux transfuns [] (St (strs, insts)) in
  St (strs, insts),
  List.map (fun (id, l) -> id, try List.hd l with _ -> Nil)
    (List.filter (fun (id, _) -> List.mem_assoc id n.kn_output) strs)

(*                          Running the interpreter                          *)

(** Create random inputs of the right type for a node *)
let generate_rd_input (cls : Asttypes.clockdec list) (n : k_node) =
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
    ) n.kn_input

(** Run nodes of the file, for testing purposes *)
let run_node (f : k_file) (name : ident) k =
  Random.self_init ();
  let ns = List.map (fun n -> (n.kn_name, n)) f.kf_nodes in
  let node = List.assoc name ns in
  let init = get_node_init ns node in
  let trans = get_node_trans ns node in
  let rec aux n st =
    match n with
    | 0 -> st
    | n -> aux (n-1) (fst (trans (generate_rd_input f.kf_clocks node, st)))
  in
  let st = (aux k init) in
  print_endline (Printf.sprintf "Streams after %d iterations:" k);
  List.iter (fun (id, vs) ->
      print_endline (Printf.sprintf "(%s, [%s])"
                       id (String.concat ";"
                             (List.map string_of_value (List.rev vs)))))
    (match st with St (st, _) -> st)

let run_file (f : k_file) =
  List.iter (fun n -> run_node f n.kn_name 10) f.kf_nodes
