(*                  Denotational semantics based interpreter                  *)

open Asttypes
open Minils

exception InterpreterError of string
exception MissingInEnv of ident

(** Value of the interpreter *)
type value = Nil
           | Int of int | Bool of bool | Real of float
           | Constr of ident
           | Tuple of value list

let rec string_of_value = function
  | Nil -> "nil"
  | Int i -> string_of_int i
  | Bool b -> if b then "true" else "false"
  | Real f -> string_of_float f
  | Constr id -> id
  | Tuple vs -> Printf.sprintf "(%s)" (String.concat ","
                                         (List.map string_of_value vs))

(** Association from name to values (either state or inputs or outputs) *)
type assoc = (ident * value) list

let value_of_const = function
  | Cbool b -> Bool b
  | Cint i -> Int i
  | Creal r -> Real r

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

(** Get the initial state for an expression *)
let rec get_expr_init ins (e : k_expr) : value =
  try
    match e.kexpr_desc with
    | KE_const c -> value_of_const c
    | KE_ident x ->
      (match List.assoc_opt x ins with
       | Some v -> v
       | None -> Nil)
    | KE_op (op, es) ->
      apply_op op (List.map (get_expr_init ins) es)
    | KE_app (_, es, e) ->
      Nil (* FIXME ? *)
    | KE_fby (c, _) -> value_of_const c
    | KE_tuple es ->
      Tuple (List.map (get_expr_init ins) es)
    | KE_when (e, _, _) -> get_expr_init ins e
    | KE_merge (clid, brs) ->
      let c = (match (List.assoc_opt clid ins) with
          | None -> raise (MissingInEnv clid)
          | Some c -> c) in
      let c = (match c with
          | Bool true -> "True" | Bool false -> "False"
          | Constr c -> c
          | _ -> failwith "merge expects either bool or constr") in
      let e = (match (List.assoc_opt c brs) with
          | None -> failwith "constructor not found in merge branches"
          | Some e -> e) in
      get_expr_init ins e

  with _ -> Nil

(** Get the initial states for an equation *)
let get_eq_init ins (e : k_equation) =
  let v = get_expr_init ins e.keq_expr in
  match e.keq_patt.kpatt_desc with
  | KP_ident id -> if v = Nil then [] else [(id, v)]
  | KP_tuple ids ->
    (match v with
     | Tuple vs when not (List.mem Nil vs) -> List.combine ids vs
     | _ -> [])

(** Get the initial state for a node *)
let get_node_init ins (n : k_node) : assoc =
  let locouts = List.flatten (List.map (fun eq ->
      get_eq_init ins eq) n.kn_equs) in
  locouts

(** Transition function for expressions *)
type trans_expr = (assoc * assoc) -> value

(** Get the transition function for an expression *)
let rec get_expr_trans (e : k_expr) : trans_expr =
  match e.kexpr_desc with
  | KE_const c -> fun _ -> value_of_const c
  | KE_ident id ->
    (fun (env, _) ->
       match (List.assoc_opt id env) with
       | None -> raise (MissingInEnv id)
       | Some v -> v)
  | KE_op (op, es) ->
    fun cont -> apply_op op (List.map (fun e -> get_expr_trans e cont) es)
  | KE_app (f, es, e) ->
    failwith "TODO"
  | KE_fby (_, e) ->
    fun (env, st) -> get_expr_trans e ((st@env), [])
  | KE_tuple es ->
    fun cont -> Tuple (List.map (fun e -> get_expr_trans e cont) es)
  | KE_when (e, constr, clid) ->
    fun (env, st) ->
      let c = (match (List.assoc_opt clid env) with
        | None -> raise (MissingInEnv clid)
        | Some c -> c) in
      if (match c with
          | Bool true -> constr = "True"
          | Bool false -> constr = "False"
          | Constr constr' -> constr = constr'
          | _ -> failwith "when expects either bool or constr")
      then get_expr_trans e (env, st)
      else Nil
  | KE_merge (clid, brs) ->
    fun (env, st) ->
      let c = (match (List.assoc_opt clid env) with
          | None -> raise (MissingInEnv clid)
          | Some c -> c) in
      let c = (match c with
          | Bool true -> "True" | Bool false -> "False"
          | Constr c -> c
          | _ -> failwith "merge expects either bool or constr") in
      let e = (match (List.assoc_opt c brs) with
          | None -> failwith "constructor not found in merge branches"
          | Some e -> e) in
      get_expr_trans e (env, st)

(** Get the transitions for an equation *)
let get_eq_trans (e : k_equation) = fun cont ->
  let v = get_expr_trans e.keq_expr cont in
  match e.keq_patt.kpatt_desc with
  | KP_ident id -> [(id, v)]
  | KP_tuple ids ->
    (match v with
     | Tuple vs -> List.combine ids vs
     | _ -> [])

(** Transition function for nodes (input, st) -> (st, output) *)
type trans_node = (assoc * assoc) -> (assoc * assoc)

(** Get transition functions for a node *)
let get_node_trans (n : k_node) : trans_node =
  (* Transition functions for all the equations *)
  let transfuns = List.map (fun eq ->
      defined_of_equation eq, get_eq_trans eq) n.kn_equs in
  fun (inputs, st) ->
    let rec gnt_aux eqs stack env =
      if (eqs = [] && stack = []) then []
      else (match stack with
        | [] -> gnt_aux (List.tl eqs) [List.hd eqs] env
        | hd::tl ->
          let res = (try ((snd hd) (env, st))
                     with MissingInEnv id ->
                       let eqmis = List.find (fun (decs, _) ->
                           List.mem id decs) eqs in
                       if (List.mem eqmis stack) then failwith "Causality error";
                       gnt_aux (List.remove_assoc (fst eqmis) eqs)
                         (eqmis::stack) env
                    )
          in res@(gnt_aux eqs tl (env@res)))
          in let locouts = gnt_aux transfuns [] inputs in
  locouts,
  List.filter (fun (id, _) -> List.mem_assoc id n.kn_output) locouts

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
