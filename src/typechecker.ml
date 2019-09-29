(** Basic typechecking, doesn't take clocks or causality into account *)

open Asttypes
open Minils
open TMinils

exception TypeError of (string * location)
exception MissingEquationError of (ident * location)
exception UnexpectedEquationError of (ident * location)

(** Get the type expected for a pattern [pat],
    and removes the relevant target streams from [streams] *)
let get_pattern_type (streams : (ident * ty) list) pat =
  match pat.kpatt_desc with
  | KP_ident id ->
    (try base_ty_of_ty (List.assoc id streams)
     with _ -> raise (UnexpectedEquationError (id, pat.kpatt_loc))),
    List.remove_assoc id streams
  | KP_tuple ids ->
    let (tys, streams) = List.fold_left (fun (ty, streams) id ->
        try
          (base_ty_of_ty (List.assoc id streams))::ty,
          List.remove_assoc id streams
        with _ -> raise (UnexpectedEquationError (id, pat.kpatt_loc)))
       ([], streams) ids in
    Ttuple (List.rev tys), streams

(** Check that [const] has the [expected] type *)
let type_const = function
  | Cbool _ -> Tbool
  | Cint _ -> Tint
  | Creal _ -> Treal

(** Get the constructions associated with a clock type *)
let constrs_of_clock clocks loc = function
  | Tbool -> ["False";"True"]
  | Tclock clid ->
    (try List.assoc clid clocks
     with _ -> raise (TypeError
                        (Printf.sprintf "Clock %s not found in file" clid, loc)))
  | ty -> raise (TypeError
                   (Printf.sprintf
                      "Type %s is not supported as a clock"
                      (string_of_base_ty ty), loc))

(** Gives the expected input types for an [expected] output types on op *)
let type_op (inputs : base_ty list) loc op =
  match op with
  | Op_eq | Op_neq
    when inputs = [Tbool;Tbool] -> Tbool
  | Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge
    when inputs = [Tint;Tint] || inputs = [Treal;Treal] -> Tbool
  | Op_sub when inputs = [Tint] -> Tint
  | Op_add | Op_sub | Op_mul | Op_div | Op_mod
    when inputs = [Tint;Tint] -> Tint
  | Op_sub when inputs = [Treal] -> Treal
  | Op_add | Op_sub | Op_mul | Op_div
    when inputs = [Treal;Treal] -> Treal
  | Op_not when inputs = [Tbool] -> Tbool
  | Op_and | Op_or | Op_xor when inputs = [Tbool;Tbool] -> Tbool
  | Op_not when inputs = [Tint] -> Tint
  | Op_and | Op_or | Op_xor when inputs = [Tint;Tint] -> Tint
  | Op_if when List.length inputs = 3 &&
               List.nth inputs 1 = List.nth inputs 2 -> List.nth inputs 1
  | _ -> raise (TypeError
                  (Printf.sprintf "Wrong input types (%s) for operator %s"
                     (String.concat "," (List.map string_of_base_ty inputs))
                     (string_of_op op), loc))

(** Check that an expression has the [expected] type *)
let rec type_expr nodes streams clocks (e : k_expr) : t_expr =
  let loc = e.kexpr_loc in
  match e.kexpr_desc with
  | KE_const c ->
    { texpr_desc = TE_const c; texpr_ty = type_const c; texpr_loc = e.kexpr_loc }
  | KE_ident id ->
    let bty =
      (try base_ty_of_ty (List.assoc id streams)
       with _ -> raise (TypeError
                          (Printf.sprintf "Stream %s not found in node"
                             id, e.kexpr_loc))) in
    { texpr_desc = TE_ident id; texpr_ty = bty; texpr_loc = e.kexpr_loc }
  | KE_op (op, es) ->
    let tes = List.map (type_expr nodes streams clocks) es in
    let outy = type_op (List.map (fun te -> te.texpr_ty) tes) e.kexpr_loc op in
    { texpr_desc = TE_op (op, tes); texpr_ty = outy; texpr_loc = loc }
  | KE_app (id, es, ever) ->
    let tes = List.map (type_expr nodes streams clocks) es in
    (* Check that reset stream is bool *)
    let tever = type_expr nodes streams clocks ever in
    if(tever.texpr_ty <> Tbool)
    then raise (TypeError
                  (Printf.sprintf
                     "The reset stream should be of type bool, found %s"
                     (string_of_base_ty tever.texpr_ty), ever.kexpr_loc));
    (* Find the node *)
    let node = try List.assoc id nodes
      with _ -> raise (TypeError
                         (Printf.sprintf "Node %s not found in file"
                            id, e.kexpr_loc)) in
    (* Check input types *)
    (try List.iter2 (fun exp act ->
         if (exp <> act)
         then raise
             (TypeError
                (Printf.sprintf
                   "Wrong argument type for node %s, expected %s, found %s"
                   id (string_of_base_ty exp) (string_of_base_ty act),
                 e.kexpr_loc)))
         (List.map (fun (_, t) -> base_ty_of_ty t) node.tn_input)
         (List.map (fun te -> te.texpr_ty) tes)
     with Invalid_argument _ ->
       raise (TypeError
                (Printf.sprintf
                   "Wrong number of arguments for node %s, expected %s, found %s"
                   id (string_of_int (List.length node.tn_input))
                   (string_of_int (List.length tes)), e.kexpr_loc)));

    (* Output type *)
    let outy = (match node.tn_output with
        | [] -> failwith "Should not happen (syntax)"
        | [(_, ty)] -> base_ty_of_ty ty
        | _ -> Ttuple (List.map (fun (_, t) -> base_ty_of_ty t)
                         node.tn_output)) in
    { texpr_desc = TE_app (id, tes, tever);
      texpr_ty = outy; texpr_loc = loc }
  | KE_fby (c, e) ->
    let t1 = type_const c and te = type_expr nodes streams clocks e in
    if (t1 <> te.texpr_ty)
    then raise
        (TypeError
           (Printf.sprintf
              "Both sides of fby should have the same type, found %s and %s"
              (string_of_base_ty t1) (string_of_base_ty te.texpr_ty),
            e.kexpr_loc));
    { texpr_desc = TE_fby(c, te); texpr_ty = t1; texpr_loc = loc }
  | KE_tuple es ->
    let tes = (List.map (type_expr nodes streams clocks) es) in
    let tys = List.map (fun te -> te.texpr_ty) tes in
    { texpr_desc = TE_tuple tes;
      texpr_ty = Ttuple tys; texpr_loc = loc }
  | KE_when (e, constr, cl) ->
    let clt = (try base_ty_of_ty (List.assoc cl streams)
               with _ -> raise (TypeError
                                  (Printf.sprintf "Clock %s not found in node"
                                     cl, e.kexpr_loc))) in
    let constrs = constrs_of_clock clocks loc clt in
    if not (List.mem constr constrs) then
      raise (TypeError
               (Printf.sprintf
                  "Constructor %s does not belong to clock type %s"
                  constr (string_of_base_ty clt), loc));
    let te = type_expr nodes streams clocks e in
    { texpr_desc = TE_when (te, constr, cl);
      texpr_ty = te.texpr_ty; texpr_loc = loc }
  | KE_merge (cl, es) ->
    let clt = (try base_ty_of_ty (List.assoc cl streams)
               with _ -> raise (TypeError
                                  (Printf.sprintf "Clock %s not found in node"
                                     cl, e.kexpr_loc))) in

    (* Check the constructors *)
    let constrs = constrs_of_clock clocks loc clt in
    if (constrs <> List.map fst es)
    then raise
        (TypeError
           (Printf.sprintf
              "Constructors in merge are incorrect for type %s :\
               expected %s, found %s"
              (string_of_base_ty clt)
              (String.concat "," constrs)
              (String.concat "," (List.map fst es)), loc));

    (* Check the expression types *)
    let tes = List.map
        (fun (c, te) -> c, type_expr nodes streams clocks te) es in
    let ty = (snd (List.hd tes)).texpr_ty in
    List.iter (fun (_, te) ->
        if (te.texpr_ty <> ty)
        then raise
            (TypeError
               (Printf.sprintf
                  "Both args of merge should have the same type, found %s and %s"
                  (string_of_base_ty ty)
                  (string_of_base_ty te.texpr_ty), e.kexpr_loc))) tes;
    { texpr_desc = TE_merge (cl, tes);
      texpr_ty = ty; texpr_loc = loc }

(** Check that the equation [eq] is correctly typed.
    Returns the [out_streams] minus the ones we just type-checked *)
let check_equation nodes streams out_streams clocks (eq : k_equation) =
  let (expected, os) = get_pattern_type out_streams eq.keq_patt
  and te = type_expr nodes streams clocks eq.keq_expr in
  if te.texpr_ty <> expected
  then raise (TypeError
                (Printf.sprintf
                   "Wrong type for equation %s; expected %s, found %s"
                   (Minils.string_of_equation eq)
                   (string_of_base_ty expected)
                   (string_of_base_ty te.texpr_ty), eq.keq_expr.kexpr_loc));
  { teq_patt = eq.keq_patt; teq_expr = te }, os

(** Check that the node [n] is correctly typed *)
let check_node (nodes: (ident * t_node) list) clocks (n : k_node) =
  let out_streams = (n.kn_local@n.kn_output) in
  let all_streams = (n.kn_input@out_streams) in

  (* Check that there are no duplicate stream names *)
  let sorted_streams = List.sort
      (fun (id1, _) (id2, _) -> String.compare id1 id2)
      all_streams in

  let rec find_consecutives = function
    | [] | [_] -> None
    | (hd1, _)::(hd2, s2)::tl ->
      if hd1 = hd2 then Some hd1
      else (find_consecutives ((hd2, s2)::tl)) in
  (match (find_consecutives sorted_streams)
   with None -> ()
      | Some id -> raise (TypeError
                            (Printf.sprintf
                               "Stream name %s was defined twice in node %s"
                               id n.kn_name, n.kn_loc)));

  (* Check that all declared types are using correct clocks *)
  ignore (List.fold_left (fun streams (id, (ty:ty)) -> match ty with
      | Base _ -> (id, ty)::streams
      | Clocked (_, _, cl) ->
        let clt =
          (try base_ty_of_ty (List.assoc cl streams)
           with _ -> raise (TypeError
                              (Printf.sprintf "Clock %s not found in node %s"
                                 cl n.kn_name, n.kn_loc))) in
        ignore (constrs_of_clock clocks n.kn_loc clt);
        (id, ty)::streams
    ) [] all_streams);

  (* Check the equations of the node *)
  let teqs, rem_streams = List.fold_left
      (fun (teqs, streams) eq ->
         let teq, streams =
           check_equation nodes all_streams streams clocks eq in
         teq::teqs, streams)
      ([], out_streams) n.kn_equs in
  (match rem_streams with
   | [] -> ()
   | (hd, _)::_ -> raise (MissingEquationError (hd, n.kn_loc)));

    (* Construct the resultting node *)
  { tn_name = n.kn_name;
    tn_input = n.kn_input;
    tn_output = n.kn_output;
    tn_local = n.kn_local;
    tn_equs = List.rev teqs;
    tn_loc = n.kn_loc }

(** Check that the file [f] is correctly typed *)
let check_file (f : k_file) : t_file =
  let clocks = f.kf_clocks in
  try
    let nodes = List.fold_left (fun env n ->
        (n.kn_name, check_node env clocks n)::env) [] f.kf_nodes in
    { tf_clocks = clocks;
      tf_nodes = List.map snd (List.rev nodes); }
  with
  | UnexpectedEquationError (id, loc) ->
    Printf.printf "Type checking error : UnexpectedEquation for %s at %s\n"
      id (string_of_loc loc); exit 1
  | MissingEquationError (id, loc) ->
    Printf.printf "Type checking error : MissingEquation for %s at %s\n"
      id (string_of_loc loc); exit 1
  | TypeError (msg, loc) ->
    Printf.printf "Type checking error : %s at %s\n"
      msg (string_of_loc loc); exit 1

(*                           Check equivalence between ASTs                    *)

(** Check that a parsed pattern [p] and typed pattearn [t] are equivalent *)
let equiv_parse_clock_patt (k : k_patt) (t : t_patt) =
  k = t

(** Check that a parsed expr [p] and typed expr [t] are equivalent *)
let rec equiv_parse_clock_expr (k : k_expr) (t : t_expr) =
  match k.kexpr_desc, t.texpr_desc with
  | KE_const c1, TE_const c2 -> c1 = c2
  | KE_ident c1, TE_ident c2 -> c1 = c2
  | KE_op (op1, es1), TE_op (op2, es2) ->
    op1 = op2 && List.for_all2 equiv_parse_clock_expr es1 es2
  | KE_app (id1, es1, ev1), TE_app (id2, es2, ev2) ->
    id1 = id2 && List.for_all2 equiv_parse_clock_expr es1 es2 &&
    equiv_parse_clock_expr ev1 ev2
  | KE_fby (c1, e1), TE_fby (c2, e2) ->
    c1 = c2 && equiv_parse_clock_expr e1 e2
  | KE_tuple es1, TE_tuple es2 ->
    List.for_all2 equiv_parse_clock_expr es1 es2
  | KE_when (e1, c1, id1), TE_when (e2, c2, id2) ->
    equiv_parse_clock_expr e1 e2 && c1 = c2 && id1 = id2
  | KE_merge (id1, es1), TE_merge (id2, es2) ->
    id1 = id2 &&
    List.for_all2 (fun (c1, e1) (c2, e2) ->
        c1 = c2 && equiv_parse_clock_expr e1 e2) es1 es2
  | _, _ -> false

(** Check that a parsed equation [p] and typed equation [t] are equivalent *)
let equiv_parse_clock_eq (k : k_equation) (t : t_equation) =
  equiv_parse_clock_patt k.keq_patt t.teq_patt &&
  equiv_parse_clock_expr k.keq_expr t.teq_expr

(** Check that a parsed node [p] and typed node [t] are equivalent *)
let equiv_parse_clock_node (k : k_node) (t : t_node) =
  k.kn_name = t.tn_name &&
  k.kn_input = t.tn_input &&
  k.kn_output = t.tn_output &&
  k.kn_local = t.tn_local &&
  List.for_all2 equiv_parse_clock_eq k.kn_equs t.tn_equs

(** Check that a parsed file [p] and typed file [t] are equivalent *)
let equiv_parse_clock_file (k : k_file) (t : t_file) =
  try
    k.kf_clocks = t.tf_clocks &&
    List.for_all2 equiv_parse_clock_node k.kf_nodes t.tf_nodes
  with _ -> false
