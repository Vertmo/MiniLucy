(** Basic typechecking, doesn't take clocks or causality into account *)

open Asttypes
open Minils

exception TypeError of (string * location)
exception MissingEquationError of (ident * location)
exception UnexpectedEquationError of (ident * location)

type node_ty = ((ident * ty) list) * ((ident * ty) list)

type checker_ty =
  | Tbool | Tint | Treal
  | Ttuple of checker_ty list

let checker_ty_of_ty : ty -> checker_ty = function
  | Base Tbool | Clocked (Tbool, _, _) -> Tbool
  | Base Tint | Clocked (Tint, _, _) -> Tint
  | Base Treal | Clocked (Treal, _, _) -> Treal

let rec string_of_checker_ty = function
  | Tbool -> "bool" | Tint -> "int" | Treal -> "real"
  | Ttuple tys -> Printf.sprintf "(%s)"
                    (String.concat "," (List.map string_of_checker_ty tys))

(** Get the type expected for a pattern [pat],
    and removes the relevant target streams from [streams] *)
let get_pattern_type (streams : (ident * ty) list) pat =
  match pat.ppatt_desc with
  | PP_ident id ->
    (try checker_ty_of_ty (List.assoc id streams)
     with _ -> raise (UnexpectedEquationError (id, pat.ppatt_loc))),
    List.remove_assoc id streams
  | PP_tuple ids ->
    let (tys, streams) = List.fold_left (fun (ty, streams) id ->
        try
          (checker_ty_of_ty (List.assoc id streams))::ty,
          List.remove_assoc id streams
        with _ -> raise (UnexpectedEquationError (id, pat.ppatt_loc)))
       ([], streams) ids in
    Ttuple (List.rev tys), streams

(** Check that [const] has the [expected] type *)
let type_const = function
  | Cbool _ -> Tbool
  | Cint _ -> Tint
  | Creal _ -> Treal

(** Gives the expected input types for an [expected] output types on op *)
let type_op (inputs : checker_ty list) loc op =
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
                     (String.concat "," (List.map string_of_checker_ty inputs))
                     (string_of_op op), loc))

(** Check that an expression has the [expected] type *)
let rec type_expr nodes streams (e : p_expr) =
  match e.pexpr_desc with
  | PE_const c -> type_const c
  | PE_ident id ->
    (try checker_ty_of_ty (List.assoc id streams)
     with _ -> raise (TypeError
                        (Printf.sprintf "Stream %s not found in node"
                           id, e.pexpr_loc)))
  | PE_op (op, es) ->
    let est = List.map (type_expr nodes streams) es in
    type_op est e.pexpr_loc op
  | PE_app (id, es, ever) ->
    let est = List.map (type_expr nodes streams) es in
    (* Check that reset stream is bool *)
    let evert = type_expr nodes streams ever in
    if(evert <> Tbool)
    then raise (TypeError
                  (Printf.sprintf
                     "The reset stream should be of type bool, found %s"
                     (string_of_checker_ty evert), ever.pexpr_loc));
    (* Find the node *)
    let (node_in, node_out) = try List.assoc id nodes
      with _ -> raise (TypeError
                         (Printf.sprintf "Node %s not found in file"
                            id, e.pexpr_loc)) in
    (* Check input types *)
    (try List.iter2 (fun exp act ->
         if (exp <> act)
         then raise
             (TypeError
                (Printf.sprintf
                   "Wrong argument type for node %s, expected %s, found %s"
                   id (string_of_checker_ty exp) (string_of_checker_ty act),
                 e.pexpr_loc)))
         (List.map (fun (_, t) -> checker_ty_of_ty t) node_in) est
     with Invalid_argument _ ->
       raise (TypeError
                (Printf.sprintf
                   "Wrong number of arguments for node %s, expected %s, found %s"
                   id (string_of_int (List.length node_in))
                   (string_of_int (List.length est)), e.pexpr_loc)));
    (* Output type *)
    (match node_out with
     | [] -> failwith "Should not happen (syntax)"
     | [(_, ty)] -> checker_ty_of_ty ty
     | _ -> Ttuple (List.map (fun (_, t) -> checker_ty_of_ty t) node_out))
  | PE_fby (c, e) ->
    let t1 = type_const c and t2 = type_expr nodes streams e in
    if (t1 <> t2)
    then raise
        (TypeError
           (Printf.sprintf
              "Both sides of fby should have the same type, found %s and %s"
              (string_of_checker_ty t1) (string_of_checker_ty t2),
            e.pexpr_loc));
    t1
  | PE_tuple es -> Ttuple (List.map (type_expr nodes streams) es)
  | PE_when (ew, cl, _) ->
    let clt = (try checker_ty_of_ty (List.assoc cl streams)
               with _ -> raise (TypeError
                                  (Printf.sprintf "Clock %s not found in node"
                                     cl, e.pexpr_loc))) in
    if (clt <> Tbool)
    then raise (TypeError
                  (Printf.sprintf "Clock should be bool stream, found %s"
                     (string_of_checker_ty clt), e.pexpr_loc));
    type_expr nodes streams ew
  | PE_merge (cl, e1, e2) ->
    let clt = (try checker_ty_of_ty (List.assoc cl streams)
               with _ -> raise (TypeError
                                  (Printf.sprintf "Clock %s not found in node"
                                     cl, e.pexpr_loc))) in
    if (clt <> Tbool)
    then raise (TypeError
                  (Printf.sprintf "Clock should be bool stream, found %s"
                     (string_of_checker_ty clt), e.pexpr_loc));
    let t1 = type_expr nodes streams e1 and t2 = type_expr nodes streams e2 in
    if (t1 <> t2)
    then raise
        (TypeError
           (Printf.sprintf
              "Both args of merge should have the same type, found %s and %s"
              (string_of_checker_ty t1) (string_of_checker_ty t2), e.pexpr_loc));
    t1

(** Check that the equation [eq] is correctly typed.
    Returns the [out_streams] minus the ones we just type-checked *)
let check_equation nodes streams out_streams (eq : p_equation) =
  let (expected, os) = get_pattern_type out_streams eq.peq_patt
  and actual = type_expr nodes streams eq.peq_expr in
  if actual <> expected
  then raise (TypeError
                (Printf.sprintf
                   "Wrong type for equation %s; expected %s, found %s"
                   (string_of_equation eq)
                   (string_of_checker_ty expected)
                   (string_of_checker_ty actual), eq.peq_expr.pexpr_loc));
  os

(** Check that the node [n] is correctly typed *)
let check_node (nodes: (ident * node_ty) list) (n : p_node) =
  let out_streams = (n.pn_local@n.pn_output) in
  let all_streams = (n.pn_input@out_streams) in

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
                               id n.pn_name, n.pn_loc)));

  (* Check that all declared types are using bool clocks *)
  ignore (List.fold_left (fun streams (id, (ty:ty)) -> match ty with
      | Base _ -> (id, ty)::streams
      | Clocked (_, cl, _) ->
        let clt =
          (try checker_ty_of_ty (List.assoc cl streams)
           with _ -> raise (TypeError
                              (Printf.sprintf "Clock %s not found in node %s"
                                 cl n.pn_name, n.pn_loc))) in
        if (clt <> Tbool)
        then raise (TypeError
                      (Printf.sprintf "Clock should be bool stream, found %s"
                         (string_of_checker_ty clt), n.pn_loc));
        (id, ty)::streams
    ) [] all_streams);

  (* Check the equations of the node *)
  let rem_streams = List.fold_left (check_equation nodes all_streams)
      out_streams n.pn_equs in
  match rem_streams with
  | [] -> ()
  | (hd, _)::_ -> raise (MissingEquationError (hd, n.pn_loc))

(** Check that the file [f] is correctly typed *)
let check_file (f : p_file) =
  try
    ignore (List.fold_left (fun env n ->
        check_node env n; (n.pn_name, (n.pn_input, n.pn_output))::env) [] f)
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
