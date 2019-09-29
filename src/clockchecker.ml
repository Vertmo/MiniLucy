(** Clock checking *)

open Asttypes
open TMinils
open CMinils

exception ClockError of (string * location)

(** Get the clocks(s) expected for a pattern [pat],
    as well as the translated pattern *)
let get_pattern_clock (streams : (ident * clock) list) (pat : t_patt) =
  match pat.kpatt_desc with
  | KP_ident id ->
    (List.assoc id streams),
    { cpatt_desc = CP_ident id; cpatt_loc = pat.kpatt_loc }
  | KP_tuple ids ->
    (Ctuple (List.map (fun id -> (List.assoc id streams)) ids)),
     { cpatt_desc = CP_tuple ids; cpatt_loc = pat.kpatt_loc }

(** Composes clocks [cl1] and [cl2] to give (returns [cl1] o [cl2]) *)
let rec compose_clock cl1 cl2 =
  match cl1 with
  | Base -> cl2
  | Cl (base, constr, clid) -> Cl (compose_clock base cl2, constr, clid)
  | Ctuple cls -> Ctuple (List.map (fun cl -> compose_clock cl cl2) cls)

(** Substitute a (CE_ident) to another identifier in a clock expression *)
let subst_clock (x : ident) (y : c_expr) (cl : clock) =
  let rec subst_aux (x : ident) (y : ident) = function
    | Base -> Base
    | Cl (base, constr, x') ->
      Cl (subst_aux x y base, constr, if x = x' then y else x')
    | Ctuple cls ->
      Ctuple (List.map (subst_aux x y) cls) in
  match y.cexpr_desc with
  | CE_ident y -> subst_aux x y cl
  | _ -> cl

(** Check and get the clocked version of expression [e] *)
let rec clock_expr nodes streams (e : t_expr) =
  let loc = e.texpr_loc and ty = e.texpr_ty in
  match e.texpr_desc with
  | TE_const c ->
    { cexpr_desc = CE_const c; cexpr_ty = ty;
      cexpr_clock = Base; cexpr_loc = loc }
  | TE_ident id ->
    let cl = (List.assoc id streams) in
    { cexpr_desc = CE_ident id; cexpr_ty = ty;
      cexpr_clock = cl; cexpr_loc = loc }
  | TE_op (op, es) ->
    let ces = List.map (clock_expr nodes streams) es in
    let cl = (List.hd ces).cexpr_clock in
    if (not (List.for_all (fun ce -> ce.cexpr_clock = cl) ces))
    then raise (ClockError
                  (Printf.sprintf
                     "All the operands of %s should be on the same clock"
                   (string_of_op op), loc));
    { cexpr_desc = CE_op (op, ces); cexpr_ty = ty;
      cexpr_clock = cl; cexpr_loc = loc}
  | TE_fby (c, e) ->
    let ce = clock_expr nodes streams e in
    { cexpr_desc = CE_fby (c, ce) ; cexpr_ty = ty;
      cexpr_clock = ce.cexpr_clock; cexpr_loc = loc }
  | TE_tuple es ->
    let ces = List.map (clock_expr nodes streams) es in
    let cls = List.map (fun ce -> ce.cexpr_clock) ces in
    { cexpr_desc = CE_tuple ces; cexpr_ty = ty;
      cexpr_clock = Ctuple cls; cexpr_loc = loc}
  | TE_when (ew, constr, clid) ->
    let cew = clock_expr nodes streams ew in
    { cexpr_desc = CE_when (cew, constr, clid); cexpr_ty = ty;
      cexpr_clock = Cl (cew.cexpr_clock, constr, clid); cexpr_loc = loc }
  | TE_merge (clid, es) ->
    let ces = List.map (fun (c, e) -> c, clock_expr nodes streams e) es in
    let ce = snd (List.hd ces) in
    let base, clid = match ce.cexpr_clock with
      | Base ->
        raise (ClockError
                 (Printf.sprintf "Argument %s of merge is not on a clock"
                    (string_of_expr ce), loc))
      | Cl (base, _, clid) -> base, clid
      | Ctuple _ -> failwith "Should not happen" in

    (* Verify that all the clocks are on the same base and using the same
       stream, and that they are on the right constructor  *)
    List.iter (fun (constr, ce) -> match ce.cexpr_clock with
        | Base ->
          raise (ClockError
                   (Printf.sprintf "Argument %s of merge is not on a clock"
                      (string_of_expr ce), loc))
        | Cl (base', constr', clid') ->
          if base' <> base
          then raise (ClockError
                        (Printf.sprintf
                           "Arguments of merge are not on the same base :\
                            %s and %s found"
                           (string_of_clock base)
                           (string_of_clock base'), loc));
          if clid <> clid'
          then raise (ClockError
                        (Printf.sprintf
                           "Arguments of merge are not on the same clock :\
                            %s and %s found" clid clid', loc));
          if constr <> constr'
          then raise (ClockError
                        (Printf.sprintf
                           "Argument %s of merge is not on the right \
                            clock constructor, expected %s, found %s"
                           (string_of_expr ce) constr constr', ce.cexpr_loc))
        | Ctuple _ -> failwith "Should not happen") ces;
      { cexpr_desc = CE_merge (clid, ces); cexpr_ty = ty;
      cexpr_clock = base; cexpr_loc = loc }
  | TE_app (fid, es, ever) ->
    let ces = List.map (clock_expr nodes streams) es
    and cever = clock_expr nodes streams ever in
    let node = List.assoc fid nodes in

    (* Check the association between formal and actual parameters are correct,
       and get an association table for clocks passed as parameters *)
    let assocs =
      List.fold_left2 (fun assocs (id, ty) actual ->
          let clform = List.fold_left (fun cl (x, y) -> subst_clock x y cl)
              (clock_of_ty ty) assocs in
          let clform = compose_clock clform cever.cexpr_clock in
          if(clform <> actual.cexpr_clock)
          then raise
              (ClockError
                 (Printf.sprintf
                    "Wrong clock for argument %s of %s : expected %s, found %s"
                    id fid (string_of_clock clform)
                    (string_of_clock actual.cexpr_clock), loc));
          (id, actual)::assocs)
        [] node.cn_input ces in

    (* Compute the output clocks by substitution and composition *)
    let outcls = List.map (fun (_, ty) ->
        let cl = List.fold_left (fun cl (x, y) -> subst_clock x y cl)
            (clock_of_ty ty) assocs in
        compose_clock cl cever.cexpr_clock)
        node.cn_output in
    let outcl =
      (match outcls with
       | [] -> failwith "Should not happen (syntax)"
       | [cl] -> cl
       | _ -> Ctuple outcls) in
    { cexpr_desc = CE_app (fid, ces, cever); cexpr_ty = ty;
      cexpr_clock = outcl; cexpr_loc = loc }

(** Check the clocks for the equation [eq] *)
let clock_equation nodes streams (eq : t_equation) =
  let (expected, pat) = get_pattern_clock streams eq.teq_patt
  and ce = clock_expr nodes streams eq.teq_expr in
  if (ce.cexpr_clock <> expected)
  then raise (ClockError
                (Printf.sprintf
                   "Wrong clock for equation %s; expected %s, found %s"
                   (TMinils.string_of_equation eq)
                   (string_of_clock expected)
                   (string_of_clock ce.cexpr_clock), eq.teq_expr.texpr_loc));
  { ceq_patt = pat ; ceq_expr = ce }

(** Check the clocks for the node [f] *)
let clock_node (nodes : (ident * c_node) list) (n : t_node) : c_node =
  let streams = List.map (fun (id, ty) -> (id, clock_of_ty ty))
      (n.tn_input@n.tn_local@n.tn_output) in
  { cn_name = n.tn_name;
    cn_input = n.tn_input;
    cn_output = n.tn_output;
    cn_local = n.tn_local;
    cn_equs = List.map (clock_equation nodes streams) n.tn_equs;
    cn_loc = n.tn_loc }

(** Check the clocks for the file [f] *)
let clock_file (f : t_file) : c_file =
  let nodes =
    try List.rev
          (List.map snd
             (List.fold_left (fun env n ->
                  (n.tn_name, (clock_node env n))::env) [] f.tf_nodes))
    with
    | ClockError (msg, loc) ->
      Printf.printf "Clock checking error : %s at %s\n"
        msg (string_of_loc loc); exit 1 in
  { cf_nodes = nodes; cf_clocks = f.tf_clocks }

(*                           Check equivalence between ASTs                    *)

(** Check that a typed pattern [t] and clocked pattern [c] are equivalent *)
let equiv_parse_clock_patt (t : t_patt) (c : c_patt) =
    match t.kpatt_desc, c.cpatt_desc with
    | KP_ident id1, CP_ident id2 when id1 = id2 -> true
    | KP_tuple ids1, CP_tuple ids2 ->
      List.for_all2 (fun id1 id2 -> id1 = id2) ids1 ids2
    | _, _ -> false

(** Check that a typed expr [t] and clocked expr [c] are equivalent *)
let rec equiv_parse_clock_expr (t : t_expr) (c : c_expr) =
  t.texpr_ty = c.cexpr_ty &&
  match t.texpr_desc, c.cexpr_desc with
  | TE_const c1, CE_const c2 -> c1 = c2
  | TE_ident c1, CE_ident c2 -> c1 = c2
  | TE_op (op1, es1), CE_op (op2, es2) ->
    op1 = op2 && List.for_all2 equiv_parse_clock_expr es1 es2
  | TE_app (id1, es1, ev1), CE_app (id2, es2, ev2) ->
    id1 = id2 && List.for_all2 equiv_parse_clock_expr es1 es2 &&
    equiv_parse_clock_expr ev1 ev2
  | TE_fby (c1, e1), CE_fby (c2, e2) ->
    c1 = c2 && equiv_parse_clock_expr e1 e2
  | TE_tuple es1, CE_tuple es2 ->
    List.for_all2 equiv_parse_clock_expr es1 es2
  | TE_when (e1, c1, id1), CE_when (e2, c2, id2) ->
    equiv_parse_clock_expr e1 e2 && c1 = c2 && id1 = id2
  | TE_merge (id1, es1), CE_merge (id2, es2) ->
    id1 = id2 &&
    List.for_all2 (fun (c1, e1) (c2, e2) ->
        c1 = c2 && equiv_parse_clock_expr e1 e2) es1 es2
  | _, _ -> false

(** Check that a typed equation [t] and clocked equation [c] are equivalent *)
let equiv_parse_clock_eq (t : t_equation) (c : c_equation) =
  equiv_parse_clock_patt t.teq_patt c.ceq_patt &&
  equiv_parse_clock_expr t.teq_expr c.ceq_expr

(** Check that a typed node [t] and clocked node [c] are equivalent *)
let equiv_parse_clock_node (t : t_node) (c : c_node) =
  t.tn_name = c.cn_name &&
  t.tn_input = c.cn_input &&
  t.tn_output = c.cn_output &&
  t.tn_local = c.cn_local &&
  List.for_all2 equiv_parse_clock_eq t.tn_equs c.cn_equs

(** Check that a typed file [t] and clocked file [c] are equivalent *)
let equiv_parse_clock_file (t : t_file) (c : c_file) =
  t.tf_clocks = c.cf_clocks &&
  try
    List.for_all2 equiv_parse_clock_node t.tf_nodes c.cf_nodes
  with _ -> false
