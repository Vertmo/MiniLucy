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

(** Unify two clocks [cl1] and [cl2] *)
let rec unify_clock cl1 cl2 =
  match cl1, cl2 with
  | Base, Base -> ([], Base, Base)
  | c, Base -> ([], c, Base)
  | Base, c -> ([], Base, c)
  | Cl (b1, c1, clid1), Cl (b2, c2, clid2) ->
    if c1 <> c2
    then raise (ClockError
                  (Printf.sprintf "Could not unify clocks %s and %s"
                     (string_of_clock cl1) (string_of_clock cl2), dummy_loc));
    let (assocs, b1, b2) = unify_clock b1 b2 in
    ((clid1, clid2)::assocs, b1, b2)
  | _, _ ->
    raise (ClockError
             (Printf.sprintf "Clock tuple not supported in unification",
              dummy_loc))

(** Apply a set of substitutions to a clock *)
let rec apply_substs substs = function
  | Base -> Base
  | Cl (base, constr, clid) ->
    (match (List.assoc_opt clid substs) with
     | Some clid -> Cl (apply_substs substs base, constr, clid)
     | None -> Cl (apply_substs substs base, constr, clid))
  | Ctuple cls ->
    Ctuple (List.map (apply_substs substs) cls)

(** Remove the whens in front of an expression *)
let rec strip_whens e =
  match e.texpr_desc with
  | TE_when (e, _, _) -> strip_whens e
  | _ -> e

(** Check and get the clocked version of expression [e] *)
let rec clock_expr nodes streams expected_cl (e : t_expr) =
  let loc = e.texpr_loc and ty = e.texpr_ty in
  match e.texpr_desc with
  | TE_const c ->
    (* A constant can be subsampled to any clock ! *)
    { cexpr_desc = CE_const c; cexpr_ty = ty;
      cexpr_clock = expected_cl; cexpr_loc = loc }
  | TE_ident id ->
    let cl = (List.assoc id streams) in
    if (cl <> expected_cl)
    then raise
        (ClockError
           (Printf.sprintf
              "The stream %s doesn't have the expected clock %s (found %s)"
              id (string_of_clock cl) (string_of_clock expected_cl),
            loc));
    { cexpr_desc = CE_ident id; cexpr_ty = ty;
      cexpr_clock = cl; cexpr_loc = loc }
  | TE_op (op, es) ->
    let ces = List.map (clock_expr nodes streams expected_cl) es in
    { cexpr_desc = CE_op (op, ces); cexpr_ty = ty;
      cexpr_clock = expected_cl; cexpr_loc = loc}
  | TE_fby (c, e) ->
    let ce = clock_expr nodes streams expected_cl e in
    { cexpr_desc = CE_fby (c, ce) ; cexpr_ty = ty;
      cexpr_clock = ce.cexpr_clock; cexpr_loc = loc }
  | TE_tuple es ->
    (match expected_cl with
     | Ctuple cls ->
       let ces = List.map2 (clock_expr nodes streams) cls es in
       { cexpr_desc = CE_tuple ces; cexpr_ty = ty;
         cexpr_clock = expected_cl; cexpr_loc = loc}
     | _ -> raise
              (ClockError
                 (Printf.sprintf "Incorrect clock for tuple : %s"
                    (string_of_clock expected_cl), loc)))
  | TE_when (ew, constr, clid) ->
    (match expected_cl with
     | Cl (expected_cl, constr', clid') ->
       let cew = clock_expr nodes streams expected_cl ew in
       if(clid <> clid' || constr <> constr')
       then raise
           (ClockError
              (Printf.sprintf
                 "Wrong clock parameters for when expression:\
                  expected %s, found %s(%s)"
                 (string_of_clock expected_cl) constr' clid, loc));
       { cexpr_desc = CE_when (cew, constr, clid); cexpr_ty = ty;
         cexpr_clock = Cl (cew.cexpr_clock, constr, clid); cexpr_loc = loc }
     | _ -> raise
              (ClockError
                 (Printf.sprintf
                    "Incorrect clock for when expression: %s"
                    (string_of_clock expected_cl), loc)))
  | TE_merge (clid, es) ->
    (* Get the type of the clock *)
    let ces = List.map (fun (c, e) ->
        c, clock_expr nodes streams (Cl (expected_cl, c, clid)) e) es in

    { cexpr_desc = CE_merge (clid, ces); cexpr_ty = ty;
      cexpr_clock = expected_cl; cexpr_loc = loc }
  | TE_app (fid, es, ever) ->
    (* Output clocks of the application should be the expected clock *)
    let output_cls = (match expected_cl with
      | Ctuple cls -> cls
      | cl -> [cl]) in
    let node = List.assoc fid nodes in

    (* Checking the relation between formal and expected output clocks
       allow us to get the "base" clock for the called node *)
    let unifiers =
      List.map2 (fun (_, ty) actual -> unify_clock (clock_of_ty ty) actual
                ) node.cn_output output_cls in
    let (_, _, base) = List.hd unifiers in
    let substs = List.flatten (List.map (fun (s, _, _) -> s) unifiers) in

    (* Verify that the unifiers are compatible *)
    if not ((List.for_all (fun (_, b1, b2) -> b1 = Base && b2 = base) unifiers))
    then raise (ClockError ("Unifiers are not compatible", loc));

    (* Verify that substitutions are compatible *)
    let rec verif_substs = function
      | [] -> ()
      | (x, y)::tl -> ((match List.assoc_opt x tl with
          | Some y' -> if y' <> y then
              raise (ClockError ("Unifiers are not compatible", loc));
          | None -> ()); verif_substs tl)
    in verif_substs substs;

    (* This base clock should be the clock of the "every" expression *)
    let cever = clock_expr nodes streams base ever in

    (* And should be used to clock the actual parameters of the function *)
    let ces = List.map2 (fun e (id, ty) ->
        (* Verify that the correct clock is passed *)
        if (List.mem_assoc id substs) then (
          let id' = List.assoc id substs in
          if ((strip_whens e).texpr_desc <> TE_ident id') then
            raise
              (ClockError
                 (Printf.sprintf
                    "Clock %s should be passed to function, %s found instead"
                    id' (TMinils.string_of_expr e), loc))
        );
        let cl = apply_substs substs (clock_of_ty ty) in
        clock_expr nodes streams (compose_clock cl base) e)
        es node.cn_input in

    { cexpr_desc = CE_app (fid, ces, cever); cexpr_ty = ty;
      cexpr_clock = expected_cl; cexpr_loc = loc }

(** Check the clocks for the equation [eq] *)
let clock_equation nodes streams (eq : t_equation) =
  let (expected, pat) = get_pattern_clock streams eq.teq_patt in
  let ce = clock_expr nodes streams expected eq.teq_expr in
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
let equiv_clock_patt (t : t_patt) (c : c_patt) =
    match t.kpatt_desc, c.cpatt_desc with
    | KP_ident id1, CP_ident id2 when id1 = id2 -> true
    | KP_tuple ids1, CP_tuple ids2 ->
      List.for_all2 (fun id1 id2 -> id1 = id2) ids1 ids2
    | _, _ -> false

(** Check that a typed expr [t] and clocked expr [c] are equivalent *)
let rec equiv_clock_expr (t : t_expr) (c : c_expr) =
  t.texpr_ty = c.cexpr_ty &&
  match t.texpr_desc, c.cexpr_desc with
  | TE_const c1, CE_const c2 -> c1 = c2
  | TE_ident c1, CE_ident c2 -> c1 = c2
  | TE_op (op1, es1), CE_op (op2, es2) ->
    op1 = op2 && List.for_all2 equiv_clock_expr es1 es2
  | TE_app (id1, es1, ev1), CE_app (id2, es2, ev2) ->
    id1 = id2 && List.for_all2 equiv_clock_expr es1 es2 &&
    equiv_clock_expr ev1 ev2
  | TE_fby (c1, e1), CE_fby (c2, e2) ->
    c1 = c2 && equiv_clock_expr e1 e2
  | TE_tuple es1, CE_tuple es2 ->
    List.for_all2 equiv_clock_expr es1 es2
  | TE_when (e1, c1, id1), CE_when (e2, c2, id2) ->
    equiv_clock_expr e1 e2 && c1 = c2 && id1 = id2
  | TE_merge (id1, es1), CE_merge (id2, es2) ->
    id1 = id2 &&
    List.for_all2 (fun (c1, e1) (c2, e2) ->
        c1 = c2 && equiv_clock_expr e1 e2) es1 es2
  | _, _ -> false

(** Check that a typed equation [t] and clocked equation [c] are equivalent *)
let equiv_clock_eq (t : t_equation) (c : c_equation) =
  equiv_clock_patt t.teq_patt c.ceq_patt &&
  equiv_clock_expr t.teq_expr c.ceq_expr

(** Check that a typed node [t] and clocked node [c] are equivalent *)
let equiv_clock_node (t : t_node) (c : c_node) =
  t.tn_name = c.cn_name &&
  t.tn_input = c.cn_input &&
  t.tn_output = c.cn_output &&
  t.tn_local = c.cn_local &&
  List.for_all2 equiv_clock_eq t.tn_equs c.cn_equs

(** Check that a typed file [t] and clocked file [c] are equivalent *)
let equiv_clock_file (t : t_file) (c : c_file) =
  t.tf_clocks = c.cf_clocks &&
  try
    List.for_all2 equiv_clock_node t.tf_nodes c.cf_nodes
  with _ -> false
