(** Clock checking *)

open Asttypes
open TMinils
open CMinils

exception ClockError of (string * location)

(** Get the clocks(s) expected for a pattern [pat],
    as well as the translated pattern *)
let get_pattern_clock (streams : (ident * clock) list) (pat : t_patt) =
  match pat.ppatt_desc with
  | PP_ident id ->
    (List.assoc id streams),
    { cpatt_desc = CP_ident id; cpatt_loc = pat.ppatt_loc }
  | PP_tuple ids ->
    (Ctuple (List.map (fun id -> (List.assoc id streams)) ids)),
     { cpatt_desc = CP_tuple ids; cpatt_loc = pat.ppatt_loc }

(** Composes clocks [cl1] and [cl2] to give (returns [cl1] o [cl2]) *)
let rec compose_clock cl1 cl2 =
  match cl1 with
  | Base -> cl2
  | Cl (cl, x') -> Cl (compose_clock cl cl2, x')
  | NotCl (cl, x') -> NotCl (compose_clock cl cl2, x')
  | Ctuple cls -> Ctuple (List.map (fun cl -> compose_clock cl cl2) cls)

(** Substitute a (CE_ident) to another identifier in a clock expression *)
let subst_clock (x : ident) (y : c_expr) (cl : clock) =
  let rec subst_aux (x : ident) (y : ident) = function
    | Base -> Base
    | Cl (cl, x') ->
      Cl (subst_aux x y cl, if x = x' then y else x')
    | NotCl (cl, x') ->
      NotCl (subst_aux x y cl, if x = x' then y else x')
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
  | TE_when (ew, clid, b) ->
    let cew = clock_expr nodes streams ew in
    let cl = if b
      then Cl (cew.cexpr_clock, clid)
      else NotCl (cew.cexpr_clock, clid) in
    { cexpr_desc = CE_when (cew, clid, b); cexpr_ty = ty;
      cexpr_clock = cl; cexpr_loc = loc }
  | TE_merge (clid, e1, e2) ->
    let ce1 = clock_expr nodes streams e1
    and ce2 = clock_expr nodes streams e2 in
    let cl = (match ce1.cexpr_clock, ce2.cexpr_clock with
        | Cl (base1, id1), NotCl (base2, id2)
          when base1 = base2 && id1 = id2 -> base1
        | NotCl (base1, id1), Cl (base2, id2)
          when base1 = base2 && id1 = id2 -> base1
        | cl1, cl2 ->
          raise
            (ClockError
               (Printf.sprintf
                  "Clocks of merge do not match expected id %s, found %s and %s"
                  clid (string_of_clock cl1) (string_of_clock cl2), loc))) in
    { cexpr_desc = CE_merge (clid, ce1, ce2); cexpr_ty = ty;
      cexpr_clock = cl; cexpr_loc = loc }
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
  try List.rev
        (List.map snd
           (List.fold_left (fun env n ->
                (n.tn_name, (clock_node env n))::env) [] f))
  with
  | ClockError (msg, loc) ->
    Printf.printf "Clock checking error : %s at %s\n"
      msg (string_of_loc loc); exit 1

(*                           Check equivalence between ASTs                    *)

(** Check that a parsed pattern [p] and clocked pattern [c] are equivalent *)
let equiv_parse_clock_pat (p : t_patt) (c : c_patt) =
    match p.ppatt_desc, c.cpatt_desc with
    | PP_ident id1, CP_ident id2 when id1 = id2 -> true
    | PP_tuple ids1, CP_tuple ids2 ->
      List.for_all2 (fun id1 id2 -> id1 = id2) ids1 ids2
    | _, _ -> false

(** Check that a parsed expr [p] and clocked expr [c] are equivalent *)
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
  | TE_when (e1, id1, b1), CE_when (e2, id2, b2) ->
    equiv_parse_clock_expr e1 e2 && id1 = id2 && b1 = b2
  | TE_merge (id1, e11, e12), CE_merge (id2, e21, e22) ->
    id1 = id2 &&
    equiv_parse_clock_expr e11 e21 && equiv_parse_clock_expr e12 e22
  | _, _ -> false

(** Check that a parsed equation [p] and clocked equation [c] are equivalent *)
let equiv_parse_clock_eq (p : t_equation) (c : c_equation) =
  equiv_parse_clock_pat p.teq_patt c.ceq_patt &&
  equiv_parse_clock_expr p.teq_expr c.ceq_expr

(** Check that a parsed node [p] and clocked node [c] are equivalent *)
let equiv_parse_clock_node (p : t_node) (c : c_node) =
  p.tn_name = c.cn_name &&
  p.tn_input = c.cn_input &&
  p.tn_output = c.cn_output &&
  p.tn_local = c.cn_local &&
  List.for_all2 equiv_parse_clock_eq p.tn_equs c.cn_equs

(** Check that a parsed file [p] and clocked file [c] are equivalent *)
let equiv_parse_clock_file (p : t_file) (c : c_file) =
  try
    List.for_all2 equiv_parse_clock_node p c
  with _ -> false
