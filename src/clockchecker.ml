(** Clock checking *)

open Asttypes
open Minils
open PMinils

type nclock = (clock * ident option)

module TypeClockAnnot : (Annotations with type t = (ty * nclock)) = struct
  type t = (ty * nclock)
  let string_of_t (ty, (ck, _)) =
    Printf.sprintf "(%s when %s)" (string_of_ty ty) (string_of_clock ck)
end

module CPMinils = PMINILS(TypeClockAnnot)

open Typechecker.TPMinils

exception ClockError of (string * location)

let clocks_of (es : CPMinils.k_expr list) =
  List.concat (List.map (fun (e : CPMinils.k_expr) -> List.map snd e.kexpr_annot) es)

(** Composes clocks [ck1] and [ck2] to give (returns [ck1] o [ck2]) *)
let rec compose_clock ck1 ck2 =
  match ck1 with
  | Cbase -> ck2
  | Con (constr, ckid, base) -> Con (constr, ckid, compose_clock base ck2)

(** Unify two clocks [cl1] and [cl2] *)
let rec unify_clock cl1 cl2 =
  match cl1, cl2 with
  | Cbase, Cbase -> ([], Cbase, Cbase)
  | c, Cbase -> ([], c, Cbase)
  | Cbase, c -> ([], Cbase, c)
  | Con (c1, ckid1, b1), Con (c2, ckid2, b2) ->
    if c1 <> c2
    then raise (ClockError
                  (Printf.sprintf "Could not unify clocks %s and %s"
                     (string_of_clock cl1) (string_of_clock cl2), dummy_loc));
    let (assocs, b1, b2) = unify_clock b1 b2 in
    ((ckid1, ckid2)::assocs, b1, b2)

(* (\** Apply a set of substitutions to a clock *\)
 * let rec apply_substs substs = function
 *   | Cbase -> Cbase
 *   | Con (constr, ckid, base) ->
 *     (match (List.assoc_opt ckid substs) with
 *      | Some ckid -> Con (constr, ckid, apply_substs substs base)
 *      | None -> Con (constr, ckid, apply_substs substs base))
 *   | Ctuple cls ->
 *     Ctuple (List.map (apply_substs substs) cls)
 * 
 * (\** Remove the whens in front of an expression *\)
 * let rec strip_whens e =
 *   match e.kexpr_desc with
 *   | KE_when (e, _, _) -> strip_whens e
 *   | _ -> e
 * 
 * (\** Check and get the clocked version of expression [e] *\)
 * let rec elab_expr (nodes : (ident * CPMinils.p_node) list)
 *     vars expected_cl (e : k_expr) : CPMinils.k_expr =
 *   let loc = e.kexpr_loc and ty = e.kexpr_annot in
 *   match e.kexpr_desc with
 *   | KE_const c ->
 *     (\* A constant can be subsampled to any clock ! *\)
 *     { kexpr_desc = KE_const c; kexpr_annot = (ty, expected_cl);
 *       kexpr_loc = loc }
 *   | KE_ident id ->
 *     let cl = (List.assoc id vars) in
 *     if (cl <> expected_cl)
 *     then raise
 *         (ClockError
 *            (Printf.sprintf
 *               "The stream %s doesn't have the expected clock %s (found %s)"
 *               id (string_of_clock expected_cl) (string_of_clock cl),
 *             loc));
 *     { kexpr_desc = KE_ident id; kexpr_annot = (ty, cl);
 *       kexpr_loc = loc }
 *   | KE_op (op, es) ->
 *     let ces = List.map (elab_expr nodes vars expected_cl) es in
 *     { kexpr_desc = KE_op (op, ces); kexpr_annot = (ty, expected_cl);
 *       kexpr_loc = loc}
 *   | KE_fby (e0, e) ->
 *     let ce0 = elab_expr nodes vars expected_cl e0 in
 *     let ce = elab_expr nodes vars expected_cl e in
 *     { kexpr_desc = KE_fby (ce0, ce) ; kexpr_annot = (ty, snd ce.kexpr_annot);
 *       kexpr_loc = loc }
 *   | KE_arrow (e0, e) ->
 *     let ce0 = elab_expr nodes vars expected_cl e0 in
 *     let ce = elab_expr nodes vars expected_cl e in
 *     { kexpr_desc = KE_arrow (ce0, ce) ; kexpr_annot = (ty, snd ce.kexpr_annot);
 *       kexpr_loc = loc }
 *   | KE_tuple es ->
 *     (match expected_cl with
 *      | Ctuple cls ->
 *        let ces = List.map2 (elab_expr nodes vars) cls es in
 *        { kexpr_desc = KE_tuple ces; kexpr_annot = (ty, expected_cl);
 *          kexpr_loc = loc}
 *      | _ -> raise
 *               (ClockError
 *                  (Printf.sprintf "Incorrect clock for tuple : %s"
 *                     (string_of_clock expected_cl), loc)))
 *   | KE_switch (e, es) ->
 *     (\* Get the type of the clock *\)
 *     let ce = elab_expr nodes vars expected_cl e in
 *     let ces = List.map (fun (c, e) ->
 *         c, elab_expr nodes vars expected_cl e) es in
 * 
 *     { kexpr_desc = KE_switch (ce, ces); kexpr_annot = (ty, expected_cl);
 *       kexpr_loc = loc }
 *   | KE_when (ew, constr, clid) ->
 *     (match expected_cl with
 *      | Con (constr', clid', expected_cl) ->
 *        let cew = elab_expr nodes vars expected_cl ew in
 *        if(clid <> clid' || constr <> constr')
 *        then raise
 *            (ClockError
 *               (Printf.sprintf
 *                  "Wrong clock parameters for when expression:\
 *                   expected %s, found %s(%s)"
 *                  (string_of_clock expected_cl) constr' clid, loc));
 *        { kexpr_desc = KE_when (cew, constr, clid);
 *          kexpr_annot = (ty, Con (constr, clid, snd cew.kexpr_annot));
 *          kexpr_loc = loc }
 *      | _ -> raise
 *               (ClockError
 *                  (Printf.sprintf
 *                     "Incorrect clock for when expression: %s"
 *                     (string_of_clock expected_cl), loc)))
 *   | KE_merge (clid, es) ->
 *     (\* Get the type of the clock *\)
 *     let ces = List.map (fun (c, e) ->
 *         c, elab_expr nodes vars (Con (c, clid, expected_cl)) e) es in
 * 
 *     { kexpr_desc = KE_merge (clid, ces); kexpr_annot = (ty, expected_cl);
 *       kexpr_loc = loc }
 *   | KE_app (fid, es, ever) ->
 *     (\* Output clocks of the application should be the expected clock *\)
 *     let output_cls = (match expected_cl with
 *       | Ctuple cls -> cls
 *       | cl -> [cl]) in
 *     let node = List.assoc fid nodes in
 * 
 *     (\* Checking the relation between formal and expected output clocks
 *        allow us to get the "base" clock for the called node *\)
 *     let unifiers =
 *       List.map2 (fun (_, (ty, ck)) actual -> unify_clock ck actual
 *                 ) node.pn_output output_cls in
 *     let (_, _, base) = List.hd unifiers in
 *     let substs = List.flatten (List.map (fun (s, _, _) -> s) unifiers) in
 * 
 *     (\* Verify that the unifiers are compatible *\)
 *     if not ((List.for_all (fun (_, b1, b2) -> b1 = Cbase && b2 = base) unifiers))
 *     then raise (ClockError ("Unifiers are not compatible", loc));
 * 
 *     (\* Verify that substitutions are compatible *\)
 *     let rec verif_substs = function
 *       | [] -> ()
 *       | (x, y)::tl -> ((match List.assoc_opt x tl with
 *           | Some y' -> if y' <> y then
 *               raise (ClockError ("Unifiers are not compatible", loc));
 *           | None -> ()); verif_substs tl)
 *     in verif_substs substs;
 * 
 *     (\* This base clock should be the clock of the "every" expression *\)
 *     let cever = elab_expr nodes vars base ever in
 * 
 *     (\* And should be used to clock the actual parameters of the function *\)
 *     let ces = List.map2 (fun e (id, (ty, ck)) ->
 *         (\* Verify that the correct clock is passed *\)
 *         if (List.mem_assoc id substs) then (
 *           let id' = List.assoc id substs in
 *           if ((strip_whens e).kexpr_desc <> KE_ident id') then
 *             raise
 *               (ClockError
 *                  (Printf.sprintf
 *                     "Clock %s should be passed to function, %s found instead"
 *                     id' (string_of_expr e), loc))
 *         );
 *         let cl = apply_substs substs ck in
 *         elab_expr nodes vars (compose_clock cl base) e)
 *         es node.pn_input in
 * 
 *     { kexpr_desc = KE_app (fid, ces, cever); kexpr_annot = (ty, expected_cl);
 *       kexpr_loc = loc }
 * 
 * (\** Get the clocks(s) expected for a pattern [pat],
 *     as well as the translated pattern *\)
 * let get_pattern_clock (vars : (ident * clock) list) (pat : k_patt) :
 *   clock * CPMinils.k_patt =
 *   match pat.kpatt_desc with
 *   | KP_ident id ->
 *     (List.assoc id vars),
 *     { kpatt_desc = KP_ident id; kpatt_loc = pat.kpatt_loc }
 *   | KP_tuple ids ->
 *     (Ctuple (List.map (fun id -> (List.assoc id vars)) ids)),
 *     { kpatt_desc = KP_tuple ids; kpatt_loc = pat.kpatt_loc }
 * 
 * (\** Check the clocks for the equation [eq] *\)
 * let elab_equation nodes vars (eq : k_equation) : CPMinils.k_equation =
 *   let (expected, pat) = get_pattern_clock vars eq.keq_patt in
 *   let ce = elab_expr nodes vars expected eq.keq_expr in
 *   { keq_patt = pat ; keq_expr = ce }
 * 
 * let rec elab_instr nodes vars (ins : p_instr) : CPMinils.p_instr =
 *   match ins with
 *   | Eq eq -> Eq (elab_equation nodes vars eq)
 *   | Reset (ins, er) ->
 *     Reset (elab_instrs nodes vars ins,
 *            elab_expr nodes vars Cbase (\* TODO *\) er)
 *   | _ -> failwith "TODO elab_instr"
 * and elab_instrs nodes vars ins =
 *   List.map (elab_instr nodes vars) ins
 * 
 * (\** Check the clocks for the node [f] *\)
 * let elab_node (nodes : (ident * CPMinils.p_node) list) (n : p_node) : CPMinils.p_node =
 *   let streams = List.map (fun (id, (ty, ck)) -> (id, ck))
 *       (n.pn_input@n.pn_local@n.pn_output) in
 *   { pn_name = n.pn_name;
 *     pn_input = n.pn_input;
 *     pn_output = n.pn_output;
 *     pn_local = n.pn_local;
 *     pn_instrs = elab_instrs nodes streams n.pn_instrs;
 *     pn_loc = n.pn_loc } *)

(** Check the clocks for the file [f] *)
let elab_file (f : p_file) : CPMinils.p_file =
  failwith "TODO"
  (* let nodes =
   *   try List.rev
   *         (List.map snd
   *            (List.fold_left (fun (env : (ident * CPMinils.p_node) list) n ->
   *                 (n.pn_name, (elab_node env n))::env) [] f.pf_nodes))
   *   with
   *   | ClockError (msg, loc) ->
   *     Printf.printf "Clock checking error : %s at %s\n"
   *       msg (string_of_loc loc); exit 1 in
   * { pf_nodes = nodes; pf_clocks = f.pf_clocks } *)
