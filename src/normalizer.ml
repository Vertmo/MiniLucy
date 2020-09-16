(** Normalize the equations *)

open Asttypes
open Kernelizer.CMinils
open NMinils

(** First pass : separating app, fby and control exprs,
    distribute constructions *)

let idents_for_anns anns =
  List.map (fun (ty, (ck, _)) -> (Atom.fresh "$", (ty, ck))) anns

let idents_for_anns' anns =
  List.map (fun (ty, (ck, id)) ->
      match id with
      | Some id -> (id, (ty, ck))
      | None -> (Atom.fresh "$", (ty, ck))) anns

let dist_make_vars ids =
  List.map (fun (id, (ty, ck)) ->
      { kexpr_desc = KE_ident id; kexpr_annot = [(ty, (ck, Some id))];
        kexpr_loc = dummy_loc })
    ids

let dist_make_eqs ids es =
  List.map (fun ((id, _), e) ->
      { keq_patt = [id]; keq_expr = [e]; keq_loc = dummy_loc }
    ) (List.combine ids es)

let dist_fby e0s es anns =
  List.map (fun ((e0, e), a) ->
      { kexpr_desc = KE_fby ([e0], [e]); kexpr_annot = [a]; kexpr_loc = dummy_loc }
    ) (List.combine (List.combine e0s es) anns)

let dist_arrow e0s es anns =
  List.map (fun ((e0, e), a) ->
      { kexpr_desc = KE_arrow ([e0], [e]); kexpr_annot = [a]; kexpr_loc = dummy_loc }
    ) (List.combine (List.combine e0s es) anns)

let dist_switch e branches anns =
  List.mapi (fun i a ->
      { kexpr_desc = KE_switch (e, List.map (fun (c, es) -> (c, [List.nth es i])) branches);
        kexpr_annot = [a]; kexpr_loc = dummy_loc }
    ) anns

let dist_when constr ckid es anns =
  List.map (fun (e, a) ->
      { kexpr_desc = KE_when ([e], constr, ckid); kexpr_annot = [a]; kexpr_loc = dummy_loc }
    ) (List.combine es anns)

let dist_merge ckid branches anns =
  List.mapi (fun i a ->
      { kexpr_desc = KE_merge (ckid, List.map (fun (c, es) -> (c, [List.nth es i])) branches);
        kexpr_annot = [a]; kexpr_loc = dummy_loc }
    ) anns

let rec dist_expr (is_control : bool) (e : k_expr) :
  (k_expr list * k_equation list * (ident * ann) list) =
  let anns = e.kexpr_annot in
  match e.kexpr_desc with
  | KE_const _ | KE_ident _ ->
    [e], [], []
  | KE_unop (op, e1) ->
    let e1', eqs1, vs1 = dist_expr false e1 in
    let e1' = List.hd e1' in
    [{ e with kexpr_desc = KE_unop (op, e1') }], eqs1, vs1
  | KE_binop (op, e1, e2) ->
    let e1', eqs1, vs1 = dist_expr false e1
    and e2', eqs2, vs2 = dist_expr false e2 in
    let e1' = List.hd e1' and e2' = List.hd e2' in
    [{ e with kexpr_desc = KE_binop (op, e1', e2') }], eqs1@eqs2, vs1@vs2
  | KE_fby (e0s, es) ->
    let e0s', eqs1, vs1 = dist_exprs false e0s
    and es', eqs2, vs2 = dist_exprs false es in
    let fbys = dist_fby e0s' es' anns in
    let ids = idents_for_anns anns in
    dist_make_vars ids,
    (dist_make_eqs ids fbys)@eqs1@eqs2,
    vs1@vs2@ids
  | KE_arrow (e0s, es) ->
    let e0s', eqs1, vs1 = dist_exprs false e0s
    and es', eqs2, vs2 = dist_exprs false es in
    let arrows = dist_arrow e0s' es' anns in
    let ids = idents_for_anns anns in
    dist_make_vars ids,
    (dist_make_eqs ids arrows)@eqs1@eqs2,
    vs1@vs2@ids
  | KE_switch (e, branches) ->
    let e', eqs1, vs1 = dist_expr false e
    and branches', eqs2, vs2 = dist_branches branches in
    let switches = dist_switch e branches anns in
    if is_control then
      switches, eqs1@eqs2, vs1@vs2
    else let ids = idents_for_anns anns in
      dist_make_vars ids,
      (dist_make_eqs ids switches)@eqs1@eqs2,
      vs1@vs2@ids
  | KE_when (es, constr, ckid) ->
    let es', eqs1, vs1 = dist_exprs false es in
    dist_when constr ckid es' anns, eqs1, vs1
  | KE_merge (ckid, branches) ->
    let branches', eqs1, vs1 = dist_branches branches in
    let merges = dist_merge ckid branches anns in
    if is_control then
      merges, eqs1, vs1
    else let ids = idents_for_anns anns in
      dist_make_vars ids,
      (dist_make_eqs ids merges)@eqs1,
      vs1@ids
  | KE_app (fid, es, er) ->
    let es', eqs1, vs1 = dist_exprs false es
    and er', eqs2, vs2 = dist_expr false er in
    let ids = idents_for_anns' anns in
    dist_make_vars ids,
    { keq_patt = List.map fst ids;
      keq_expr = [{ kexpr_desc = KE_app (fid, es', List.hd er');
                    kexpr_annot = anns;
                    kexpr_loc = dummy_loc }];
      keq_loc = dummy_loc }::eqs1@eqs2,
    vs1@vs2@ids

and dist_exprs (is_control : bool) (es : k_expr list) =
  let res = List.map (dist_expr is_control) es in
  (List.concat (List.map (fun (e, _, _) -> e) res),
   List.concat (List.map (fun (_, eq, _) -> eq) res),
   List.concat (List.map (fun (_, _, v) -> v) res))

and dist_branches (branches : (constr * k_expr list) list) =
  let res = List.map (fun (cstr, es) ->
      let es', eqs, vs = dist_exprs true es in
      (cstr, es'), eqs, vs) branches in
  (List.map (fun (e, _, _) -> e) res,
   List.concat (List.map (fun (_, eq, _) -> eq) res),
   List.concat (List.map (fun (_, _, v) -> v) res))

(** Distribute operators in an equation an equation *)
let rec firstn n l =
  if n = 0 then []
  else match l with
    | hd::tl -> hd::firstn (n - 1) tl
    | _ -> invalid_arg "firstn"

let rec skipn n l =
  if n = 0 then l
  else match l with
    | hd::tl -> skipn (n - 1) tl
    | _ -> invalid_arg "skipn"

let rec combine_for_numstreams (es : k_expr list) (vs : 'a list) =
  match es with
  | [] -> []
  | (hd::tl) -> let n = List.length hd.kexpr_annot in
    (hd, (firstn n vs))::(combine_for_numstreams tl (skipn n vs))

let dist_eq (eq : k_equation) : (k_equation list * (ident * ann) list) =
  let (es, eqs, vs) = dist_exprs true eq.keq_expr in
  let eqs' = combine_for_numstreams es eq.keq_patt in
  (List.map (fun (e, ids) ->
       { keq_patt = ids; keq_expr = [e]; keq_loc = dummy_loc }
     ) eqs')@eqs, vs

let dist_eqs (eqs : k_equation list) =
  let res = List.map dist_eq eqs in
  (List.concat (List.map fst res),
   List.concat (List.map snd res))

(** Second pass : put reset expressions aside *)

let norm_reset_eq (eq : k_equation) : (k_equation list * (ident * ann) list) =
  match eq.keq_expr with
  | [{ kexpr_desc = KE_app (f, es, { kexpr_desc = KE_ident _}) }] -> [eq], []
  | [{ kexpr_desc = KE_app (f, es, er) } as e] ->
    let y = Atom.fresh "$"
    and (ty, (ck, _)) = List.hd er.kexpr_annot in
    [{ keq_patt = [y]; keq_expr = [er]; keq_loc = dummy_loc };
     { eq with keq_expr = [{ e with
                             kexpr_desc = KE_app (f, es, { kexpr_desc = KE_ident y;
                                                           kexpr_annot = er.kexpr_annot;
                                                           kexpr_loc = dummy_loc })}]}],
    [(y, (ty, ck))]
  | _ -> [eq], []

let norm_reset_eqs (eqs : k_equation list) =
  let res = List.map norm_reset_eq eqs in
  (List.concat (List.map fst res),
   List.concat (List.map snd res))

(** Third pass : initialize fbys with constant only, eliminate arrows *)

let rec is_constant e =
  match e.kexpr_desc with
  | KE_const _ -> true
  | KE_when ([e], _, _) -> is_constant e
  | _ -> false

let rec extract_constant e =
  match e.kexpr_desc with
  | KE_const c -> c
  | KE_when ([e], _, _) -> extract_constant e
  | _ -> failwith "Should not happen"

let rec add_whens ty ck e : k_expr =
  match ck with
  | Cbase -> e
  | Con (constr, ckid, ck) ->
    let e = add_whens ty ck e in
    { kexpr_desc = KE_when ([e], constr, ckid);
      kexpr_annot = [(ty, (Con (constr, ckid, ck), None))];
      kexpr_loc = dummy_loc }

let init_expr ck : k_expr =
  let annot = [(Tbool, (Cbase, None))] in
  { kexpr_desc = KE_fby
        ([add_whens Tbool ck { kexpr_desc = KE_const (Cbool true);
                               kexpr_annot = annot; kexpr_loc = dummy_loc }],
         [add_whens Tbool ck { kexpr_desc = KE_const (Cbool false);
                               kexpr_annot = annot; kexpr_loc = dummy_loc }]);
    kexpr_loc = dummy_loc; kexpr_annot = [(Tbool, (ck, None))] }

let delay_expr e ty ck : k_expr =
  { kexpr_desc = KE_fby
        ([add_whens Tbool ck { kexpr_desc = KE_const (Cint 0);
                               kexpr_annot = [(ty, (Cbase, None))];
                               kexpr_loc = dummy_loc }],
         [e]);
    kexpr_annot = [(Tbool, (ck, None))]; kexpr_loc = dummy_loc }

let norm_fby_eq (eq : k_equation) : (k_equation list * (ident * ann) list) =
  match eq.keq_expr with
  | [{ kexpr_desc = KE_fby ([e0], [e1]) }] when is_constant e0 -> [eq], []
  | [{ kexpr_desc = KE_fby ([e0], [e1]) } as e] ->
    let (ty, (ck, _)) = List.hd e.kexpr_annot in
    let xinit = Atom.fresh "$" and px = Atom.fresh "$" in
    [{ keq_patt = [xinit]; keq_expr = [init_expr ck]; keq_loc = dummy_loc };
     { keq_patt = [px]; keq_expr = [delay_expr e1 ty ck]; keq_loc = dummy_loc };
     { eq with keq_expr = [{ kexpr_desc = KE_switch ({ kexpr_desc = KE_ident xinit;
                                                       kexpr_annot = [(Tbool, (ck, None))];
                                                       kexpr_loc = dummy_loc },
                                                     [("False", [{ kexpr_desc = KE_ident px;
                                                                  kexpr_annot = [(Tbool, (ck, None))];
                                                                  kexpr_loc = dummy_loc }]);
                                                      ("True", [e0])]);
                             kexpr_annot = [(ty, (ck, None))];
                             kexpr_loc = dummy_loc }] }],
    [ (xinit, (Tbool, ck)); (px, (ty, ck)) ]
  | [{ kexpr_desc = KE_arrow ([e0], [e1]) } as e] ->
    let (ty, (ck, _)) = List.hd e.kexpr_annot in
    let xinit = Atom.fresh "$" in
    [{ keq_patt = [xinit]; keq_expr = [init_expr ck]; keq_loc = dummy_loc };
     { eq with keq_expr = [{ kexpr_desc = KE_switch ({ kexpr_desc = KE_ident xinit;
                                                       kexpr_annot = [(Tbool, (ck, None))];
                                                       kexpr_loc = dummy_loc },
                                                     [("False", [e1]); ("True", [e0])]);
                             kexpr_annot = [(ty, (ck, None))];
                             kexpr_loc = dummy_loc }] }],
    [ (xinit, (Tbool, ck)) ]

  | _ -> [eq], []

let norm_fby_eqs (eqs : k_equation list) =
  let res = List.map norm_fby_eq eqs in
  (List.concat (List.map fst res),
   List.concat (List.map snd res))

(** Last pass : transcription *)

let rec tr_lexp (e : k_expr) : n_expr =
  let (ty, (ck, _)) = List.hd e.kexpr_annot
  and desc = match e.kexpr_desc with
    | KE_const c -> NE_const c
    | KE_ident i -> NE_ident i
    | KE_unop (op, e1) -> NE_op (op, [tr_lexp e1])
    | KE_binop (op, e1, e2) -> NE_op (op, [tr_lexp e1; tr_lexp e2])
    | KE_when ([e], constr, ckid) -> NE_when (tr_lexp e, constr, ckid)
    | _ -> invalid_arg "tr_lexp"
  in { nexpr_desc = desc; nexpr_ty = ty; nexpr_clock = ck }

let tr_lexps = List.map tr_lexp

let rec tr_cexp (e : k_expr) : n_cexpr =
  let (ty, (ck, _)) = List.hd e.kexpr_annot
  and desc = match e.kexpr_desc with
    | KE_switch (e, branches) ->
      NCE_switch (tr_lexp e,
                  List.map (fun (constr, es) ->
                      (constr, tr_cexp (List.hd es))
                    ) branches)
    | KE_merge (ckid, branches) ->
      NCE_merge (ckid,
                 List.map (fun (constr, es) ->
                     (constr, tr_cexp (List.hd es)))
                   branches)
    | _ -> NCE_expr (tr_lexp e).nexpr_desc
  in { ncexpr_desc = desc; ncexpr_ty = ty; ncexpr_clock = ck }

let tr_eq (e : k_equation) : n_equation =
  match e.keq_patt, (List.hd e.keq_expr).kexpr_desc with
    | [x], KE_fby ([{ kexpr_desc = KE_const c}], [e]) ->
      NQ_fby (x, c, tr_lexp e)
    | xs, KE_app (f, es, { kexpr_desc = KE_ident i; kexpr_annot = [(_, (ck, _))] }) ->
      NQ_app (xs, f, tr_lexps es, i, ck)
    | [x], _ ->
      NQ_ident (x, tr_cexp (List.hd e.keq_expr))
    | _ -> invalid_arg "tr_eq"

let tr_eqs = List.map tr_eq

(** Normalize a node *)

let norm_node (n : k_node) =
  let (eqs, vs1) = dist_eqs n.kn_equs in
  let (eqs, vs2) = norm_reset_eqs eqs in
  let (eqs, vs3) = norm_fby_eqs eqs in
  let eqs = tr_eqs eqs in
  { nn_name = n.kn_name;
    nn_input = n.kn_input;
    nn_output = n.kn_output;
    nn_local = n.kn_local@vs1@vs2@vs3;
    nn_equs = eqs }

(** Normalize the whole file *)
let norm_file (f : k_file) =
  { nf_clocks = f.kf_clocks;
    nf_nodes = List.map norm_node f.kf_nodes }

(*                           Check equivalence between ASTs                    *)

(* let rec denorm_expr (e : n_expr) : k_expr =
 *   let desc = match e.nexpr_desc with
 *     | NE_const c -> KE_const c
 *     | NE_ident id -> KE_ident id
 *     | NE_op (op, es) -> KE_op (op, List.map denorm_expr es)
 *     | NE_when (e, c, cid) -> KE_when (denorm_expr e, c, cid)
 *   in { kexpr_desc = desc; kexpr_annot = (e.nexpr_ty, e.nexpr_clock);
 *        kexpr_loc = dummy_loc }
 * 
 * let rec denorm_kexpr (e : n_cexpr) : k_expr =
 *   let desc = match e.ncexpr_desc with
 *     | NCE_merge (cid, branches) ->
 *       KE_merge (cid, List.map (fun (c, e) -> c, denorm_kexpr e) branches)
 *     | NCE_expr e' ->
 *       (denorm_expr { nexpr_desc = e';
 *                      nexpr_clock = e.ncexpr_clock;
 *                      nexpr_ty = e.ncexpr_ty }).kexpr_desc
 *   in { kexpr_desc = desc; kexpr_annot = (e.ncexpr_ty, e.ncexpr_clock);
 *        kexpr_loc = dummy_loc }
 * 
 * (\** Inline variables inside an expression *\)
 * let rec inline_expr asso e =
 *   let desc = match e.kexpr_desc with
 *     | KE_const c -> KE_const c
 *     | KE_ident id ->
 *       (match List.assoc_opt id asso with
 *        | Some e when (String.sub id 0 1 = "_") ->
 *          (inline_expr asso e).kexpr_desc
 *        | _ -> KE_ident id)
 *     | KE_op (op, es) -> KE_op (op, List.map (inline_expr asso) es)
 *     | KE_app (f, es, e) ->
 *       KE_app (f, List.map (inline_expr asso) es, inline_expr asso e)
 *     | KE_fby (c, e) -> KE_fby (c, inline_expr asso e)
 *     | KE_tuple es -> KE_tuple (List.map (inline_expr asso) es)
 *     | KE_when (e, c, clid) -> KE_when (inline_expr asso e, c, clid)
 *     | KE_merge (c, brs) ->
 *       KE_merge (c, List.map (fun (c, e) -> c, inline_expr asso e) brs)
 *   in { e with kexpr_desc = desc }
 * 
 * (\** Check that two expressions are equivalent *\)
 * let rec equiv_kexpr e1 e2 =
 *   match e1.kexpr_desc, e2.kexpr_desc with
 *   | KE_const c1, KE_const c2 -> c1 = c2
 *   | KE_ident id1, KE_ident id2 -> id1 = id2
 *   | KE_op (op1, es1), KE_op (op2, es2) ->
 *     op1 = op2 && List.for_all2 equiv_kexpr es1 es2
 *   | KE_app (f1, es1, e1), KE_app (f2, es2, e2) ->
 *     f1 = f2 && List.for_all2 equiv_kexpr es1 es2 && equiv_kexpr e1 e2
 *   | KE_fby (c1, e1), KE_fby (c2, e2) -> c1 = c2 && equiv_kexpr e1 e2
 *   | KE_tuple ces1, KE_tuple ces2 -> List.for_all2 equiv_kexpr ces1 ces2
 *   | KE_when (e1, c1, clid1), KE_when (e2, c2, clid2) ->
 *     equiv_kexpr e1 e2 && c1 = c2 && clid1 = clid2
 *   | KE_merge (clid1, br1), KE_merge (clid2, br2) ->
 *     clid1 = clid2 &&
 *     List.for_all2 (fun (c1, e1) (c2, e2) -> c1 = c2 && equiv_kexpr e1 e2) br1 br2
 *   | _ -> false
 * 
 * (\** Check that two nodes are indeed equivalent *\)
 * let equiv_norm_node (c : k_node) (n : n_node) =
 *   let assocs = List.fold_left (fun asso -> function
 *       | NQ_ident (id, e) -> (id, denorm_kexpr e)::asso
 *       | NQ_app (ids, fid, es, clid, cl) ->
 *         (match ids with
 *          | [id] ->
 *            (id, { kexpr_desc =
 *                     KE_app (fid, List.map denorm_expr es,
 *                             { kexpr_desc = KE_ident clid;
 *                               kexpr_annot = (Tbool, cl); kexpr_loc = dummy_loc });
 *                   kexpr_annot = (Tint, cl);
 *                   kexpr_loc = dummy_loc })::asso
 *          | _ -> asso)
 *       | NQ_fby (id, c, e) ->
 *         (id, { kexpr_desc = KE_fby (c, denorm_expr e);
 *                     kexpr_annot = (e.nexpr_ty, e.nexpr_clock);
 *                     kexpr_loc = dummy_loc })::asso)
 *       [] n.nn_equs in
 *   c.kn_name = n.nn_name &&
 *   c.kn_input = n.nn_input &&
 *   c.kn_output = n.nn_output &&
 *   List.for_all (fun loc -> List.mem loc n.nn_local) c.kn_local &&
 *   List.for_all (fun eq ->
 *       let e1 = eq.keq_expr in
 *       match eq.keq_patt.kpatt_desc with
 *       | KP_ident id ->
 *         let e2 = List.assoc id assocs in
 *         equiv_kexpr e1 (inline_expr assocs e2)
 *       | KP_tuple ids -> (match e1.kexpr_desc with
 *           | KE_tuple es ->
 *             List.for_all2 (fun id e1 ->
 *                 let e2 = List.assoc id assocs in
 *                 equiv_kexpr e1 (inline_expr assocs e2)) ids es
 *           | KE_app (fid, es, e) -> true
 *           | _ -> failwith "Should not happen")
 *     ) c.kn_equs
 * 
 * let equiv_norm_file (c : k_file) (n : n_file) =
 *   try
 *     c.kf_clocks = n.nf_clocks &&
 *     List.for_all2 equiv_norm_node c.kf_nodes n.nf_nodes
 *   with _ -> false *)
