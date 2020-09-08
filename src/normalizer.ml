(** Normalize the equations *)

open Asttypes
open Clockchecker.CMinils
open NMinils

(** NormeE, compute a normalized n_expr for [e] *)
let rec normE (d : n_equation list) (e : k_expr) :
  n_expr * n_equation list * (ident * ty) list =
  let ty = fst e.kexpr_annot and cl = snd e.kexpr_annot in
  match e.kexpr_desc with
  | KE_const c ->
    { nexpr_desc = NE_const c; nexpr_ty = ty; nexpr_clock = cl }, d, []
  | KE_ident id ->
    { nexpr_desc = NE_ident id; nexpr_ty = ty; nexpr_clock = cl }, d, []
  | KE_op (op, es) ->
    let nes, d, vars = normEs d es in
    { nexpr_desc = NE_op (op, nes); nexpr_ty = ty; nexpr_clock = cl }, d, vars
  | KE_fby ({ kexpr_desc = KE_const c }, e) ->
    let ne, d, vars = normE d e in
    let x = Atom.fresh "_var" in
    { nexpr_desc = NE_ident x; nexpr_ty = ty; nexpr_clock = cl },
    (NQ_fby (x, c, ne))::d, (x, Base ty)::vars
  | KE_arrow (e0, e) ->
    failwith "TODO : arrow"
  | KE_switch (e, es) ->
    failwith "TODO : switch"
  | KE_when (e, constr, clid) ->
    let ne, d, vars = normE d e in
    { nexpr_desc = NE_when (ne, constr, clid); nexpr_ty = ty; nexpr_clock = cl },
    d, vars
  | KE_merge (clid, es) ->
    let y = Atom.fresh "_var" in
    let nes, d, vs =
      List.fold_left (fun (nes, d, vs) (c, e) ->
          let ne, d, vs' = normKE d e in
          ((c, ne)::nes, d, vs@vs')) ([], d, []) es in
    { nexpr_desc = NE_ident y; nexpr_ty = ty; nexpr_clock = cl },
    (NQ_ident (y, { ncexpr_desc = (NCE_merge (clid, List.rev nes));
                    ncexpr_ty = ty; ncexpr_clock = cl } ))::d,
    (y, Base ty)::vs
  | KE_app (fid, es, ever) ->
    let nes, d, vs1 = normEs d es in let x, d, vs2 = normV d ever in
    let y = Atom.fresh "_var" in
    { nexpr_desc = NE_ident y; nexpr_ty = ty; nexpr_clock = cl },
    (NQ_app ([y], fid, nes, x, snd ever.kexpr_annot))::d,
    (y, Base ty)::(vs1@vs2)
  | _ -> invalid_arg "normE"

(** NormeElist, compute a list of normalized n_expr *)
and normEs (d : n_equation list) (es : k_expr list) =
  let (nes, d, vars) =
    List.fold_left (fun (nes, d, vars) e ->
        let (ne, d, vs) = normE d e in ((ne::nes), d, vars@vs)) ([], d, []) es in
  List.rev nes, d, vars

(** NormV, create a fresh variable and assigns it the result of the expr *)
and normV (d : n_equation list) (e : k_expr) =
  let ne, d, vars = normKE d e in
  let x = Atom.fresh "_var" in
  x, (NQ_ident (x, ne))::d, (x, Base (fst e.kexpr_annot))::vars

(** NormeCA, compute a normalized n_kexpr for [e] *)
and normKE (d : n_equation list) (e : k_expr) =
  let (ne, d, vars) = normE d e in
  { ncexpr_desc = NCE_expr ne.nexpr_desc;
    ncexpr_ty = ne.nexpr_ty; ncexpr_clock = ne.nexpr_clock }, d, vars

(** Normalize an equation *)
let norm_eq (eq : k_equation) =
  let eqs, vars =
    (match eq.keq_patt.kpatt_desc with
     | KP_ident id -> let (ne, d, vars) = normKE [] eq.keq_expr in
       (NQ_ident (id, ne))::d, vars
     | KP_tuple ids ->
       (match eq.keq_expr.kexpr_desc with
        | KE_app (fid, es, ever) ->
          let nes, d, vs1 = normEs [] es in let x, d, vs2 = normV d ever in
          (NQ_app (ids, fid, nes, x, snd ever.kexpr_annot))::d, vs1@vs2
        | KE_tuple es ->
          let eqs, vars =
            (List.fold_left2
               (fun (eqs, vars) id e ->
                  let (ne, d, vars') = normKE [] e in
                  ((NQ_ident (id, ne))::d)::eqs, vars@vars') ([], [])
               ids es) in
          List.concat eqs, vars
        | _ -> invalid_arg "norm_eq"
       )
    ) in eqs, vars

(** Normalize a node *)
let norm_node (n : k_node) =
  let equs, vars =
    List.fold_left
      (fun (equs, vars) eq ->
         let (eq, vars') = norm_eq eq in (equs@eq, vars@vars'))
      ([], []) n.kn_equs in
  { nn_name = n.kn_name;
    nn_input = n.kn_input;
    nn_output = n.kn_output;
    nn_local = n.kn_local@vars;
    nn_equs = equs }

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
