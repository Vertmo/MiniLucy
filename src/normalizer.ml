(** Normalize the equations *)

open Asttypes
open CMinils
open NMinils

(** NormeE, compute a normalized n_expr for [e] *)
let rec normE (d : n_equation list) (e : c_expr) :
  n_expr * n_equation list * (ident * ty) list =
  let ty = e.cexpr_ty and cl = e.cexpr_clock in
  match e.cexpr_desc with
  | CE_const c ->
    { nexpr_desc = NE_const c; nexpr_ty = ty; nexpr_clock = cl }, d, []
  | CE_ident id ->
    { nexpr_desc = NE_ident id; nexpr_ty = ty; nexpr_clock = cl }, d, []
  | CE_op (op, es) ->
    let nes, d, vars = normEs d es in
    { nexpr_desc = NE_op (op, nes); nexpr_ty = ty; nexpr_clock = cl }, d, vars
  | CE_fby (c, e) ->
    let ne, d, vars = normE d e in
    let x = Atom.fresh "_var" in
    { nexpr_desc = NE_ident x; nexpr_ty = ty; nexpr_clock = cl },
    (NQ_fby (x, c, ne))::d, (x, Base ty)::vars
  | CE_when (e, constr, clid) ->
    let ne, d, vars = normE d e in
    { nexpr_desc = NE_when (ne, constr, clid); nexpr_ty = ty; nexpr_clock = cl },
    d, vars
  | CE_merge (clid, es) ->
    let y = Atom.fresh "_var" in
    let nes, d, vs =
      List.fold_left (fun (nes, d, vs) (c, e) ->
          let ne, d, vs' = normCE d e in
          ((c, ne)::nes, d, vs@vs')) ([], d, []) es in
    { nexpr_desc = NE_ident y; nexpr_ty = ty; nexpr_clock = cl },
    (NQ_ident (y, { ncexpr_desc = (NCE_merge (clid, List.rev nes));
                    ncexpr_ty = ty; ncexpr_clock = cl } ))::d,
    (y, Base ty)::vs
  | CE_app (fid, es, ever) ->
    let nes, d, vs1 = normEs d es in let x, d, vs2 = normV d ever in
    let y = Atom.fresh "_var" in
    { nexpr_desc = NE_ident y; nexpr_ty = ty; nexpr_clock = cl },
    (NQ_app ([y], fid, nes, x, ever.cexpr_clock))::d,
    (y, Base ty)::(vs1@vs2)
  | _ -> invalid_arg "normE"

(** NormeElist, compute a list of normalized n_expr *)
and normEs (d : n_equation list) (es : c_expr list) =
  let (nes, d, vars) =
    List.fold_left (fun (nes, d, vars) e ->
        let (ne, d, vs) = normE d e in ((ne::nes), d, vars@vs)) ([], d, []) es in
  List.rev nes, d, vars

(** NormV, create a fresh variable and assigns it the result of the expr *)
and normV (d : n_equation list) (e : c_expr) =
  let ne, d, vars = normCE d e in
  let x = Atom.fresh "_var" in
  x, (NQ_ident (x, ne))::d, (x, Base e.cexpr_ty)::vars

(** NormeCA, compute a normalized n_cexpr for [e] *)
and normCE (d : n_equation list) (e : c_expr) =
  let (ne, d, vars) = normE d e in
  { ncexpr_desc = NCE_expr ne.nexpr_desc;
    ncexpr_ty = ne.nexpr_ty; ncexpr_clock = ne.nexpr_clock }, d, vars

(** Normalize an equation *)
let norm_eq (eq : c_equation) =
  let eqs, vars =
    (match eq.ceq_patt.cpatt_desc with
     | CP_ident id -> let (ne, d, vars) = normCE [] eq.ceq_expr in
       (NQ_ident (id, ne))::d, vars
     | CP_tuple ids ->
       (match eq.ceq_expr.cexpr_desc with
        | CE_app (fid, es, ever) ->
          let nes, d, vs1 = normEs [] es in let x, d, vs2 = normV d ever in
          (NQ_app (ids, fid, nes, x, ever.cexpr_clock))::d, vs1@vs2
        | CE_tuple es ->
          let eqs, vars =
            (List.fold_left2
               (fun (eqs, vars) id e ->
                  let (ne, d, vars') = normCE [] e in
                  ((NQ_ident (id, ne))::d)::eqs, vars@vars') ([], [])
               ids es) in
          List.concat eqs, vars
        | _ -> invalid_arg "norm_eq"
       )
    ) in eqs, vars

(** Normalize a node *)
let norm_node (n : c_node) =
  let equs, vars =
    List.fold_left
      (fun (equs, vars) eq ->
         let (eq, vars') = norm_eq eq in (equs@eq, vars@vars'))
      ([], []) n.cn_equs in
  { nn_name = n.cn_name;
    nn_input = n.cn_input;
    nn_output = n.cn_output;
    nn_local = n.cn_local@vars;
    nn_equs = equs }

(** Normalize the whole file *)
let norm_file (f : c_file) =
  { nf_clocks = f.cf_clocks;
    nf_nodes = List.map norm_node f.cf_nodes }

(*                           Check equivalence between ASTs                    *)

let rec denorm_expr (e : n_expr) : c_expr =
  let desc = match e.nexpr_desc with
    | NE_const c -> CE_const c
    | NE_ident id -> CE_ident id
    | NE_op (op, es) -> CE_op (op, List.map denorm_expr es)
    | NE_when (e, c, cid) -> CE_when (denorm_expr e, c, cid)
  in { cexpr_desc = desc; cexpr_clock = e.nexpr_clock;
       cexpr_ty = e.nexpr_ty; cexpr_loc = dummy_loc }

let rec denorm_cexpr (e : n_cexpr) : c_expr =
  let desc = match e.ncexpr_desc with
    | NCE_merge (cid, branches) ->
      CE_merge (cid, List.map (fun (c, e) -> c, denorm_cexpr e) branches)
    | NCE_expr e' ->
      (denorm_expr { nexpr_desc = e';
                     nexpr_clock = e.ncexpr_clock;
                     nexpr_ty = e.ncexpr_ty }).cexpr_desc
  in { cexpr_desc = desc; cexpr_clock = e.ncexpr_clock;
       cexpr_ty = Tint; cexpr_loc = dummy_loc }

(** Inline variables inside an expression *)
let rec inline_expr asso e =
  let desc = match e.cexpr_desc with
    | CE_const c -> CE_const c
    | CE_ident id ->
      (match List.assoc_opt id asso with
       | Some e when (String.sub id 0 1 = "_") ->
         (inline_expr asso e).cexpr_desc
       | _ -> CE_ident id)
    | CE_op (op, es) -> CE_op (op, List.map (inline_expr asso) es)
    | CE_app (f, es, e) ->
      CE_app (f, List.map (inline_expr asso) es, inline_expr asso e)
    | CE_fby (c, e) -> CE_fby (c, inline_expr asso e)
    | CE_tuple es -> CE_tuple (List.map (inline_expr asso) es)
    | CE_when (e, c, clid) -> CE_when (inline_expr asso e, c, clid)
    | CE_merge (c, brs) ->
      CE_merge (c, List.map (fun (c, e) -> c, inline_expr asso e) brs)
  in { e with cexpr_desc = desc }

(** Check that two expressions are equivalent *)
let rec equiv_cexpr e1 e2 =
  match e1.cexpr_desc, e2.cexpr_desc with
  | CE_const c1, CE_const c2 -> c1 = c2
  | CE_ident id1, CE_ident id2 -> id1 = id2
  | CE_op (op1, es1), CE_op (op2, es2) ->
    op1 = op2 && List.for_all2 equiv_cexpr es1 es2
  | CE_app (f1, es1, e1), CE_app (f2, es2, e2) ->
    f1 = f2 && List.for_all2 equiv_cexpr es1 es2 && equiv_cexpr e1 e2
  | CE_fby (c1, e1), CE_fby (c2, e2) -> c1 = c2 && equiv_cexpr e1 e2
  | CE_tuple ces1, CE_tuple ces2 -> List.for_all2 equiv_cexpr ces1 ces2
  | CE_when (e1, c1, clid1), CE_when (e2, c2, clid2) ->
    equiv_cexpr e1 e2 && c1 = c2 && clid1 = clid2
  | CE_merge (clid1, br1), CE_merge (clid2, br2) ->
    clid1 = clid2 &&
    List.for_all2 (fun (c1, e1) (c2, e2) -> c1 = c2 && equiv_cexpr e1 e2) br1 br2
  | _ -> false

(** Check that two nodes are indeed equivalent *)
let equiv_norm_node (c : c_node) (n : n_node) =
  let assocs = List.fold_left (fun asso -> function
      | NQ_ident (id, e) -> (id, denorm_cexpr e)::asso
      | NQ_app (ids, fid, es, clid, cl) ->
        (match ids with
         | [id] ->
           (id, { cexpr_desc =
                    CE_app (fid, List.map denorm_expr es,
                            { cexpr_desc = CE_ident clid; cexpr_ty = Tbool;
                              cexpr_clock = cl; cexpr_loc = dummy_loc });
                  cexpr_ty = Tint; cexpr_clock = cl;
                  cexpr_loc = dummy_loc })::asso
         | _ -> asso)
      | NQ_fby (id, c, e) ->
        (id, { cexpr_desc = CE_fby (c, denorm_expr e);
                    cexpr_ty = e.nexpr_ty; cexpr_clock = e.nexpr_clock;
                    cexpr_loc = dummy_loc })::asso)
      [] n.nn_equs in
  c.cn_name = n.nn_name &&
  c.cn_input = n.nn_input &&
  c.cn_output = n.nn_output &&
  List.for_all (fun loc -> List.mem loc n.nn_local) c.cn_local &&
  List.for_all (fun eq ->
      let e1 = eq.ceq_expr in
      match eq.ceq_patt.cpatt_desc with
      | CP_ident id ->
        let e2 = List.assoc id assocs in
        equiv_cexpr e1 (inline_expr assocs e2)
      | CP_tuple ids -> (match e1.cexpr_desc with
          | CE_tuple es ->
            List.for_all2 (fun id e1 ->
                let e2 = List.assoc id assocs in
                equiv_cexpr e1 (inline_expr assocs e2)) ids es
          | CE_app (fid, es, e) -> true
          | _ -> failwith "Should not happen")
    ) c.cn_equs

let equiv_norm_file (c : c_file) (n : n_file) =
  try
    c.cf_clocks = n.nf_clocks &&
    List.for_all2 equiv_norm_node c.cf_nodes n.nf_nodes
  with _ -> false
