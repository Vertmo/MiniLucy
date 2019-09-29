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
(* TODO *)
