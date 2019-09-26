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
    d@[NQ_fby (x, c, ne)], (x, Base ty)::vars
  | CE_when (e, id, b) ->
    let ne, d, vars = normE d e in
    { nexpr_desc = NE_when (ne, id, b); nexpr_ty = ty; nexpr_clock = cl },
    d, vars
  | CE_merge (id, e1, e2) ->
    let y = Atom.fresh "_var" in
    let ne1, d, vs1 = normCE d e1 in let ne2, d, vs2 = normCE d e2 in
    { nexpr_desc = NE_ident y; nexpr_ty = ty; nexpr_clock = cl },
    d@[NQ_ident (y, { ncexpr_desc = (NCE_merge (id, ne1, ne2));
                      ncexpr_ty = ty; ncexpr_clock = cl } )],
    (y, Base ty)::(vs1@vs2)
  | CE_app (fid, es, ever) ->
    let nes, d, vs1 = normEs d es in let x, d, vs2 = normV d ever in
    let y = Atom.fresh "_var" in
    { nexpr_desc = NE_ident y; nexpr_ty = ty; nexpr_clock = cl },
    d@[NQ_app ([y], fid, nes, x, ever.cexpr_clock)],
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
       d@[NQ_ident (id, ne)], vars
     | CP_tuple ids ->
       (match eq.ceq_expr.cexpr_desc with
        | CE_app (fid, es, ever) ->
          let nes, d, vs1 = normEs [] es in let x, d, vs2 = normV d ever in
          d@[NQ_app (ids, fid, nes, x, ever.cexpr_clock)], vs1@vs2
        | CE_tuple es ->
          let eqs, vars =
            (List.fold_left2
               (fun (eqs, vars) id e ->
                  let (ne, d, vars') = normCE [] e in
                  (d@[NQ_ident (id, ne)])::eqs, vars@vars') ([], [])
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
  List.map norm_node f

(*                           Check equivalence between ASTs                    *)
(* TODO *)
