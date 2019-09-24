(** Normalize the equations *)

open Asttypes
open CMinils
open NMinils

(** Generation of fresh variables *)
module Atom = struct
  let counter : int ref = ref 0
  let fresh (s:string) =
    counter := !counter+1; Printf.sprintf "%s%d" s !counter
end

(** NormeE, compute a normalized n_expr for [e] *)
let rec normE (d : n_equation list) (e : c_expr) =
  let cl = e.cexpr_clock in
  match e.cexpr_desc with
  | CE_const c ->
    { nexpr_desc = NE_const c; nexpr_clock = cl }, d
  | CE_ident id ->
    { nexpr_desc = NE_ident id; nexpr_clock = cl }, d
  | CE_op (op, es) ->
    let nes, d = normEs d es in
    { nexpr_desc = NE_op (op, nes); nexpr_clock = cl }, d
  | CE_fby (c, e) ->
    let ne, d = normE d e in
    let x = Atom.fresh "_var" in
    { nexpr_desc = NE_ident x; nexpr_clock = cl },
    (NQ_fby (x, c, ne))::d
  | CE_when (e, id, b) ->
    let ne, d = normE d e in
    { nexpr_desc = NE_when (ne, id, b); nexpr_clock = cl }, d
  | CE_merge (id, e1, e2) ->
    let y = Atom.fresh "_var" in
    let ne1, d = normCE d e1 in let ne2, d = normCE d e2 in
    { nexpr_desc = NE_ident y; nexpr_clock = cl },
    (NQ_ident (y, { ncexpr_desc = (NCE_merge (id, ne1, ne2));
                    ncexpr_clock = cl } ))::d
  | CE_app (fid, es, ever) ->
    let nes, d = normEs d es in let x, d = normV d ever in
    let y = Atom.fresh "_var" in
    { nexpr_desc = NE_ident y; nexpr_clock = cl },
    (NQ_app ([y], fid, nes, x, cl))::d
  | _ -> invalid_arg "normE"

(** NormeElist, compute a list of normalized n_expr *)
and normEs (d : n_equation list) (es : c_expr list) =
  let (nes, d) =
    List.fold_left (fun (nes, d) e ->
        let (ne, d) = normE d e in ((ne::nes), d)) ([], d) es in
  List.rev nes, d

(** NormV, create a fresh variable and assigns it the result of the expr *)
and normV (d : n_equation list) (e : c_expr) =
  let ne, d = normCE d e in
  let x = Atom.fresh "_var" in
  x, (NQ_ident (x, ne))::d

(** NormeCA, compute a normalized n_cexpr for [e] *)
and normCE (d : n_equation list) (e : c_expr) =
  let (ne, d) = normE d e in
  { ncexpr_desc = NCE_expr ne.nexpr_desc; ncexpr_clock = ne.nexpr_clock }, d

(** Normalize an equation *)
let norm_eq (eq : c_equation) =
  List.rev
    (match eq.ceq_patt.cpatt_desc with
     | CP_ident id -> let (ne, d) = normCE [] eq.ceq_expr in
       (NQ_ident (id, ne))::d
     | CP_tuple ids ->
       (match eq.ceq_expr.cexpr_desc with
        | CE_app (fid, es, ever) ->
          let nes, d = normEs [] es in let x, d = normV d ever in
          (NQ_app (ids, fid, nes, x, eq.ceq_expr.cexpr_clock))::d
        | CE_tuple es ->
          List.concat (List.map2 (fun id e ->
              let (ne, d) = normCE [] e in
              (NQ_ident (id, ne)::d)) ids es)
        | _ -> invalid_arg "norm_eq"
       )
    )

(** Normalize a node *)
let norm_node (n : c_node) =
  { nn_name = n.cn_name;
    nn_input = n.cn_input;
    nn_output = n.cn_output;
    nn_local = n.cn_local;
    nn_equs = List.flatten
        (List.map norm_eq n.cn_equs); }

(** Normalize the whole file *)
let norm_file (f : c_file) =
  List.map norm_node f

(*                           Check equivalence between ASTs                    *)
(* TODO *)
