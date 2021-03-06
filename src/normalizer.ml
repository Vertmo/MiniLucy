(** Normalize the equations *)

open Common
open Kernelizer.CMinils
open NMinils

(** First pass : separating app, fby and control exprs,
    distribute constructions *)

let idents_for_anns anns =
  List.map (fun (ty, (ck, _)) -> (Atom.fresh "_", (ty, ck))) anns

let idents_for_anns' anns =
  List.map (fun (ty, (ck, id)) ->
      match id with
      | Some id -> (id, (ty, ck))
      | None -> (Atom.fresh "_", (ty, ck))) anns

let dist_make_vars ids =
  List.map (fun (id, (ty, ck)) ->
      { kexpr_desc = KE_ident id; kexpr_annot = [(ty, (ck, Some id))];
        kexpr_loc = dummy_loc })
    ids

let dist_make_eqs ids es =
  List.map (fun ((id, _), e) ->
      { keq_patt = [id]; keq_expr = [e]; keq_loc = dummy_loc }
    ) (List.combine ids es)

let dist_fby e0s es er anns =
  List.map (fun ((e0, e), a) ->
      { kexpr_desc = KE_fby ([e0], [e], er); kexpr_annot = [a]; kexpr_loc = dummy_loc }
    ) (List.combine (List.combine e0s es) anns)

let dist_arrow e0s es er anns =
  List.map (fun ((e0, e), a) ->
      { kexpr_desc = KE_arrow ([e0], [e], er); kexpr_annot = [a]; kexpr_loc = dummy_loc }
    ) (List.combine (List.combine e0s es) anns)

let dist_match e branches anns =
  List.mapi (fun i a ->
      { kexpr_desc = KE_match (e, List.map (fun (c, es) -> (c, [List.nth es i])) branches);
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

let rec dist_expr (is_rhs : bool) (is_control : bool) (e : k_expr) :
  (k_expr list * k_equation list * (ident * ann) list) =
  let anns = e.kexpr_annot in
  match e.kexpr_desc with
  | KE_const _ | KE_ident _ ->
    [e], [], []
  | KE_unop (op, e1) ->
    let e1', eqs1, vs1 = dist_expr false false e1 in
    let e1' = List.hd e1' in
    [{ e with kexpr_desc = KE_unop (op, e1') }], eqs1, vs1
  | KE_binop (op, e1, e2) ->
    let e1', eqs1, vs1 = dist_expr false false e1
    and e2', eqs2, vs2 = dist_expr false false e2 in
    let e1' = List.hd e1' and e2' = List.hd e2' in
    [{ e with kexpr_desc = KE_binop (op, e1', e2') }], eqs1@eqs2, vs1@vs2
  | KE_fby (e0s, es, er) ->
    let e0s', eqs1, vs1 = dist_exprs false false e0s
    and es', eqs2, vs2 = dist_exprs false false es
    and er', eqs3, vs3 = dist_and_var_expr er in
    let fbys = dist_fby e0s' es' er' anns in
    let ids = idents_for_anns anns in
    dist_make_vars ids,
    (dist_make_eqs ids fbys)@eqs1@eqs2@eqs3,
    vs1@vs2@vs3@ids
  | KE_arrow (e0s, es, er) ->
    let e0s', eqs1, vs1 = dist_exprs false false e0s
    and es', eqs2, vs2 = dist_exprs false false es
    and er', eqs3, vs3 = dist_and_var_expr er in
    let arrows = dist_arrow e0s' es' er' anns in
    let ids = idents_for_anns anns in
    dist_make_vars ids,
    (dist_make_eqs ids arrows)@eqs1@eqs2@eqs3,
    vs1@vs2@vs3@ids
  | KE_match (e, branches) ->
    let e', eqs1, vs1 = dist_expr false false e
    and branches', eqs2, vs2 = dist_branches branches in
    let switches = dist_match (List.hd e') branches' anns in
    if is_control then
      switches, eqs1@eqs2, vs1@vs2
    else let ids = idents_for_anns anns in
      dist_make_vars ids,
      (dist_make_eqs ids switches)@eqs1@eqs2,
      vs1@vs2@ids
  | KE_when (es, constr, ckid) ->
    let es', eqs1, vs1 = dist_exprs false false es in
    dist_when constr ckid es' anns, eqs1, vs1
  | KE_merge (ckid, branches) ->
    let branches', eqs1, vs1 = dist_branches branches in
    let merges = dist_merge ckid branches' anns in
    if is_control then
      merges, eqs1, vs1
    else let ids = idents_for_anns anns in
      dist_make_vars ids,
      (dist_make_eqs ids merges)@eqs1,
      vs1@ids
  | KE_app (fid, es, er) ->
    let es', eqs1, vs1 = dist_exprs false false es
    and er', eqs2, vs2 = dist_and_var_expr er in
    let app = {  kexpr_desc = KE_app (fid, es', er');
                 kexpr_annot = anns; kexpr_loc = dummy_loc } in
    if is_rhs then
      [app], eqs1@eqs2, vs1@vs2
    else
      let ids = idents_for_anns' anns in
      dist_make_vars ids,
      { keq_patt = List.map fst ids;
        keq_expr = [app];
        keq_loc = dummy_loc }::eqs1@eqs2,
      vs1@vs2@ids
  | KE_last _ -> invalid_arg "dist_expr"

and dist_exprs (is_rhs : bool) (is_control : bool) (es : k_expr list) =
  let res = List.map (dist_expr is_rhs is_control) es in
  (List.concat (List.map (fun (e, _, _) -> e) res),
   List.concat (List.map (fun (_, eq, _) -> eq) res),
   List.concat (List.map (fun (_, _, v) -> v) res))

and dist_and_var_expr (e : k_expr) =
  let e', eqs, vs = dist_expr true true e in
  match (List.hd e') with
  | { kexpr_desc = KE_ident _ } as e' -> e', eqs, vs
  | e' ->
    let y = Atom.fresh "_" and (ty, (ck, _)) = List.hd e'.kexpr_annot in
    { kexpr_desc = KE_ident y;
      kexpr_annot = [(ty, (ck, Some y))];
      kexpr_loc = e'.kexpr_loc },
    { keq_patt = [y]; keq_expr = [e']; keq_loc = dummy_loc }::eqs,
    (y, (ty, ck))::vs

and dist_branches (branches : (constr * k_expr list) list) =
  let res = List.map (fun (cstr, es) ->
      let es', eqs, vs = dist_exprs false true es in
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
  let (es, eqs, vs) = dist_exprs true true eq.keq_expr in
  let eqs' = combine_for_numstreams es eq.keq_patt in
  (List.map (fun (e, ids) ->
       { keq_patt = ids; keq_expr = [e]; keq_loc = dummy_loc }
     ) eqs')@eqs, vs

let dist_eqs (eqs : k_equation list) =
  let res = List.map dist_eq eqs in
  (List.concat (List.map fst res),
   List.concat (List.map snd res))

(** Second pass : initialize fbys with constant only, eliminate arrows *)

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

let init_expr er ck : k_expr =
  let annot = [(Tbool, (Cbase, None))] in
  { kexpr_desc = KE_fby
        ([Clockchecker.add_whens Tbool ck { kexpr_desc = KE_const (Cbool true);
                                            kexpr_annot = annot; kexpr_loc = dummy_loc }],
         [Clockchecker.add_whens Tbool ck { kexpr_desc = KE_const (Cbool false);
                                            kexpr_annot = annot; kexpr_loc = dummy_loc }],
         er);
    kexpr_loc = dummy_loc; kexpr_annot = [(Tbool, (ck, None))] }

let delay_expr e er ty ck : k_expr =
  { kexpr_desc = KE_fby
        ([Clockchecker.add_whens Tbool ck { kexpr_desc = KE_const (Cint 0);
                                            kexpr_annot = [(ty, (Cbase, None))];
                                            kexpr_loc = dummy_loc }],
         [e], er);
    kexpr_annot = [(Tbool, (ck, None))]; kexpr_loc = dummy_loc }

let norm_fby_eq (eq : k_equation) : (k_equation list * (ident * ann) list) =
  match eq.keq_expr with
  | [{ kexpr_desc = KE_fby ([e0], [e1], er) }] when is_constant e0 -> [eq], []
  | [{ kexpr_desc = KE_fby ([e0], [e1], er) } as e] ->
    let (ty, (ck, _)) = List.hd e.kexpr_annot in
    let xinit = Atom.fresh "_" and px = Atom.fresh "_" in
    [{ keq_patt = [xinit]; keq_expr = [init_expr er ck]; keq_loc = dummy_loc };
     { keq_patt = [px]; keq_expr = [delay_expr e1 er ty ck]; keq_loc = dummy_loc };
     { eq with keq_expr = [{ kexpr_desc = KE_match ({ kexpr_desc = KE_ident xinit;
                                                      kexpr_annot = [(Tbool, (ck, None))];
                                                      kexpr_loc = dummy_loc },
                                                    [("True", [e0]);
                                                     ("False", [{ kexpr_desc = KE_ident px;
                                                                  kexpr_annot = [(Tbool, (ck, None))];
                                                                  kexpr_loc = dummy_loc }])]);
                             kexpr_annot = [(ty, (ck, None))];
                             kexpr_loc = dummy_loc }] }],
    [ (xinit, (Tbool, ck)); (px, (ty, ck)) ]
  | [{ kexpr_desc = KE_arrow ([e0], [e1], er) } as e] ->
    let (ty, (ck, _)) = List.hd e.kexpr_annot in
    let xinit = Atom.fresh "_" in
    [{ keq_patt = [xinit]; keq_expr = [init_expr er ck]; keq_loc = dummy_loc };
     { eq with keq_expr = [{ kexpr_desc = KE_match ({ kexpr_desc = KE_ident xinit;
                                                      kexpr_annot = [(Tbool, (ck, None))];
                                                      kexpr_loc = dummy_loc },
                                                    [("True", [e0]); ("False", [e1])]);
                             kexpr_annot = [(ty, (ck, None))];
                             kexpr_loc = dummy_loc }] }],
    [ (xinit, (Tbool, ck)) ]

  | _ -> [eq], []

let norm_fby_eqs (eqs : k_equation list) =
  let res = List.map norm_fby_eq eqs in
  (List.concat (List.map fst res),
   List.concat (List.map snd res))

(** Last pass : transcription *)

(* We need to find the base clock for instanciations *)

let clocks_of (es : k_expr list) =
  List.concat (List.map (fun e -> List.map (fun (_, (ck, _)) -> ck) e.kexpr_annot) es)

let rec suffix_of_clock ck acc =
  match ck with
  | Cbase -> acc
  | Con (x, b, ck') -> suffix_of_clock ck' ((x, b)::acc)

let rec clock_of_suffix sfx ck =
  match sfx with
  | [] -> ck
  | (x, b)::sfx' -> clock_of_suffix sfx' (Con (x, b, ck))

let rec common_suffix sfx1 sfx2 =
  match sfx1, sfx2 with
  | [], _ -> []
  | _, [] -> []
  | (x1, b1)::sfx1', (x2, b2)::sfx2' ->
    if (x1 = x2 && b1 = b2)
    then (x1, b1)::common_suffix sfx1' sfx2'
    else []

let find_base_clock (cks : clock list) =
  match cks with
  | [] -> Cbase
  | ck::cks ->
    let sfx = List.fold_left
        (fun sfx1 ck2 -> common_suffix sfx1 (suffix_of_clock ck2 []))
        (suffix_of_clock ck []) cks
    in clock_of_suffix sfx Cbase

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
    | KE_match (e, branches) ->
      NCE_match (tr_lexp e,
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
    | [x], KE_fby ([e0], [e], { kexpr_desc = KE_ident r; kexpr_annot = [(_, (ckr, _))]}) when is_constant e0 ->
      NQ_fby (x, extract_constant e0, tr_lexp e, r, ckr)
    | xs, KE_app (f, es, { kexpr_desc = KE_ident i; kexpr_annot = [(_, (ckr, _))] }) ->
      NQ_app (xs, f, tr_lexps es, i, (find_base_clock (clocks_of es)), ckr)
    | [x], _ ->
      NQ_ident (x, tr_cexp (List.hd e.keq_expr))
    | _ -> invalid_arg "tr_eq"

let tr_eqs = List.map tr_eq

(** Normalize a node *)

let norm_node (n : k_node) =
  let (eqs, vs1) = dist_eqs n.kn_equs in
  let (eqs, vs2) = norm_fby_eqs eqs in
  let eqs = tr_eqs eqs in
  { nn_name = n.kn_name;
    nn_input = n.kn_input;
    nn_output = n.kn_output;
    nn_local = n.kn_local@vs1@vs2;
    nn_equs = eqs;
    nn_loc = n.kn_loc }

(** Normalize the whole file *)
let norm_file (f : k_file) =
  { nf_clocks = f.kf_clocks;
    nf_nodes = List.map norm_node f.kf_nodes }
