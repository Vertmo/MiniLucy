(** Desugarizer from parsed AST to kernel AST *)

open Asttypes
open PMinils
open Minils.KMinils

let desugar_patt (p : p_patt) : k_patt =
  let desc = match p.ppatt_desc with
    | PP_ident id -> KP_ident id
    | PP_tuple ids -> KP_tuple ids in
  { kpatt_desc = desc; kpatt_loc = p.ppatt_loc; }

let rec desugar_expr (e : p_expr) : k_expr =
  let desc = match e.pexpr_desc with
    | PE_const c -> KE_const c
    | PE_ident id -> KE_ident id
    | PE_op (op, es) -> KE_op (op, List.map desugar_expr es)
    | PE_app (id, es, e) ->
      KE_app (id, List.map desugar_expr es, desugar_expr e)
    | PE_fby (c, e) -> KE_fby (c, desugar_expr e)
    | PE_arrow (c, e) ->
      let cond = { kexpr_desc = KE_const (Cbool false);
                   kexpr_annot = ();
                   kexpr_loc = e.pexpr_loc } in
      let cond = { kexpr_desc = KE_fby (Cbool true, cond);
                   kexpr_annot = ();
                   kexpr_loc = e.pexpr_loc } in
      KE_op (Op_if, [cond; desugar_expr c; desugar_expr e])
    | PE_pre e -> KE_fby (Cnil, desugar_expr e)
    | PE_tuple es -> KE_tuple (List.map desugar_expr es)
    | PE_when (e, constr, clid) -> KE_when (desugar_expr e, constr, clid)
    | PE_merge (id, es) ->
      KE_merge (id,
                List.sort (fun (c1, e1) (c2, e2) -> String.compare c1 c2)
                  (List.map (fun (c, e) -> c, desugar_expr e) es)) in
  { kexpr_desc = desc; kexpr_annot = (); kexpr_loc = e.pexpr_loc; }

let desugar_equation (eq : p_equation) : k_equation =
  { keq_patt = desugar_patt eq.peq_patt;
    keq_expr = desugar_expr eq.peq_expr; }

(*                            Automata processing                              *)

(** Get the vars defined in a pattern *)
let get_patt_var pat =
  match pat.ppatt_desc with
  | PP_ident id -> id
  | PP_tuple ids ->
    failwith "Tuple assignment is not supported in automata"

(** Get the vars defined in an instruction *)
let rec get_instr_vars = function
  | Eq eq -> [get_patt_var eq.peq_patt]
  | Automaton branches ->
    List.flatten (List.map (fun (_, _, ins, _) ->
        List.flatten (List.map get_instr_vars ins)) branches)

(** Tree of automatas *)
type automata_tree =
  | Leaf of p_equation
  | Node of ident *
            (constr * ((ident * ident * ty * p_expr) list) *
             automata_tree list * p_until list) list

(** Get the tree represneting a hierarchy of automata *)
let rec get_automata_tree = function
  | Eq eq -> Leaf eq
  | Automaton branches ->
    Node (Atom.fresh "auto_state",
          List.map (fun (c, lets, ins, untils) ->
              (c, List.map (fun (id, ty, e) ->
                 let nid = Atom.fresh ("let_"^id) in (id, nid, ty, e)) lets,
               List.map get_automata_tree ins, untils)) branches)

(** Automata-derived clock *)
type automata_clock =
  | Base of ident * constr list
  | Clocked of automata_clock * constr * ident

(** Get the clocks of the automata tree *)
let rec get_automata_clocks : automata_tree -> (automata_clock list) =
  function
  | Leaf eq -> []
  | Node (clid, branches) ->
    let newCl = (Base (clid, (List.map (fun (c, _, _, _) -> c) branches))) in
    let cls = List.map (fun (c, _, trs, _) ->
        let cls = List.flatten (List.map get_automata_clocks trs) in
        List.map (fun cl -> Clocked (cl, c, clid)) cls) branches in
    newCl::(List.flatten cls)

(** Get a clock declaration for the automaton clock *)
let rec clockdec_of_automata_clock : automata_clock -> clockdec =
  function
  | Base (id, constrs) -> ("_ty"^id, constrs)
  | Clocked (cl, _, _) -> clockdec_of_automata_clock cl

let clockvar_of_automata_clock cl =
  let rec ty_of_automata_clock : automata_clock -> ty = function
    | Base (id, _) -> Base (Tclock ("_ty"^id))
    | Clocked (cl, constr, clid) ->
      Clocked (ty_of_automata_clock cl, constr, clid)
  and ident_of_automata_clock = function
    | Base (id, _) -> id
    | Clocked (cl, _, _) -> ident_of_automata_clock cl in
  (ident_of_automata_clock cl, ty_of_automata_clock cl)

(** Apply a substitution of variables to an expression *)
let rec apply_subst x y e =
  let desc = match e.kexpr_desc with
    | KE_const c -> KE_const c
    | KE_ident id -> if id = x then KE_ident y else KE_ident id
    | KE_op (op, es) -> KE_op (op, List.map (apply_subst x y) es)
    | KE_app (fid, es, ev) ->
      KE_app (fid, List.map (apply_subst x y) es, apply_subst x y ev)
    | KE_fby (c, e) -> KE_fby (c, apply_subst x y e)
    | KE_tuple es -> KE_tuple (List.map (apply_subst x y) es)
    | KE_when (e, c, clid) ->
      KE_when (apply_subst x y e, c, if clid = x then y else clid)
    | KE_merge (clid, branches) ->
      KE_merge ((if clid = x then y else clid),
                List.map (fun (c, e) -> c, apply_subst x y e) branches)
  in { e with kexpr_desc = desc }

(** Apply several substitutions to an expression *)
let apply_substs substs e =
  List.fold_left (fun e (x, y) -> apply_subst x y e) e substs

(** Tree of expressions *)
type expr_tree =
  | None
  | Leaf of k_expr
  (* The second parameter is a set of applicable substitutions *)
  | Node of ident * ((constr * (ident * ident) list * expr_tree) list)

(** Get the expression tree for [var] in an automata tree *)
let rec get_expr_tree (tree : automata_tree) var =
  match tree with
  | Leaf eq ->
    if (get_patt_var eq.peq_patt) = var
    then Leaf (desugar_expr eq.peq_expr) else None
  | Node (clid, branches) ->
    let subtrees = List.map (fun (c, lets, trs, _) ->
        (c,
         (List.map (fun (id, nid, _, _) -> id, nid) lets),
         List.fold_left (fun n tr ->
            if n = None then get_expr_tree tr var else n) None trs)) branches in
    if (List.for_all (fun (c, _, n) -> n = None) subtrees)
    then None else Node (clid, subtrees)

(** Add a list of when in front of an equation *)
let rec add_whens e = function
  | [] -> e
  | (c, clid)::tl ->
    { kexpr_desc = KE_when (add_whens e tl, c, clid);
      kexpr_annot = (); kexpr_loc = dummy_loc }

(** Add a list of when in front of a type *)
let rec add_whens_ty ty = function
  | [] -> ty
  | (c, clid)::tl ->
    Asttypes.Clocked (add_whens_ty ty tl, c, clid)

(** Extract a list of constructor * clockid for whens *)
let rec whens_of_ty : ty -> (constr * ident) list = function
  | Base _ -> []
  | Clocked (ty, c, clid) -> (c, clid)::(whens_of_ty ty)

(** Reset the term and add some whens where they are needed *)
let rec reset_expr whens nwhens e =
  let loc = e.kexpr_loc in
  match e.kexpr_desc with
    | KE_const c -> e
    | KE_ident id ->
      let nwhens = try List.assoc id nwhens with _ -> [] in
      add_whens e (List.filter (fun (_, clid) ->
          not (List.mem clid nwhens)) whens)
    | KE_op (op, es) ->
      { e with kexpr_desc =
                 KE_op (op, List.map (reset_expr whens nwhens) es) }
    | KE_app (fid, es, _) ->
      let rexpr = List.fold_left (fun e (constr, clid) ->
          let x = clid^constr^"_reset" in
          let rexpr = { kexpr_desc = KE_ident x;
                        kexpr_annot = (); kexpr_loc = loc } in
          let rexpr = { rexpr with kexpr_desc = KE_op (Op_or, [rexpr; e]) } in
          { rexpr with kexpr_desc = KE_when (rexpr, constr, clid) })
          { kexpr_desc = KE_const (Cbool false);
            kexpr_annot = (); kexpr_loc = loc }
          (List.rev whens) in
      let rexpr = match rexpr.kexpr_desc with
        | KE_when (e, _, _) -> e | _ -> rexpr in
      let rexpr = { kexpr_desc = KE_fby (Cbool false, rexpr);
                    kexpr_annot = (); kexpr_loc = loc } in
      let (constr, clid) = List.hd whens in
      let rexpr = { kexpr_desc = KE_when (rexpr, constr, clid);
                    kexpr_annot = (); kexpr_loc = loc } in
      { e with kexpr_desc =
                 KE_app (fid, List.map (fun e -> reset_expr whens nwhens e) es,
                         rexpr) }
    | KE_fby (c, e) ->
      let cond = List.fold_left (fun e (constr, clid) ->
          let x = clid^constr^"_reset" in
          let rexpr = { kexpr_desc = KE_ident x;
                        kexpr_annot = (); kexpr_loc = loc } in
          let rexpr = { rexpr with kexpr_desc = KE_op (Op_or, [rexpr; e]) } in
          { rexpr with kexpr_desc = KE_when (rexpr, constr, clid) })
          { kexpr_desc = KE_const (Cbool false);
            kexpr_annot = (); kexpr_loc = loc }
          (List.rev whens) in
      let cond = match cond.kexpr_desc with
        | KE_when (e, _, _) -> e | _ -> cond in
      let cond = { kexpr_desc = KE_fby (Cbool false, cond);
                   kexpr_annot = (); kexpr_loc = loc } in
      let (constr, clid) = List.hd whens in
      let cond = { kexpr_desc = KE_when (cond, constr, clid);
                   kexpr_annot = (); kexpr_loc = loc } in
      let the =
        add_whens { kexpr_desc = KE_const c;
                    kexpr_annot = (); kexpr_loc = loc } whens
      and el = { kexpr_desc = KE_fby (c, reset_expr whens nwhens e);
                 kexpr_annot = (); kexpr_loc = loc } in
      { e with kexpr_desc = KE_op (Op_if, [cond; the; el]) }
    | KE_tuple es ->
      { e with kexpr_desc = KE_tuple (List.map (reset_expr whens nwhens) es) }
    | KE_when (e, constr, clid) -> e
    | KE_merge (id, es) -> e

(** Merge a tree of expressions according to clocks and constructors *)
let generate_merged_exprs (tree : expr_tree) =
  let rec gen_mer_e whens nwhens = function
    | None -> invalid_arg "gen_mer_e"
    | Leaf e -> reset_expr whens nwhens e
    | Node (clid, branches) ->
      let eMerge =
        KE_merge (clid,
                  List.sort (fun (s1, _) (s2, _) -> String.compare s1 s2)
                    (List.map (fun (c, substs, t) ->
                         let whens = (c, clid)::whens in
                         let e = apply_substs substs
                             (gen_mer_e whens
                                ((List.map (fun (id, _) ->
                                   id, (List.map snd whens)) substs)@nwhens) t) in
                         (c, e)) branches)) in
      { kexpr_desc = eMerge;
        kexpr_annot = (); kexpr_loc = dummy_loc } in
  gen_mer_e [] [] tree

(** Tree of local let bindings *)
type let_tree =
  | None
  (* The first ident is for the original id (in code), the second for the fresh id *)
  | Leaf of (ident * ident * ty * k_expr)
  | Node of ident * (constr * let_tree list) list

(** Get the let-tree of an automata tree *)
let rec get_let_tree : automata_tree -> let_tree = function
  | Leaf eq -> None
  | Node (clid, branches) ->
    Node (clid, List.map (fun (c, lets, ins, _) ->
        c, (List.map (fun (id, nid, ty, e) -> Leaf (id, nid, ty, desugar_expr e)) lets)@
           (List.map get_let_tree ins)
      ) branches)

(** Generate the local bindings equations from a let-tree *)
let generate_local_bindings (t : let_tree) :
  ((ident * ident) list) * ((k_equation * (ident * ty)) list) =
  let rec gen_loc_b substs whens = function
    | None -> [], []
    | Leaf (id, nid, ty, e) ->
      let substs = (id, nid)::substs in
      [(id, nid)],
      [{ keq_patt = { kpatt_desc = KP_ident nid; kpatt_loc = dummy_loc };
         keq_expr = reset_expr whens
             (List.map (fun (_, nid) -> nid, List.map snd whens)
                ((id, nid)::substs))
             (apply_substs substs e) },
       (nid, add_whens_ty ty whens)]
    | Node (clid, branches) ->
      List.fold_left (fun (substs, equs) (c, trs) ->
          let (substs', equs') =
            List.fold_left
              (fun (substs, equs) tr ->
                 let (substs', equs') = gen_loc_b substs ((c, clid)::whens) tr in
                 (substs@substs', equs@equs'))
              ([], []) trs in
          (substs@substs', equs@equs')) ([], []) branches
  in gen_loc_b [] [] t

(** Tree of until equations *)
type until_tree =
  | Node of ident * (constr * k_expr * until_tree list) list

(** Desugar a list of until statement in an automaton *)
let desugar_untils clid auto_constr untils =
  let untils = List.rev untils in
  let startE = { kexpr_desc = KE_const (Cconstr (auto_constr, "_ty"^clid));
                 kexpr_annot = (); kexpr_loc = dummy_loc; } in
  List.fold_left (fun e (cond, constr) ->
      let e' = KE_op (Op_if,
                      [desugar_expr cond;
                       { kexpr_desc = KE_const (Cconstr (constr, "_ty"^clid));
                         kexpr_annot = (); kexpr_loc = dummy_loc };
                       e]) in
      { kexpr_desc = e'; kexpr_annot = (); kexpr_loc = dummy_loc }) startE untils

(** Get the until tree in an automata tree *)
let rec get_until_tree : automata_tree -> until_tree = function
  | Leaf eq -> invalid_arg "get_until_tree"
  | Node (clid, branches) ->
    let untils = List.map (fun (c, _, instrs, unt) ->
        c, desugar_untils clid c unt,
        (List.fold_left (fun trs i ->
             try (get_until_tree i)::trs
             with _ -> trs) [] instrs)) branches in
    Node (clid, untils)

(** Generate a set of equations from an until tree *)
let rec generate_merged_untils tree =
  let rec gen_mer_u whens = function
    | Node (clid, branches) ->
      (* Compute the base cases *)
      let base =
        KE_merge (clid,
                  List.sort (fun (s1,_) (s2,_) -> String.compare s1 s2)
                    (List.map (fun (c, e, _) ->
                         let e' = add_whens e whens in
                         c, { kexpr_desc = KE_when (e', c, clid);
                              kexpr_annot = ();
                              kexpr_loc = dummy_loc; }) branches)) in
      let (constr1, _, _) = List.hd branches in
      let base =
        { kexpr_desc =
            KE_fby (Cconstr (constr1, "_ty"^clid),
                    { kexpr_desc = base;
                      kexpr_annot = (); kexpr_loc = dummy_loc });
          kexpr_annot = (); kexpr_loc = dummy_loc; } in
      let base = (if whens <> [] then reset_expr whens [] base else base) in
      let base =
        { keq_patt = { kpatt_desc = KP_ident clid; kpatt_loc = dummy_loc };
          keq_expr = base } in

      (* Compute the recursive cases *)
      let recu = List.flatten (List.map (fun (c, _, trs) ->
          List.flatten
            (List.map (gen_mer_u ((c, clid)::whens)) trs)) branches) in
      base::recu in
  gen_mer_u [] tree

let desugar_instr instr =
  match instr with
  | Eq eq -> [desugar_equation eq], [], []
  | Automaton branches ->
    (* Get the tree representing the hierarchy of automatas *)
    let automataTree = get_automata_tree instr in

    (* Get the variables and the expressions they correspond to *)
    let vars = List.sort_uniq String.compare (get_instr_vars instr) in
    let trees = List.combine vars
        (List.map (get_expr_tree automataTree) vars) in

    (* Create the equations for the local let bindings *)
    let lettree = get_let_tree automataTree in
    let lsubst, leqs = generate_local_bindings lettree in

    (* Create the equations from the found expressions *)
    let eqs = List.map (fun (v, tr) ->
        { keq_patt = { kpatt_desc = KP_ident v; kpatt_loc = dummy_loc; };
          keq_expr = apply_substs lsubst (generate_merged_exprs tr); }) trees in

    (* Get the untils *)
    let untilTree = get_until_tree automataTree in
    let untils = generate_merged_untils untilTree in

    (* Create the necessary clock types and clocks *)
    let clocks = get_automata_clocks automataTree in
    ((List.map fst leqs)@eqs@untils, clocks, (List.map snd leqs))

let desugar_node (n : p_node) =
  let (eqs, clocks, locals) =
    List.fold_left (fun (eqs, cl, vars) ins ->
        let (eqs', cl', vars') = desugar_instr ins in
        (eqs@eqs', cl@cl', vars@vars')) ([], [], []) n.pn_instrs in
  let clockdecs = List.map clockdec_of_automata_clock clocks
  and clockvars = List.map clockvar_of_automata_clock clocks in

  (* Reset clocks and equations *)

  (* Change the base of a clocked type *)
  let rec change_base ba : ty -> ty = function
    | Base _ -> Base ba
    | Clocked (t, c, id) ->
      Asttypes.Clocked (change_base ba t, c, id) in

  (* Reset clocks *)
  let resetclocks = List.flatten (
      List.map2 (fun (id, ty) (tyid, constrs) ->
          List.map (fun c ->
              ((id^c^"_reset",
                change_base Tbool ty),
               (id, c, List.filter (fun c' -> c' <> c) constrs))) constrs)
        clockvars clockdecs) in

  (* Reset equations *)
  let reset_equs = List.map (fun ((id, ty), (clid, c, otherconstrs)) ->
      let texpr = { kexpr_desc = KE_const (Cbool false);
                    kexpr_annot = (); kexpr_loc = dummy_loc }
      and fexpr = { kexpr_desc = KE_const (Cbool true);
                    kexpr_annot = (); kexpr_loc = dummy_loc } in
      let texpr = add_whens texpr ((c, clid)::(whens_of_ty ty)) in
      let fexprs = List.map (fun c ->
          c, add_whens fexpr ((c, clid)::(whens_of_ty ty))) otherconstrs in
      { keq_patt = { kpatt_desc = KP_ident id; kpatt_loc = dummy_loc };
        keq_expr = { kexpr_desc = KE_merge (clid,
                         List.sort (fun (s1,_) (s2,_) -> String.compare s1 s2)
                         ((c, texpr)::fexprs));
                     kexpr_annot = (); kexpr_loc = dummy_loc }}) resetclocks in

  { kn_name = n.pn_name;
    kn_input = n.pn_input;
    kn_output = n.pn_output;
    kn_local = n.pn_local@clockvars@locals@(List.map fst resetclocks);
    kn_equs = eqs@reset_equs;
    kn_loc = n.pn_loc },
  clockdecs

let desugar_file (f : p_file) : k_file =
  let (nodes, clocks) =
    List.fold_left (fun (nod, cl) n ->
      let (n', cl') = desugar_node n in (n'::nod, cl@cl')) ([], []) f.pf_nodes in
  { kf_clocks = (List.map (fun (c, constrs) ->
        (c, List.sort String.compare constrs)) (f.pf_clocks@clocks));
    kf_nodes = List.rev nodes; }
