(** Clock checking *)

open Asttypes
open Minils
open PMinils

type nclock = (clock * ident option)

module TypeClockAnnot : (Annotations with type t = (ty * nclock)) = struct
  type t = (ty * nclock)
  let string_of_t (ty, (ck, id)) =
    match id with
    | None -> Printf.sprintf "(%s when %s)"
                (string_of_ty ty) (string_of_clock ck)
    | Some id -> Printf.sprintf "(%s : %s when %s)"
                   id (string_of_ty ty) (string_of_clock ck)
end

module CPMinils = PMINILS(TypeClockAnnot)

type sclock =
  | Sbase
  | Svar of instck ref
  | Son of (constr * instident ref * sclock)

and instident =
  | UnknownIdent of ident
  | InstIdent of ident

and instck =
  | UnknownCk of ident
  | InstCk of sclock

let rec string_of_sclock = function
  | Sbase -> "."
  | Svar inst -> string_of_instck !inst
  | Son (constr, id, ck) ->
    Printf.sprintf "(%s on %s(%s))" (string_of_sclock ck) constr (string_of_instident !id)

and string_of_instck = function
  | UnknownCk i -> Printf.sprintf "?%s" i
  | InstCk ck -> string_of_sclock ck

and string_of_instident = function
  | UnknownIdent id -> Printf.sprintf "?%s" id
  | InstIdent id -> id

let rec sclock_of_clock = function
  | Cbase -> Sbase
  | Con (constr, id, ck) ->
    Son (constr, ref (InstIdent id), (sclock_of_clock ck))

let rec clock_of_sclock = function
  | Sbase | Svar { contents = UnknownCk _ } -> Cbase
  | Svar { contents = InstCk ck } -> clock_of_sclock ck
  | Son (constr, id, sck) ->
    Con (constr, ident_of_instident !id, clock_of_sclock sck)
and ident_of_instident = function
  | UnknownIdent id -> id
  | InstIdent id -> id

module ClockElabAnnot : (Annotations with type t = (ty * (sclock * (instident ref) option))) = struct
  type t = ty * (sclock * (instident ref) option)
  let string_of_t (ty, (sck, _)) =
    Printf.sprintf "(%s when %s)" (string_of_ty ty) (string_of_sclock sck)
end

module CEPMinils = PMINILS(ClockElabAnnot)

open Typechecker.TPMinils

exception UnifError of (instident * instident)
exception ClockError of (string * location)

(* let clocks_of (es : CPMinils.k_expr list) =
 *   List.concat (List.map (fun (e : CPMinils.k_expr) -> List.map snd e.kexpr_annot) es) *)

let sclocks_of (es : CEPMinils.k_expr list) =
  List.concat (List.map (fun (e : CEPMinils.k_expr) -> List.map (fun (_, (ck, _)) -> ck) e.kexpr_annot) es)

let anons_of (es : CEPMinils.k_expr list) =
  List.concat (List.map (fun (e : CEPMinils.k_expr) -> List.map (fun (_, (_, id)) -> id) e.kexpr_annot) es)

(** unify two idents [id1] and [id2] *)
let unify_ident id1 id2 =
  match id1, id2 with
  | ({ contents = UnknownIdent _ } as id1), id2 | id2, ({ contents = UnknownIdent _ } as id1) ->
    id1 := !id2
  | { contents = InstIdent id1 }, { contents = InstIdent id2 } when id1 = id2 -> ()
  | _ -> raise (UnifError (!id1, !id2))

let rec occurs_check ck id =
  match ck with
  | Sbase -> ()
  | Svar { contents = UnknownCk id' } when id = id' -> invalid_arg "occurs_check"
  | Svar _ -> ()
  | Son (_, _, ck) -> occurs_check ck id

(** unify two clocks [ck1] and [ck2] *)
let unify_sclock loc (ck1 : sclock) (ck2 : sclock) =
  let error msg =
    raise (ClockError
             (Printf.sprintf "Could not unify clocks %s and %s%s"
                (string_of_sclock ck1) (string_of_sclock ck2) msg, loc)) in
  let rec aux (ck1 : sclock) (ck2 : sclock) =
    match ck1, ck2 with
    | Sbase, Sbase -> ()
    | Svar ({ contents = UnknownCk id } as v), ck | ck, Svar ({ contents = UnknownCk id } as v) ->
      (try occurs_check ck id;
       with _ -> error (Printf.sprintf " : %s occurs in %s" id (string_of_sclock ck)));
      v:= InstCk ck;
    | Svar ({ contents = InstCk ck1}), ck2 | ck1, Svar ({ contents = InstCk ck2 }) ->
      aux ck1 ck2
    | Son (c1, ckid1, b1), Son (c2, ckid2, b2) when c1 = c2 ->
      (try unify_ident ckid1 ckid2 with _ -> error "");
      aux b1 b2
    | _ -> error ""
  in aux ck1 ck2

(** unify two pairs containing each a clock and potentially an ident *)
let unify_nsclock loc (ck1, id1) (ck2, id2) =
  unify_sclock loc ck1 ck2;
  match id1, id2 with
  | Some id1, Some id2 ->
    (try (unify_ident id1 id2)
     with UnifError (id1, id2) ->
       raise (ClockError (Printf.sprintf "could not unify %s and %s"
                            (string_of_instident id1) (string_of_instident id2), loc)))
  | _ -> ()

(** Instantiate an identifier *)
let inst_ident id = InstIdent id

(** Turn an unknown ident into an instantiated ident *)
let freeze_ident id =
  match id with
  | { contents = UnknownIdent x } -> id := InstIdent x
  | _ -> ()

(** Instantiate a clock *)
let rec inst_clock bck subst = function
  | Cbase -> bck
  | Con (constr, id, ck) ->
    Son (constr, (subst id), inst_clock bck subst ck)

let get_clock_in_env id vars loc =
  try (List.assoc id vars)
  with Not_found -> raise (ClockError (Printf.sprintf "%s not found in env, maybe it doesnt have the correct clock for the block ?" id, loc))

(** Check and get the clocked version of expression [e] *)
let rec elab_expr ?(is_top=false) (nodes : (ident * CPMinils.p_node) list) vars (e : k_expr) : CEPMinils.k_expr =
  let loc = e.kexpr_loc and ty = e.kexpr_annot in
  match e.kexpr_desc with
  | KE_const c ->
    let ck = Svar (ref (UnknownCk (Atom.fresh "$"))) in
    (* A constant can be subsampled to any clock ! *)
    { kexpr_desc = KE_const c; kexpr_annot = [(List.hd ty, (ck, None))];
      kexpr_loc = loc }
  | KE_ident id ->
    let ck = get_clock_in_env id vars e.kexpr_loc in
    { kexpr_desc = KE_ident id;
      kexpr_annot = [(List.hd ty, (sclock_of_clock ck,
                                   if is_top then None
                                   else Some (ref (InstIdent id))))];
      kexpr_loc = loc }
  | KE_unop (op, e1) ->
    let e1' = elab_expr nodes vars e1 in
    let (_, (ck, _)) = List.hd (e1'.kexpr_annot) in
    { kexpr_desc = KE_unop (op, e1'); kexpr_annot = [(List.hd ty, (ck, None))];
      kexpr_loc = loc }
  | KE_binop (op, e1, e2) ->
    let e1' = elab_expr nodes vars e1 and e2' = elab_expr nodes vars e2 in
    let (_, (ck1, _)) = List.hd (e1'.kexpr_annot)
    and (_, (ck2, _)) = List.hd (e2'.kexpr_annot) in
    unify_sclock loc ck1 ck2;
    { kexpr_desc = KE_binop (op, e1', e2'); kexpr_annot = [(List.hd ty, (ck1, None))];
      kexpr_loc = loc }
  | KE_fby (e0s, es) ->
    let e0s' = elab_exprs nodes vars e0s and es' = elab_exprs nodes vars es in
    let ck0s = sclocks_of e0s' and cks = sclocks_of es' in
    List.iter2 (unify_sclock loc) ck0s cks;
    { kexpr_desc = KE_fby (e0s', es');
      kexpr_annot = List.combine ty (List.map (fun ck -> (ck, None)) ck0s);
      kexpr_loc = loc }
  | KE_arrow (e0s, es) ->
    let e0s' = elab_exprs nodes vars e0s and es' = elab_exprs nodes vars es in
    let ck0s = sclocks_of e0s' and cks = sclocks_of es' in
    List.iter2 (unify_sclock loc) ck0s cks;
    { kexpr_desc = KE_arrow (e0s', es');
      kexpr_annot = List.combine ty (List.map (fun ck -> (ck, None)) ck0s);
      kexpr_loc = loc }
  | KE_match (e, branches) ->
    let e' = elab_expr nodes vars e and branches' = elab_branches nodes vars branches in
    let (_, (ck, _)) = List.hd e'.kexpr_annot in
    List.iter (fun (_, es) ->
        List.iter (fun ck' -> unify_sclock loc ck ck') (sclocks_of es)) branches';
    { kexpr_desc = KE_match (e', branches');
      kexpr_annot = List.map (fun ty -> (ty, (ck, None))) ty;
      kexpr_loc = loc }
  | KE_when (es, constr, ckid) ->
    let es' = elab_exprs nodes vars es in
    let ck = sclock_of_clock (get_clock_in_env ckid vars loc)
    and cks = sclocks_of es' in
    List.iter (fun ck' -> unify_sclock loc ck ck') cks;
    { kexpr_desc = KE_when (es', constr, ckid);
      kexpr_annot = List.map (fun ty -> (ty, (Son (constr, ref (InstIdent ckid), ck), None))) ty;
      kexpr_loc = loc }
  | KE_merge (ckid, branches) ->
    let branches' = elab_branches nodes vars branches in
    let ck = sclock_of_clock (get_clock_in_env ckid vars loc) in

    List.iter (fun (constr, es) ->
        let cks = sclocks_of es in
        List.iter (fun ck' -> unify_sclock loc (Son (constr, ref (InstIdent ckid), ck)) ck') cks;
      ) branches';

    { kexpr_desc = KE_merge (ckid, branches');
      kexpr_annot = List.map (fun ty -> (ty, (ck, None))) ty;
      kexpr_loc = loc }
  | KE_app (fid, es, er) ->
    let es' = elab_exprs nodes vars es and er' = elab_expr nodes vars er in
    let cks = sclocks_of es' and anons = anons_of es' in

    (** freeze the input idents that weren't unified, as they are anonymous *)
    List.iter (fun id -> match id with
        | Some id -> freeze_ident id
        | None -> ()) anons;

    let node = List.assoc fid nodes in

    let subst = List.map (fun (id, _) -> (id, ref (UnknownIdent (Atom.fresh "$")))) (node.pn_input@node.pn_output) in
    let subst = fun x -> List.assoc x subst and bck = Svar (ref (UnknownCk (Atom.fresh "$"))) in
    let inck = List.map (fun (id, (_, ck)) -> (inst_clock bck subst ck, Some (subst id))) node.pn_input
    and outck = List.map (fun (id, (_, ck)) -> (inst_clock bck subst ck, Some (subst id))) node.pn_output in

    List.iter2 (unify_nsclock loc) inck (List.combine cks anons);

    { kexpr_desc = KE_app (fid, es', er');
      kexpr_annot = List.combine ty outck;
      kexpr_loc = loc }
and elab_exprs ?(is_top=false) nodes vars (es : k_expr list) =
  List.map (elab_expr ~is_top nodes vars) es
and elab_branches nodes vars branches =
  List.map (fun (c, es) -> (c, elab_exprs nodes vars es)) branches

(** Once an expression is elaborated, its clocks can be "frozen".
    Its also at this point that we infer additional whens around constants *)

let rec add_whens ty ck e : CPMinils.k_expr =
  match ck with
  | Cbase -> e
  | Con (constr, ckid, ck) ->
    let e = add_whens ty ck e in
    { kexpr_desc = KE_when ([e], constr, ckid);
      kexpr_annot = [(ty, (Con (constr, ckid, ck), None))];
      kexpr_loc = dummy_loc }

let rec freeze_expr (e : CEPMinils.k_expr) : CPMinils.k_expr =
  let annot = List.map (fun (ty, (ck, id)) ->
      (ty, (clock_of_sclock ck, match id with
         | None -> None
         | Some id -> Some (ident_of_instident !id)))) e.kexpr_annot in
  let desc = match e.kexpr_desc with
    | KE_const c ->
      let (ty, (ck, _)) = List.hd annot in
      (add_whens ty ck { kexpr_desc = (CPMinils.KE_const c);
                         kexpr_annot = [(ty, (Cbase, None))];
                         kexpr_loc = e.kexpr_loc; }).kexpr_desc
    | KE_ident i -> KE_ident i
    | KE_unop (op, e1) -> KE_unop (op, freeze_expr e1)
    | KE_binop (op, e1, e2) -> KE_binop (op, freeze_expr e1, freeze_expr e2)
    | KE_fby (e0s, es) -> KE_fby (freeze_exprs e0s, freeze_exprs es)
    | KE_arrow (e0s, es) -> KE_arrow (freeze_exprs e0s, freeze_exprs es)
    | KE_match (e, branches) -> KE_match (freeze_expr e, freeze_branches branches)
    | KE_when (es, constr, ckid) -> KE_when (freeze_exprs es, constr, ckid)
    | KE_merge (ckid, branches) -> KE_merge (ckid, freeze_branches branches)
    | KE_app (f, es, er) -> KE_app (f, freeze_exprs es, freeze_expr er)
  in { kexpr_desc = desc;
       kexpr_annot = annot;
       kexpr_loc = e.kexpr_loc }
and freeze_exprs es = List.map freeze_expr es
and freeze_branches branches = List.map (fun (c, es) -> (c, freeze_exprs es)) branches

(** Get the clocks(s) expected for a pattern [pat],
    as well as the translated pattern *)
let get_pattern_clock (vars : (ident * clock) list) pat loc =
  List.map (fun id -> sclock_of_clock (get_clock_in_env id vars loc)) pat

(** Check the clocks for the equation [eq] *)
let elab_equation nodes vars (eq : k_equation) : CPMinils.k_equation =
  let es' = elab_exprs ~is_top:true nodes vars eq.keq_expr in

  (** Check that the clocks are correct *)
  let expected = get_pattern_clock vars eq.keq_patt eq.keq_loc
  and actual = sclocks_of es' in
  List.iter2 (unify_sclock eq.keq_loc) expected actual;

  (** Check that the anons are correct *)
  let ids = eq.keq_patt and anons = anons_of es' in
  List.iter2 (fun ex act ->
      match act with
      | None -> ()
      | Some act ->
        (try unify_ident (ref (inst_ident ex)) act
         with UnifError (id1, id2) ->
           raise (ClockError (Printf.sprintf "Cannot unify anon names in eq : expected %s, got %s"
                                (string_of_instident id1) (string_of_instident id2)
                             , eq.keq_loc)))
    ) ids anons;

  { keq_patt = eq.keq_patt; keq_expr = freeze_exprs es'; keq_loc = eq.keq_loc }

let rec elab_instr nodes vars (ins : p_instr) : CPMinils.p_instr =
  let (desc : CPMinils.p_instr_desc) =
    match ins.pinstr_desc with
    | Eq eq -> Eq (elab_equation nodes vars eq)
    | Reset (ins, er) ->
      Reset (elab_instrs nodes vars ins,
             freeze_expr (elab_expr nodes vars er)) (* TODO should there be a constraint ? *)
    | Switch (e, brs) ->
      let e' = freeze_expr (elab_expr nodes vars e) in
      let ck = match e'.kexpr_annot with
        | [(_, (ck, _))] -> ck
        | _ -> failwith "Should not happen" in
      (* Only keep variables on the clock ck in the env *)
      let vars' = List.filter (fun (_, ck') -> ck = ck') vars in
      Switch (e', elab_branches nodes vars' brs)
    | _ -> failwith "TODO elab_instr"
  in { pinstr_desc = desc; pinstr_loc = ins.pinstr_loc }
and elab_instrs nodes vars ins =
  List.map (elab_instr nodes vars) ins
and elab_branches nodes vars brs =
  List.map (fun (c, ins) -> (c, elab_instrs nodes vars ins)) brs

(** Check a clock in a clocking env *)
let check_clock (n : p_node) vars ck =
  let error idck ck1 ck2 =
    raise (ClockError
             (Printf.sprintf "in %s, %s should be on %s, %s found instead"
                (string_of_clock ck) idck (string_of_clock ck1) (string_of_clock ck2), n.pn_loc)) in
  let rec aux ck =
    match ck with
    | Cbase -> ()
    | Con (_, idck, ck) ->
      aux ck;
      let ck' = List.assoc idck vars in
      if (ck <> ck') then error idck ck' ck
  in aux ck

(** Check the clocks for the node [f] *)
let elab_node (nodes : (ident * CPMinils.p_node) list) (n : p_node) : CPMinils.p_node =
  let idck = List.map (fun (id, (_, ck)) -> (id, ck)) in
  let in_vars = idck n.pn_input
  and inout_vars = idck (n.pn_input@n.pn_output)
  and vars = idck (n.pn_input@n.pn_output@n.pn_local) in

  (* check clocks *)
  List.iter (fun (_, (_, ck)) -> check_clock n in_vars ck) n.pn_input;
  List.iter (fun (_, (_, ck)) -> check_clock n inout_vars ck) n.pn_output;
  List.iter (fun (_, (_, ck)) -> check_clock n vars ck) n.pn_local;

  (* elab instructions *)
  let instrs' = elab_instrs nodes vars n.pn_instrs in

  { pn_name = n.pn_name;
    pn_input = n.pn_input;
    pn_output = n.pn_output;
    pn_local = n.pn_local;
    pn_instrs = instrs';
    pn_loc = n.pn_loc }

(** Check the clocks for the file [f] *)
let elab_file (f : p_file) : CPMinils.p_file =
  let nodes =
    try List.rev
          (List.map snd
             (List.fold_left (fun (env : (ident * CPMinils.p_node) list) n ->
                  (n.pn_name, (elab_node env n))::env) [] f.pf_nodes))
    with
    | ClockError (msg, loc) ->
      Printf.eprintf "Clock checking error : %s at %s\n"
        msg (string_of_loc loc); exit 1 in
  { pf_nodes = nodes; pf_clocks = f.pf_clocks }
