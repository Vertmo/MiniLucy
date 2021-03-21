(** Clock checking *)

open Common
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

let block_error id bck ck loc =
  ClockError
    (Printf.sprintf "%s is declared to have clock %s, but should have the block clock %s"
    id (string_of_sclock bck) (string_of_sclock ck), loc)

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

(** collapse path : Svar (InstCk (Svar ck)) becomes (Svar ck) *)
(* let rec collapse_path ck =
 *   match ck with
 *   | Sbase | Svar { contents = UnknownCk _ } -> ()
 *   | Svar ({ contents = InstCk ck' } as ckref) ->
 *     collapse_path ck';
 *     (match ck' with
 *      | Svar { contents = x } -> ckref := x
 *      | _ -> ())
 *   | Son (constr, id, ck) -> collapse_path ck *)

(** check that two clocks are equal modulo paths *)
let rec sclock_eq ck1 ck2 =
  match ck1, ck2 with
  | Sbase, Sbase -> true
  | Svar { contents = UnknownCk id1 }, Svar { contents = UnknownCk id2 } -> id1 = id2
  | Svar { contents = InstCk ck1 }, ck2
  | ck1, Svar { contents = InstCk ck2 } -> sclock_eq ck1 ck2
  | Son (c1, id1, ck1), Son (c2, id2, ck2) ->
    c1 = c2 && id1 = id2 && sclock_eq ck1 ck2
  | _, _ -> false

let rec occurs_check ck id =
  match ck with
  | Sbase -> ()
  | Svar { contents = UnknownCk id' } when id = id' -> invalid_arg "occurs_check"
  | Svar { contents = InstCk ck }
  | Son (_, _, ck) -> occurs_check ck id
  | _ -> ()

(** unify two clocks [ck1] and [ck2] *)
let unify_sclock loc (ck1 : sclock) (ck2 : sclock) =
  let error msg =
    raise (ClockError
             (Printf.sprintf "Could not unify clocks %s and %s%s"
                (string_of_sclock ck1) (string_of_sclock ck2) msg, loc)) in
  let rec aux (ck1 : sclock) (ck2 : sclock) =
    match ck1, ck2 with
    | ck1, ck2 when sclock_eq ck1 ck2 -> ()
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

(* Environment handling *)

module Env = Map.Make(String)

(** Environment with explicit representation of block hierarchy *)
type clock_env =
  | EnvBase of sclock Env.t
  | EnvOn of (clock_env * sclock * constr * ident)

(** Recover a clock from an environment *)
let rec env_get id env loc =
  match env with
  | EnvBase env ->
    (try Env.find id env with
     | _ -> raise (ClockError (Printf.sprintf "%s not found in env" id, loc)))
  | EnvOn (env, ck, cons, ckid) ->
    let ck' = env_get id env loc in
    unify_sclock loc ck ck';
    Son (cons, ref (InstIdent ckid), ck')

let rec env_add id ck env loc =
  match env with
  | EnvBase env -> EnvBase (Env.add id ck env)
  | EnvOn (env, ck', c, ckid) ->
    unify_sclock loc (Son (c, ref (InstIdent ckid), ck')) ck;
    EnvOn (env_add id ck' env loc, ck', c, ckid)

(** check that a clock is in an environment *)
let rec env_mem id env =
  match env with
  | EnvBase e -> Env.mem id e
  | EnvOn (env, _, _, _) -> env_mem id env

(** Check and get the clocked version of expression [e] *)
let rec elab_expr ?(is_top=false) (nodes : (ident * CPMinils.p_node) list) env (e : k_expr) : CEPMinils.k_expr =
  let loc = e.kexpr_loc and ty = e.kexpr_annot in
  match e.kexpr_desc with
  | KE_const c ->
    let ck = Svar (ref (UnknownCk (Atom.fresh "_"))) in
    (* A constant can be subsampled to any clock ! *)
    { kexpr_desc = KE_const c; kexpr_annot = [(List.hd ty, (ck, None))];
      kexpr_loc = loc }
  | KE_ident id ->
    let ck = env_get id env e.kexpr_loc in
    { kexpr_desc = KE_ident id;
      kexpr_annot = [(List.hd ty, (ck,
                                   if is_top then None
                                   else Some (ref (InstIdent id))))];
      kexpr_loc = loc }
  | KE_unop (op, e1) ->
    let e1' = elab_expr nodes env e1 in
    let (_, (ck, _)) = List.hd (e1'.kexpr_annot) in
    { kexpr_desc = KE_unop (op, e1'); kexpr_annot = [(List.hd ty, (ck, None))];
      kexpr_loc = loc }
  | KE_binop (op, e1, e2) ->
    let e1' = elab_expr nodes env e1 and e2' = elab_expr nodes env e2 in
    let (_, (ck1, _)) = List.hd (e1'.kexpr_annot)
    and (_, (ck2, _)) = List.hd (e2'.kexpr_annot) in
    unify_sclock loc ck1 ck2;
    { kexpr_desc = KE_binop (op, e1', e2'); kexpr_annot = [(List.hd ty, (ck1, None))];
      kexpr_loc = loc }
  | KE_fby (e0s, es, er) ->
    let e0s' = elab_exprs nodes env e0s and es' = elab_exprs nodes env es
    and er' = elab_expr nodes env er in
    let ck0s = sclocks_of e0s' and cks = sclocks_of es' in
    List.iter2 (unify_sclock loc) ck0s cks;
    { kexpr_desc = KE_fby (e0s', es', er');
      kexpr_annot = List.combine ty (List.map (fun ck -> (ck, None)) ck0s);
      kexpr_loc = loc }
  | KE_arrow (e0s, es, er) ->
    let e0s' = elab_exprs nodes env e0s and es' = elab_exprs nodes env es
    and er' = elab_expr nodes env er in
    let ck0s = sclocks_of e0s' and cks = sclocks_of es' in
    List.iter2 (unify_sclock loc) ck0s cks;
    { kexpr_desc = KE_arrow (e0s', es', er');
      kexpr_annot = List.combine ty (List.map (fun ck -> (ck, None)) ck0s);
      kexpr_loc = loc }
  | KE_match (e, branches) ->
    let e' = elab_expr nodes env e and branches' = elab_branches nodes env branches in
    let (_, (ck, _)) = List.hd e'.kexpr_annot in
    List.iter (fun (_, es) ->
        List.iter (fun ck' -> unify_sclock loc ck ck') (sclocks_of es)) branches';
    { kexpr_desc = KE_match (e', branches');
      kexpr_annot = List.map (fun ty -> (ty, (ck, None))) ty;
      kexpr_loc = loc }
  | KE_when (es, constr, ckid) ->
    let es' = elab_exprs nodes env es in
    let ck = env_get ckid env loc
    and cks = sclocks_of es' in
    List.iter (fun ck' -> unify_sclock loc ck ck') cks;
    { kexpr_desc = KE_when (es', constr, ckid);
      kexpr_annot = List.map (fun ty -> (ty, (Son (constr, ref (InstIdent ckid), ck), None))) ty;
      kexpr_loc = loc }
  | KE_merge (ckid, branches) ->
    let branches' = elab_branches nodes env branches in
    let ck = env_get ckid env loc in

    List.iter (fun (constr, es) ->
        let cks = sclocks_of es in
        List.iter (fun ck' -> unify_sclock loc (Son (constr, ref (InstIdent ckid), ck)) ck') cks;
      ) branches';

    { kexpr_desc = KE_merge (ckid, branches');
      kexpr_annot = List.map (fun ty -> (ty, (ck, None))) ty;
      kexpr_loc = loc }
  | KE_app (fid, es, er) ->
    let es' = elab_exprs nodes env es and er' = elab_expr nodes env er in
    let cks = sclocks_of es' and anons = anons_of es' in

    (** freeze the input idents that weren't unified, as they are anonymous *)
    List.iter (fun id -> match id with
        | Some id -> freeze_ident id
        | None -> ()) anons;

    let node = List.assoc fid nodes in

    let subst = List.map (fun (id, _) -> (id, ref (UnknownIdent (Atom.fresh "_")))) (node.pn_input@node.pn_output) in
    let subst = fun x -> List.assoc x subst and bck = Svar (ref (UnknownCk (Atom.fresh "_"))) in
    let inck = List.map (fun (id, (_, ck)) -> (inst_clock bck subst ck, Some (subst id))) node.pn_input
    and outck = List.map (fun (id, (_, ck)) -> (inst_clock bck subst ck, Some (subst id))) node.pn_output in

    List.iter2 (unify_nsclock loc) inck (List.combine cks anons);

    { kexpr_desc = KE_app (fid, es', er');
      kexpr_annot = List.combine ty outck;
      kexpr_loc = loc }
  | KE_last id ->
    let ck = env_get id env e.kexpr_loc in
    { kexpr_desc = KE_last id;
      kexpr_annot = [(List.hd ty, (ck, None))];
      kexpr_loc = loc }
and elab_exprs ?(is_top=false) nodes env (es : k_expr list) =
  List.map (elab_expr ~is_top nodes env) es
and elab_branches nodes env branches =
  List.map (fun (c, es) -> (c, elab_exprs nodes env es)) branches

(** Once an expression is elaborated, its clocks can be "frozen".
    Its also at this point that we infer additional whens around constants.
    We also check that none of the clocks that were inferred escape are anonymous
    that escape their scope *)

let rec check_ck_in_scope (env : clock_env) loc = function
  | Cbase -> ()
  | Con (_, ckid, ck) ->
    check_ck_in_scope env loc ck;
    if (not (env_mem ckid env))
    then raise (ClockError
                  (Printf.sprintf "Constant is subsampled by %s which escapes its scope" ckid,
                   loc))

let rec add_whens ty ck e : CPMinils.k_expr =
  match ck with
  | Cbase -> e
  | Con (constr, ckid, ck) ->
    let e = add_whens ty ck e in
    { kexpr_desc = KE_when ([e], constr, ckid);
      kexpr_annot = [(ty, (Con (constr, ckid, ck), None))];
      kexpr_loc = dummy_loc }

let rec freeze_expr env (e : CEPMinils.k_expr) : CPMinils.k_expr =
  let annot = List.map (fun (ty, (ck, id)) ->
      (ty, (clock_of_sclock ck, match id with
         | None -> None
         | Some id -> Some (ident_of_instident !id)))) e.kexpr_annot in
  let desc = match e.kexpr_desc with
    | KE_const c ->
      let (ty, (ck, _)) = List.hd annot in
      check_ck_in_scope env e.kexpr_loc ck;
      (add_whens ty ck
         { kexpr_desc = (CPMinils.KE_const c);
           kexpr_annot = [(ty, (Cbase, None))];
           kexpr_loc = e.kexpr_loc; }).kexpr_desc
    | KE_ident i -> KE_ident i
    | KE_unop (op, e1) -> KE_unop (op, freeze_expr env e1)
    | KE_binop (op, e1, e2) -> KE_binop (op, freeze_expr env e1, freeze_expr env e2)
    | KE_fby (e0s, es, er) ->
      KE_fby (freeze_exprs env e0s, freeze_exprs env es, freeze_expr env er)
    | KE_arrow (e0s, es, er) ->
      KE_arrow (freeze_exprs env e0s, freeze_exprs env es, freeze_expr env er)
    | KE_match (e, branches) -> KE_match (freeze_expr env e, freeze_branches env branches)
    | KE_when (es, constr, ckid) -> KE_when (freeze_exprs env es, constr, ckid)
    | KE_merge (ckid, branches) -> KE_merge (ckid, freeze_branches env branches)
    | KE_app (f, es, er) -> KE_app (f, freeze_exprs env es, freeze_expr env er)
    | KE_last i -> KE_last i
  in { kexpr_desc = desc;
       kexpr_annot = annot;
       kexpr_loc = e.kexpr_loc }
and freeze_exprs env = List.map (freeze_expr env)
and freeze_branches env = List.map (fun (c, es) -> (c, freeze_exprs env es))

(** Get the clocks(s) expected for a pattern [pat],
    as well as the translated pattern *)
let get_pattern_clock (env : clock_env) pat loc =
  List.map (fun id -> env_get id env loc) pat

(** Check the clocks for the equation [eq] *)
let elab_equation nodes env (eq : k_equation) : CPMinils.k_equation =
  let es' = elab_exprs ~is_top:true nodes env eq.keq_expr in

  (** Check that the clocks are correct *)
  let expected = get_pattern_clock env eq.keq_patt eq.keq_loc
  and actual = sclocks_of es' in

  (** Check that the clocks correspond *)
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

  { keq_patt = eq.keq_patt; keq_expr = freeze_exprs env es'; keq_loc = eq.keq_loc }

let rec elab_instr nodes env (ins : p_instr) : CPMinils.p_instr =
  let (desc : CPMinils.p_instr_desc) =
    match ins.pinstr_desc with
    | Eq eq -> Eq (elab_equation nodes env eq)
    | Block bck -> Block (elab_block nodes env bck)
    | Reset (ins, er) ->
      Reset (elab_instrs nodes env ins,
             freeze_expr env (elab_expr nodes env er)) (* TODO should there be a constraint ? *)
    | Switch (e, brs, (_, defs)) ->
      let e' = elab_expr nodes env e in
      let (_, (ck, _)) = List.hd e'.kexpr_annot in
      let ckid = Atom.fresh "_" in
      let env' = env_add ckid ck env ins.pinstr_loc in
      let brs' = List.map (fun (c, ins) ->
          (c, elab_instrs nodes (EnvOn (env', ck, c, ckid)) ins)) brs in
      let e' = freeze_expr env e' in
      Switch (e', brs', (Some ckid, defs))
    | Automaton (brs, (ckid, _, defs)) ->
      let ckid = match ckid with Some ckid -> ckid | _ -> failwith "Should not happen"
      and bck = Svar (ref (UnknownCk (Atom.fresh "_"))) in
      let env' = env_add ckid bck env ins.pinstr_loc in
      let brs' = List.map (fun (c, unlesss, instrs, untils) ->
          let bck' = Son (c, ref (InstIdent ckid), bck)
          and env' = EnvOn (env', bck, c, ckid) in
          let unlesss' = List.map (elab_un nodes env' bck') unlesss
          and untils' = List.map (elab_un nodes env' bck') untils
          and instrs' = elab_instrs nodes env' instrs in
          (c, unlesss', instrs', untils')
        ) brs in
      Automaton (brs', (Some ckid, Some (clock_of_sclock bck), defs))
  in { pinstr_desc = desc; pinstr_loc = ins.pinstr_loc }
and elab_instrs nodes env = List.map (elab_instr nodes env)

and elab_un nodes env bck (e, s, b) =
  let e' = elab_expr nodes env e in
  let (_, (ck, _)) = List.hd e'.kexpr_annot in
  unify_sclock e.kexpr_loc bck ck;
  (freeze_expr env e', s, b)

and elab_block nodes env block : CPMinils.p_block =
  let bck = Svar (ref (UnknownCk (Atom.fresh "_"))) in
  let locals = List.map (fun (x, (ty, ck), l) ->
      (x, (ty, inst_clock bck (fun x -> ref (InstIdent x)) ck), l)) block.pb_local in
  let env' = List.fold_left (fun env (x, (_, ck), _) -> env_add x ck env block.pb_loc) env locals in
  { pb_local = List.map (fun (x, (ty, ck), l) -> (x, (ty, clock_of_sclock ck), l)) locals;
    pb_instrs = elab_instrs nodes env' block.pb_instrs;
    pb_loc = block.pb_loc }

(** Check a clock in a clocking env *)
let check_clock (n : p_node) env ck =
  let error idck ck1 ck2 =
    raise (ClockError
             (Printf.sprintf "in %s, %s should be on %s, %s found instead"
                (string_of_clock ck) idck (string_of_clock ck1) (string_of_clock ck2), n.pn_loc)) in
  let rec aux ck =
    match ck with
    | Cbase -> ()
    | Con (_, idck, ck) ->
      aux ck;
      let ck' = List.assoc idck env in
      if (ck <> ck') then error idck ck' ck
  in aux ck

let inst_clocks (cks : (ident * (ty * clock)) list) : (ident * sclock) list =
  List.map (fun (id, (_, ck)) ->
      (id, inst_clock
         (Svar (ref (UnknownCk (Atom.fresh "_"))))
         (fun id -> (ref (InstIdent id)))
         ck))
    cks

let rec elab_clock (cks : (ident * sclock) list) = function
  | Sbase | Svar { contents = UnknownCk _ } -> ()
  | Svar { contents = InstCk ck } -> elab_clock cks ck
  | Son (constr, { contents = InstIdent ckid }, ck' ) ->
    elab_clock cks ck';
    let ck'' = List.assoc ckid cks in
    unify_sclock dummy_loc ck'' ck';
  | _ -> invalid_arg "elab_clock"

(* let elab_clocks (cks : (ident * sclock) list) =
 *   List.iter (fun (_, ck) -> elab_clock cks ck) cks *)

let freeze_clocks (cks : (ident * sclock) list) =
  List.map (fun (id, ck) -> (id, clock_of_sclock ck)) cks

(** Check the clocks for the node [f] *)
let elab_node (nodes : (ident * CPMinils.p_node) list) (n : p_node) : CPMinils.p_node =
  let in_env = inst_clocks n.pn_input and out_env = inst_clocks n.pn_output in

  (* check clocks *)
  let env =
    try
      List.iter (fun (_, ck) -> elab_clock in_env ck) in_env;
      List.iter (fun (_, ck) -> elab_clock (in_env@out_env) ck) out_env;
      freeze_clocks (in_env@out_env)
    with _ -> raise (ClockError
                       (Printf.sprintf "Cyclic clock declarations in node %s" n.pn_name,
                        n.pn_loc)) in

  (* elab instructions *)
  let env' = List.map (fun (id, ck) -> (id, sclock_of_clock ck)) env in
  let bck' = elab_block nodes (EnvBase (Env.of_seq (List.to_seq env'))) n.pn_body in

  { pn_name = n.pn_name;
    pn_input = (List.map (fun (id, (ty, _)) -> (id, (ty, List.assoc id env))) n.pn_input);
    pn_output = (List.map (fun (id, (ty, _)) -> (id, (ty, List.assoc id env))) n.pn_output);
    pn_body = bck';
    pn_loc = n.pn_loc }

(** Check the clocks for the file [f] *)
let elab_file (f : p_file) : CPMinils.p_file =
  let nodes =
    List.rev
      (List.map snd
         (List.fold_left (fun (env : (ident * CPMinils.p_node) list) n ->
              (n.pn_name, (elab_node env n))::env) [] f.pf_nodes)) in
  { pf_nodes = nodes; pf_clocks = f.pf_clocks }
