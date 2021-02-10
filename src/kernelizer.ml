(** Desugarizer from parsed AST to kernel AST *)

open Asttypes
open PMinils
open Minils
open Clockchecker
open Clockchecker.CPMinils

module CMinils = MINILS(TypeClockAnnot)

(** Eliminate last expressions                                                 *)

let rec last_expr id id' (e : k_expr) : k_expr =
  let desc =
    match e.kexpr_desc with
    | KE_const c -> KE_const c
    | KE_ident x -> KE_ident x
    | KE_unop (op, e1) ->
      KE_unop (op, last_expr id id' e1)
    | KE_binop (op, e1, e2) ->
      KE_binop (op, last_expr id id' e1, last_expr id id' e2)
    | KE_fby (e0s, es, er) ->
      KE_fby (last_exprs id id' e0s, last_exprs id id' es, last_expr id id' er)
    | KE_arrow (e0s, es, er) ->
      KE_arrow (last_exprs id id' e0s, last_exprs id id' es, last_expr id id' er)
    | KE_match (e, brs) ->
      KE_match (last_expr id id' e, last_branches id id' brs)
    | KE_when (es, c, ckid) -> KE_when (last_exprs id id' es, c, ckid)
    | KE_merge (x, brs) -> KE_merge (x, last_branches id id' brs)
    | KE_app (id, es, er) ->
      KE_app (id, last_exprs id id' es, last_expr id id' er)
    | KE_last x when x = id -> KE_ident id'
    | KE_last x -> KE_last x
  in { e with kexpr_desc = desc }
and last_exprs id id' = List.map (last_expr id id')
and last_branches id id' = List.map (fun (c, es) -> (c, last_exprs id id' es))

let last_eq id id' (eq : k_equation) : k_equation =
  { eq with keq_expr = last_exprs id id' eq.keq_expr }

let rec last_instr id id' (ins : p_instr) : p_instr =
  let desc =
    match ins.pinstr_desc with
    | Eq eq -> Eq (last_eq id id' eq)
    | Let (x, a, e, instrs) ->
      Let (x, a, last_expr id id' e, last_instrs id id' instrs)
    | Reset (instrs, e) ->
      Reset (last_instrs id id' instrs, last_expr id id' e)
    | Switch (e, brs, ckid) ->
      Switch (last_expr id id' e,
              List.map (fun (c, ins) -> (c, last_instrs id id' ins)) brs,
              ckid)
    | Automaton (brs, ckid) ->
      let last_un (e, s, b) = (last_expr id id' e, s, b) in
      Automaton (List.map
                   (fun (c, unt, ins, unl) ->
                      (c,
                       List.map last_un unt,
                       last_instrs id id' ins,
                       List.map last_un unl)) brs,
                 ckid)
  in { ins with pinstr_desc = desc }
and last_instrs id id' = List.map (last_instr id id')

let last_node (n : p_node) : p_node =
  let nlocals = List.map (fun (x, a, c) ->
      (x, a,
       match c with
       | Some constr -> Some (Atom.fresh (x^"_"), constr)
       | None -> None)) n.pn_local in
  let instrs = List.fold_left
      (fun instrs (x, (ty, ck), c) ->
         match c with
         | Some (x', c) ->
           let mk_expr desc =
             { kexpr_desc = desc; kexpr_annot = [(ty, (ck, None))]; kexpr_loc = dummy_loc } in
           let eq_fby =
             { pinstr_desc =
                 Eq { keq_patt = [x'];
                      keq_expr = [mk_expr (KE_fby ([mk_expr (KE_const c)],
                                                   [mk_expr (KE_ident x)],
                                                   mk_expr (KE_const (Cbool false))))];
                      keq_loc = dummy_loc };
               pinstr_loc = dummy_loc } in
           eq_fby::(last_instrs x x' instrs)
         | None -> instrs)
      n.pn_instrs nlocals
  and nlocals = List.fold_left
      (fun acc (x, a, c) ->
         match c with
         | Some (x', c) ->
           (x', a, None)::(x, a, None)::acc
         | None -> (x, a, None)::acc
      ) [] nlocals in
  { n with pn_local = List.rev nlocals;
           pn_instrs = instrs }

let last_file (f : p_file) : p_file =
  { f with pf_nodes = List.map last_node f.pf_nodes }

(** alpha-conversion, needed for automaton, switch and let compilation         *)

let alpha_conv id id' x =
  if x = id then id' else x

let rec alpha_conv_ck id id' = function
  | Cbase -> Cbase
  | Con (constr, ckid, ck) ->
    Con (constr, alpha_conv id id' ckid, alpha_conv_ck id id' ck)

let alpha_conv_annot id id' (ty, ck) =
  (ty, alpha_conv_ck id id' ck)

let alpha_conv_nannot id id' (ty, (ck, name)) =
  (ty, (alpha_conv_ck id id' ck,
        match name with
        | None -> None
        | Some x -> Some (alpha_conv id id' x)))

let rec alpha_conv_expr id id' e =
  let desc =
    match e.kexpr_desc with
    | KE_const c -> KE_const c
    | KE_ident x -> KE_ident (alpha_conv id id' x)
    | KE_unop (op, e1) ->
      KE_unop (op, alpha_conv_expr id id' e1)
    | KE_binop (op, e1, e2) ->
      KE_binop (op, alpha_conv_expr id id' e1, alpha_conv_expr id id' e2)
    | KE_fby (e0s, es, er) ->
      KE_fby (alpha_conv_exprs id id' e0s, alpha_conv_exprs id id' es,
              alpha_conv_expr id id' er)
    | KE_arrow (e0s, es, er) ->
      KE_arrow (alpha_conv_exprs id id' e0s, alpha_conv_exprs id id' es,
                alpha_conv_expr id id' er)
    | KE_match (e, brs) ->
      KE_match (alpha_conv_expr id id' e, alpha_conv_branches id id' brs)
    | KE_when (es, constr, x) ->
      KE_when (alpha_conv_exprs id id' es, constr, alpha_conv id id' x)
    | KE_merge (x, brs) ->
      KE_merge (alpha_conv id id' x, alpha_conv_branches id id' brs)
    | KE_app (f, es, er) ->
      KE_app (f, alpha_conv_exprs id id' es, alpha_conv_expr id id' er)
    | KE_last _ -> invalid_arg "alpha_conv_expr"
  in { e with kexpr_desc = desc;
              kexpr_annot = List.map (alpha_conv_nannot id id') e.kexpr_annot }
and alpha_conv_exprs id id' =
  List.map (alpha_conv_expr id id')
and alpha_conv_branches id id' =
  List.map (fun (c, es) -> (c, alpha_conv_exprs id id' es))

let alpha_conv_eq id id' eq =
  { eq with keq_patt = List.map (alpha_conv id id') eq.keq_patt;
            keq_expr = alpha_conv_exprs id id' eq.keq_expr }

let rec alpha_conv_instr id id' ins =
  let desc =
    match ins.pinstr_desc with
    | Eq eq -> Eq (alpha_conv_eq id id' eq)
    | Let (x, ann, e, instrs) ->
      Let (alpha_conv id id' x, alpha_conv_annot id id' ann,
           alpha_conv_expr id id' e, alpha_conv_instrs id id' instrs)
    | _ -> invalid_arg "alpha_conv_instr"
  in { ins with pinstr_desc = desc }
and alpha_conv_instrs id id' = List.map (alpha_conv_instr id id')

(** Eliminate automata                                                        *)

let rec auto_instr (ins : p_instr) =
  match ins.pinstr_desc with
  | Eq _ -> [ins], []
  | Let (id, ann, e, instrs) ->
    let (instrs', ys) = auto_instrs instrs in
    [{ ins with pinstr_desc = Let (id, ann, e, instrs') }], ys
  | Reset (instrs, e) ->
    let (instrs', ys) = auto_instrs instrs in
    [{ ins with pinstr_desc = Reset (instrs', e) }], ys
  | Switch (e, brs, ckid) ->
    let brsys' = List.map (fun (c, ins) ->
        let (ins', ys) = auto_instrs ins in ((c, ins'), ys)) brs in
    [{ ins with pinstr_desc = Switch (e, List.map fst brsys', ckid) }],
    List.concat (List.map snd brsys')
  | Automaton (brs, (ckid, ck, defs)) ->
    let (ckid, ck) = match (ckid, ck) with
      | (Some ckid, Some ck) -> (ckid, ck)
      | _ -> failwith "Should not happen" in

    let mk_expr annot desc =
      { kexpr_desc = desc; kexpr_annot = annot; kexpr_loc = dummy_loc }
    in
    let mk_ckexpr ck = mk_expr [(Tclock ckid, (ck, None))]
    and mk_bexpr ck = mk_expr [(Tbool, (ck, None))]
    and mk_2expr ck = mk_expr [(Tclock ckid, (ck, None)); (Tbool, (ck, None))] in

    let rec generate_un_if ck (l : (k_expr * constr * bool) list) (default : (constr * k_expr)) =
      match l with
      | [] -> let (s, r) = default in
        [mk_ckexpr ck (KE_const (Cconstr (s, ckid))); r]
      | (cond, s, r)::tl ->
        let elses = generate_un_if ck tl default in
        [mk_2expr ck (KE_match (cond, [("False", elses);
                                       ("True", [mk_ckexpr ck (KE_const (Cconstr (s, ckid)));
                                                 mk_bexpr ck (KE_const (Cbool r))])]))]
    in

    (* Recursive call *)
    let brsys' = List.map (fun (c, unl, ins, unt) ->
        let (ins', ys) = auto_instrs ins in ((c, unl, ins', unt), ys)) brs in
    let brs' = List.map fst brsys' and ys' = List.concat (List.map snd brsys') in

    (* Initial state *)
    let (fconstr, _, _, _) = List.hd brs in

    (* Necessary idents *)
    let ckid2 = Atom.fresh "_saut" in
    let s = Atom.fresh "_s" and r = Atom.fresh "_r"
    and ns = Atom.fresh "_ns" and nr = Atom.fresh "_nr"
    and pns = Atom.fresh "_pns" and pnr = Atom.fresh "_pnr" in

    (* Delay equations *)
    let pnseq = { pinstr_desc =
                    Eq { keq_patt = [pns];
                         keq_expr = [mk_ckexpr ck
                                       (KE_fby
                                          ([mk_ckexpr ck (KE_const (Cconstr (fconstr, ckid)))],
                                           [mk_ckexpr ck (KE_ident ns)],
                                           mk_bexpr ck (KE_const (Cbool false))))];
                         keq_loc = dummy_loc };
                  pinstr_loc = dummy_loc }
    and pnreq = { pinstr_desc =
                    Eq { keq_patt = [pnr];
                         keq_expr = [mk_bexpr ck
                                       (KE_fby
                                          ([mk_bexpr ck (KE_const (Cbool false))],
                                           [mk_bexpr ck (KE_ident nr)],
                                           mk_bexpr ck (KE_const (Cbool false))))];
                       keq_loc = dummy_loc };
                  pinstr_loc = dummy_loc } in

    (* strong transitions *)
    let hasstrongtrans = [] <> List.concat (List.map (fun (_, unl, _, _) -> unl) brs) in
    let strongswitch =
      if not hasstrongtrans then
        { pinstr_desc = Eq { keq_patt = [s; r];
                             keq_expr = [ mk_ckexpr ck (KE_ident pns);
                                          mk_bexpr ck (KE_ident pnr) ];
                             keq_loc = dummy_loc };
          pinstr_loc = dummy_loc }
      else
        let strongbranches = List.map (fun (c, unl, _, _) ->
            let ck' = Con (c, ckid2, ck) in
            let sr_eq =
              { pinstr_desc =
                  Eq { keq_patt = [s; r];
                       keq_expr = generate_un_if ck'
                           (List.map (fun (e, c, b) -> (alpha_conv_expr ckid ckid2 e, c, b)) unl)
                           (c, mk_bexpr ck' (KE_ident pnr));
                       keq_loc = dummy_loc };
                pinstr_loc = dummy_loc } in
            (c,
             [{ pinstr_desc = Reset ([sr_eq], mk_bexpr ck' (KE_ident pnr));
                pinstr_loc = dummy_loc }])) brs' in
        { pinstr_desc = Switch (mk_ckexpr ck (KE_ident pns),
                                strongbranches,
                                (Some ckid2, [s;r]));
          pinstr_loc = dummy_loc } in

    (* weak transitions and content *)
    let weakbranches = List.map (fun (c, _, ins, unt) ->
        let ck' = Con (c, ckid, ck) in
        let nsnr_eq =
          { pinstr_desc =
              Eq { keq_patt = [ns; nr];
                   keq_expr = generate_un_if ck' unt (c, mk_bexpr ck' (KE_const (Cbool false)));
                   keq_loc = dummy_loc };
            pinstr_loc = dummy_loc } in
        (c,
         [{ pinstr_desc = Reset (nsnr_eq::ins, mk_bexpr ck' (KE_ident r));
            pinstr_loc = dummy_loc }])) brs' in
    let weakswitch = { pinstr_desc = Switch (mk_ckexpr ck (KE_ident s),
                                             weakbranches,
                                             (Some ckid, ns::nr::defs));
                       pinstr_loc = dummy_loc } in
    [ pnseq; pnreq; strongswitch; weakswitch ],
    (List.map (fun id -> (id, (Tclock ckid, ck))) [s;ns;pns])@
    (List.map (fun id -> (id, (Tbool, ck))) [r;nr;pnr])@ys'
and auto_instrs (ins : p_instr list) =
  List.fold_left (fun (inss1, ys1) ins ->
      let (inss2, ys2) = auto_instr ins in (inss1@inss2, ys1@ys2))
    ([], []) ins

let auto_node (n : p_node) : p_node =
  let (instrs, ys) = auto_instrs n.pn_instrs in
  { n with pn_instrs = instrs; pn_local = n.pn_local@(List.map (fun (x, a) -> (x, a, None)) ys) }

let rec auto_file (f : p_file) : p_file =
  { f with pf_nodes = List.map auto_node f.pf_nodes }

(** Eliminate reset blocks                                                    *)

module Env = Map.Make(String)

type ctx = { cks : Asttypes.clockdec list;
             ckenv : (ident list) Env.t }

let add_constrs_of_ty ctx id ty =
  match ty with
  | Tbool -> { ctx with ckenv = Env.add id [cfalse;ctrue] ctx.ckenv }
  | Tclock ckid -> { ctx with ckenv = Env.add id (List.assoc ckid ctx.cks) ctx.ckenv }
  | ty -> ctx

let rec add_whens ty ck e : CPMinils.k_expr =
  match ck with
  | Cbase -> e
  | Con (constr, ckid, ck) ->
    let e = add_whens ty ck e in
    { kexpr_desc = KE_when ([e], constr, ckid);
      kexpr_annot = [(ty, (Con (constr, ckid, ck), None))];
      kexpr_loc = dummy_loc }

let rec merge_reset_to_base (ctx : ctx) (e : k_expr) : k_expr =
  let (ty, (ck, _)) = List.hd e.kexpr_annot in
  let rec aux e = function
    | Cbase -> e
    | Con (cstr, ckid, ck') ->
      let constrs = Env.find ckid ctx.ckenv in
      let brs = List.map
          (fun c ->
             if c = cstr then (c, [e])
             else (c,
                   [add_whens Tbool (Con (c, ckid, ck'))
                      { kexpr_desc = KE_const (Cbool false);
                        kexpr_annot = [(Tbool, (Cbase, None))];
                        kexpr_loc = dummy_loc }])) constrs in
      let e' = { kexpr_desc = KE_merge (ckid, brs);
                 kexpr_annot = [(Tbool, (ck', None))];
                 kexpr_loc = dummy_loc }
      in aux e' ck'
  in aux e ck

let or_resets ctx e1 e2 =
  { kexpr_desc = KE_binop (Op_or, merge_reset_to_base ctx e1, merge_reset_to_base ctx e2);
    kexpr_annot = [(Tbool, (Cbase, None))];
    kexpr_loc = dummy_loc }

let or_resets_opt (ctx : ctx) e1 e2 =
  match e1, e2 with
  | None, e | e, None -> e
  | Some e1, Some e2 -> Some (or_resets ctx e1 e2)

let when_reset constr ckid = function
  | None -> None
  | Some ({ kexpr_annot = [(Tbool, (ck, None))] } as e) ->
    Some { e with kexpr_annot = [(Tbool, (Con (constr, ckid, ck), None))]}
  | _ -> invalid_arg "when_reset"

let rec reset_expr ctx res (e : k_expr) =
  let reset_expr = reset_expr ctx res
  and reset_exprs = reset_exprs ctx res
  and reset_branches = reset_branches ctx res in
  let desc = match e.kexpr_desc with
    | KE_const c -> KE_const c
    | KE_ident id -> KE_ident id
    | KE_unop (op, e1) -> KE_unop (op, reset_expr e1)
    | KE_binop (op, e1, e2) -> KE_binop (op, reset_expr e1, reset_expr e2)
    | KE_match (e, es) ->
      KE_match (reset_expr e, reset_branches es)
    | KE_when (e, constr, ckid) -> KE_when (reset_exprs e, constr, ckid)
    | KE_merge (ckid, es) ->
      KE_merge (ckid, reset_branches es)
    | KE_fby (e0, e1, er) ->
      let e0' = reset_exprs e0 and e1' = reset_exprs e1
      and er' = reset_expr er in
      let er'' = or_resets ctx er' res in
      KE_fby (e0', e1', er'')
    | KE_arrow (e0, e1, er) ->
      let e0' = reset_exprs e0 and e1' = reset_exprs e1
      and er' = reset_expr er in
      let er'' = or_resets ctx er' res in
      KE_arrow (e0', e1', er'')
    | KE_app (f, es, er) ->
      let es' = reset_exprs es and er' = reset_expr er in
      let er'' = or_resets ctx er' res in
      KE_app (f, es', er'')
    | KE_last _ -> invalid_arg "reset_expr"
  in { e with kexpr_desc = desc }
and reset_exprs ctx res es = List.map (reset_expr ctx res) es
and reset_branches ctx res brs =
  List.map (fun (constr, es) -> (constr, reset_exprs ctx res es)) brs

let reset_eq ctx res (eq : k_equation) : k_equation =
  { eq with keq_expr = reset_exprs ctx res eq.keq_expr }

let rec reset_instr ctx res (ins : p_instr) : p_instr =
  let desc =
    match ins.pinstr_desc with
    | Eq eq -> Eq (match res with Some res -> reset_eq ctx res eq | None -> eq)
    | Let (id, ann, e, instrs) ->
      let ctx' = add_constrs_of_ty ctx id (fst ann) in
      let e' = match res with Some res -> reset_expr ctx res e | None -> e in
      Let (id, ann, e', reset_instrs ctx' res instrs)
    | Switch (e, brs, ckid) ->
      let id = Option.get (fst ckid) in
      let ctx' = { ctx with ckenv = Env.add id (List.map fst brs) ctx.ckenv } in
      Switch (e, reset_branches ctx' res id brs, ckid)
    | Reset (instrs, er) ->
      let y = Atom.fresh "_" and (ty, (ckr, _)) = List.hd er.kexpr_annot in
      let res' = or_resets_opt ctx res (Some { kexpr_desc = KE_ident y;
                                               kexpr_annot = [(Tbool, (ckr, None))];
                                               kexpr_loc = dummy_loc }) in
      let instrs' = reset_instrs ctx res' instrs in
      Let (y, (ty, ckr), er, instrs')
    | _ -> invalid_arg "reset_instr"
  in { ins with pinstr_desc = desc }
and reset_instrs ctx res = List.map (reset_instr ctx res)
and reset_branches ctx res ckid = List.map (fun (c, ins) -> (c, reset_instrs ctx (when_reset c ckid res) ins))

let idty = List.map (fun (id, (ty, _)) -> (id, ty))
let idty' = List.map (fun (id, (ty, _), _) -> (id, ty))

let reset_node cks (n : p_node) : p_node =
  let ctx = { cks; ckenv = Env.empty } in
  let ctx = List.fold_left (fun ctx (id, ty) -> add_constrs_of_ty ctx id ty)
      ctx ((idty n.pn_input)@(idty n.pn_output)@(idty' n.pn_local))
  in { n with pn_instrs = reset_instrs ctx None n.pn_instrs }

let reset_file (f : p_file) : p_file =
  { f with pf_nodes = List.map (reset_node f.pf_clocks) f.pf_nodes }

(** Eliminate switch                                                          *)

let rec add_lets ins (lets : (ident * ann * k_expr) list) =
  match lets with
  | [] -> ins
  | (id, ann, e)::tl ->
    let ins' = [{ pinstr_desc = Let (id, ann, e, ins);
                  pinstr_loc = dummy_loc }] in
    add_lets ins' tl

(** Generates the let-bindings necessary to project vars used and defined in a switch block.
    Does not add let-bindings for names defined by the instrs.
    Returns both the new let-binding instr, and a substitution for the vars defined inside *)
let switch_proj (vars : (ident * ann) list) (ck : clock) constr ckid defs (ins : p_instr list) =
  let nvars = List.map (fun (id, ann) -> (id, (Atom.fresh (id^"_"), ann)))
      (List.filter (fun (id, (_, ck')) -> ck' = ck && not (List.mem id defs)) vars)
  and ndefs = List.map (fun (id, (ty, ck)) -> (id, (Atom.fresh (id^"_"), (ty, (Con (constr, ckid, ck))))))
      (List.filter (fun (id, (_, ck')) -> List.mem id defs) vars) in
  let ins' = List.fold_left (fun ins (id, (id', _)) -> alpha_conv_instrs id id' ins) ins (nvars@ndefs) in
  let ins' = add_lets ins'
      (List.map (fun (id, (id', ((ty, ck) as ann))) ->
           (id', ann, { kexpr_desc = KE_when ([{ kexpr_desc = KE_ident id;
                                                 kexpr_annot = [(ty, (ck, Some id))];
                                                 kexpr_loc = dummy_loc }], constr, ckid);
                        kexpr_annot = [(ty, (Con (constr, ckid, ck), None))];
                        kexpr_loc = dummy_loc })) nvars) in
  ins', ndefs

let mk_merge ty ck ckid (cvars : (constr * ident) list) =
  { kexpr_desc = KE_merge (ckid,
                           List.map (fun (constr, id) ->
                               (constr, [{ kexpr_desc = KE_ident id;
                                           kexpr_annot = [(ty, (Con (constr, ckid, ck), Some id))];
                                           kexpr_loc = dummy_loc }])) cvars);
    kexpr_annot = [(ty, (ck, None))];
    kexpr_loc = dummy_loc }

let rec switch_instr vars (ins : p_instr) : (p_instr list * (ident * ann) list) =
  match ins.pinstr_desc with
  | Eq eq -> [ins], []
  | Let (id, ann, e, instrs) ->
    let (instrs', ys) = switch_instrs ((id, ann)::vars) instrs in
    [{ ins with pinstr_desc = Let (id, ann, e, instrs')}], ys
  | Switch (e, brs, (ckid, defs)) ->
    let (ty, (ck, _)) = List.hd e.kexpr_annot in
    let ckid = Option.get ckid in
    let (brs', ys) = switch_branches vars ckid brs in
    let brs' = List.map (fun (c, ins) -> (c, switch_proj (vars@ys) ck c ckid defs ins)) brs' in
    let (_, (_, ndefs)) = List.hd brs' in
    let mergeeqs =
      List.map (fun (id, _) ->
          let cvars = List.map (fun (c, (_, ndefs)) -> (c, fst (List.assoc id ndefs))) brs' in
          { pinstr_desc = Eq { keq_patt = [id];
                               keq_expr = [mk_merge ty ck ckid cvars];
                               keq_loc = dummy_loc; };
            pinstr_loc = dummy_loc }
        ) ndefs in
    { pinstr_desc = Eq { keq_patt = [ckid];
                         keq_expr = [e];
                         keq_loc = dummy_loc };
      pinstr_loc = dummy_loc }::mergeeqs@(List.concat (List.map (fun (_, (ins, _)) -> ins) brs')),
    (ckid, (ty, ck))::ys@(List.map snd (List.concat (List.map (fun (_, (_, ndefs)) -> ndefs) brs')))
  | _ -> invalid_arg "switch_instr"
and switch_instrs vars ins =
  let (ins, ys) =
    List.fold_left (fun (inss1, ys1) ins ->
        let (ins', ys2) = switch_instr vars ins in (ins'::inss1, ys1@ys2))
      ([], []) ins in List.concat (List.rev ins), ys
and switch_branches vars ckid brs =
  let (brs, ys) =
    List.fold_left (fun (brss1, ys1) (c, ins) ->
        let (ins', ys2) = switch_instrs vars ins
        in ((c, ins')::brss1, ys1@ys2))
      ([], []) brs in List.rev brs, ys


let switch_node (n : p_node) : p_node =
  let (ins, names) =
    switch_instrs (n.pn_input@n.pn_output@
                   (List.map (fun (x, a, _) -> (x, a)) n.pn_local))
      n.pn_instrs in
  { n with pn_instrs = ins; pn_local = n.pn_local@(List.map (fun (x, a) -> (x, a, None)) names) }

let switch_file (f : p_file) : p_file =
  { f with pf_nodes = List.map switch_node f.pf_nodes }

(** Eliminate let blocks                                                      *)

(** check if ident appears in expr, eq, instr *)
let rec free_in_expr id e =
  match e.kexpr_desc with
  | KE_const _ -> false
  | KE_ident x -> id = x
  | KE_unop (_, e1) -> free_in_expr id e1
  | KE_binop (_, e1, e2) -> free_in_expr id e1 || free_in_expr id e2
  | KE_fby (e0s, es, er) -> free_in_exprs id e0s || free_in_exprs id es || free_in_expr id er
  | KE_arrow (e0s, es, er) -> free_in_exprs id e0s || free_in_exprs id es || free_in_expr id er
  | KE_match (e, brs) -> free_in_expr id e || free_in_branches id brs
  | KE_when (es, _, x) -> free_in_exprs id es || id = x
  | KE_merge (x, brs) -> id = x || free_in_branches id brs
  | KE_app (_, es, er) -> free_in_exprs id es || free_in_expr id er
  | KE_last x -> id = x
and free_in_exprs id = List.exists (free_in_expr id)
and free_in_branches id = List.exists (fun (_, es) -> free_in_exprs id es)

let free_in_eq id eq =
  free_in_exprs id eq.keq_expr

let rec free_in_instr id ins =
  match ins.pinstr_desc with
  | Eq eq -> free_in_eq id eq
  | _ -> invalid_arg "free_in_instr"
and free_in_instrs id =
  List.exists (free_in_instr id)

let rec let_instr (ins : p_instr) : (p_instr list * (ident * ann) list) =
  match ins.pinstr_desc with
  | Eq eq -> ([ins], [])
  | Let (id, ann, e, instrs) ->
    let (instrs', ys) = let_instrs instrs in
    if free_in_instrs id instrs' then
      let id' = Atom.fresh (id^"_") in
      ({ pinstr_desc = Eq { keq_patt = [id'];
                            keq_expr = [alpha_conv_expr id id' e];
                            keq_loc = dummy_loc };
         pinstr_loc = dummy_loc}::List.map (alpha_conv_instr id id') instrs',
       (id', ann)::ys)
    else (instrs', ys)
  | _ -> invalid_arg "let_instr"
and let_instrs (ins : p_instr list) =
  List.fold_left (fun (inss1, ys1) ins ->
      let (inss2, ys2) = let_instr ins in (inss1@inss2, ys1@ys2))
    ([], []) ins

let let_node (n : p_node) : p_node =
  let (instrs', names) = let_instrs n.pn_instrs in
  { n with pn_instrs = instrs';
           pn_local = n.pn_local@(List.map (fun (x, a) -> (x, a, None)) names) }

let let_file (f : p_file) : p_file =
  { f with pf_nodes = List.map let_node f.pf_nodes }

(** Transcription                                                             *)

let tr_instr (ins : p_instr) : k_equation =
  match ins.pinstr_desc with
  | Eq eq -> eq
  | _ -> invalid_arg "tr_instr"

let tr_node (n : p_node) : k_node =
  { kn_name = n.pn_name;
    kn_input = n.pn_input;
    kn_output = n.pn_output;
    kn_local = List.map (fun (x, a, _) -> (x, a)) n.pn_local;
    kn_equs = List.map tr_instr n.pn_instrs;
    kn_loc = n.pn_loc }

let tr_file (f : p_file) : k_file =
  { kf_clocks = f.pf_clocks;
    kf_nodes = List.map tr_node f.pf_nodes }

(** Conclusion                                                                *)

let kernelize_file (f : p_file) : k_file =
  f |> last_file |> auto_file |> reset_file |> switch_file |> let_file |> tr_file
