(** Desugarizer from parsed AST to kernel AST *)

open Common
open PMinils
open Minils
open Clockchecker
open Clockchecker.CPMinils

module CMinils = MINILS(TypeClockAnnot)

(** Eliminate last expressions                                                 *)

let rec last_expr substs (e : k_expr) : k_expr =
  let desc =
    match e.kexpr_desc with
    | KE_const c -> KE_const c
    | KE_ident x -> KE_ident x
    | KE_unop (op, e1) ->
      KE_unop (op, last_expr substs e1)
    | KE_binop (op, e1, e2) ->
      KE_binop (op, last_expr substs e1, last_expr substs e2)
    | KE_fby (e0s, es, er) ->
      KE_fby (last_exprs substs e0s, last_exprs substs es, last_expr substs er)
    | KE_arrow (e0s, es, er) ->
      KE_arrow (last_exprs substs e0s, last_exprs substs es, last_expr substs er)
    | KE_match (e, brs) ->
      KE_match (last_expr substs e, last_branches substs brs)
    | KE_when (es, c, ckid) -> KE_when (last_exprs substs es, c, ckid)
    | KE_merge (x, brs) -> KE_merge (x, last_branches substs brs)
    | KE_app (id, es, er) ->
      KE_app (id, last_exprs substs es, last_expr substs er)
    | KE_last x -> KE_ident (List.assoc x substs)
  in { e with kexpr_desc = desc }
and last_exprs substs = List.map (last_expr substs)
and last_branches substs = List.map (fun (c, es) -> (c, last_exprs substs es))

let last_eq substs (eq : k_equation) : k_equation =
  { eq with keq_expr = last_exprs substs eq.keq_expr }

let rec last_instr substs (ins : p_instr) : p_instr =
  let desc =
    match ins.pinstr_desc with
    | Eq eq -> Eq (last_eq substs eq)
    | Block bck -> Block (last_block substs bck)
    | Reset (instrs, e) ->
      Reset (last_instrs substs instrs, last_expr substs e)
    | Switch (e, brs, ckid) ->
      Switch (last_expr substs e,
              List.map (fun (c, ins) -> (c, last_instrs substs ins)) brs,
              ckid)
    | Automaton (brs, ckid) ->
      let last_un (e, s, b) = (last_expr substs e, s, b) in
      Automaton (List.map
                   (fun (c, unt, ins, unl) ->
                      (c,
                       List.map last_un unt,
                       last_instrs substs ins,
                       List.map last_un unl)) brs,
                 ckid)
  in { ins with pinstr_desc = desc }
and last_instrs substs = List.map (last_instr substs)

and last_block substs bck =
  let nlocals = List.map (fun (x, a, c) ->
      (x, a, match c with
        | Some constr -> Some (Atom.fresh (x^"_"), constr)
        | None -> None)) bck.pb_local in
  let substs' = List.filter_map (fun (x, a, c) ->
      Option.map (fun (x', _) -> (x, x')) c) nlocals in
  let preinstrs = List.filter_map (fun (x, (ty, ck), c) ->
      Option.map (fun (x', c) ->
          let mk_expr desc =
            { kexpr_desc = desc; kexpr_annot = [(ty, (ck, None))]; kexpr_loc = dummy_loc } in
          { pinstr_desc =
              Eq { keq_patt = [x'];
                   keq_expr = [mk_expr (KE_fby ([mk_expr (KE_const c)],
                                                [mk_expr (KE_ident x)],
                                                mk_expr (KE_const (Cbool false))))];
                   keq_loc = dummy_loc };
            pinstr_loc = dummy_loc }
        ) c
    ) nlocals
  and instrs' = last_instrs (substs'@substs) bck.pb_instrs
  and nlocals = List.fold_left
      (fun acc (x, a, c) ->
         match c with
         | Some (x', c) ->
           (x', a, None)::(x, a, None)::acc
         | None -> (x, a, None)::acc
      ) [] nlocals in
  { bck with pb_local = nlocals; pb_instrs = preinstrs@instrs' }


let last_node (n : p_node) : p_node =
  { n with pn_body = last_block [] n.pn_body }

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
    | Block bck ->
      Block (alpha_conv_block id id' bck)
    | _ -> invalid_arg "alpha_conv_instr"
  in { ins with pinstr_desc = desc }

and alpha_conv_instrs id id' = List.map (alpha_conv_instr id id')

and alpha_conv_block id id' bck =
  { bck with pb_instrs = alpha_conv_instrs id id' bck.pb_instrs }

(** Eliminate automata                                                        *)

let rec auto_instr (ins : p_instr) : p_instr =
  let desc =
    match ins.pinstr_desc with
    | Eq eq -> Eq eq
    | Block bck -> Block (auto_block bck)
    | Reset (instrs, e) -> Reset (auto_instrs instrs, e)
    | Switch (e, brs, ckid) ->
      let brs' = List.map (fun (c, ins) -> (c, auto_instrs ins)) brs in
      Switch (e, brs', ckid)
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
      let brs' = List.map (fun (c, unl, ins, unt) -> (c, unl, auto_instrs ins, unt)) brs in

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
      Block { pb_local = (List.map (fun id -> (id, (Tclock ckid, ck), None)) [s;ns;pns])@
                         (List.map (fun id -> (id, (Tbool, ck), None)) [r;nr;pnr]);
              pb_instrs = [ pnseq; pnreq; strongswitch; weakswitch ];
              pb_loc = ins.pinstr_loc }

  in { ins with pinstr_desc = desc}

  and auto_instrs (ins : p_instr list) =
    List.map auto_instr ins

and auto_block (bck : p_block) =
  { bck with pb_instrs = auto_instrs bck.pb_instrs }

let auto_node (n : p_node) : p_node =
  { n with pn_body = auto_block n.pn_body }

let rec auto_file (f : p_file) : p_file =
  { f with pf_nodes = List.map auto_node f.pf_nodes }

(** Eliminate reset blocks                                                    *)

module Env = Map.Make(String)

type ctx = { cks : clockdec list;
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
    | Block bck -> Block (reset_block ctx res bck)
    | Switch (e, brs, ckid) ->
      let id = Option.get (fst ckid) in
      let ctx' = { ctx with ckenv = Env.add id (List.map fst brs) ctx.ckenv } in
      Switch (e, reset_branches ctx' res id brs, ckid)
    | Reset (instrs, er) ->
      let er' = match res with Some res -> reset_expr ctx res er | None -> er in
      let y = Atom.fresh "_" and (ty, (ckr, _)) = List.hd er'.kexpr_annot in
      let eqy = { keq_patt = [y]; keq_expr = [er']; keq_loc = er'.kexpr_loc } in
      let res' = or_resets_opt ctx res (Some { kexpr_desc = KE_ident y;
                                               kexpr_annot = [(Tbool, (ckr, None))];
                                               kexpr_loc = dummy_loc }) in
      let instrs' = reset_instrs ctx res' instrs in
      Block { pb_local = [(y, (ty, ckr), None)];
              pb_instrs = { pinstr_desc = (Eq eqy); pinstr_loc = er'.kexpr_loc }::instrs';
              pb_loc = ins.pinstr_loc; }
    | _ -> invalid_arg "reset_instr"
  in { ins with pinstr_desc = desc }
and reset_instrs ctx res = List.map (reset_instr ctx res)
and reset_branches ctx res ckid = List.map (fun (c, ins) -> (c, reset_instrs ctx (when_reset c ckid res) ins))
and reset_block ctx res bck = { bck with pb_instrs = reset_instrs ctx res bck.pb_instrs }

let idty = List.map (fun (id, (ty, _)) -> (id, ty))
(* let idty' = List.map (fun (id, (ty, _), _) -> (id, ty)) *)

let reset_node cks (n : p_node) : p_node =
  let ctx = { cks; ckenv = Env.empty } in
  let ctx = List.fold_left (fun ctx (id, ty) -> add_constrs_of_ty ctx id ty)
      ctx ((idty n.pn_input)@(idty n.pn_output))
  in { n with pn_body = reset_block ctx None n.pn_body }

let reset_file (f : p_file) : p_file =
  { f with pf_nodes = List.map (reset_node f.pf_clocks) f.pf_nodes }

(** Eliminate switch                                                          *)

let add_block locals ins (decls : (ident * ann * k_expr) list) =
  let eqs = List.map (fun (x, _, e) -> { keq_patt = [x]; keq_expr = [e]; keq_loc = dummy_loc }) decls in
  let inseqs = List.map (fun eq -> { pinstr_desc = Eq eq; pinstr_loc = dummy_loc }) eqs in
  Block { pb_local = locals@(List.map (fun (x, ann, _) -> (x, ann, None)) decls);
          pb_instrs = inseqs@ins;
          pb_loc = dummy_loc }

(** Generates the let-bindings necessary to project vars used and defined in a switch block.
    Does not add let-bindings for names defined by the instrs.
    Returns both the new let-binding instr, and a substitution for the vars defined inside *)
let switch_proj (vars : (ident * ann) list) (ck : clock) constr ckid defs (ins : p_instr list) =
  let nvars = List.map (fun (id, (ty, ck)) -> (id, (Atom.fresh (id^"_"), (ty, (Con (constr, ckid, ck))))))
      (List.filter (fun (id, (_, ck')) -> ck' = ck && not (List.mem id defs)) vars)
  and ndefs = List.map (fun (id, (ty, ck)) -> (id, (Atom.fresh (id^"_"), (ty, (Con (constr, ckid, ck))))))
      (List.filter (fun (id, (_, ck')) -> List.mem id defs) vars) in
  let ins' = List.fold_left (fun ins (id, (id', _)) -> alpha_conv_instrs id id' ins) ins (nvars@ndefs) in
  let ins' = add_block [] ins'
      (List.map (fun (id, (id', ((ty, ck) as ann))) ->
           (id', ann, { kexpr_desc = KE_when ([{ kexpr_desc = KE_ident id;
                                                 kexpr_annot = [(ty, (ck, Some id))];
                                                 kexpr_loc = dummy_loc }], constr, ckid);
                        kexpr_annot = [(ty, (Con (constr, ckid, ck), None))];
                        kexpr_loc = dummy_loc })) nvars) in
  { pinstr_desc = ins'; pinstr_loc = dummy_loc }, ndefs

let mk_merge ty ck ckid (cvars : (constr * ident) list) =
  { kexpr_desc = KE_merge (ckid,
                           List.map (fun (constr, id) ->
                               (constr, [{ kexpr_desc = KE_ident id;
                                           kexpr_annot = [(ty, (Con (constr, ckid, ck), Some id))];
                                           kexpr_loc = dummy_loc }])) cvars);
    kexpr_annot = [(ty, (ck, None))];
    kexpr_loc = dummy_loc }

let rec switch_instr vars (ins : p_instr) : p_instr =
  let desc =
    match ins.pinstr_desc with
    | Eq eq -> Eq eq
    | Block bck -> Block (switch_block vars bck)
    | Switch (e, brs, (ckid, defs)) ->
      let (ty, (ck, _)) = List.hd e.kexpr_annot in
      let ckid = Option.get ckid in
      let brs' = switch_branches vars brs in
      let brs' = List.map (fun (c, ins) -> (c, switch_proj vars ck c ckid defs ins)) brs' in
      let (_, (_, ndefs)) = List.hd brs' in
      let mergeeqs =
        List.map (fun (id, (_, (ty, _))) ->
            let cvars = List.map (fun (c, (_, ndefs)) -> (c, fst (List.assoc id ndefs))) brs' in
            { pinstr_desc = Eq { keq_patt = [id];
                                 keq_expr = [mk_merge ty ck ckid cvars];
                                 keq_loc = dummy_loc; };
              pinstr_loc = dummy_loc }
          ) ndefs
      and locals = List.concat (List.map (fun (_, (_, ndefs)) ->
          List.map (fun (_, (x, ann)) -> (x, ann, None)) ndefs) brs') in
      add_block locals (mergeeqs@(List.map (fun (_, (ins, _)) -> ins) brs')) [(ckid, (ty, ck), e)]
    | _ -> invalid_arg "switch_instr"
  in { ins with pinstr_desc = desc }
and switch_instrs vars = List.map (switch_instr vars)
and switch_branches vars = List.map (fun (c, ins) -> (c, switch_instrs vars ins))
and switch_block vars bck =
  { bck with pb_instrs = switch_instrs ((List.map (fun (x, ann, _) -> (x, ann)) bck.pb_local)@vars) bck.pb_instrs }

let switch_node (n : p_node) : p_node =
  { n with pn_body = switch_block (n.pn_input@n.pn_output) n.pn_body }

let switch_file (f : p_file) : p_file =
  { f with pf_nodes = List.map switch_node f.pf_nodes }

(** Eliminate let blocks                                                      *)

let rec block_instr (ins : p_instr) : (p_instr list * (ident * ann) list) =
  match ins.pinstr_desc with
  | Eq eq -> ([ins], [])
  | Block bck -> block_block bck
  | _ -> invalid_arg "let_instr"
and block_instrs (ins : p_instr list) =
  List.fold_left (fun (inss1, ys1) ins ->
      let (inss2, ys2) = block_instr ins in (inss1@inss2, ys1@ys2))
    ([], []) ins

and block_block (bck : p_block) =
  let instrs', ys = block_instrs bck.pb_instrs in
  let locals = List.map (fun (x, ann, _) -> (x, Atom.fresh (x^"_"), ann)) bck.pb_local in
  let instrs' = List.fold_left (fun ins (x, x', _) -> alpha_conv_instrs x x' ins) instrs' locals in
  instrs', (List.map (fun (_, x, ann) -> (x, ann)) locals)@ys

let block_node (n : p_node) : p_node =
  let (instrs, locals) = block_block n.pn_body in
  { n with pn_body = { pb_local = List.map (fun (x, a) -> (x, a, None)) locals;
                       pb_instrs = instrs;
                       pb_loc = dummy_loc }}

let block_file (f : p_file) : p_file =
  { f with pf_nodes = List.map block_node f.pf_nodes }

(** Transcription                                                             *)

let tr_instr (ins : p_instr) : k_equation =
  match ins.pinstr_desc with
  | Eq eq -> eq
  | _ -> invalid_arg "tr_instr"

let tr_node (n : p_node) : k_node =
  { kn_name = n.pn_name;
    kn_input = n.pn_input;
    kn_output = n.pn_output;
    kn_local = List.map (fun (x, a, _) -> (x, a)) n.pn_body.pb_local;
    kn_equs = List.map tr_instr n.pn_body.pb_instrs;
    kn_loc = n.pn_loc }

let tr_file (f : p_file) : k_file =
  { kf_clocks = f.pf_clocks;
    kf_nodes = List.map tr_node f.pf_nodes }

(** Conclusion                                                                *)

let kernelize_file (step : step) (f : p_file) : k_file =
  let pass_and_print pass step' f =
    let f' = pass f in
    if step' = step
    then (CPMinils.print_file Format.std_formatter f'; exit 0)
    else f'
  in f
     |> pass_and_print last_file Last
     |> pass_and_print auto_file Automaton
     |> pass_and_print reset_file Reset
     |> pass_and_print switch_file Switch
     |> pass_and_print block_file Block
     |> tr_file
