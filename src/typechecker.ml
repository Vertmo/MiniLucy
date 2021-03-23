(** Basic typechecking, doesn't take clocks or causality into account *)

open Common
open Minils
open PMinils

module TypeAnnot : (Annotations with type t = ty) = struct
  type t = ty
  let print_t = print_ty
end

module TPMinils = PMINILS(TypeAnnot)

open TPMinils
open PMinils

(** Sort fields                                                                *)

let rec sort_expr (e : k_expr) : k_expr =
  let desc = match e.kexpr_desc with
    | KE_const c -> KE_const c
    | KE_ident id -> KE_ident id
    | KE_unop (op, e1) -> KE_unop (op, sort_expr e1)
    | KE_binop (op, e1, e2) -> KE_binop (op, sort_expr e1, sort_expr e2)
    | KE_fby (e0, e, er) -> KE_fby (sort_exprs e0, sort_exprs e, sort_expr er)
    | KE_arrow (e0, e, er) -> KE_arrow (sort_exprs e0, sort_exprs e, sort_expr er)
    (* | KE_pre e -> KE_fby (Cnil, sort_expr e) *)
    | KE_when (e, constr, clid) -> KE_when (sort_exprs e, constr, clid)
    | KE_match (e, es) ->
      KE_match (sort_expr e,
                List.sort (fun (c1, e1) (c2, e2) -> String.compare c1 c2)
                  (List.map (fun (c, e) -> (c, sort_exprs e)) es))
    | KE_merge (id, es) ->
      KE_merge (id,
                List.sort (fun (c1, e1) (c2, e2) -> String.compare c1 c2)
                  (List.map (fun (c, e) -> (c, sort_exprs e)) es))
    | KE_app (id, es, e) ->
      KE_app (id, List.map sort_expr es, sort_expr e)
    | KE_last id -> KE_last id
  in { e with kexpr_desc = desc }

and sort_exprs es = List.map sort_expr es

let sort_equation (eq : k_equation) : k_equation =
  { eq with keq_expr = sort_exprs eq.keq_expr; }

let rec sort_instr (ins : p_instr) : p_instr =
  let desc =
    match ins.pinstr_desc with
    | Eq eq -> Eq (sort_equation eq)
    | Block bck -> Block (sort_block bck)
    | Reset (ins, er) ->
      Reset (sort_instrs ins, sort_expr er)
    | Switch (e, branches, ckid) ->
      Switch (sort_expr e,
              List.sort (fun (c1, _) (c2, _) -> String.compare c1 c2)
                (List.map (fun (c, ins) -> (c, sort_instrs ins)) branches),
             ckid)
    | Automaton (branches, ckid) ->
      Automaton ((List.map
                    (fun (c, unl, ins, unt) ->
                       let sort_un (e, c, b) = (sort_expr e, c, b) in
                       (c,
                        List.map sort_un unl,
                        sort_instrs ins,
                        List.map sort_un unt))
                    branches),
                 ckid)
  in { ins with pinstr_desc = desc }
and sort_instrs ins = List.map sort_instr ins
and sort_block bck = { bck with pb_instrs = sort_instrs bck.pb_instrs }

let sort_node (n : p_node) : p_node =
  { n with pn_body = sort_block n.pn_body }

let sort_file (f : p_file) : p_file =
    { pf_clocks =
        (List.map
           (fun (c, constrs) -> (c, List.sort String.compare constrs))
           f.pf_clocks);
      pf_nodes = List.map sort_node f.pf_nodes }

(** Elaboration                                                               *)

exception TypeError of (string * location)
exception UnexpectedEquationError of (ident * location)

let unary_type_error tys loc =
  TypeError
    (Printf.sprintf "Expression should have a unary type, found %s"
       (string_of_tys tys), loc)

let get_unary_type tys loc =
  match tys with
  | [ty] -> ty
  | _ -> raise (unary_type_error tys loc)

let constructors_error expected got loc =
  TypeError
    (Printf.sprintf "Incorrect constructors in branches, expected [%s], found [%s]"
    (String.concat ";" expected) (String.concat ";" got), loc)

(** Typecheck constant. Can take a [hint] for the nil case *)
let type_const loc = function
  | Cbool _ -> Tbool
  | Cint _ -> Tint
  | Creal _ -> Treal
  | Cconstr (_, tyid) -> Tclock tyid

(** Get the constructions associated with a clock type *)
let constrs_of_clock clocks loc = function
  | Tbool -> [cfalse;ctrue]
  | Tclock clid ->
    (try List.assoc clid clocks
     with _ -> raise (TypeError
                        (Printf.sprintf "Clock %s not found in file" clid, loc)))
  | ty -> raise (TypeError
                   (Printf.sprintf
                      "Type %s is not supported as a clock"
                      (string_of_ty ty), loc))

(** Gives operator output type relating to input types *)
let type_op op (inputs : ty list) loc =
  match op with
  | Op_eq | Op_neq
    when inputs = [Tbool;Tbool] -> Tbool
  | Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge
    when inputs = [Tint;Tint] || inputs = [Treal;Treal] -> Tbool
  | Op_sub when inputs = [Tint] -> Tint
  | Op_add | Op_sub | Op_mul | Op_div | Op_mod
    when inputs = [Tint;Tint] -> Tint
  | Op_sub when inputs = [Treal] -> Treal
  | Op_add | Op_sub | Op_mul | Op_div
    when inputs = [Treal;Treal] -> Treal
  | Op_not when inputs = [Tbool] -> Tbool
  | Op_and | Op_or | Op_xor when inputs = [Tbool;Tbool] -> Tbool
  | Op_not when inputs = [Tint] -> Tint
  | Op_and | Op_or | Op_xor when inputs = [Tint;Tint] -> Tint
  | _ -> raise (TypeError
                  (Printf.sprintf "Wrong input types (%s) for operator %s"
                     (String.concat "," (List.map string_of_ty inputs))
                     (string_of_op op), loc))

let types_of es =
  List.concat (List.map (fun (e : TPMinils.k_expr) -> e.kexpr_annot) es)

(** Check that an expression has the [expected] type *)
let rec elab_expr (nodes : (ident * TPMinils.p_node) list) clocks
    vars e : TPMinils.k_expr =
  let loc = e.kexpr_loc in
  match e.kexpr_desc with
  | KE_const c ->
    { kexpr_desc = KE_const c;
      kexpr_annot = [type_const loc c];
      kexpr_loc = e.kexpr_loc }
  | KE_ident id ->
    let bty =
      (try (List.assoc id vars)
       with _ -> raise (TypeError
                          (Printf.sprintf "Stream %s not found in node"
                             id, e.kexpr_loc))) in
    { kexpr_desc = KE_ident id; kexpr_annot = [bty]; kexpr_loc = e.kexpr_loc }
  | KE_unop (op, e1) ->
    let e1' = elab_expr nodes clocks vars e1 in
    let ty = get_unary_type e1'.kexpr_annot e1.kexpr_loc in

    { kexpr_desc = KE_unop (op, e1');
      kexpr_annot = [type_op op [ty] loc];
      kexpr_loc = loc }
  | KE_binop (op, e1, e2) ->
    let e1' = elab_expr nodes clocks vars e1
    and e2' = elab_expr nodes clocks vars e2 in
    let ty1 = get_unary_type e1'.kexpr_annot e1.kexpr_loc
    and ty2 = get_unary_type e2'.kexpr_annot e2.kexpr_loc in

    { kexpr_desc = KE_binop (op, e1', e2');
      kexpr_annot = [type_op op [ty1;ty2] loc];
      kexpr_loc = loc }
  | KE_fby (e0s, es, er) ->
    let e0s' = List.map (elab_expr nodes clocks vars) e0s
    and es' = List.map (elab_expr nodes clocks vars) es
    and er' = elab_expr nodes clocks vars er in

    let tys0 = types_of e0s' and tys = types_of es' in
    if (tys0 <> tys)
    then raise
        (TypeError
           (Printf.sprintf
              "Both sides of fby should have the same type, found %s and %s"
              (string_of_tys tys0) (string_of_tys tys),
            e.kexpr_loc));
    let tyr = er'.kexpr_annot in
    if (tyr <> [Tbool])
    then raise
        (TypeError
           (Printf.sprintf
              "Reset expression of fby should have type bool, found %s"
              (string_of_tys tyr),
            e.kexpr_loc));
    { kexpr_desc = KE_fby(e0s', es', er'); kexpr_annot = tys0; kexpr_loc = loc }
  | KE_arrow (e0s, es, er) ->
    let e0s' = List.map (elab_expr nodes clocks vars) e0s
    and es' = List.map (elab_expr nodes clocks vars) es
    and er' = elab_expr nodes clocks vars er in

    let tys0 = types_of e0s' and tys = types_of es' in
    if (tys0 <> tys)
    then raise
        (TypeError
           (Printf.sprintf
              "Both sides of fby should have the same type, found %s and %s"
              (string_of_tys tys0) (string_of_tys tys),
            e.kexpr_loc));
    let tyr = er'.kexpr_annot in
    if (tyr <> [Tbool])
    then raise
        (TypeError
           (Printf.sprintf
              "Reset expression of fby should have type bool, found %s"
              (string_of_tys tyr),
            e.kexpr_loc));
    { kexpr_desc = KE_arrow(e0s', es', er'); kexpr_annot = tys0; kexpr_loc = loc }
  | KE_match (e, branches) ->
    let e' = elab_expr nodes clocks vars e in
    let clt = get_unary_type e'.kexpr_annot e.kexpr_loc in

    (* Check the constructors *)
    let constrs = constrs_of_clock clocks loc clt in
    if (constrs <> List.map fst branches)
    then raise (constructors_error constrs (List.map fst branches) loc);

    (* Check the expression types *)
    let branches' = List.map
        (fun (c, es) -> c, List.map (elab_expr nodes clocks vars) es) branches in

    let tys = types_of (snd (List.hd branches')) in
    List.iter (fun ((_, es) : (constr * TPMinils.k_expr list)) ->
        let tys' = types_of es in
        if (tys' <> tys)
        then raise
            (TypeError
               (Printf.sprintf
                  "All args of switch should have the same type, found %s and %s"
                  (string_of_tys tys)
                  (string_of_tys tys'), e.kexpr_loc))) branches';
    { kexpr_desc = KE_match (e', branches');
      kexpr_annot = tys; kexpr_loc = loc }
  | KE_when (es, constr, cl) ->
    let clt = (try (List.assoc cl vars)
               with _ -> raise (TypeError
                                  (Printf.sprintf "Clock %s not found in node"
                                     cl, loc))) in
    let constrs = constrs_of_clock clocks loc clt in
    if not (List.mem constr constrs) then
      raise (TypeError
               (Printf.sprintf
                  "Constructor %s does not belong to clock type %s"
                  constr (string_of_ty clt), loc));
    let es' = List.map (elab_expr nodes clocks vars) es in
    { kexpr_desc = KE_when (es', constr, cl);
      kexpr_annot = types_of es'; kexpr_loc = loc }
  | KE_merge (cl, branches) ->
    let clt = (try (List.assoc cl vars)
               with _ -> raise (TypeError
                                  (Printf.sprintf "Clock %s not found in node"
                                     cl, e.kexpr_loc))) in

    (* Check the constructors *)
    let constrs = constrs_of_clock clocks loc clt in
    if (constrs <> List.map fst branches)
    then raise (constructors_error constrs (List.map fst branches) loc);

    (* Check the expression types *)
    let branches' = List.map
        (fun (c, es) -> c, List.map (elab_expr nodes clocks vars) es) branches in

    let tys = types_of (snd (List.hd branches')) in
    List.iter (fun ((_, es) : (constr * TPMinils.k_expr list)) ->
        let tys' = types_of es in
        if (tys' <> tys)
        then raise
            (TypeError
               (Printf.sprintf
                  "All args of merge should have the same type, found %s and %s"
                  (string_of_tys tys)
                  (string_of_tys tys'), e.kexpr_loc))) branches';
    { kexpr_desc = KE_merge (cl, branches');
      kexpr_annot = tys; kexpr_loc = loc }
  | KE_app (id, es, er) ->
    let es' = List.map (elab_expr nodes clocks vars) es in
    let er' = elab_expr nodes clocks vars er in
    (* Check that reset stream is bool *)
    if(er'.kexpr_annot <> [Tbool])
    then raise (TypeError
                  (Printf.sprintf
                     "Reset expr should be of type bool, found %s"
                     (string_of_tys er'.kexpr_annot), er.kexpr_loc));
    (* Find the node *)
    let node = try List.assoc id nodes
      with _ -> raise (TypeError
                         (Printf.sprintf "Node %s not found in file"
                            id, e.kexpr_loc)) in
    (* Check input types *)
    let expected = List.map (fun (_, (ty, _)) -> ty) node.pn_input
    and actual = types_of es' in

    if actual <> expected
    then raise
        (TypeError
           (Printf.sprintf
              "Wrong input type for instantiation %s, expected %s, found %s"
              id (string_of_tys expected) (string_of_tys actual),
                 e.kexpr_loc));

    (* Output type *)
    let outy = List.map (fun (_, (ty, _)) -> ty) node.pn_output in
    { kexpr_desc = KE_app (id, es', er');
      kexpr_annot = outy; kexpr_loc = loc }
  | KE_last id ->
    let bty =
      (try (List.assoc id vars)
       with _ -> raise (TypeError
                          (Printf.sprintf "Stream %s not found in node"
                             id, e.kexpr_loc))) in
    { kexpr_desc = KE_last id; kexpr_annot = [bty]; kexpr_loc = e.kexpr_loc }

(** Get the type expected for a pattern [pat] *)
let get_pattern_type (vars : (ident * ty) list) pat loc =
  List.map (fun id ->
      try (List.assoc id vars)
      with _ -> raise (UnexpectedEquationError (id, loc))) pat

(** Check that the equation [eq] is correctly typed. *)
let elab_equation nodes clocks vars (eq : k_equation) : TPMinils.k_equation =
  let expected = get_pattern_type vars eq.keq_patt eq.keq_loc in
  let es' = List.map (elab_expr nodes clocks vars) eq.keq_expr in
  let tys = types_of es' in
  if tys <> expected
  then raise (TypeError
                (Printf.sprintf
                   "Wrong type for equation : expected %s, found %s"
                   (string_of_tys expected)
                   (string_of_tys tys), eq.keq_loc));
  { keq_patt = eq.keq_patt; keq_expr = es'; keq_loc = eq.keq_loc }

(** Get all the names defined in a set of instructions *)
let rec get_def_instr (i : p_instr) : ident list =
  match i.pinstr_desc with
  | Eq eq -> defined_of_equation eq
  | Block bck -> get_def_block bck
  | Reset (ins, _) -> get_def_instrs ins
  | Switch (e, brs, _) ->
    let defs = List.map (fun (_, ins) -> get_def_instrs ins) brs in
    let defs = List.map (List.sort String.compare) defs in
    let def = List.hd defs in
    (** All the branches should define the same idents *)
    if (not (List.for_all (fun def' -> def = def') defs))
    then raise (TypeError
                  ("All the branches of switch should define the same idents",
                   i.pinstr_loc));
    def
  | Automaton (brs, _) ->
    let defs = List.map (fun (_, _, ins, _) -> get_def_instrs ins) brs in
    let defs = List.map (List.sort String.compare) defs in
    let def = List.hd defs in
    (** All the branches should define the same idents *)
    if (not (List.for_all (fun def' -> def = def') defs))
    then raise (TypeError
                  ("All the branches of automaton should define the same idents",
                   i.pinstr_loc));
    def
and get_def_instrs (ins : p_instr list) =
  List.concat (List.map get_def_instr ins)

and get_def_block (bck : p_block) =
  let defs = get_def_instrs bck.pb_instrs in
  List.fold_left (fun defs x ->
      if List.mem x defs
      then remove_one x defs
      else raise (TypeError (Printf.sprintf "Missing a definition for %s" x, bck.pb_loc))
    ) defs (List.map (fun (x, _, _) -> x) bck.pb_local)

(** Check a clock in a typing env *)
let check_clock loc clocks (vars : (ident * ty) list) ck =
  let rec aux ck =
    match ck with
    | Cbase -> ()
    | Con (constr, idck, ck) ->
      aux ck;
      let ckt = (try (List.assoc idck vars)
                 with _ ->
                   raise (TypeError
                            (Printf.sprintf "Clock variable %s not found" idck, loc))) in
      let constrs = constrs_of_clock clocks loc ckt in
      if not (List.mem constr constrs)
      then raise (TypeError
                    (Printf.sprintf "%s is not a constructor of %s"
                       constr (string_of_ty ckt), loc))
  in aux ck

(** Check that the instruction [ins] is correctly typed. *)
let rec elab_instr nodes clocks vars (ins : p_instr) : TPMinils.p_instr =
  let (desc : TPMinils.p_instr_desc) =
    match ins.pinstr_desc with
    | Eq eq -> Eq (elab_equation nodes clocks vars eq)
    | Block bck -> Block (elab_block nodes clocks vars bck)
    | Reset (ins, er) ->
      let ins' = elab_instrs nodes clocks vars ins
      and er' = elab_expr nodes clocks vars er in
      if er'.kexpr_annot <> [Tbool] then
        raise (TypeError
                 (Printf.sprintf
                    "Reset expr should be of type bool, found %s"
                    (string_of_tys er'.kexpr_annot), er.kexpr_loc));
      Reset (ins', er')
    | Switch (e, brs, (ckid, _)) ->
      let e' = elab_expr nodes clocks vars e in
      let clt = get_unary_type e'.kexpr_annot e.kexpr_loc in
      let constrs = constrs_of_clock clocks e.kexpr_loc clt in
      if (constrs <> List.map fst brs)
      then raise (constructors_error constrs (List.map fst brs) ins.pinstr_loc);
      let brs' = List.map (fun (c, ins) -> (c, elab_instrs nodes clocks vars ins)) brs in
      Switch (e', brs', (ckid, get_def_instr ins))
    | Automaton (brs, (_, ck, _)) ->
      let tyid = Atom.fresh "_aut"
      and constrs = List.map (fun (c, _, _, _) -> c) brs in
      let elab_un (e, s, b) =
        let e' = elab_expr nodes clocks vars e in
        if e'.kexpr_annot <> [Tbool] then
          raise (TypeError
                   (Printf.sprintf
                      "unless/until expr should be of type bool, found %s"
                      (string_of_tys e'.kexpr_annot), e.kexpr_loc));
        if not (List.mem s constrs) then
          raise (TypeError
                   (Printf.sprintf
                      "state %s is not defined in automaton" s, ins.pinstr_loc));
        (e', s, b)
      in
      let brs' = List.map (fun (c, unlesss, instrs, untils) ->
          let unlesss' = List.map elab_un unlesss
          and instrs' = elab_instrs nodes clocks vars instrs
          and untils' = List.map elab_un untils in
          (c, unlesss', instrs', untils')
        ) brs in
      Automaton (brs', (Some tyid, ck, get_def_instr ins))
  in { pinstr_desc = desc; pinstr_loc = ins.pinstr_loc }
and elab_instrs nodes clocks vars ins =
  List.map (elab_instr nodes clocks vars) ins
and elab_block nodes clocks vars bck : TPMinils.p_block =
  let vars' = (List.map (fun (x, (ty, _), _) -> (x, ty)) bck.pb_local)@vars in

  List.iter (fun (id, (_, ck), _) -> check_clock bck.pb_loc clocks vars' ck) bck.pb_local;

  (* Check that the last init constants are well typed *)
  List.iter (fun (id, (ty, _), const) ->
      match const with
      | Some const ->
        let ty' = type_const bck.pb_loc const in
        if ty' <> ty then
          raise (TypeError
                   (Printf.sprintf "last %s was declared with type %s, but found %s for its init constant"
                      id (string_of_ty ty) (string_of_ty ty'), bck.pb_loc))
      | _ -> ()) bck.pb_local;

  { pb_local = bck.pb_local;
    pb_instrs = elab_instrs nodes clocks vars' bck.pb_instrs;
    pb_loc = bck.pb_loc }

(** Check that the node [n] is correctly typed *)
let elab_node (nodes: (ident * TPMinils.p_node) list) clocks (n : p_node) :
  TPMinils.p_node =
  let all_streams = (n.pn_output@n.pn_input) in

  (* Check that there are no duplicate stream names *)
  let sorted_streams = List.sort
      (fun (id1, _) (id2, _) -> String.compare id1 id2)
      all_streams in

  let rec find_consecutives = function
    | [] | [_] -> None
    | (hd1, _)::(hd2, s2)::tl ->
      if hd1 = hd2 then Some hd1
      else (find_consecutives ((hd2, s2)::tl)) in
  (match (find_consecutives sorted_streams)
   with None -> ()
      | Some id -> raise (TypeError
                            (Printf.sprintf
                               "Stream name %s was defined twice in node %s"
                               id n.pn_name, n.pn_loc)));

  (* Check that all declared types are using correct clocks *)
  let idty = List.map (fun (id, (ty, _)) -> (id, ty)) in
  List.iter (fun (id, (_, ck)) -> check_clock n.pn_loc clocks (idty n.pn_input) ck) n.pn_input;
  List.iter (fun (id, (_, ck)) -> check_clock n.pn_loc clocks (idty (n.pn_input@n.pn_output)) ck) n.pn_output;

  (* Check that all the streams are defined *)
  let expected = List.sort String.compare (List.map fst n.pn_output)
  and defined = List.sort String.compare (get_def_block n.pn_body) in
  if (defined <> expected) then
    raise (TypeError
             (Printf.sprintf "Incorrect list of definitions; expected [%s], got [%s]"
                (String.concat ";" expected) (String.concat ";" defined),
              n.pn_loc));

  (* Elab the instructions *)
  let body = elab_block nodes clocks (List.map (fun (id, (ty, _)) -> (id, ty)) all_streams) n.pn_body in

  (* Construct the resultting node *)
  { pn_name = n.pn_name;
    pn_input = n.pn_input;
    pn_output = n.pn_output;
    pn_body = body;
    pn_loc = n.pn_loc }

(** Check that the file [f] is correctly typed *)
let elab_file (f : p_file) : TPMinils.p_file =
  let clocks = f.pf_clocks in
  let nodes = List.fold_left (fun env n ->
      (n.pn_name, elab_node env clocks n)::env) [] f.pf_nodes in
  { pf_clocks = clocks;
    pf_nodes = List.map snd (List.rev nodes); }

(** Add the new clock types corresponding to automata                         *)

let rec collect_ctypes_instr (ins : TPMinils.p_instr) =
  match ins.pinstr_desc with
  | Eq _ -> []
  | Block bck -> collect_ctypes_block bck
  | Reset (instrs, _) -> collect_ctypes_instrs instrs
  | Switch (_, brs, _) ->
    List.concat (List.map (fun (_, ins) -> collect_ctypes_instrs ins) brs)
  | Automaton (brs, (tyid, _, defs)) ->
    let tyid = match tyid with Some tyid -> tyid | _ -> failwith "Should not happen"
    and constrs = List.map (fun (c, _, _, _) -> c) brs in
    let nclocks = List.concat (List.map (fun (_, _, ins, _) -> collect_ctypes_instrs ins) brs) in
    (tyid, constrs)::nclocks
and collect_ctypes_instrs ins =
  List.concat (List.map collect_ctypes_instr ins)
and collect_ctypes_block (bck : TPMinils.p_block) =
  collect_ctypes_instrs bck.pb_instrs

let collect_ctypes_node (n : TPMinils.p_node) =
  collect_ctypes_block n.pn_body

let add_ctypes_file (f : TPMinils.p_file) : TPMinils.p_file =
  let nclocks = List.concat (List.map collect_ctypes_node f.pf_nodes) in
  { f with pf_clocks = f.pf_clocks@nclocks }

let type_file (f : p_file) : TPMinils.p_file =
  f |> sort_file |> elab_file |> add_ctypes_file
