(** Basic typechecking, doesn't take clocks or causality into account *)

open Asttypes
open Minils
open PMinils

module TypeAnnot : (Annotations with type t = ty) = struct
  type t = ty
  let string_of_t = string_of_ty
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
    | KE_fby (e0, e) -> KE_fby (sort_exprs e0, sort_exprs e)
    | KE_arrow (e0, e) -> KE_arrow (sort_exprs e0, sort_exprs e)
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
  in { e with kexpr_desc = desc }

and sort_exprs es = List.map sort_expr es

let sort_equation (eq : k_equation) : k_equation =
  { eq with keq_expr = sort_exprs eq.keq_expr; }

let rec sort_instr (ins : p_instr) : p_instr =
  let desc =
    match ins.pinstr_desc with
    | Eq eq -> Eq (sort_equation eq)
    | Let (id, ann, e, ins) ->
      Let (id, ann, sort_expr e, sort_instrs ins)
    | Reset (ins, er) ->
      Reset (sort_instrs ins, sort_expr er)
    | Switch (e, branches) ->
      Switch (sort_expr e,
              List.sort (fun (c1, e1) (c2, e1) -> String.compare c1 c2)
                (List.map (fun (c, ins) -> (c, sort_instrs ins)) branches))
    | _ -> failwith "TODO sort_instr"
  in { ins with pinstr_desc = desc }
and sort_instrs ins = List.map sort_instr ins

let sort_node (n : p_node) : p_node =
  { n with pn_instrs = List.map sort_instr n.pn_instrs }

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
let rec elab_expr (nodes : (ident * TPMinils.p_node) list)
    vars clocks e : TPMinils.k_expr =
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
    let e1' = elab_expr nodes vars clocks e1 in
    let ty = get_unary_type e1'.kexpr_annot e1.kexpr_loc in

    { kexpr_desc = KE_unop (op, e1');
      kexpr_annot = [type_op op [ty] loc];
      kexpr_loc = loc }
  | KE_binop (op, e1, e2) ->
    let e1' = elab_expr nodes vars clocks e1
    and e2' = elab_expr nodes vars clocks e2 in
    let ty1 = get_unary_type e1'.kexpr_annot e1.kexpr_loc
    and ty2 = get_unary_type e2'.kexpr_annot e2.kexpr_loc in

    { kexpr_desc = KE_binop (op, e1', e2');
      kexpr_annot = [type_op op [ty1;ty2] loc];
      kexpr_loc = loc }
  | KE_fby (e0s, es) ->
    let e0s' = List.map (elab_expr nodes vars clocks) e0s
    and es' = List.map (elab_expr nodes vars clocks) es in

    let tys0 = types_of e0s' and tys = types_of es' in
    if (tys0 <> tys)
    then raise
        (TypeError
           (Printf.sprintf
              "Both sides of fby should have the same type, found %s and %s"
              (string_of_tys tys0) (string_of_tys tys),
            e.kexpr_loc));
    { kexpr_desc = KE_fby(e0s', es'); kexpr_annot = tys0; kexpr_loc = loc }
  | KE_arrow (e0s, es) ->
    let e0s' = List.map (elab_expr nodes vars clocks) e0s
    and es' = List.map (elab_expr nodes vars clocks) es in

    let tys0 = types_of e0s' and tys = types_of es' in
    if (tys0 <> tys)
    then raise
        (TypeError
           (Printf.sprintf
              "Both sides of fby should have the same type, found %s and %s"
              (string_of_tys tys0) (string_of_tys tys),
            e.kexpr_loc));
    { kexpr_desc = KE_arrow(e0s', es'); kexpr_annot = tys0; kexpr_loc = loc }
  | KE_match (e, branches) ->
    let e' = elab_expr nodes vars clocks e in
    let clt = get_unary_type e'.kexpr_annot e.kexpr_loc in

    (* Check the constructors *)
    let constrs = constrs_of_clock clocks loc clt in
    if (constrs <> List.map fst branches)
    then raise (constructors_error constrs (List.map fst branches) loc);

    (* Check the expression types *)
    let branches' = List.map
        (fun (c, es) -> c, List.map (elab_expr nodes vars clocks) es) branches in

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
    let es' = List.map (elab_expr nodes vars clocks) es in
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
        (fun (c, es) -> c, List.map (elab_expr nodes vars clocks) es) branches in

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
    let es' = List.map (elab_expr nodes vars clocks) es in
    let er' = elab_expr nodes vars clocks er in
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

(** Get the type expected for a pattern [pat] *)
let get_pattern_type (vars : (ident * ty) list) pat loc =
  List.map (fun id ->
      try (List.assoc id vars)
      with _ -> raise (UnexpectedEquationError (id, loc))) pat

(** Check that the equation [eq] is correctly typed. *)
let elab_equation nodes vars clocks (eq : k_equation) : TPMinils.k_equation =
  let expected = get_pattern_type vars eq.keq_patt eq.keq_loc in
  let es' = List.map (elab_expr nodes vars clocks) eq.keq_expr in
  let tys = types_of es' in
  if tys <> expected
  then raise (TypeError
                (Printf.sprintf
                   "Wrong type for equation %s; expected %s, found %s"
                   (KMinils.string_of_equation eq)
                   (string_of_tys expected)
                   (string_of_tys tys), eq.keq_loc));
  { keq_patt = eq.keq_patt; keq_expr = es'; keq_loc = eq.keq_loc }

(** Check that the instruction [ins] is correctly typed. *)
let rec elab_instr nodes vars clocks (ins : p_instr) : TPMinils.p_instr =
  let (desc : TPMinils.p_instr_desc) =
    match ins.pinstr_desc with
    | Eq eq -> Eq (elab_equation nodes vars clocks eq)
    | Let (id, ann, e, instrs) ->
      let e' = elab_expr nodes vars clocks e in
      if (e'.kexpr_annot <> [fst ann])
      then raise (TypeError
                    (Printf.sprintf
                       "Wrong type in let binding; expected %s, found %s"
                       (string_of_ty (fst ann))
                       (string_of_tys e'.kexpr_annot), ins.pinstr_loc));
      let instrs' = elab_instrs nodes ((id, fst ann)::vars) clocks instrs in
      Let (id, ann, e', instrs')
    | Reset (ins, er) ->
      let ins' = elab_instrs nodes vars clocks ins
      and er' = elab_expr nodes vars clocks er in
      if er'.kexpr_annot <> [Tbool] then
        raise (TypeError
                 (Printf.sprintf
                    "Reset expr should be of type bool, found %s"
                    (string_of_tys er'.kexpr_annot), er.kexpr_loc));
      Reset (ins', er')
    | Switch (e, brs) ->
      let e' = elab_expr nodes vars clocks e in
      let clt = get_unary_type e'.kexpr_annot e.kexpr_loc in
      let constrs = constrs_of_clock clocks e.kexpr_loc clt in
      if (constrs <> List.map fst brs)
      then raise (constructors_error constrs (List.map fst brs) ins.pinstr_loc);
      let brs' = List.map (fun (c, ins) -> (c, elab_instrs nodes vars clocks ins)) brs in
      Switch (e', brs')
    | _ -> failwith "TODO elab_instr"
  in { pinstr_desc = desc; pinstr_loc = ins.pinstr_loc }
and elab_instrs nodes vars clocks ins =
  List.map (elab_instr nodes vars clocks) ins

(** Get all the names defined in a set of instructions *)
let rec get_def_instr (i : p_instr) : ident list =
  match i.pinstr_desc with
  | Eq eq -> defined_of_equation eq
  | Let (_, _, _, ins) -> get_def_instrs ins
  | Reset (ins, _) -> get_def_instrs ins
  | Switch (e, brs) ->
    let defs = List.map (fun (_, ins) -> get_def_instrs ins) brs in
    let defs = List.map (List.sort String.compare) defs in
    let def = List.hd defs in
    (** All the branches should define the same idents *)
    if (not (List.for_all (fun def' -> def = def') defs))
    then raise (TypeError
                  ("All the branches of switch should define the same idents",
                   i.pinstr_loc));
    def
  | _ -> failwith "TODO get_def_instr"
and get_def_instrs (ins : p_instr list) =
  List.concat (List.map get_def_instr ins)

(** Check a clock in a typing env *)
let check_clock clocks (n : p_node) (vars : (ident * ty) list) ck =
  let rec aux ck =
    match ck with
    | Cbase -> ()
    | Con (constr, idck, ck) ->
      aux ck;
      let ckt = (try (List.assoc idck vars)
                 with _ ->
                   raise (TypeError
                            (Printf.sprintf "Clock %s not found in node %s"
                               idck n.pn_name, n.pn_loc))) in
      let constrs = constrs_of_clock clocks n.pn_loc ckt in
      if not (List.mem constr constrs)
      then raise (TypeError
                    (Printf.sprintf "%s is not a constructor of %s"
                     constr (string_of_ty ckt), n.pn_loc))
  in aux ck

(** Check that the node [n] is correctly typed *)
let elab_node (nodes: (ident * TPMinils.p_node) list) clocks (n : p_node) :
  TPMinils.p_node =
  let out_streams = (n.pn_output@n.pn_local) in
  let all_streams = (n.pn_input@out_streams) in

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
  List.iter (fun (id, (_, ck)) -> check_clock clocks n (idty n.pn_input) ck) n.pn_input;
  List.iter (fun (id, (_, ck)) -> check_clock clocks n (idty (n.pn_input@n.pn_output)) ck) n.pn_output;
  List.iter (fun (id, (_, ck)) -> check_clock clocks n (idty (n.pn_input@n.pn_output@n.pn_local)) ck) n.pn_local;

  (* Check that all the streams are defined *)
  let expected = List.sort String.compare (List.map fst out_streams)
  and defined = List.sort String.compare (get_def_instrs n.pn_instrs) in
  if (defined <> expected) then
    raise (TypeError
             (Printf.sprintf "Incorrect list of definitions; expected [%s], got [%s]"
                (String.concat ";" expected) (String.concat ";" defined),
              n.pn_loc));

  (* Elab the instructions *)
  let ins = elab_instrs nodes (List.map (fun (id, (ty, _)) -> (id, ty)) all_streams) clocks n.pn_instrs in

  (* Construct the resultting node *)
  { pn_name = n.pn_name;
    pn_input = n.pn_input;
    pn_output = n.pn_output;
    pn_local = n.pn_local;
    pn_instrs = ins;
    pn_loc = n.pn_loc }

(** Check that the file [f] is correctly typed *)
let elab_file (f : p_file) : TPMinils.p_file =
  let clocks = f.pf_clocks in
  try
    let nodes = List.fold_left (fun env n ->
        (n.pn_name, elab_node env clocks n)::env) [] f.pf_nodes in
    { pf_clocks = clocks;
      pf_nodes = List.map snd (List.rev nodes); }
  with
  | UnexpectedEquationError (id, loc) ->
    Printf.eprintf "Type checking error : UnexpectedEquation for %s at %s\n"
      id (string_of_loc loc); exit 1
  | TypeError (msg, loc) ->
    Printf.eprintf "Type checking error : %s at %s\n"
      msg (string_of_loc loc); exit 1

let type_file (f : p_file) : TPMinils.p_file =
  f |> sort_file |> elab_file
