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

exception TypeError of (string * location)
exception MissingHintError of location
exception MissingEquationError of (ident * location)
exception UnexpectedEquationError of (ident * location)

(** Typecheck constant. Can take a [hint] for the nil case *)
let type_const ?hint loc = function
  | Cbool _ -> Tbool
  | Cint _ -> Tint
  | Creal _ -> Treal
  | Cconstr (_, tyid) -> Tclock tyid
  | Cnil ->
    (match hint with
     | Some t ->
       if t = Tbool || t = Tint || t = Treal then t
       else raise (TypeError
                     (Printf.sprintf "Type %s incompatible with constant nil"
                        (string_of_ty t), loc))
     | None ->
       raise (MissingHintError loc))

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
let type_op (inputs : ty list) loc op =
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
  | Op_if when List.length inputs = 3 &&
               List.nth inputs 1 = List.nth inputs 2 -> List.nth inputs 1
  | _ -> raise (TypeError
                  (Printf.sprintf "Wrong input types (%s) for operator %s"
                     (String.concat "," (List.map string_of_ty inputs))
                     (string_of_op op), loc))

(** Provides hints for input of an operator *)
let hint_op hint arity = function
  | Op_sub | Op_not -> List.init arity (fun _ -> hint)
  | Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge -> [None;None]
  | Op_add | Op_mul | Op_div | Op_and | Op_or | Op_xor -> [hint;hint]
  | Op_mod -> [Some Tint;Some Tint]
  | Op_if -> [Some Tbool;hint;hint]

(** Check that an expression has the [expected] type *)
let rec elab_expr ?hint (nodes : (ident * TPMinils.p_node) list)
    vars clocks e : TPMinils.k_expr =
  let loc = e.kexpr_loc in
  match e.kexpr_desc with
  | KE_const c ->
    { kexpr_desc = KE_const c; kexpr_annot = type_const ?hint loc c;
      kexpr_loc = e.kexpr_loc }
  | KE_ident id ->
    let bty =
      (try (List.assoc id vars)
       with _ -> raise (TypeError
                          (Printf.sprintf "Stream %s not found in node"
                             id, e.kexpr_loc))) in
    { kexpr_desc = KE_ident id; kexpr_annot = bty; kexpr_loc = e.kexpr_loc }
  | KE_op (op, es) ->
    (* This is a bit more complicated than expected, because we need to keep
       some hints if we want Nil constants to be typed further down the line *)
    let hints = hint_op hint (List.length es) op in
    let tes = if op = Op_if
      then [elab_expr ~hint:Tbool nodes vars clocks (List.nth es 0);
            elab_expr ?hint nodes vars clocks (List.nth es 1);
            elab_expr ?hint nodes vars clocks (List.nth es 2)]
      else
        let rec get_one_type = function
          | [] -> None
          | (e, hint)::tl ->
            try Some (elab_expr ?hint:hint nodes vars clocks e)
            with (MissingHintError _) -> get_one_type tl in
        match (get_one_type (List.combine es hints)) with
        | None ->
          raise (TypeError
                   (Printf.sprintf
                      "Could not infer types of operands of expression %s"
                      (string_of_expr e), loc))
        | Some e ->
          List.map (elab_expr ~hint:(e.kexpr_annot) nodes vars clocks) es in
    let outy = type_op
        (List.map (fun (te:TPMinils.k_expr) -> te.kexpr_annot) tes)
        e.kexpr_loc op in
    { kexpr_desc = KE_op (op, tes); kexpr_annot = outy; kexpr_loc = loc }
  | KE_app (id, es, ever) ->
    let tes = List.map (elab_expr nodes vars clocks) es in
    (* Check that reset stream is bool *)
    let tever = elab_expr nodes vars clocks ever in
    if(tever.kexpr_annot <> Tbool)
    then raise (TypeError
                  (Printf.sprintf
                     "The reset stream should be of type bool, found %s"
                     (string_of_ty tever.kexpr_annot), ever.kexpr_loc));
    (* Find the node *)
    let node = try List.assoc id nodes
      with _ -> raise (TypeError
                         (Printf.sprintf "Node %s not found in file"
                            id, e.kexpr_loc)) in
    (* Check input types *)
    (try List.iter2 (fun exp act ->
         if (exp <> act)
         then raise
             (TypeError
                (Printf.sprintf
                   "Wrong argument type for node %s, expected %s, found %s"
                   id (string_of_ty exp) (string_of_ty act),
                 e.kexpr_loc)))
         (List.map (fun (_, (ty, _)) -> ty) node.pn_input)
         (List.map (fun (te : TPMinils.k_expr) -> te.kexpr_annot) tes)
     with Invalid_argument _ ->
       raise (TypeError
                (Printf.sprintf
                   "Wrong number of arguments for node %s, expected %s, found %s"
                   id (string_of_int (List.length node.pn_input))
                   (string_of_int (List.length tes)), e.kexpr_loc)));

    (* Output type *)
    let outy = (match node.pn_output with
        | [] -> failwith "Should not happen (syntax)"
        | [(_, (ty, _))] -> ty
        | _ -> Ttuple (List.map (fun (_, (ty, _)) -> ty)
                         node.pn_output)) in
    { kexpr_desc = KE_app (id, tes, tever);
      kexpr_annot = outy; kexpr_loc = loc }
  | KE_fby (e0, e) ->
    let te0 = elab_expr ?hint nodes vars clocks e0 in
    let te = elab_expr ~hint:te0.kexpr_annot nodes vars clocks e in
    if (te0.kexpr_annot <> te.kexpr_annot)
    then raise
        (TypeError
           (Printf.sprintf
              "Both sides of fby should have the same type, found %s and %s"
              (string_of_ty te0.kexpr_annot) (string_of_ty te.kexpr_annot),
            e.kexpr_loc));
    { kexpr_desc = KE_fby(te0, te); kexpr_annot = te0.kexpr_annot; kexpr_loc = loc }
  | KE_arrow (e0, e) ->
    let te0 = elab_expr ?hint nodes vars clocks e0 in
    let te = elab_expr ~hint:te0.kexpr_annot nodes vars clocks e in
    if (te0.kexpr_annot <> te.kexpr_annot)
    then raise
        (TypeError
           (Printf.sprintf
              "Both sides of fby should have the same type, found %s and %s"
              (string_of_ty te0.kexpr_annot) (string_of_ty te.kexpr_annot),
            e.kexpr_loc));
    { kexpr_desc = KE_arrow(te0, te); kexpr_annot = te0.kexpr_annot; kexpr_loc = loc }
  | KE_tuple es ->
    let tes = (List.map (elab_expr nodes vars clocks) es) in
    let tys = List.map (fun (te : TPMinils.k_expr) -> te.kexpr_annot) tes in
    { kexpr_desc = KE_tuple tes;
      kexpr_annot = Ttuple tys; kexpr_loc = loc }
  | KE_switch (e, es) ->
    let te = elab_expr nodes vars clocks e in
    let clt = te.kexpr_annot in
    (* Check the constructors *)
    let constrs = constrs_of_clock clocks loc clt in
    if (constrs <> List.map fst es)
    then raise
        (TypeError
           (Printf.sprintf
              "Constructors in merge are incorrect for type %s :\
               expected %s, found %s"
              (string_of_ty clt)
              (String.concat "," constrs)
              (String.concat "," (List.map fst es)), loc));

    (* Check the expression types *)
    let tes = List.map
        (fun (c, te) -> c, elab_expr ?hint nodes vars clocks te) es in
    let ty = (snd (List.hd tes)).kexpr_annot in
    List.iter (fun ((_, te) : (constr * TPMinils.k_expr)) ->
        if (te.kexpr_annot <> ty)
        then raise
            (TypeError
               (Printf.sprintf
                  "Both args of merge should have the same type, found %s and %s"
                  (string_of_ty ty)
                  (string_of_ty te.kexpr_annot), e.kexpr_loc))) tes;
    { kexpr_desc = KE_switch (te, tes);
      kexpr_annot = ty; kexpr_loc = loc }
  | KE_when (e, constr, cl) ->
    let clt = (try (List.assoc cl vars)
               with _ -> raise (TypeError
                                  (Printf.sprintf "Clock %s not found in node"
                                     cl, e.kexpr_loc))) in
    let constrs = constrs_of_clock clocks loc clt in
    if not (List.mem constr constrs) then
      raise (TypeError
               (Printf.sprintf
                  "Constructor %s does not belong to clock type %s"
                  constr (string_of_ty clt), loc));
    let te = elab_expr ?hint nodes vars clocks e in
    { kexpr_desc = KE_when (te, constr, cl);
      kexpr_annot = te.kexpr_annot; kexpr_loc = loc }
  | KE_merge (cl, es) ->
    let clt = (try (List.assoc cl vars)
               with _ -> raise (TypeError
                                  (Printf.sprintf "Clock %s not found in node"
                                     cl, e.kexpr_loc))) in

    (* Check the constructors *)
    let constrs = constrs_of_clock clocks loc clt in
    if (constrs <> List.map fst es)
    then raise
        (TypeError
           (Printf.sprintf
              "Constructors in merge are incorrect for type %s :\
               expected %s, found %s"
              (string_of_ty clt)
              (String.concat "," constrs)
              (String.concat "," (List.map fst es)), loc));

    (* Check the expression types *)
    let tes = List.map
        (fun (c, te) -> c, elab_expr ?hint nodes vars clocks te) es in
    let ty = (snd (List.hd tes)).kexpr_annot in
    List.iter (fun ((_, te) : (constr * TPMinils.k_expr)) ->
        if (te.kexpr_annot <> ty)
        then raise
            (TypeError
               (Printf.sprintf
                  "Both args of merge should have the same type, found %s and %s"
                  (string_of_ty ty)
                  (string_of_ty te.kexpr_annot), e.kexpr_loc))) tes;
    { kexpr_desc = KE_merge (cl, tes);
      kexpr_annot = ty; kexpr_loc = loc }

(** Convert a KMinils.k_patt into a TMinils.k_patt (trivial) *)
let convert_patt (p : KMinils.k_patt) : TPMinils.k_patt =
  let desc = match p.kpatt_desc with
    | KP_ident i -> TPMinils.KP_ident i
    | KP_tuple t -> TPMinils.KP_tuple t
  in { kpatt_desc = desc; kpatt_loc = p.kpatt_loc }

(** Get the type expected for a pattern [pat] *)
let get_pattern_type (streams : (ident * ty) list) pat =
  match pat.kpatt_desc with
  | KP_ident id ->
    (try (List.assoc id streams)
     with _ -> raise (UnexpectedEquationError (id, pat.kpatt_loc)))
  | KP_tuple ids ->
    let tys = List.map (fun id ->
        try (List.assoc id streams)
        with _ -> raise (UnexpectedEquationError (id, pat.kpatt_loc))) ids in
    Ttuple (List.rev tys)

(** Check that the equation [eq] is correctly typed. *)
let elab_equation nodes vars clocks (eq : k_equation) : TPMinils.k_equation =
  let expected = get_pattern_type vars eq.keq_patt in
  let te = elab_expr ~hint:expected nodes vars clocks eq.keq_expr in
  if te.kexpr_annot <> expected
  then raise (TypeError
                (Printf.sprintf
                   "Wrong type for equation %s; expected %s, found %s"
                   (KMinils.string_of_equation eq)
                   (string_of_ty expected)
                   (string_of_ty te.kexpr_annot), eq.keq_expr.kexpr_loc));
  { keq_patt = convert_patt eq.keq_patt; keq_expr = te }

(** Check that the instruction [ins] is correctly typed. *)
let rec elab_instr nodes vars clocks (ins : p_instr) : TPMinils.p_instr =
  match ins with
  | Eq eq -> Eq (elab_equation nodes vars clocks eq)
  | Reset (ins, er) ->
    Reset (elab_instrs nodes vars clocks ins,
           elab_expr ~hint:Tbool nodes vars clocks er)
  | _ -> failwith "TODO elab_instr"
and elab_instrs nodes vars clocks ins =
  List.map (elab_instr nodes vars clocks) ins

(** Get all the names defined in an equation *)
let rec get_def_eq ({ keq_patt = p }) : ident list =
  match p.kpatt_desc with
  | KP_ident i -> [i]
  | KP_tuple t -> t

(** Get all the names defined in a set of instructions *)
let rec get_def_instr (i : p_instr) : ident list =
  match i with
  | Eq eq -> get_def_eq eq
  | Reset (ins, _) ->
    get_def_instrs ins
  | _ -> failwith "TODO get_def_instr"
and get_def_instrs (ins : p_instr list) =
  List.concat (List.map get_def_instr ins)

(** Check that the node [n] is correctly typed *)
let elab_node (nodes: (ident * TPMinils.p_node) list) clocks (n : p_node) :
  TPMinils.p_node =
  let out_streams = (n.pn_local@n.pn_output) in
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
  ignore (List.fold_left (fun streams (id, (ty, ck)) ->
      match ck with
      | Cbase -> (id, ty)::streams
      | Con (_, idck, _) ->
        let ckt =
          (try (List.assoc idck streams)
           with _ -> raise (TypeError
                              (Printf.sprintf "Clock %s not found in node %s"
                                 idck n.pn_name, n.pn_loc))) in
        ignore (constrs_of_clock clocks n.pn_loc ckt);
        (id, ty)::streams
      | Ctuple _ -> failwith "Should not happen"
    ) [] all_streams);

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
    Printf.printf "Type checking error : UnexpectedEquation for %s at %s\n"
      id (string_of_loc loc); exit 1
  | MissingEquationError (id, loc) ->
    Printf.printf "Type checking error : MissingEquation for %s at %s\n"
      id (string_of_loc loc); exit 1
  | TypeError (msg, loc) ->
    Printf.printf "Type checking error : %s at %s\n"
      msg (string_of_loc loc); exit 1
  | MissingHintError loc ->
    Printf.printf "Type checking error : Could not infer type of nil at %s"
      (string_of_loc loc); exit 1
