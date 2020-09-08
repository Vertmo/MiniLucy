(** Basic typechecking, doesn't take clocks or causality into account *)

open Asttypes
open Minils

module TypeAnnot : (Annotations with type t = base_ty) = struct
  type t = base_ty
  let string_of_t ty = string_of_base_ty ty
end

module TMinils = MINILS(TypeAnnot)

open TMinils
open KMinils

exception TypeError of (string * location)
exception MissingHintError of location
exception MissingEquationError of (ident * location)
exception UnexpectedEquationError of (ident * location)

(** Get the type expected for a pattern [pat],
    and removes the relevant target streams from [streams] *)
let get_pattern_type (streams : (ident * ty) list) pat =
  match pat.kpatt_desc with
  | KP_ident id ->
    (try base_ty_of_ty (List.assoc id streams)
     with _ -> raise (UnexpectedEquationError (id, pat.kpatt_loc))),
    List.remove_assoc id streams
  | KP_tuple ids ->
    let (tys, streams) = List.fold_left (fun (ty, streams) id ->
        try
          (base_ty_of_ty (List.assoc id streams))::ty,
          List.remove_assoc id streams
        with _ -> raise (UnexpectedEquationError (id, pat.kpatt_loc)))
       ([], streams) ids in
    Ttuple (List.rev tys), streams

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
                        (string_of_base_ty t), loc))
     | None ->
       raise (MissingHintError loc))

(** Get the constructions associated with a clock type *)
let constrs_of_clock clocks loc = function
  | Tbool -> ["False";"True"]
  | Tclock clid ->
    (try List.assoc clid clocks
     with _ -> raise (TypeError
                        (Printf.sprintf "Clock %s not found in file" clid, loc)))
  | ty -> raise (TypeError
                   (Printf.sprintf
                      "Type %s is not supported as a clock"
                      (string_of_base_ty ty), loc))

(** Gives operator output type relating to input types *)
let type_op (inputs : base_ty list) loc op =
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
                     (String.concat "," (List.map string_of_base_ty inputs))
                     (string_of_op op), loc))

(** Provides hints for input of an operator *)
let hint_op hint arity = function
  | Op_sub | Op_not -> List.init arity (fun _ -> hint)
  | Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge -> [None;None]
  | Op_add | Op_mul | Op_div | Op_and | Op_or | Op_xor -> [hint;hint]
  | Op_mod -> [Some Tint;Some Tint]
  | Op_if -> [Some Tbool;hint;hint]

(** Check that an expression has the [expected] type *)
let rec type_expr ?hint (nodes : (ident * TMinils.k_node) list)
    streams clocks e : TMinils.k_expr =
  let loc = e.kexpr_loc in
  match e.kexpr_desc with
  | KE_const c ->
    { kexpr_desc = KE_const c; kexpr_annot = type_const ?hint loc c;
      kexpr_loc = e.kexpr_loc }
  | KE_ident id ->
    let bty =
      (try base_ty_of_ty (List.assoc id streams)
       with _ -> raise (TypeError
                          (Printf.sprintf "Stream %s not found in node"
                             id, e.kexpr_loc))) in
    { kexpr_desc = KE_ident id; kexpr_annot = bty; kexpr_loc = e.kexpr_loc }
  | KE_op (op, es) ->
    (* This is a bit more complicated than expected, because we need to keep
       some hints if we want Nil constants to be typed further down the line *)
    let hints = hint_op hint (List.length es) op in
    let tes = if op = Op_if
      then [type_expr ~hint:Tbool nodes streams clocks (List.nth es 0);
            type_expr ?hint nodes streams clocks (List.nth es 1);
            type_expr ?hint nodes streams clocks (List.nth es 2)]
      else
        let rec get_one_type = function
          | [] -> None
          | (e, hint)::tl ->
            try Some (type_expr ?hint:hint nodes streams clocks e)
            with (MissingHintError _) -> get_one_type tl in
        match (get_one_type (List.combine es hints)) with
        | None ->
          raise (TypeError
                   (Printf.sprintf
                      "Could not infer types of operands of expression %s"
                      (string_of_expr e), loc))
        | Some e ->
          List.map (type_expr ~hint:(e.kexpr_annot) nodes streams clocks) es in
    let outy = type_op
        (List.map (fun (te:TMinils.k_expr) -> te.kexpr_annot) tes)
        e.kexpr_loc op in
    { kexpr_desc = KE_op (op, tes); kexpr_annot = outy; kexpr_loc = loc }
  | KE_app (id, es, ever) ->
    let tes = List.map (type_expr nodes streams clocks) es in
    (* Check that reset stream is bool *)
    let tever = type_expr nodes streams clocks ever in
    if(tever.kexpr_annot <> Tbool)
    then raise (TypeError
                  (Printf.sprintf
                     "The reset stream should be of type bool, found %s"
                     (string_of_base_ty tever.kexpr_annot), ever.kexpr_loc));
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
                   id (string_of_base_ty exp) (string_of_base_ty act),
                 e.kexpr_loc)))
         (List.map (fun (_, t) -> base_ty_of_ty t) node.kn_input)
         (List.map (fun (te : TMinils.k_expr) -> te.kexpr_annot) tes)
     with Invalid_argument _ ->
       raise (TypeError
                (Printf.sprintf
                   "Wrong number of arguments for node %s, expected %s, found %s"
                   id (string_of_int (List.length node.kn_input))
                   (string_of_int (List.length tes)), e.kexpr_loc)));

    (* Output type *)
    let outy = (match node.kn_output with
        | [] -> failwith "Should not happen (syntax)"
        | [(_, ty)] -> base_ty_of_ty ty
        | _ -> Ttuple (List.map (fun (_, t) -> base_ty_of_ty t)
                         node.kn_output)) in
    { kexpr_desc = KE_app (id, tes, tever);
      kexpr_annot = outy; kexpr_loc = loc }
  | KE_fby (e0, e) ->
    let te0 = type_expr ?hint nodes streams clocks e0 in
    let te = type_expr ~hint:te0.kexpr_annot nodes streams clocks e in
    if (te0.kexpr_annot <> te.kexpr_annot)
    then raise
        (TypeError
           (Printf.sprintf
              "Both sides of fby should have the same type, found %s and %s"
              (string_of_base_ty te0.kexpr_annot) (string_of_base_ty te.kexpr_annot),
            e.kexpr_loc));
    { kexpr_desc = KE_fby(te0, te); kexpr_annot = te0.kexpr_annot; kexpr_loc = loc }
  | KE_arrow (e0, e) ->
    let te0 = type_expr ?hint nodes streams clocks e0 in
    let te = type_expr ~hint:te0.kexpr_annot nodes streams clocks e in
    if (te0.kexpr_annot <> te.kexpr_annot)
    then raise
        (TypeError
           (Printf.sprintf
              "Both sides of fby should have the same type, found %s and %s"
              (string_of_base_ty te0.kexpr_annot) (string_of_base_ty te.kexpr_annot),
            e.kexpr_loc));
    { kexpr_desc = KE_arrow(te0, te); kexpr_annot = te0.kexpr_annot; kexpr_loc = loc }
  | KE_tuple es ->
    let tes = (List.map (type_expr nodes streams clocks) es) in
    let tys = List.map (fun (te : TMinils.k_expr) -> te.kexpr_annot) tes in
    { kexpr_desc = KE_tuple tes;
      kexpr_annot = Ttuple tys; kexpr_loc = loc }
  | KE_switch (e, es) ->
    let te = type_expr nodes streams clocks e in
    let clt = te.kexpr_annot in
    (* Check the constructors *)
    let constrs = constrs_of_clock clocks loc clt in
    if (constrs <> List.map fst es)
    then raise
        (TypeError
           (Printf.sprintf
              "Constructors in merge are incorrect for type %s :\
               expected %s, found %s"
              (string_of_base_ty clt)
              (String.concat "," constrs)
              (String.concat "," (List.map fst es)), loc));

    (* Check the expression types *)
    let tes = List.map
        (fun (c, te) -> c, type_expr ?hint nodes streams clocks te) es in
    let ty = (snd (List.hd tes)).kexpr_annot in
    List.iter (fun ((_, te) : (constr * TMinils.k_expr)) ->
        if (te.kexpr_annot <> ty)
        then raise
            (TypeError
               (Printf.sprintf
                  "Both args of merge should have the same type, found %s and %s"
                  (string_of_base_ty ty)
                  (string_of_base_ty te.kexpr_annot), e.kexpr_loc))) tes;
    { kexpr_desc = KE_switch (te, tes);
      kexpr_annot = ty; kexpr_loc = loc }
  | KE_when (e, constr, cl) ->
    let clt = (try base_ty_of_ty (List.assoc cl streams)
               with _ -> raise (TypeError
                                  (Printf.sprintf "Clock %s not found in node"
                                     cl, e.kexpr_loc))) in
    let constrs = constrs_of_clock clocks loc clt in
    if not (List.mem constr constrs) then
      raise (TypeError
               (Printf.sprintf
                  "Constructor %s does not belong to clock type %s"
                  constr (string_of_base_ty clt), loc));
    let te = type_expr ?hint nodes streams clocks e in
    { kexpr_desc = KE_when (te, constr, cl);
      kexpr_annot = te.kexpr_annot; kexpr_loc = loc }
  | KE_merge (cl, es) ->
    let clt = (try base_ty_of_ty (List.assoc cl streams)
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
              (string_of_base_ty clt)
              (String.concat "," constrs)
              (String.concat "," (List.map fst es)), loc));

    (* Check the expression types *)
    let tes = List.map
        (fun (c, te) -> c, type_expr ?hint nodes streams clocks te) es in
    let ty = (snd (List.hd tes)).kexpr_annot in
    List.iter (fun ((_, te) : (constr * TMinils.k_expr)) ->
        if (te.kexpr_annot <> ty)
        then raise
            (TypeError
               (Printf.sprintf
                  "Both args of merge should have the same type, found %s and %s"
                  (string_of_base_ty ty)
                  (string_of_base_ty te.kexpr_annot), e.kexpr_loc))) tes;
    { kexpr_desc = KE_merge (cl, tes);
      kexpr_annot = ty; kexpr_loc = loc }

(** Convert a KMinils.k_patt into a TMinils.k_patt (trivial) *)
let convert_patt (p : KMinils.k_patt) : TMinils.k_patt =
  let desc = match p.kpatt_desc with
    | KP_ident i -> TMinils.KP_ident i
    | KP_tuple t -> TMinils.KP_tuple t
  in { kpatt_desc = desc; kpatt_loc = p.kpatt_loc }

(** Check that the equation [eq] is correctly typed.
    Returns the [out_streams] minus the ones we just type-checked *)
let check_equation nodes streams out_streams clocks (eq : k_equation) :
  TMinils.k_equation * ((ident * ty) list)=
  let (expected, os) = get_pattern_type out_streams eq.keq_patt in
  let te = type_expr ~hint:expected nodes streams clocks eq.keq_expr in
  if te.kexpr_annot <> expected
  then raise (TypeError
                (Printf.sprintf
                   "Wrong type for equation %s; expected %s, found %s"
                   (KMinils.string_of_equation eq)
                   (string_of_base_ty expected)
                   (string_of_base_ty te.kexpr_annot), eq.keq_expr.kexpr_loc));
  { keq_patt = convert_patt eq.keq_patt; keq_expr = te }, os

(** Check that the node [n] is correctly typed *)
let check_node (nodes: (ident * TMinils.k_node) list) clocks (n : k_node) :
  TMinils.k_node =
  let out_streams = (n.kn_local@n.kn_output) in
  let all_streams = (n.kn_input@out_streams) in

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
                               id n.kn_name, n.kn_loc)));

  (* Check that all declared types are using correct clocks *)
  ignore (List.fold_left (fun streams (id, (ty:ty)) -> match ty with
      | Base _ -> (id, ty)::streams
      | Clocked (_, _, cl) ->
        let clt =
          (try base_ty_of_ty (List.assoc cl streams)
           with _ -> raise (TypeError
                              (Printf.sprintf "Clock %s not found in node %s"
                                 cl n.kn_name, n.kn_loc))) in
        ignore (constrs_of_clock clocks n.kn_loc clt);
        (id, ty)::streams
    ) [] all_streams);

  (* Check the equations of the node *)
  let teqs, rem_streams = List.fold_left
      (fun (teqs, streams) eq ->
         let teq, streams =
           check_equation nodes all_streams streams clocks eq in
         teq::teqs, streams)
      ([], out_streams) n.kn_equs in
  (match rem_streams with
   | [] -> ()
   | (hd, _)::_ -> raise (MissingEquationError (hd, n.kn_loc)));

    (* Construct the resultting node *)
  { kn_name = n.kn_name;
    kn_input = n.kn_input;
    kn_output = n.kn_output;
    kn_local = n.kn_local;
    kn_equs = List.rev teqs;
    kn_loc = n.kn_loc }

(** Check that the file [f] is correctly typed *)
let check_file (f : k_file) : TMinils.k_file =
  let clocks = f.kf_clocks in
  try
    let nodes = List.fold_left (fun env n ->
        (n.kn_name, check_node env clocks n)::env) [] f.kf_nodes in
    { kf_clocks = clocks;
      kf_nodes = List.map snd (List.rev nodes); }
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
