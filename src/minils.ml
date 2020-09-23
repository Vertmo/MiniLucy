(** Kernel AST *)

open Asttypes

module type Annotations = sig
  type t
  val string_of_t : t -> string
end

module NoAnnot : (Annotations with type t = unit) = struct
  type t = unit
  let string_of_t () = ""
end

module MINILS(A : Annotations) = struct
  type k_expr =
    { kexpr_desc: k_expr_desc;
      kexpr_annot: A.t list;
      kexpr_loc: location; }

  and k_expr_desc =
    | KE_const of const
    | KE_ident of ident
    | KE_unop of op * k_expr
    | KE_binop of op * k_expr * k_expr
    | KE_app of ident * k_expr list * k_expr
    | KE_fby of k_expr list * k_expr list
    | KE_arrow of k_expr list * k_expr list
    | KE_match of k_expr * (constr * k_expr list) list
    | KE_when of k_expr list * constr * ident
    | KE_merge of ident * (constr * k_expr list) list

  let string_of_annots anns =
    Printf.sprintf "[%s]"
      (String.concat "," (List.map A.string_of_t anns))

  let rec string_of_expr ?(print_anns=false) e =
    let desc = string_of_expr_desc ~print_anns e.kexpr_desc in
    if print_anns then
      Printf.sprintf "%s [%s]"
        desc
        (string_of_annots e.kexpr_annot)
    else desc

  and string_of_expr_desc ?(print_anns=false) (e : k_expr_desc) =
    let string_of_expr = string_of_expr ~print_anns
    and string_of_exprs = string_of_exprs ~print_anns in
    match e with
    | KE_const c -> string_of_const c
    | KE_ident i -> i
    | KE_unop (op, e1) ->
      Printf.sprintf "(%s %s)" (string_of_op op) (string_of_expr e1)
    | KE_binop (op, e1, e2) ->
      Printf.sprintf "(%s %s %s)"
        (string_of_expr e1) (string_of_op op) (string_of_expr e2)
    | KE_app (id, es, ever) ->
      Printf.sprintf "(%s(%s) every %s)" id
        (string_of_exprs es) (string_of_expr ever)
    | KE_fby (e0, e) ->
      Printf.sprintf "(%s fby %s)" (string_of_exprs e0) (string_of_exprs e)
    | KE_arrow (e0, e) ->
      Printf.sprintf "(%s -> %s)" (string_of_exprs e0) (string_of_exprs e)
    | KE_match (e, es) ->
      Printf.sprintf "match %s with %s"
        (string_of_expr e) (String.concat " "
                              (List.map
                                 (fun (constr, e) -> Printf.sprintf "(%s -> %s)"
                                     constr (string_of_exprs e)) es))
    | KE_when (e, constr, clid) ->
      Printf.sprintf "%s when %s(%s)"
        (string_of_exprs e) constr clid
    | KE_merge (id, es) ->
      Printf.sprintf "merge %s %s"
        id (String.concat " "
              (List.map
                 (fun (constr, e) -> Printf.sprintf "(%s -> %s)"
                     constr (string_of_exprs e)) es))

  and string_of_exprs ?(print_anns=false) es =
    Printf.sprintf (if List.length es = 1 then "%s" else "(%s)")
      (String.concat "," (List.map (string_of_expr ~print_anns) es))

  let rec string_of_patt p =
    Printf.sprintf
      (if List.length p = 1 then "%s" else "(%s)")
      (String.concat ", " p)

  type k_equation =
    { keq_patt: ident list;
      keq_expr: k_expr list;
      keq_loc: location }

  let string_of_equation ?(print_anns=false) eq =
    Printf.sprintf "%s = %s"
      (string_of_patt eq.keq_patt)
      (string_of_exprs ~print_anns eq.keq_expr)

  (** Variables defined by an equation *)
  let defined_of_equation eq = eq.keq_patt

  type k_node =
    { kn_name: ident;
      kn_input: (ident * ann) list;
      kn_output: (ident * ann) list;
      kn_local: (ident * ann) list;
      kn_equs: k_equation list;
      kn_loc: location; }

  let string_of_node ?(print_anns=false) n =
    Printf.sprintf "node %s(%s) returns (%s);\n\
                    var %s;\n\
                    let\n\
                    %s\
                    tel\n"
      n.kn_name
      (string_of_ident_ann_list n.kn_input)
      (string_of_ident_ann_list n.kn_output)
      (string_of_ident_ann_list n.kn_local)
      (String.concat "" (List.map (fun eq ->
           Printf.sprintf "  %s;\n" (string_of_equation ~print_anns eq)) n.kn_equs))

  type k_file =
    { kf_clocks: clockdec list;
      kf_nodes: k_node list; }

  let string_of_file ?(print_anns=false) f =
    Printf.sprintf "%s\n%s"
      (String.concat "\n" (List.map string_of_clockdec f.kf_clocks))
      (String.concat "\n" (List.map (string_of_node ~print_anns) f.kf_nodes))
end

module KMinils = MINILS(NoAnnot)
