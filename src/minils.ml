(** Kernel AST *)

open Common

module type Annotations = sig
  type t
  val print_t : Format.formatter -> t -> unit
end

module NoAnnot : (Annotations with type t = unit) = struct
  type t = unit
  let print_t fmt () = Format.fprintf fmt ""
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
    | KE_fby of k_expr list * k_expr list * k_expr (* last expr is the reset bit *)
    | KE_arrow of k_expr list * k_expr list * k_expr
    | KE_match of k_expr * (constr * k_expr list) list
    | KE_when of k_expr list * constr * ident
    | KE_merge of ident * (constr * k_expr list) list
    | KE_last of ident

  type k_equation =
    { keq_patt: ident list;
      keq_expr: k_expr list;
      keq_loc: location }

  type k_node =
    { kn_name: ident;
      kn_input: (ident * ann) list;
      kn_output: (ident * ann) list;
      kn_local: (ident * ann) list;
      kn_equs: k_equation list;
      kn_loc: location; }

  type k_file =
    { kf_clocks: clockdec list;
      kf_nodes: k_node list; }

  (** Variables defined by an equation *)
  let defined_of_equation eq = eq.keq_patt

  open Format

  let print_annots fmt anns =
    fprintf fmt "[%a]"
      (print_col_list A.print_t) anns

  let rec print_expr ?(print_anns=false) fmt e =
    let print_expr_desc = print_expr_desc ~print_anns in
    if print_anns then
      fprintf fmt "%a %a" print_expr_desc e.kexpr_desc print_annots e.kexpr_annot
    else print_expr_desc fmt e.kexpr_desc

  and print_expr_desc ?(print_anns=false) fmt (e : k_expr_desc) =
    let print_expr = print_expr ~print_anns
    and print_exprs = print_exprs ~print_anns
    and print_branch = print_branch ~print_anns in
    match e with
    | KE_const c -> print_const fmt c
    | KE_ident i -> print_ident fmt i
    | KE_unop (op, e1) ->
      fprintf fmt "@[<hov 2>(%s@;%a)@]" (string_of_op op) print_expr e1
    | KE_binop (op, e1, e2) ->
      fprintf fmt "@[<hov 2>(%a %s@;%a)@]"
        print_expr e1 (string_of_op op) print_expr e2
    | KE_app (id, es, ever) ->
      fprintf fmt "@[<hov 2>(%s(%a)@;every@;%a)@]" id
        print_exprs es print_expr ever
    | KE_fby (e0, e, er) ->
      fprintf fmt "@[<hov 2>(%a@;fby@;%a@;every %a)@]"
        print_exprs e0 print_exprs e print_expr er
    | KE_arrow (e0, e, _) ->
      fprintf fmt "@[<hov 2>(%a@;->@;%a)@]" print_exprs e0 print_exprs e
    | KE_match (e, es) ->
      fprintf fmt "@[<hov 2>match %a@;with@;%a@]"
        print_expr e
        (pp_print_list ~pp_sep:(fun p () -> fprintf p "@;") print_branch) es
    | KE_when (e, constr, clid) ->
      fprintf fmt "@[<hov 2>(%a when %s(%s))@]"
        print_exprs e constr clid
    | KE_merge (id, es) ->
      fprintf fmt "@[<hov 2>(merge %s@;%a)@]"
        id
        (pp_print_list ~pp_sep:(fun p () -> fprintf p "@;") print_branch) es
    | KE_last id ->
      fprintf fmt "@[<h>last %s@]" id
  and print_exprs ?(print_anns=false) fmt es =
    fprintf fmt (if List.length es = 1 then "%a" else "(%a)")
      (print_col_list print_expr) es
  and print_branch ?(print_anns=false) fmt (constr, exprs) =
    fprintf fmt "@[<hov 2>\
                 (%s -> %a)@]"
      constr
      (print_exprs ~print_anns) exprs

  let rec print_patt fmt p =
    fprintf fmt
      (if List.length p = 1 then "%a" else "(%a)")
      (print_col_list print_ident) p

  let print_equation ?(print_anns=false) fmt eq =
    fprintf fmt "@[<hov>%a = %a@]"
      print_patt eq.keq_patt
      (print_exprs ~print_anns) eq.keq_expr

  let print_node ?(print_anns=false) fmt n =
    fprintf fmt "@[<v>\
                 @[<hov 0>\
                 @[<h>node %a (%a)@]@;\
                 @[<h>returns (%a)@]@]@;\
                 @[<hov 2>var %a;@]@;\
                 @[<v 2>let@;%a@;<0 -2>@]\
                 tel@]"
      print_ident n.kn_name
      print_decl_list n.kn_input
      print_decl_list n.kn_output
      print_decl_list n.kn_local
      (print_semicol_list print_equation) n.kn_equs

  let print_file ?(print_anns=false) fmt file =
    fprintf fmt "@[<v 0>%a%a%a@]@."
      (pp_print_list ~pp_sep:(fun p () -> fprintf p "@;@;") print_clock_decl) file.kf_clocks
      (fun fmt _ -> if file.kf_clocks <> [] then fprintf fmt "@;@;" else fprintf fmt "") ()
      (pp_print_list ~pp_sep:(fun p () -> fprintf p "@;@;") print_node) file.kf_nodes
end

module KMinils = MINILS(NoAnnot)
