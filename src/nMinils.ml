(** Normalized abstract syntax tree *)

open Common
open Format

type n_expr =
  { nexpr_desc: n_expr_desc;
    nexpr_ty: ty;
    nexpr_clock: clock; }

and n_expr_desc =
  | NE_const of const
  | NE_ident of ident
  | NE_op of op * n_expr list
  | NE_when of n_expr * constr * ident

type n_cexpr =
  { ncexpr_desc: n_cexpr_desc;
    ncexpr_ty: ty;
    ncexpr_clock: clock; }

and n_cexpr_desc =
  | NCE_match of n_expr * (constr * n_cexpr) list
  | NCE_merge of ident * (constr * n_cexpr) list
  | NCE_expr of n_expr_desc

type n_equation =
  | NQ_ident of ident * n_cexpr
  | NQ_fby of ident * const * n_expr * ident * clock
  | NQ_app of ident list * ident * n_expr list * ident * clock * clock

type n_node =
  { nn_name: ident;
    nn_input: (ident * ann) list;
    nn_output: (ident * ann) list;
    nn_local: (ident * ann) list;
    nn_equs: n_equation list;
    nn_loc: location }

type n_file =
  { nf_clocks: clockdec list;
    nf_nodes : n_node list; }

let print_ident = pp_print_string

let print_col_list p =
  pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") p

let print_semicol_list p =
  pp_print_list ~pp_sep:(fun p () -> fprintf p ";@ ") p

let print_decl fmt (id, (ty, ck)) =
  fprintf fmt "@[<h>%a@ : %s :: %s@]"
    print_ident id
    (string_of_ty ty)
    (string_of_clock ck)

let print_decl_list = print_semicol_list print_decl

let rec print_expr fmt e =
  print_expr_desc fmt e.nexpr_desc

and print_expr_desc fmt = function
  | NE_const c -> fprintf fmt "%s" (string_of_const c)
  | NE_ident i -> fprintf fmt "%s" i
  | NE_op (op, es) ->
    fprintf fmt "@[<hov 2>(%s [%a])@]" (string_of_op op)
      (print_col_list print_expr) es
  | NE_when (e, c, id) ->
    fprintf fmt "@[<hov 2>%a when %s(%s)@]"
      print_expr e c id

let rec print_cexpr fmt e =
  print_cexpr_desc fmt e.ncexpr_desc

and print_cexpr_desc fmt = function
  | NCE_match (e, es) ->
    fprintf fmt "@[<hov 2>match %a %a@]"
      print_expr e
      (pp_print_list print_branch) es
  | NCE_merge (id, es) ->
    fprintf fmt "@[<hov 2>merge %s %a@]"
      id
      (pp_print_list print_branch) es
  | NCE_expr e -> print_expr_desc fmt e

and print_branch fmt (c, e) =
  fprintf fmt "@[<v>(%s -> %a)@]" c print_cexpr e

let print_equation fmt = function
  | NQ_ident (id, e) ->
    fprintf fmt "@[<hov 0>%s = %a@]" id print_cexpr e
  | NQ_fby (id, c, e, r, _) ->
    fprintf fmt "@[<hov 0>%s = %s fby %a every %s@]"
      id (string_of_const c) print_expr e r
  | NQ_app (ids, f, es, ever, _, _) ->
    fprintf fmt "@[<hov 0>(%s) = %s(%a) every %s@]"
      (String.concat ", " ids) f
      (print_col_list print_expr) es
      ever

let print_node fmt n =
  fprintf fmt "@[<v>\
               @[<hov 0>\
               @[<h>node %a (%a)@]@;\
               @[<h>returns (%a)@]@]@;\
               @[<hov 2>var %a;@]@;\
               @[<v 2>let@;%a@;<0 -2>@]\
               tel@]"
    print_ident n.nn_name
    print_decl_list n.nn_input
    print_decl_list n.nn_output
    print_decl_list n.nn_local
    (print_semicol_list print_equation) n.nn_equs

let print_clock_decl fmt decl =
  fprintf fmt "%s" (string_of_clockdec decl)

let print_file ?(print_anns=false) fmt file =
  fprintf fmt "@[<v 0>%a%a%a@]@."
    (pp_print_list ~pp_sep:(fun p () -> fprintf fmt "@;@;") print_clock_decl) file.nf_clocks
    (fun fmt _ -> if file.nf_clocks <> [] then fprintf fmt "@;@;" else fprintf fmt "") ()
    (pp_print_list ~pp_sep:(fun p () -> fprintf fmt "@;@;") print_node) file.nf_nodes
