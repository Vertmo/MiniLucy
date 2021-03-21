(** Parsed AST *)

open Common
open Minils
open Format

module PMINILS(A : Annotations) = struct
  include MINILS(A)

  type p_unless = k_expr * constr * bool
  type p_until = k_expr * constr * bool

  type p_instr =
    { pinstr_desc: p_instr_desc;
      pinstr_loc: location }

  and p_instr_desc =
    | Eq of k_equation
    | Block of p_block
    | Switch of (k_expr * (constr * p_instr list) list * (ident option * ident list))
    | Reset of (p_instr list * k_expr)
    | Automaton of ((constr * p_unless list * p_instr list * p_until list) list * (ident option * clock option * ident list))

  and p_block =
    { pb_local: (ident * ann * const option) list;
      pb_instrs: p_instr list;
      pb_loc: location; }

  type p_node =
    { pn_name: ident;
      pn_input: (ident * ann) list;
      pn_output: (ident * ann) list;
      pn_body: p_block;
      pn_loc: location; }

  type p_file =
    { pf_clocks: clockdec list;
      pf_nodes: p_node list; }

  let print_ident = pp_print_string

  let print_semicol_list p =
    pp_print_list ~pp_sep:(fun p () -> fprintf p ";@ ") p

  let print_decl fmt (id, (ty, ck)) =
    fprintf fmt "@[<h>%a@ : %s :: %s@]"
      print_ident id
      (string_of_ty ty)
      (string_of_clock ck)

  let print_decl_list = print_semicol_list print_decl

  let print_local fmt (id, (ty, ck), c) =
    fprintf fmt "@[<h>%s%a@ : %s :: %s%s@]"
      (match c with Some _ -> "last " | None -> "")
      print_ident id
      (string_of_ty ty)
      (string_of_clock ck)
      (match c with Some c -> " = "^(string_of_const c) | None -> "")

  let print_local_list = print_semicol_list print_local

  let print_locals fmt locals =
    if locals <> [] then
      fprintf fmt "@[<hov 2>var %a;@]@;" print_local_list locals

  let print_unless ?(print_anns=false) fmt (e, c, r) =
    fprintf fmt "@[<h>unless %s %s %s@]"
      (string_of_expr ~print_anns e)
      (if r then "then" else "continue") c

  let print_unlesss ?(print_anns=false) fmt unl =
    if unl <> [] then
      fprintf fmt "@[<v>%a;@]@;" (print_semicol_list (print_unless ~print_anns)) unl

  let print_until ?(print_anns=false) fmt (e, c, r) =
    fprintf fmt "@[<h>until %s %s %s@]"
      (string_of_expr ~print_anns e)
      (if r then "then" else "continue") c

  let print_untils ?(print_anns=false) fmt unt =
    if unt <> [] then
      fprintf fmt "@;@[<v>%a;@]" (print_semicol_list (print_until ~print_anns)) unt

  let rec print_instr ?(print_anns=false) fmt i =
    match i.pinstr_desc with
    | Eq eq -> fprintf fmt "%s" (string_of_equation ~print_anns eq)
    | Block bck -> print_block ~print_anns fmt bck
    | Reset (ins, er) ->
      fprintf fmt "@[<v 2>\
                   reset@;\
                   @[<v>%a@;<0 -2>@]\
                   every %s@]\
                  "
        (print_instrs ~print_anns) ins
        (string_of_expr ~print_anns er)
    | Switch (e, branches, (ckid, _)) ->
      fprintf fmt "@[<v 0>\
                   switch %s@;\
                   %a@;\
                   end@]"
        (string_of_expr ~print_anns e)
        (pp_print_list (print_switch_branch ~print_anns)) branches
    | Automaton (branches, _) ->
      fprintf fmt "@[<v 0>\
                   automaton@;\
                   %a@;\
                   end@]"
        (pp_print_list (print_auto_branch ~print_anns)) branches
  and print_instrs ?(print_anns=false) fmt ins =
    print_semicol_list (print_instr ~print_anns) fmt ins

  and print_switch_branch ?(print_anns=false) fmt (constr, ins) =
    fprintf fmt "@[<hv 2>\
                 | %s ->@;\
                 %a@]"
      constr
      (print_instrs ~print_anns) ins

  and print_auto_branch ?(print_anns=false) fmt (constr, unl, ins, unt) =
    fprintf fmt "@[<v 2>\
                 | %s ->@;\
                 %a%a%a@]"
      constr
      (print_unlesss ~print_anns) unl
      (print_instrs ~print_anns) ins
      (print_untils ~print_anns) unt

  and print_block fmt ?(print_anns=false) bck =
    fprintf fmt "@[%a\
                 @[<v 2>let@;%a@;<0 -2>@]\
                 tel@]"
      print_locals bck.pb_local
      (print_instrs ~print_anns) bck.pb_instrs

  let print_node ?(print_anns=false) fmt n =
    fprintf fmt "@[<v>\
                 @[<hov 0>\
                 @[<h>node %a (%a)@]@;\
                 @[<h>returns (%a)@]@;\
                 @]@;\
                 %a\
                 @]"
      print_ident n.pn_name
      print_decl_list n.pn_input
      print_decl_list n.pn_output
      (print_block ~print_anns) n.pn_body

  let print_clock_decl fmt decl =
    fprintf fmt "%s" (string_of_clockdec decl)

  let print_file ?(print_anns=false) fmt file =
    fprintf fmt "@[<v 0>%a%a%a@]@."
      (pp_print_list ~pp_sep:(fun p () -> fprintf fmt "@;@;") print_clock_decl) file.pf_clocks
      (fun fmt _ -> if file.pf_clocks <> [] then fprintf fmt "@;@;" else fprintf fmt "") ()
      (pp_print_list ~pp_sep:(fun p () -> fprintf fmt "@;@;") (print_node ~print_anns)) file.pf_nodes
end

module PMinils = PMINILS(NoAnnot)
