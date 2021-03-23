type location = Lexing.position * Lexing.position
let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

type ident = string
type constr = string
let ctrue = "True" and cfalse = "False"

type ty =
  | Tbool
  | Tint
  | Treal
  | Tclock of ident

type clock =
  | Cbase
  | Con of constr * ident * clock

(** Get the "variables" of a clock *)
let rec clock_vars = function
  | Cbase -> []
  | Con (_, id, ck) -> id::(clock_vars ck)

type ann = (ty * clock)

type const =
  | Cbool of bool
  | Cint of int
  | Creal of float
  | Cconstr of constr * ident (* constructor * clock type identifier *)

type op =
  | Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge
  | Op_add | Op_sub | Op_mul | Op_div | Op_mod
  | Op_not
  | Op_and | Op_or | Op_xor

(** Clock declaration *)
type clockdec = ident * constr list

(* Some printers *)

open Format

let print_col_list p =
  pp_print_list ~pp_sep:(fun p () -> fprintf p ",@ ") p

let print_semicol_list p =
  pp_print_list ~pp_sep:(fun p () -> fprintf p ";@ ") p

let print_ident = pp_print_string

let print_loc fmt ((ls, le):location) =
  fprintf fmt "[(%d,%d);(%d,%d)]"
    ls.pos_lnum (ls.pos_cnum - ls.pos_bol)
    le.pos_lnum (le.pos_cnum - le.pos_bol)
let string_of_loc loc =
  print_loc Format.str_formatter loc;
  Format.flush_str_formatter ()

let print_ty fmt = function
  | Tbool -> fprintf fmt "bool"
  | Tint -> fprintf fmt "int"
  | Treal -> fprintf fmt "real"
  | Tclock id -> print_ident fmt id
let string_of_ty ty =
  print_ty str_formatter ty;
  flush_str_formatter ()

let print_tys fmt tys =
  fprintf fmt "(%a)" (print_col_list print_ty) tys
let string_of_tys tys =
  print_tys str_formatter tys;
  flush_str_formatter ()

let print_const fmt = function
  | Cbool b -> fprintf fmt "%s" (if b then "true" else "false")
  | Cint i -> fprintf fmt "%d" i
  | Creal f -> fprintf fmt "%f" f
  | Cconstr (c, _) -> print_ident fmt c

let rec print_clock fmt = function
  | Cbase -> fprintf fmt "."
  | Con (constr, id, ck) ->
    fprintf fmt "(%a on %s(%s))" print_clock ck constr id
let string_of_clock ck =
  print_clock str_formatter ck;
  flush_str_formatter ()

let print_ann fmt (ty, ck) =
  fprintf fmt "%a :: %a" print_ty ty print_clock ck

let string_of_op = function
  | Op_eq -> "=" | Op_neq -> "<>"
  | Op_lt -> "<" | Op_le -> "<="
  | Op_gt -> ">" | Op_ge -> ">="
  | Op_add -> "+" | Op_sub -> "-"
  | Op_mul -> "*" | Op_div -> "/" | Op_mod -> "mod"
  | Op_not -> "not" | Op_and -> "and"
  | Op_or -> "or" | Op_xor -> "xor"

let print_decl fmt (id, ann) =
  fprintf fmt "@[<h>%a@ : %a@]"
    print_ident id
    print_ann ann

let print_decl_list = print_semicol_list print_decl

let print_clock_decl fmt (ckid, constrs) =
  fprintf fmt "@[<h>type %s = %a@]"
    ckid
    (pp_print_list ~pp_sep:(fun p () -> fprintf p "@ +@ ") print_ident) constrs

(** Generation of fresh variables *)
module Atom = struct
  let counter : int ref = ref 0
  let fresh (s:string) =
    counter := !counter+1; Printf.sprintf "%s%d" s !counter
end

(** Remove one element from a list *)
let rec remove_one x = function
  | [] -> []
  | hd::tl when hd = x -> tl
  | hd::tl -> hd::(remove_one x tl)

type step =
  | Parse
  | Last | Automaton | Reset | Switch | Block
  | Check
  | Norm
  | Sched
  | Translate
  | Generate

exception Done
