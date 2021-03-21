type location = Lexing.position * Lexing.position
let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

type ident = string
type constr = string
let ctrue = "True" and cfalse = "False"

let string_of_loc ((ls, le):location) =
  Printf.sprintf "[(%d,%d);(%d,%d)]"
    ls.pos_lnum (ls.pos_cnum - ls.pos_bol)
    le.pos_lnum (le.pos_cnum - le.pos_bol)

type ty =
  | Tbool
  | Tint
  | Treal
  | Tclock of ident

let rec string_of_ty = function
  | Tbool -> "bool"
  | Tint -> "int"
  | Treal -> "real"
  | Tclock id -> id

and string_of_tys tys =
  Printf.sprintf "(%s)" (String.concat "," (List.map string_of_ty tys))

type clock =
  | Cbase
  | Con of constr * ident * clock

let rec string_of_clock = function
  | Cbase -> "."
  | Con (constr, id, ck) ->
    Printf.sprintf "(%s on %s(%s))" (string_of_clock ck) constr id

(** Get the "variables" of a clock *)
let rec clock_vars = function
  | Cbase -> []
  | Con (_, id, ck) -> id::(clock_vars ck)

type ann = (ty * clock)

let string_of_ann (ty, ck) =
  Printf.sprintf "%s :: %s" (string_of_ty ty) (string_of_clock ck)

type const =
  | Cbool of bool
  | Cint of int
  | Creal of float
  | Cconstr of constr * ident (* constructor * clock type identifier *)

let string_of_const = function
  | Cbool b -> if b then "true" else "false"
  | Cint i -> string_of_int i
  | Creal f -> string_of_float f
  | Cconstr (c, _) -> c

type op =
  | Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge
  | Op_add | Op_sub | Op_mul | Op_div | Op_mod
  | Op_not
  | Op_and | Op_or | Op_xor

let string_of_op = function
  | Op_eq -> "=" | Op_neq -> "<>"
  | Op_lt -> "<" | Op_le -> "<="
  | Op_gt -> ">" | Op_ge -> ">="
  | Op_add -> "+" | Op_sub -> "-"
  | Op_mul -> "*" | Op_div -> "/" | Op_mod -> "mod"
  | Op_not -> "not" | Op_and -> "and"
  | Op_or -> "or" | Op_xor -> "xor"

let string_of_ident_ann_list l =
  String.concat "; " (List.map (fun (id, ann) ->
      Printf.sprintf "%s : %s" id (string_of_ann ann)) l)

(** Clock declaration *)
type clockdec = ident * constr list

let string_of_clockdec (clid, constrs) =
  Printf.sprintf "type %s = %s;"
    clid (String.concat " + " constrs)

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
