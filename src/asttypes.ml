type location = Lexing.position * Lexing.position

type ident = string

let string_of_loc ((ls, le):location) =
  Printf.sprintf "[(%d,%d);(%d,%d)]"
    ls.pos_lnum (ls.pos_cnum - ls.pos_bol)
    le.pos_lnum (le.pos_cnum - le.pos_bol)

type base_ty =
  | Tbool
  | Tint
  | Treal

let string_of_base_ty = function
  | Tbool -> "bool"
  | Tint -> "int"
  | Treal -> "real"

type ty =
  | Base of base_ty
  | Clocked of base_ty * ident * bool

let string_of_ty = function
  | Base bty -> string_of_base_ty bty
  | Clocked (bty, id, b) ->
    Printf.sprintf (if b then "%s when %s" else "%s when not %s")
      (string_of_base_ty bty) id

type clock =
  | Base
  | Cl of clock * ident (* Clock *)
  | NotCl of clock * ident (* Negated clock *)
  | Ctuple of clock list

let clock_of_ty : ty -> clock = function
  | Base _ -> Base
  | Clocked (_, cl, b) ->
    if b then Cl (Base, cl) else NotCl (Base, cl)

let rec string_of_clock = function
  | Base -> "base"
  | Cl (base, cl) ->
    Printf.sprintf "(%s on %s)" (string_of_clock base) cl
  | NotCl (base, cl) ->
    Printf.sprintf "(%s on not %s)" (string_of_clock base) cl
  | Ctuple cls ->
    Printf.sprintf "(%s)" (String.concat "," (List.map string_of_clock cls))

type const =
  | Cbool of bool
  | Cint of int
  | Creal of float

let string_of_const = function
  | Cbool b -> if b then "true" else "false"
  | Cint i -> string_of_int i
  | Creal f -> string_of_float f

type op =
  | Op_eq | Op_neq | Op_lt | Op_le | Op_gt | Op_ge
  | Op_add | Op_sub | Op_mul | Op_div | Op_mod
  | Op_not
  | Op_and | Op_or | Op_xor
  | Op_if

let string_of_op = function
  | Op_eq -> "=" | Op_neq -> "<>"
  | Op_lt -> "<" | Op_le -> "<="
  | Op_gt -> ">" | Op_ge -> ">="
  | Op_add -> "+" | Op_sub -> "-"
  | Op_mul -> "*" | Op_div -> "/" | Op_mod -> "mod"
  | Op_not -> "not" | Op_and -> "and"
  | Op_or -> "or" | Op_xor -> "xor"
  | Op_if -> "if"

let string_of_ident_type_list l =
  String.concat "; " (List.map (fun (id, t) ->
      Printf.sprintf "%s:%s" id (string_of_ty t)) l)
