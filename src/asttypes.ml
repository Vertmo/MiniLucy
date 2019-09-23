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
  (* The third parameter indicated whether the clock is negated *)

let string_of_ty = function
  | Base bty -> string_of_base_ty bty
  | Clocked (bty, id, neg) ->
    Printf.sprintf (if neg then "%s when not %s" else "%s when %s")
      (string_of_base_ty bty) id

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
