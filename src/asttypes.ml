type location = Lexing.position * Lexing.position

type ident = string

let string_of_loc ((ls, le):location) =
  Printf.sprintf "[(%d,%d);(%d,%d)]"
    ls.pos_lnum ls.pos_cnum le.pos_lnum le.pos_cnum

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
  | Op_add_f | Op_sub_f | Op_mul_f | Op_div_f
  | Op_not
  | Op_and | Op_or | Op_xor | Op_impl
  | Op_if

let string_of_op = function
  | Op_eq -> "=" | Op_neq -> "<>"
  | Op_lt -> "<" | Op_le -> "<="
  | Op_gt -> ">" | Op_ge -> ">="
  | Op_add | Op_add_f -> "+" | Op_sub | Op_sub_f -> "-"
  | Op_mul | Op_mul_f -> "*"
  | Op_div | Op_div_f -> "/" | Op_mod -> "mod"
  | Op_not -> "not" | Op_and -> "and"
  | Op_or -> "or" | Op_xor -> "xor"
  | Op_impl -> "=>"
  | Op_if -> "if"
