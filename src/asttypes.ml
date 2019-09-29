type location = Lexing.position * Lexing.position

type ident = string
type constr = string

let string_of_loc ((ls, le):location) =
  Printf.sprintf "[(%d,%d);(%d,%d)]"
    ls.pos_lnum (ls.pos_cnum - ls.pos_bol)
    le.pos_lnum (le.pos_cnum - le.pos_bol)

type base_ty =
  | Tbool
  | Tint
  | Treal
  | Tclock of ident
  | Ttuple of base_ty list

let rec string_of_base_ty = function
  | Tbool -> "bool"
  | Tint -> "int"
  | Treal -> "real"
  | Tclock id -> id
  | Ttuple tys -> Printf.sprintf "(%s)"
                    (String.concat "," (List.map string_of_base_ty tys))

type ty =
  | Base of base_ty
  | Clocked of base_ty * constr * ident

let string_of_ty = function
  | Base bty -> string_of_base_ty bty
  | Clocked (bty, constr, id) ->
    Printf.sprintf "%s when %s(%s)"
      (string_of_base_ty bty) constr id

let base_ty_of_ty : ty -> base_ty = function
  | Base t | Clocked (t, _, _) -> t

type clock =
  | Base
  | Cl of clock * constr * ident
  | Ctuple of clock list

let clock_of_ty : ty -> clock = function
  | Base _ -> Base
  | Clocked (_, constr, id) ->
    Cl (Base, constr, id)

let rec string_of_clock = function
  | Base -> "base"
  | Cl (base, constr, id) ->
    Printf.sprintf "(%s on %s(%s))" (string_of_clock base) constr id
  | Ctuple cls ->
    Printf.sprintf "(%s)" (String.concat "," (List.map string_of_clock cls))

(** Get the "variables" of a clock *)
let rec clock_vars = function
  | Base -> []
  | Cl (cl, _, id) -> id::(clock_vars cl)
  | Ctuple cls ->
    List.concat (List.map clock_vars cls)

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
