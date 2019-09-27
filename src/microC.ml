(** Representation of a subset of the C language, used for code generation *)

open Asttypes

type ty =
  | Tvoid
  | Tint | Tfloat
  | Tident of ident
  | Tpointer of ty

let rec string_of_ty = function
  | Tvoid -> "void"
  | Tint -> "int" | Tfloat -> "float"
  | Tident id -> id
  | Tpointer ty -> Printf.sprintf "%s*" (string_of_ty ty)

type const =
  | Int of int | Float of float

let string_of_const = function
  | Int i -> string_of_int i
  | Float f -> string_of_float f

type structdef = {
  struct_name : ident;
  struct_fields : (ident * ty) list;
}

let string_of_structdef (stdef : structdef) =
  Printf.sprintf "typedef struct {\n\
                 \t%s\n\
                 } %s;\n"
    (String.concat "\n\t"
       (List.map (fun (id, ty) -> (string_of_ty ty)^" "^id^";")
          stdef.struct_fields))
    stdef.struct_name

type lhs =
  | Ident of ident
  | PField of ident * ident

let string_of_lhs = function
  | Ident id -> id
  | PField (st, id) -> Printf.sprintf "%s->%s" st id

type expr =
  | Const of const
  | Ident of ident
  | Ref of expr
  | Field of expr * ident
  | PField of ident * ident
  | BinOp of (expr * op * expr)
  | UnOp of (op * expr)
  | If of (expr * expr * expr)

let string_of_cop = function
  | Op_eq -> "=" | Op_neq -> "!=" | Op_lt -> "<" | Op_le -> "<="
  | Op_gt -> ">" | Op_ge -> ">="
  | Op_add -> "+" | Op_sub -> "-" | Op_mul -> "*" | Op_div -> "/" | Op_mod -> "%"
  | Op_not -> "~" | Op_and -> "&" | Op_or -> "|" | Op_xor -> "^"
  | Op_if -> invalid_arg "string_of_cop"

let rec string_of_expr = function
  | Const c -> string_of_const c
  | Ident id -> id
  | Ref e -> "&"^(string_of_expr e)
  | Field (e, field) ->
    Printf.sprintf "%s.%s" (string_of_expr e) field
  | PField (id, field) -> id^"->"^field
  | BinOp (e1, op, e2) ->
    Printf.sprintf "(%s %s %s)" (string_of_expr e1)
      (string_of_cop op) (string_of_expr e2)
  | UnOp (op, e) ->
    Printf.sprintf "(%s %s)" (string_of_cop op) (string_of_expr e)
  | If (c, t, e) ->
    Printf.sprintf "(%s ? %s : %s)"
      (string_of_expr c) (string_of_expr t) (string_of_expr e)

type instr =
  | Assign of lhs * expr
  | If of expr * instr list * instr list
  | Call of ident * expr list
  | VarDec of ty * ident

let rec string_of_instr (indent_level : int) (i : instr) =
  let indent = String.make indent_level '\t' in
  match i with
  | Assign (l, e) ->
    Printf.sprintf "%s%s = %s;" indent (string_of_lhs l) (string_of_expr e)
  | If (c, t, e) ->
    Printf.sprintf "%sif (%s) {\n\
                    %s\n\
                    %s} else {\n\
                    %s\n\
                    %s}"
      indent (string_of_expr c)
      (String.concat "\n" (List.map (string_of_instr (indent_level + 1)) t))
      indent
      (String.concat "\n" (List.map (string_of_instr (indent_level + 1)) e))
      indent
  | Call (id, es) ->
    Printf.sprintf "%s%s(%s);" indent id
      (String.concat "," (List.map string_of_expr es))
  | VarDec (ty, id) ->
    Printf.sprintf "%s%s %s;" indent (string_of_ty ty) id

type fundef = {
  fun_name : ident;
  fun_ret : ty;
  fun_args : (ident * ty) list;
  fun_body : instr list;
}

let string_of_fundef (f : fundef) =
  Printf.sprintf "%s %s(%s) {\n %s\n}\n"
    (string_of_ty f.fun_ret) f.fun_name
    (String.concat ", "
       (List.map (fun (id, ty) -> (string_of_ty ty)^" "^id) f.fun_args))
    (String.concat "\n" (List.map (string_of_instr 1) f.fun_body))

type def =
  | Struct of structdef
  | Fun of fundef

let string_of_def = function
  | Struct std -> string_of_structdef std
  | Fun fd -> string_of_fundef fd

type file = def list

let string_of_file (f : file) =
  String.concat "\n" (List.map string_of_def f)
