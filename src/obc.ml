(* Object code AST *)

open Common

type expr =
  | Const of const
  | Ident of ident
  | StIdent of ident
  | Op of op * expr list

type instr =
  | Assign of (ident * expr)
  | StAssign of (ident * expr)
  | Reset of ident
  | StepAssign of (ident list * ident * expr list)
  | Case of expr * ty * (constr * instr list) list

type p = (ident * ty) list

type machine = {
  m_name: ident;
  m_memory: p;
  m_instances: (ident * (ident * (ident list))) list;
  m_reset: instr list;
  (* input, output, locals, body *)
  m_step : p * p * p * instr list;
}

type file =
  { clocks : clockdec list;
    machines : machine list }

(** Check if the instruction assigns the state *)
let rec updates_state = function
  | Assign _ -> false
  | StAssign (_, Const _) -> false
  | StAssign _ -> true
  | Reset _ -> false
  | StepAssign _ -> false
  | Case (_, _, instrs) ->
    List.exists (fun (_, ins) -> List.exists updates_state ins) instrs

open Format

let rec print_expr fmt = function
  | Const c -> print_const fmt c
  | Ident id -> print_ident fmt id
  | StIdent id -> fprintf fmt "state(%s)" id
  | Op (op, es) -> fprintf fmt "(%s [%a])"
                     (string_of_op op)
                     (print_col_list print_expr) es

let rec print_instr fmt ins =
  match ins with
  | Assign (id, e) ->
    fprintf fmt "@[<hov 2>%s := %a@]"
      id print_expr e
  | StAssign (id, e) ->
    fprintf fmt "@[<hov 2>state(%s) := %a@]"
      id print_expr e
  | Reset id ->
    fprintf fmt "@[<h>%s.reset@]" id
  | StepAssign (ids, fid, es) ->
    fprintf fmt "(%a) := %s.step(%a)"
      (print_col_list print_ident) ids
      fid
      (print_col_list print_expr) es
  | Case (e, _, brs) ->
    fprintf fmt "@[<v 2>case(%a) {@;%a@;<0 -2>}@]"
      print_expr e
      (pp_print_list ~pp_sep:(fun p () -> fprintf p "@;") print_branch) brs

and print_instrs fmt = print_semicol_list print_instr fmt
and print_branch fmt (x, instrs) =
  fprintf fmt "@[<v 2>%s:@;%a@]" x print_instrs instrs

let print_p fmt (id, ty) =
  fprintf fmt "%s:%a" id print_ty ty

let print_instance fmt (o, (f, _)) =
  fprintf fmt "@[<h>%s : %s@]" o f

let print_machine fmt m =
  let (input, output, vars, instrs) = m.m_step in
  fprintf fmt "@[<v 2>machine %s =@;\
               @[<hov 2>memory %a@]@;\
               @[<hov 2>instances %a@]@;\
               @[<v 2>reset () =@;%a@]@;\
               @[<v 2>step (@[<h>%a@]) returns (@[<h>%a@]) =@;\
               var (@[<hov 2>%a@]) in@;\
               %a@]@]"
    m.m_name
    (print_semicol_list print_p) m.m_memory
    (print_semicol_list print_instance) m.m_instances
    print_instrs m.m_reset
    (print_semicol_list print_p) input
    (print_semicol_list print_p) output
    (print_semicol_list print_p) vars
    print_instrs instrs

let print_file fmt file =
  fprintf fmt "@[<v 0>%a%a%a@]@."
    (pp_print_list ~pp_sep:(fun p () -> fprintf p "@;@;") print_clock_decl) file.clocks
    (fun fmt _ -> if file.clocks <> [] then fprintf fmt "@;@;" else fprintf fmt "") ()
    (pp_print_list ~pp_sep:(fun p () -> fprintf p "@;@;") print_machine) file.machines
