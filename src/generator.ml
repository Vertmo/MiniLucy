(** Code generator *)

open Asttypes
open Obc
open MicroC

(** Translate a Lustre type to a C type.
    Doesn't work on tuples (they shouldn't be encountered anyway) *)
let ty_of_base_ty : base_ty -> MicroC.ty = function
  | Tint | Tbool -> Tint
  | Treal -> Tfloat
  | Ttuple _ -> invalid_arg "ty_of_base_ty"

(** Translate a Lustre const to a C const *)
let generate_const : Asttypes.const -> MicroC.const = function
  | Cint i -> Int i
  | Cbool b -> if b then Int 1 else Int 0
  | Creal f -> Float f

(** Generate code for an expression *)
let rec generate_expr outputs : Obc.expr -> MicroC.expr = function
  | Const c -> Const (generate_const c)
  | Ident id -> if List.mem_assoc id outputs
    then PField ("_out", id)
    else Ident id
  | StIdent id -> PField ("_self", id)
  | Op (op, es) ->
    let ges = List.map (generate_expr outputs) es in
    if List.length ges = 1 then
      UnOp (op, List.nth ges 0)
    else if List.length ges = 2 then
      BinOp (List.nth ges 0, op, List.nth ges 1)
    else If (List.nth ges 0, List.nth ges 1, List.nth ges 2)

(** Generate code for an instruction *)
let rec generate_instr instances outputs : Obc.instr -> MicroC.instr list =
  function
  | Assign (id, e) ->
    if (List.mem_assoc id outputs)
    then [Assign (PField ("_out", id), generate_expr outputs e)]
    else [Assign (Ident id, generate_expr outputs e)]
  | StAssign (id, e) ->
    [Assign (PField ("_self", id), generate_expr outputs e)]
  | Reset iid -> [Call (fst (List.assoc iid instances)^"_reset",
                       [Ref (PField ("_self", iid))])]
  | StepAssign (ids, iid, es) ->
    let ges = List.map (generate_expr outputs) es in
    let (fid, oids) = List.assoc iid instances in
    let tmp = Atom.fresh ("_out_"^fid) in
    [VarDec (Tident (fid^"_out"), tmp);
     (Call (fid^"_step", ges@[Ref (PField ("_self", iid));
                              Ref (Ident tmp)]))]@
    (List.map2 (fun id oid ->
         let e = Field (Ident tmp, oid) in
         if (List.mem_assoc id outputs)
         then Assign (PField ("_out", id), e)
         else Assign (Ident id, e)) ids oids)
  | Case (id, t, e) ->
    [If (Ident id,
         List.flatten (List.map (generate_instr instances outputs) t),
         List.flatten (List.map (generate_instr instances outputs) e))]

(** Generate code for a machine *)
let generate_machine (m : machine) : def list =
  let (inputs, outputs, locals, step_body) = m.m_step in
  let st_mem = {
    struct_name = m.m_name^"_mem";
    struct_fields =
      (List.map (fun (id, ty) -> id, (ty_of_base_ty ty)) m.m_memory)@
      (List.map (fun (o, (f, _)) -> o, (Tident (f^"_mem")))
         m.m_instances)
  }
  and st_out = {
    struct_name = m.m_name^"_out";
    struct_fields =
      (List.map (fun (id, ty) -> id, (ty_of_base_ty ty)) outputs)
  }
  and fun_reset = {
    fun_name = m.m_name^"_reset";
    fun_ret = Tvoid;
    fun_args = ["_self", Tpointer (Tident (m.m_name^"_mem"))];
    fun_body = List.flatten
        (List.map (generate_instr m.m_instances outputs) m.m_reset);
  }
  and fun_step = {
    fun_name = m.m_name^"_step";
    fun_ret = Tvoid;
    fun_args =
      (List.map (fun (id, ty) -> (id, ty_of_base_ty ty)) inputs)@
      [("_self", Tpointer (Tident (m.m_name^"_mem")));
       ("_out", Tpointer (Tident (m.m_name^"_out")))];
    fun_body =
      (List.map (fun (id, ty) -> VarDec (ty_of_base_ty ty, id)) locals)@
      (List.flatten
         (List.map (generate_instr m.m_instances outputs) step_body))
  } in
  [Struct st_mem; Struct st_out;
   Fun fun_reset; Fun fun_step]

(** Generate code for a whole file *)
let generate_file (f : Obc.file) : MicroC.file =
  List.concat (List.map generate_machine f)

(*                           Check equivalence between ASTs                    *)
(* TODO *)
