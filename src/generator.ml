(** Code generator *)

open Common
open Obc
open MicroC

(** Translate a Lustre type to a C type.
    Doesn't work on tuples (they shouldn't be encountered anyway) *)
let ty_of_ty : Common.ty -> MicroC.ty = function
  | Tint | Tbool -> Tint
  | Treal -> Tfloat
  | Tclock id -> Tenum ("_clock_"^id)

(** Translate a Lustre const to a C const *)
let generate_const : Common.const -> MicroC.const = function
  | Cint i -> Int i
  | Cbool b -> if b then Int (lnot 0) else Int 0
  | Creal f -> Float f
  | Cconstr (c, clty) ->
    EnumField (Printf.sprintf "_clock_%s_%s" clty c)

(** Generate code for a clock declaration *)
let generate_clockdec (id, constrs) =
  Enum ("_clock_"^id,
        List.map (fun c -> Printf.sprintf "_clock_%s_%s" id c) constrs)

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
let rec generate_instr instances tys outputs : Obc.instr -> MicroC.instr list =
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
    (Call (fid^"_step", ges@[Ref (PField ("_self", (iid)));
                             Ref (PField ("_self", (iid^"_out")))]))::
    (List.map2 (fun id oid ->
         let e = Field ((PField ("_self", (iid^"_out"))), oid) in
         if (List.mem_assoc id outputs)
         then Assign (PField ("_out", id), e)
         else Assign (Ident id, e)) ids oids)
  | Case (e, ty, is) ->
    let constrs = List.map fst is in
    if constrs = [ctrue;cfalse]
    then [If (generate_expr outputs e,
              List.flatten (List.map (generate_instr instances tys outputs)
                              (snd (List.nth is 0))),
              List.flatten (List.map (generate_instr instances tys outputs)
                              (snd (List.nth is 1))))]
    else if constrs = [cfalse;ctrue]
    then [If (generate_expr outputs e,
              List.flatten (List.map (generate_instr instances tys outputs)
                              (snd (List.nth is 1))),
              List.flatten (List.map (generate_instr instances tys outputs)
                              (snd (List.nth is 0))))]
    else if constrs = [ctrue]
    then [If (generate_expr outputs e,
              List.flatten (List.map (generate_instr instances tys outputs)
                              (snd (List.hd is))), [])]
    else if constrs = [cfalse]
    then [If (generate_expr outputs e, [],
              List.flatten (List.map (generate_instr instances tys outputs)
                              (snd (List.hd is))))]
    else
      let clid = (match ty with
          | Tclock id -> id
          | _ -> failwith (Printf.sprintf "Should not happen %s" (Common.string_of_ty ty))) in
      [SwitchCase (generate_expr outputs e,
                   List.map (fun (c, i) ->
                       Printf.sprintf "_clock_%s_%s" clid c,
                       List.flatten (List.map (generate_instr instances tys outputs) i)) is)]

(** Generate code for a machine *)
let generate_machine (m : machine) : def list =
  let (inputs, outputs, locals, step_body) = m.m_step in
  let tys = inputs@outputs@locals in
  let st_mem = {
    struct_name = m.m_name^"_mem";
    struct_fields =
      (List.map (fun (id, ty) -> id, (ty_of_ty ty)) m.m_memory)@
      (List.map (fun (o, (f, _)) -> o, (Tident (f^"_mem")))
         m.m_instances)@
      (List.map (fun (o, (f, _)) -> (o^"_out"), (Tident (f^"_out")))
         m.m_instances)
  }
  and st_out = {
    struct_name = m.m_name^"_out";
    struct_fields =
      (List.map (fun (id, ty) -> id, (ty_of_ty ty)) outputs)
  }
  and fun_reset = {
    fun_name = m.m_name^"_reset";
    fun_ret = Tvoid;
    fun_args = ["_self", Tpointer (Tident (m.m_name^"_mem"))];
    fun_body = List.flatten
        (List.map (generate_instr m.m_instances tys outputs) m.m_reset);
  }
  and fun_step = {
    fun_name = m.m_name^"_step";
    fun_ret = Tvoid;
    fun_args =
      (List.map (fun (id, ty) -> (id, ty_of_ty ty)) inputs)@
      [("_self", Tpointer (Tident (m.m_name^"_mem")));
       ("_out", Tpointer (Tident (m.m_name^"_out")))];
    fun_body =
      (List.map (fun (id, ty) -> VarDec (ty_of_ty ty, id)) locals)@
      (List.flatten
         (List.map (generate_instr m.m_instances tys outputs) step_body))
  } in
  [Struct st_mem; Struct st_out;
   Fun fun_reset; Fun fun_step]

(** Generate code for a whole file *)
let generate_file (f : Obc.file) : MicroC.file =
  (List.map generate_clockdec f.clocks)@
  (List.concat (List.map generate_machine f.machines))
