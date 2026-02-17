(* =========================================================================
   WebAssembly Operational Semantics (Index-Referencing Instructions)

   This module defines evaluation semantics for the ~15 WASM instructions
   that reference module-level index spaces (functions, globals, tables,
   elements, data segments). These are exactly the instructions affected
   by fusion's index remapping (see instr_rewrites in fusion_spec.v).

   Non-index instructions are modeled abstractly via Eval_Pure: any
   state transition is valid. This captures that fusion doesn't affect
   their behavior while avoiding a full WASM interpreter.

   Key design: module_state already has ms_funcs, ms_tables, ms_mems,
   ms_globals — these ARE the index-to-instance mappings. eval_instr
   looks up entities via nth_error on these lists, grounding the proof
   in real index lookups rather than abstract effects.
   ========================================================================= *)

From Stdlib Require Import List ZArith Bool Lia.
From MeldSpec Require Import wasm_core.
Import ListNotations.

(* -------------------------------------------------------------------------
   Runtime Values

   Values on the operand stack. Constructor names I32/I64/F32/F64 shadow
   numtype constructors. VRefNull/VRefFunc are prefixed to avoid shadowing
   the instr constructors RefNull/RefFunc.
   ------------------------------------------------------------------------- *)

Inductive wasm_value : Type :=
  | I32 (n : Z)
  | I64 (n : Z)
  | F32 (f : Z)  (* Simplified: actual IEEE 754 floats are complex *)
  | F64 (f : Z)
  | VRefNull (rt : reftype)
  | VRefFunc (addr : nat).

(* -------------------------------------------------------------------------
   Runtime Instances

   Simplified models of WASM runtime instances, sufficient for reasoning
   about index space access patterns.
   ------------------------------------------------------------------------- *)

(* Memory instance: byte array with optional max *)
Record memory_inst : Type := mkMemoryInst {
  mem_data : list nat;  (* Byte values 0..255 *)
  mem_max : option nat;
}.

(* Table instance: array of optional function references *)
Record table_inst : Type := mkTableInst {
  tab_elem : list (option nat);  (* Function addresses *)
  tab_max : option nat;
}.

(* Global instance: mutable or immutable value *)
Record global_inst : Type := mkGlobalInst {
  glob_value : wasm_value;
  glob_mut : mutability;  (* Shadows globaltype.glob_mut; disambiguated by type *)
}.

(* -------------------------------------------------------------------------
   Module State

   Runtime state of a module instance. The index lists (ms_funcs, etc.)
   map local indices to runtime entities — exactly what eval_instr
   looks up when executing index-referencing instructions.
   ------------------------------------------------------------------------- *)

Record module_state : Type := mkModuleState {
  ms_funcs : list nat;            (* Function addresses *)
  ms_tables : list table_inst;    (* Table instances *)
  ms_mems : list memory_inst;     (* Memory instances *)
  ms_globals : list global_inst;  (* Global instances *)
  ms_elems : list (list (option nat));  (* Element segments *)
  ms_datas : list (list nat);           (* Data segments *)
  ms_locals : list wasm_value;    (* Local variables for current frame *)
  ms_value_stack : list wasm_value; (* Operand stack *)
}.

(* -------------------------------------------------------------------------
   State Update Helpers

   Each helper updates specific fields of module_state while preserving
   others. The preservation properties are used extensively in the
   forward simulation proof.
   ------------------------------------------------------------------------- *)

(* Replace a list element at index n. No-op if out of bounds. *)
Fixpoint update_nth {A : Type} (l : list A) (n : nat) (x : A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: rest, O => x :: rest
  | h :: rest, S n' => h :: update_nth rest n' x
  end.

(* Replace the value stack, preserving all other fields *)
Definition set_stack (ms : module_state) (new_stack : list wasm_value)
  : module_state :=
  mkModuleState
    (ms_funcs ms) (ms_tables ms) (ms_mems ms) (ms_globals ms)
    (ms_elems ms) (ms_datas ms)
    (ms_locals ms) new_stack.

(* Update a global's value at the given index, preserving mutability *)
Definition update_global_value (globals : list global_inst)
                               (idx : nat) (v : wasm_value)
  : list global_inst :=
  match nth_error globals idx with
  | Some g => update_nth globals idx (mkGlobalInst v (glob_mut g))
  | None => globals
  end.

(* Pop value from stack and update a global *)
Definition set_stack_and_global (ms : module_state)
    (new_stack : list wasm_value) (globalidx : nat) (v : wasm_value)
  : module_state :=
  mkModuleState
    (ms_funcs ms) (ms_tables ms) (ms_mems ms)
    (update_global_value (ms_globals ms) globalidx v)
    (ms_elems ms) (ms_datas ms)
    (ms_locals ms) new_stack.

(* -------------------------------------------------------------------------
   Instruction Classifier

   is_pure_instr returns true for Category B instructions: those that
   do NOT reference module-level index spaces. These are handled by
   Eval_Pure with abstract state transitions.

   Category A instructions (returning false) have concrete eval_instr
   rules that verify the index lookup.
   ------------------------------------------------------------------------- *)

Definition is_pure_instr (i : instr) : bool :=
  match i with
  (* Control flow: no module-level index references *)
  | Nop | Unreachable | Return | Drop => true
  | Br _ | BrIf _ | BrTable _ _ => true
  | Block _ _ | Loop _ _ | If _ _ _ => true
  | Select _ => true
  (* Locals: local indices, not module-level *)
  | LocalGet _ | LocalSet _ | LocalTee _ => true
  (* Memory: in single-memory mode, no index needed *)
  | MemorySize | MemoryGrow => true
  | Load _ _ _ | Store _ _ _ => true
  | MemoryCopy | MemoryFill => true
  (* Numeric: no indices *)
  | NumericOp _ => true
  (* Reference null/check: no index lookup *)
  | RefNull _ | RefIsNull => true
  (* --- Category A: index-referencing --- *)
  | Call _ | CallIndirect _ _ => false
  | GlobalGet _ | GlobalSet _ => false
  | RefFunc _ => false
  | TableGet _ | TableSet _ => false
  | TableSize _ | TableGrow _ | TableFill _ => false
  | TableCopy _ _ | TableInit _ _ => false
  | ElemDrop _ => false
  | MemoryInit _ | DataDrop _ => false
  end.

(* -------------------------------------------------------------------------
   Instruction Evaluation Relation

   eval_instr ms i ms' means: executing instruction i in state ms
   produces state ms'.

   Category A rules concretely verify index lookups via nth_error.
   This is what makes the forward simulation non-tautological: we
   prove that remapped indices access the SAME runtime entities.

   Some instructions (Call, TableGet, etc.) have abstract result
   stacks because we don't model full execution — only the index
   resolution. Instructions like GlobalGet and RefFunc have fully
   concrete results (the pushed value depends on the lookup).
   ------------------------------------------------------------------------- *)

Inductive eval_instr : module_state -> instr -> module_state -> Prop :=

  (* --- Function calls --- *)

  (* Call: resolve funcidx to function address *)
  | Eval_Call : forall ms funcidx func_addr new_stack,
      nth_error (ms_funcs ms) funcidx = Some func_addr ->
      eval_instr ms (Call funcidx) (set_stack ms new_stack)

  (* CallIndirect: resolve tableidx to table instance *)
  | Eval_CallIndirect : forall ms tableidx typeidx tab new_stack,
      nth_error (ms_tables ms) tableidx = Some tab ->
      eval_instr ms (CallIndirect tableidx typeidx) (set_stack ms new_stack)

  (* --- Globals --- *)

  (* GlobalGet: push the looked-up global's value onto the stack *)
  | Eval_GlobalGet : forall ms globalidx g,
      nth_error (ms_globals ms) globalidx = Some g ->
      eval_instr ms (GlobalGet globalidx)
        (set_stack ms (glob_value g :: ms_value_stack ms))

  (* GlobalSet: pop value, verify mutability, update the global *)
  | Eval_GlobalSet : forall ms globalidx v rest g,
      ms_value_stack ms = v :: rest ->
      nth_error (ms_globals ms) globalidx = Some g ->
      glob_mut g = Var ->
      eval_instr ms (GlobalSet globalidx)
        (set_stack_and_global ms rest globalidx v)

  (* --- References --- *)

  (* RefFunc: push function reference value onto stack.
     The instr constructor is RefFunc (from wasm_core), while the value
     pushed is VRefFunc (from wasm_value). *)
  | Eval_RefFunc : forall ms funcidx func_addr,
      nth_error (ms_funcs ms) funcidx = Some func_addr ->
      eval_instr ms (RefFunc funcidx)
        (set_stack ms (VRefFunc func_addr :: ms_value_stack ms))

  (* --- Table operations --- *)

  (* TableGet: resolve tableidx, abstract element access *)
  | Eval_TableGet : forall ms tableidx tab new_stack,
      nth_error (ms_tables ms) tableidx = Some tab ->
      eval_instr ms (TableGet tableidx) (set_stack ms new_stack)

  (* TableSet: resolve tableidx, abstract element update *)
  | Eval_TableSet : forall ms tableidx tab new_stack,
      nth_error (ms_tables ms) tableidx = Some tab ->
      eval_instr ms (TableSet tableidx) (set_stack ms new_stack)

  (* TableSize: push table length onto stack *)
  | Eval_TableSize : forall ms tableidx tab,
      nth_error (ms_tables ms) tableidx = Some tab ->
      eval_instr ms (TableSize tableidx)
        (set_stack ms (I32 (Z.of_nat (length (tab_elem tab)))
                       :: ms_value_stack ms))

  (* TableGrow: resolve tableidx, only target table changes.
     Frame condition: update_nth ensures non-target tables are preserved. *)
  | Eval_TableGrow : forall ms tableidx tab new_tab new_stack,
      nth_error (ms_tables ms) tableidx = Some tab ->
      eval_instr ms (TableGrow tableidx)
        (mkModuleState (ms_funcs ms)
                       (update_nth (ms_tables ms) tableidx new_tab)
                       (ms_mems ms) (ms_globals ms)
                       (ms_elems ms) (ms_datas ms) (ms_locals ms) new_stack)

  (* TableFill: resolve tableidx, only target table changes *)
  | Eval_TableFill : forall ms tableidx tab new_tab new_stack,
      nth_error (ms_tables ms) tableidx = Some tab ->
      eval_instr ms (TableFill tableidx)
        (mkModuleState (ms_funcs ms)
                       (update_nth (ms_tables ms) tableidx new_tab)
                       (ms_mems ms) (ms_globals ms)
                       (ms_elems ms) (ms_datas ms) (ms_locals ms) new_stack)

  (* TableCopy: resolve both table indices, only dst table changes *)
  | Eval_TableCopy : forall ms dst_idx src_idx tab_dst tab_src new_dst_tab new_stack,
      nth_error (ms_tables ms) dst_idx = Some tab_dst ->
      nth_error (ms_tables ms) src_idx = Some tab_src ->
      eval_instr ms (TableCopy dst_idx src_idx)
        (mkModuleState (ms_funcs ms)
                       (update_nth (ms_tables ms) dst_idx new_dst_tab)
                       (ms_mems ms) (ms_globals ms)
                       (ms_elems ms) (ms_datas ms) (ms_locals ms) new_stack)

  (* TableInit: resolve tableidx and elemidx, only target table changes *)
  | Eval_TableInit : forall ms tableidx elemidx tab elem new_tab new_stack,
      nth_error (ms_tables ms) tableidx = Some tab ->
      nth_error (ms_elems ms) elemidx = Some elem ->
      eval_instr ms (TableInit tableidx elemidx)
        (mkModuleState (ms_funcs ms)
                       (update_nth (ms_tables ms) tableidx new_tab)
                       (ms_mems ms) (ms_globals ms)
                       (ms_elems ms) (ms_datas ms) (ms_locals ms) new_stack)

  (* ElemDrop: resolve elemidx, only target element changes.
     Frame condition: update_nth ensures non-target elements are preserved. *)
  | Eval_ElemDrop : forall ms elemidx elem new_elem,
      nth_error (ms_elems ms) elemidx = Some elem ->
      eval_instr ms (ElemDrop elemidx)
        (mkModuleState (ms_funcs ms) (ms_tables ms) (ms_mems ms) (ms_globals ms)
                       (update_nth (ms_elems ms) elemidx new_elem) (ms_datas ms)
                       (ms_locals ms) (ms_value_stack ms))

  (* --- Memory bulk operations --- *)

  (* MemoryInit: resolve dataidx, abstract result.
     We model only the data segment INDEX LOOKUP. The actual memory write
     is a side effect that doesn't involve index remapping — it copies
     data from the segment into memory 0 (fixed), which is the same in
     both composed and fused modes. *)
  | Eval_MemoryInit : forall ms dataidx dat new_stack,
      nth_error (ms_datas ms) dataidx = Some dat ->
      eval_instr ms (MemoryInit dataidx) (set_stack ms new_stack)

  (* DataDrop: resolve dataidx, only target data segment changes *)
  | Eval_DataDrop : forall ms dataidx dat new_dat,
      nth_error (ms_datas ms) dataidx = Some dat ->
      eval_instr ms (DataDrop dataidx)
        (mkModuleState (ms_funcs ms) (ms_tables ms) (ms_mems ms) (ms_globals ms)
                       (ms_elems ms) (update_nth (ms_datas ms) dataidx new_dat)
                       (ms_locals ms) (ms_value_stack ms))

  (* --- Category B: Non-index instructions (abstract pass-through) --- *)

  (* Pure instructions don't reference module-level indices.
     They may change the value stack and locals but MUST preserve
     all module-level entities (funcs, tables, mems, globals, elems, datas).
     This constraint is what makes the forward simulation work: pure
     instructions can't disrupt index-space correspondence. *)
  | Eval_Pure : forall ms i ms',
      is_pure_instr i = true ->
      ms_funcs ms' = ms_funcs ms ->
      ms_tables ms' = ms_tables ms ->
      ms_mems ms' = ms_mems ms ->
      ms_globals ms' = ms_globals ms ->
      ms_elems ms' = ms_elems ms ->
      ms_datas ms' = ms_datas ms ->
      eval_instr ms i ms'.

(* -------------------------------------------------------------------------
   Preservation Lemmas

   set_stack preserves all non-stack fields. These lemmas are used
   extensively in the forward simulation proof.
   ------------------------------------------------------------------------- *)

Lemma set_stack_funcs : forall ms s, ms_funcs (set_stack ms s) = ms_funcs ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_tables : forall ms s, ms_tables (set_stack ms s) = ms_tables ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_mems : forall ms s, ms_mems (set_stack ms s) = ms_mems ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_globals : forall ms s, ms_globals (set_stack ms s) = ms_globals ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_elems : forall ms s, ms_elems (set_stack ms s) = ms_elems ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_datas : forall ms s, ms_datas (set_stack ms s) = ms_datas ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_locals : forall ms s, ms_locals (set_stack ms s) = ms_locals ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_value_stack : forall ms s, ms_value_stack (set_stack ms s) = s.
Proof. intros. reflexivity. Qed.

(* set_stack_and_global preserves funcs, tables, mems, elems, datas, locals *)
Lemma set_stack_and_global_funcs : forall ms s idx v,
    ms_funcs (set_stack_and_global ms s idx v) = ms_funcs ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_and_global_tables : forall ms s idx v,
    ms_tables (set_stack_and_global ms s idx v) = ms_tables ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_and_global_mems : forall ms s idx v,
    ms_mems (set_stack_and_global ms s idx v) = ms_mems ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_and_global_elems : forall ms s idx v,
    ms_elems (set_stack_and_global ms s idx v) = ms_elems ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_and_global_datas : forall ms s idx v,
    ms_datas (set_stack_and_global ms s idx v) = ms_datas ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_and_global_locals : forall ms s idx v,
    ms_locals (set_stack_and_global ms s idx v) = ms_locals ms.
Proof. intros. reflexivity. Qed.

Lemma set_stack_and_global_globals : forall ms s idx v,
    ms_globals (set_stack_and_global ms s idx v) =
    update_global_value (ms_globals ms) idx v.
Proof. intros. reflexivity. Qed.

Lemma set_stack_and_global_value_stack : forall ms s idx v,
    ms_value_stack (set_stack_and_global ms s idx v) = s.
Proof. intros. reflexivity. Qed.

(* update_nth preserves length *)
Lemma update_nth_length : forall {A : Type} (l : list A) n x,
    length (update_nth l n x) = length l.
Proof.
  intros A l. induction l as [|h t IH]; intros n x.
  - reflexivity.
  - destruct n; simpl.
    + reflexivity.
    + f_equal. apply IH.
Qed.

(* update_nth preserves other indices *)
Lemma update_nth_other : forall {A : Type} (l : list A) n m x,
    n <> m ->
    nth_error (update_nth l n x) m = nth_error l m.
Proof.
  intros A l. induction l as [|h t IH]; intros n m x Hneq.
  - reflexivity.
  - destruct n; destruct m; simpl.
    + exfalso. apply Hneq. reflexivity.
    + reflexivity.
    + reflexivity.
    + apply IH. intro Heq. apply Hneq. f_equal. exact Heq.
Qed.

(* update_nth at the target index *)
Lemma update_nth_same : forall {A : Type} (l : list A) n x,
    n < length l ->
    nth_error (update_nth l n x) n = Some x.
Proof.
  intros A l. induction l as [|h t IH]; intros n x Hlt.
  - simpl in Hlt. lia.
  - destruct n; simpl.
    + reflexivity.
    + apply IH. simpl in Hlt. lia.
Qed.

(* update_global_value at the target index *)
Lemma update_global_value_same : forall globals idx v g,
    nth_error globals idx = Some g ->
    nth_error (update_global_value globals idx v) idx =
      Some (mkGlobalInst v (glob_mut g)).
Proof.
  intros globals idx v g Hnth.
  unfold update_global_value. rewrite Hnth.
  apply update_nth_same.
  apply nth_error_Some. rewrite Hnth. discriminate.
Qed.

(* update_global_value preserves other indices *)
Lemma update_global_value_other : forall globals idx j v,
    j <> idx ->
    nth_error (update_global_value globals idx v) j = nth_error globals j.
Proof.
  intros globals idx j v Hneq.
  unfold update_global_value.
  destruct (nth_error globals idx) eqn:Hnth.
  - apply update_nth_other. intro H; exact (Hneq (eq_sym H)).
  - reflexivity.
Qed.

(* Opacity hints: prevent simpl from expanding these in downstream files *)
Global Opaque is_pure_instr.
Global Opaque set_stack.
Global Opaque set_stack_and_global.
Global Opaque update_global_value.
Global Opaque update_nth.

(* End of wasm_semantics *)
