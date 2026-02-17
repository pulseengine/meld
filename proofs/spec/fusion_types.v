(* =========================================================================
   Fusion Types and Index Remapping

   Lightweight types and definitions for the fusion pipeline:
   index remapping, instruction rewriting, and correctness predicates.

   This file is separated from fusion_spec.v (which contains semantic
   preservation proofs depending on wasm_semantics) so that downstream
   files like merge_correctness.v can import only these lightweight
   definitions without pulling in the full operational semantics.
   ========================================================================= *)

From Stdlib Require Import List ZArith Bool.
From MeldSpec Require Import wasm_core component_model.
Import ListNotations.

(* -------------------------------------------------------------------------
   Fusion Configuration

   Controls how fusion handles various aspects of combining modules.
   ------------------------------------------------------------------------- *)

Inductive memory_strategy : Type :=
  | SharedMemory      (* All modules share one memory, rebased addresses *)
  | SeparateMemory.   (* Each module keeps its own memory (multi-memory) *)

Record fusion_config : Type := mkFusionConfig {
  fc_memory_strategy : memory_strategy;
  fc_address_rebasing : bool;
}.

(* -------------------------------------------------------------------------
   Index Remapping

   When modules are merged, their index spaces are combined.
   A remap records how a source index maps to the fused index.
   ------------------------------------------------------------------------- *)

Record index_remap : Type := mkIndexRemap {
  ir_space : index_space;
  ir_source : module_source;  (* (component_idx, module_idx) *)
  ir_source_idx : idx;
  ir_fused_idx : idx;
}.

(* All remaps for a fusion operation *)
Definition remap_table := list index_remap.

(* -------------------------------------------------------------------------
   Memory Rebasing

   With SharedMemory strategy, each module's memory accesses are offset
   by a base address to place them in non-overlapping regions.
   ------------------------------------------------------------------------- *)

Record memory_layout : Type := mkMemoryLayout {
  ml_source : module_source;
  ml_base_address : nat;    (* Starting address in fused memory *)
  ml_size : nat;            (* Size in bytes *)
}.

Definition memory_layout_table := list memory_layout.

(* Non-overlapping memory regions *)
Definition disjoint_layouts (layouts : memory_layout_table) : Prop :=
  forall l1 l2,
    In l1 layouts ->
    In l2 layouts ->
    l1 <> l2 ->
    ml_base_address l1 + ml_size l1 <= ml_base_address l2 \/
    ml_base_address l2 + ml_size l2 <= ml_base_address l1.

(* -------------------------------------------------------------------------
   Fusion Result

   The output of fusion: a single module plus metadata about how it
   was constructed.
   ------------------------------------------------------------------------- *)

Record fusion_result : Type := mkFusionResult {
  fr_module : module;
  fr_remaps : remap_table;
  fr_memory_layout : option memory_layout_table;
  fr_config : fusion_config;
}.

(* -------------------------------------------------------------------------
   Index Remap Properties

   Core correctness properties for index remapping.
   ------------------------------------------------------------------------- *)

(* A remap is valid if the fused index is within bounds *)
Definition valid_remap (fr : fusion_result) (r : index_remap) : Prop :=
  match ir_space r with
  | FuncIdx => valid_funcidx (fr_module fr) (ir_fused_idx r)
  | TableIdx => valid_tableidx (fr_module fr) (ir_fused_idx r)
  | MemIdx => valid_memidx (fr_module fr) (ir_fused_idx r)
  | GlobalIdx => valid_globalidx (fr_module fr) (ir_fused_idx r)
  | TypeIdx => valid_typeidx (fr_module fr) (ir_fused_idx r)
  | ElemIdx => ir_fused_idx r < length (mod_elems (fr_module fr))
  | DataIdx => ir_fused_idx r < length (mod_datas (fr_module fr))
  end.

(* Remapping is injective within each index space *)
Definition injective_remaps (remaps : remap_table) : Prop :=
  forall r1 r2,
    In r1 remaps ->
    In r2 remaps ->
    ir_space r1 = ir_space r2 ->
    ir_fused_idx r1 = ir_fused_idx r2 ->
    r1 = r2.

(* Remapping preserves source identity *)
Definition remap_preserves_identity (remaps : remap_table) : Prop :=
  forall r1 r2,
    In r1 remaps ->
    In r2 remaps ->
    ir_source r1 = ir_source r2 ->
    ir_space r1 = ir_space r2 ->
    ir_source_idx r1 = ir_source_idx r2 ->
    r1 = r2.

(* -------------------------------------------------------------------------
   Lookup Functions

   Find the fused index for a given source index.
   ------------------------------------------------------------------------- *)

(* Equality for index spaces *)
Definition index_space_eqb (a b : index_space) : bool :=
  match a, b with
  | FuncIdx, FuncIdx => true
  | TableIdx, TableIdx => true
  | MemIdx, MemIdx => true
  | GlobalIdx, GlobalIdx => true
  | TypeIdx, TypeIdx => true
  | ElemIdx, ElemIdx => true
  | DataIdx, DataIdx => true
  | _, _ => false
  end.

Definition lookup_remap (remaps : remap_table) (space : index_space)
                        (src : module_source) (src_idx : idx) : option idx :=
  match List.find (fun r =>
    index_space_eqb (ir_space r) space &&
    Nat.eqb (fst (ir_source r)) (fst src) &&
    Nat.eqb (snd (ir_source r)) (snd src) &&
    Nat.eqb (ir_source_idx r) src_idx
  ) remaps with
  | Some r => Some (ir_fused_idx r)
  | None => None
  end.

(* -------------------------------------------------------------------------
   Instruction Rewriting Specification

   Instructions must be rewritten to use fused indices.
   We define this as an inductive relation rather than a function
   to avoid termination complexity with nested instructions.
   ------------------------------------------------------------------------- *)

(* Helper: sequence for option lists *)
Fixpoint option_sequence {A : Type} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | None :: _ => None
  | Some x :: rest =>
      match option_sequence rest with
      | Some xs => Some (x :: xs)
      | None => None
      end
  end.

(* Rewrite relation: instr_rewrites remaps src i i' means i rewrites to i' *)
Inductive instr_rewrites (remaps : remap_table) (src : module_source)
  : instr -> instr -> Prop :=
  (* Function calls *)
  | RW_Call : forall funcidx idx',
      lookup_remap remaps FuncIdx src funcidx = Some idx' ->
      instr_rewrites remaps src (Call funcidx) (Call idx')
  | RW_CallIndirect : forall tableidx typeidx t' ty',
      lookup_remap remaps TableIdx src tableidx = Some t' ->
      lookup_remap remaps TypeIdx src typeidx = Some ty' ->
      instr_rewrites remaps src (CallIndirect tableidx typeidx) (CallIndirect t' ty')
  (* Globals *)
  | RW_GlobalGet : forall globalidx idx',
      lookup_remap remaps GlobalIdx src globalidx = Some idx' ->
      instr_rewrites remaps src (GlobalGet globalidx) (GlobalGet idx')
  | RW_GlobalSet : forall globalidx idx',
      lookup_remap remaps GlobalIdx src globalidx = Some idx' ->
      instr_rewrites remaps src (GlobalSet globalidx) (GlobalSet idx')
  (* References *)
  | RW_RefFunc : forall funcidx idx',
      lookup_remap remaps FuncIdx src funcidx = Some idx' ->
      instr_rewrites remaps src (RefFunc funcidx) (RefFunc idx')
  (* Tables *)
  | RW_TableGet : forall tableidx idx',
      lookup_remap remaps TableIdx src tableidx = Some idx' ->
      instr_rewrites remaps src (TableGet tableidx) (TableGet idx')
  | RW_TableSet : forall tableidx idx',
      lookup_remap remaps TableIdx src tableidx = Some idx' ->
      instr_rewrites remaps src (TableSet tableidx) (TableSet idx')
  (* Control flow - instructions without indices pass through *)
  | RW_Nop : instr_rewrites remaps src Nop Nop
  | RW_Unreachable : instr_rewrites remaps src Unreachable Unreachable
  | RW_Return : instr_rewrites remaps src Return Return
  | RW_Drop : instr_rewrites remaps src Drop Drop
  | RW_Br : forall l, instr_rewrites remaps src (Br l) (Br l)
  | RW_BrIf : forall l, instr_rewrites remaps src (BrIf l) (BrIf l)
  | RW_BrTable : forall ls d, instr_rewrites remaps src (BrTable ls d) (BrTable ls d)
  (* Locals - no remapping needed *)
  | RW_LocalGet : forall l, instr_rewrites remaps src (LocalGet l) (LocalGet l)
  | RW_LocalSet : forall l, instr_rewrites remaps src (LocalSet l) (LocalSet l)
  | RW_LocalTee : forall l, instr_rewrites remaps src (LocalTee l) (LocalTee l)
  (* Memory operations - remap MemIdx for multi-memory support *)
  | RW_MemorySize : forall memidx idx',
      lookup_remap remaps MemIdx src memidx = Some idx' ->
      instr_rewrites remaps src (MemorySize memidx) (MemorySize idx')
  | RW_MemoryGrow : forall memidx idx',
      lookup_remap remaps MemIdx src memidx = Some idx' ->
      instr_rewrites remaps src (MemoryGrow memidx) (MemoryGrow idx')
  | RW_Load : forall vt memidx off align idx',
      lookup_remap remaps MemIdx src memidx = Some idx' ->
      instr_rewrites remaps src (Load vt memidx off align) (Load vt idx' off align)
  | RW_Store : forall vt memidx off align idx',
      lookup_remap remaps MemIdx src memidx = Some idx' ->
      instr_rewrites remaps src (Store vt memidx off align) (Store vt idx' off align)
  (* Numeric operations - no indices *)
  | RW_NumericOp : forall op, instr_rewrites remaps src (NumericOp op) (NumericOp op)
  (* Select *)
  | RW_Select : forall ts, instr_rewrites remaps src (Select ts) (Select ts)
  (* Ref *)
  | RW_RefNull : forall rt, instr_rewrites remaps src (RefNull rt) (RefNull rt)
  | RW_RefIsNull : instr_rewrites remaps src RefIsNull RefIsNull
  (* Block structures - recursive *)
  | RW_Block : forall bt body body',
      Forall2 (instr_rewrites remaps src) body body' ->
      instr_rewrites remaps src (Block bt body) (Block bt body')
  | RW_Loop : forall bt body body',
      Forall2 (instr_rewrites remaps src) body body' ->
      instr_rewrites remaps src (Loop bt body) (Loop bt body')
  | RW_If : forall bt then_ else_ then_' else_',
      Forall2 (instr_rewrites remaps src) then_ then_' ->
      Forall2 (instr_rewrites remaps src) else_ else_' ->
      instr_rewrites remaps src (If bt then_ else_) (If bt then_' else_')
  (* Memory bulk *)
  | RW_MemoryCopy : forall dst_mem src_mem d' s',
      lookup_remap remaps MemIdx src dst_mem = Some d' ->
      lookup_remap remaps MemIdx src src_mem = Some s' ->
      instr_rewrites remaps src (MemoryCopy dst_mem src_mem) (MemoryCopy d' s')
  | RW_MemoryFill : forall memidx idx',
      lookup_remap remaps MemIdx src memidx = Some idx' ->
      instr_rewrites remaps src (MemoryFill memidx) (MemoryFill idx')
  | RW_MemoryInit : forall dataidx memidx d' m',
      lookup_remap remaps DataIdx src dataidx = Some d' ->
      lookup_remap remaps MemIdx src memidx = Some m' ->
      instr_rewrites remaps src (MemoryInit dataidx memidx) (MemoryInit d' m')
  | RW_DataDrop : forall dataidx idx',
      lookup_remap remaps DataIdx src dataidx = Some idx' ->
      instr_rewrites remaps src (DataDrop dataidx) (DataDrop idx')
  (* Table bulk *)
  | RW_TableSize : forall tableidx idx',
      lookup_remap remaps TableIdx src tableidx = Some idx' ->
      instr_rewrites remaps src (TableSize tableidx) (TableSize idx')
  | RW_TableGrow : forall tableidx idx',
      lookup_remap remaps TableIdx src tableidx = Some idx' ->
      instr_rewrites remaps src (TableGrow tableidx) (TableGrow idx')
  | RW_TableFill : forall tableidx idx',
      lookup_remap remaps TableIdx src tableidx = Some idx' ->
      instr_rewrites remaps src (TableFill tableidx) (TableFill idx')
  | RW_TableCopy : forall dst src_t d' s',
      lookup_remap remaps TableIdx src dst = Some d' ->
      lookup_remap remaps TableIdx src src_t = Some s' ->
      instr_rewrites remaps src (TableCopy dst src_t) (TableCopy d' s')
  | RW_TableInit : forall tableidx elemidx t' e',
      lookup_remap remaps TableIdx src tableidx = Some t' ->
      lookup_remap remaps ElemIdx src elemidx = Some e' ->
      instr_rewrites remaps src (TableInit tableidx elemidx) (TableInit t' e')
  | RW_ElemDrop : forall elemidx idx',
      lookup_remap remaps ElemIdx src elemidx = Some idx' ->
      instr_rewrites remaps src (ElemDrop elemidx) (ElemDrop idx').

(* -------------------------------------------------------------------------
   Fusion Specification: Main Theorem Statements

   These are the properties that a correct fusion implementation must satisfy.
   ------------------------------------------------------------------------- *)

(* All remaps in the result are valid *)
Definition fusion_remaps_valid (fr : fusion_result) : Prop :=
  Forall (valid_remap fr) (fr_remaps fr).

(* Remapping is injective *)
Definition fusion_remaps_injective (fr : fusion_result) : Prop :=
  injective_remaps (fr_remaps fr).

(* Memory layout is disjoint (if using shared memory) *)
Definition fusion_memory_disjoint (fr : fusion_result) : Prop :=
  match fr_memory_layout fr with
  | Some layouts => disjoint_layouts layouts
  | None => True
  end.

(* The fused module is well-formed *)
Definition fusion_module_valid (fr : fusion_result) : Prop :=
  (* All function bodies can be rewritten using the remap table *)
  Forall (fun f =>
    forall src,
      exists body',
        Forall2 (instr_rewrites (fr_remaps fr) src) (func_body f) body'
  ) (mod_funcs (fr_module fr)).

(* -------------------------------------------------------------------------
   Main Correctness Specification

   The fusion function must produce a result satisfying all properties.
   ------------------------------------------------------------------------- *)

Definition fusion_correct (cc : composed_component) (config : fusion_config)
                          (fr : fusion_result) : Prop :=
  fr_config fr = config /\
  fusion_remaps_valid fr /\
  fusion_remaps_injective fr /\
  fusion_memory_disjoint fr /\
  fusion_module_valid fr.

(* End of fusion_types *)
