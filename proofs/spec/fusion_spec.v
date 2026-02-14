(* =========================================================================
   Fusion Specification

   This module defines what static component fusion should achieve:
   Given a composed component, produce a single core module that
   behaves equivalently to the runtime composition.

   Key Properties:
   1. Semantic Preservation: The fused module produces the same outputs
      for the same inputs as the composed component would at runtime.
   2. Index Validity: All indices in the fused module are valid.
   3. Export Preservation: All exposed exports remain accessible.
   4. Import Preservation: All unresolved imports are still required.
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
  (* Memory operations - indices may need remapping in multi-memory *)
  | RW_MemorySize : instr_rewrites remaps src MemorySize MemorySize
  | RW_MemoryGrow : instr_rewrites remaps src MemoryGrow MemoryGrow
  | RW_Load : forall vt off align,
      instr_rewrites remaps src (Load vt off align) (Load vt off align)
  | RW_Store : forall vt off align,
      instr_rewrites remaps src (Store vt off align) (Store vt off align)
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
  | RW_MemoryCopy : instr_rewrites remaps src MemoryCopy MemoryCopy
  | RW_MemoryFill : instr_rewrites remaps src MemoryFill MemoryFill
  | RW_MemoryInit : forall dataidx idx',
      lookup_remap remaps DataIdx src dataidx = Some idx' ->
      instr_rewrites remaps src (MemoryInit dataidx) (MemoryInit idx')
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

(* =========================================================================
   Semantic Preservation (to be developed)

   The ultimate goal: behavioral equivalence between the fused module
   and the original composed component.

   This requires defining execution semantics for both forms and proving
   a simulation relation.
   ========================================================================= *)

(* -------------------------------------------------------------------------
   WebAssembly Runtime Values and State

   Core types for execution semantics. These form the basis of both
   composed and fused execution states.
   ------------------------------------------------------------------------- *)

(* Runtime values *)
Inductive wasm_value : Type :=
  | I32 (n : Z)
  | I64 (n : Z)
  | F32 (f : Z)  (* Simplified: actual floats are complex *)
  | F64 (f : Z)
  | RefNull (rt : reftype)
  | RefFunc (addr : nat).

(* Memory instance: simplified as byte array *)
Record memory_inst : Type := mkMemoryInst {
  mem_data : list nat;  (* Byte values *)
  mem_max : option nat;
}.

(* Table instance: simplified as function reference array *)
Record table_inst : Type := mkTableInst {
  tab_elem : list (option nat);  (* Function addresses *)
  tab_max : option nat;
}.

(* Global instance *)
Record global_inst : Type := mkGlobalInst {
  glob_value : wasm_value;
  glob_mut : mutability;
}.

(* Module instance state at runtime *)
Record module_state : Type := mkModuleState {
  ms_funcs : list nat;        (* Function addresses *)
  ms_tables : list table_inst;
  ms_mems : list memory_inst;
  ms_globals : list global_inst;
  ms_locals : list wasm_value;    (* Local variables for current frame *)
  ms_value_stack : list wasm_value; (* Operand stack *)
}.

(* -------------------------------------------------------------------------
   Execution States

   Composed execution: each source module has its own state
   Fused execution: single unified module state
   ------------------------------------------------------------------------- *)

(* Composed component execution state *)
Record composed_exec_state : Type := mkComposedExecState {
  ces_module_states : list (module_source * module_state);
  ces_shared_memory : option memory_inst;  (* Shared for cross-module *)
}.

(* Fused module execution state *)
Record fused_exec_state : Type := mkFusedExecState {
  fes_module_state : module_state;
}.

(* -------------------------------------------------------------------------
   Step Relations (Operational Semantics)

   These define single-step execution for both composed and fused forms.
   Full semantics would include all WASM instructions; we provide stubs
   to establish the structure.
   ------------------------------------------------------------------------- *)

(* Composed component takes a step *)
Inductive composed_step (cc : composed_component)
  : composed_exec_state -> composed_exec_state -> Prop :=
  (* Stub constructors - to be filled with actual instruction semantics *)
  | CS_LocalOp : forall ces ces' (src : module_source),
      (* Local operation within one module *)
      (* TODO: Add actual preconditions (instruction fetch, decode, execute) *)
      In src (map fst (ces_module_states ces)) ->
      composed_step cc ces ces'
  | CS_CrossModuleCall : forall ces ces' (src_module target_module : module_source),
      (* Cross-module call requiring adapter *)
      (* TODO: Add adapter application logic *)
      In src_module (map fst (ces_module_states ces)) ->
      In target_module (map fst (ces_module_states ces)) ->
      composed_step cc ces ces'
  | CS_MemoryOp : forall ces ces' (src : module_source),
      (* Memory operation (possibly on shared memory) *)
      (* TODO: Add memory bounds checks and access logic *)
      In src (map fst (ces_module_states ces)) ->
      composed_step cc ces ces'.

(* Fused module takes a step *)
Inductive fused_step (fr : fusion_result)
  : fused_exec_state -> fused_exec_state -> Prop :=
  (* Stub constructors - to be filled with actual instruction semantics *)
  | FS_LocalOp : forall fes fes',
      (* Local operation using fused indices *)
      (* TODO: Add actual preconditions (instruction fetch, decode, execute) *)
      fused_step fr fes fes'
  | FS_InlinedCall : forall fes fes',
      (* Former cross-module call, now inlined *)
      (* TODO: Add direct call logic with remapped indices *)
      fused_step fr fes fes'
  | FS_MemoryOp : forall fes fes',
      (* Memory operation (possibly rebased) *)
      (* TODO: Add memory bounds checks with rebasing *)
      fused_step fr fes fes'.

(* Trap states *)
Inductive composed_traps (cc : composed_component) : composed_exec_state -> Prop :=
  | CT_Unreachable : forall ces, composed_traps cc ces
  | CT_OutOfBounds : forall ces, composed_traps cc ces
  | CT_TypeMismatch : forall ces, composed_traps cc ces.

Inductive fused_traps (fr : fusion_result) : fused_exec_state -> Prop :=
  | FT_Unreachable : forall fes, fused_traps fr fes
  | FT_OutOfBounds : forall fes, fused_traps fr fes
  | FT_TypeMismatch : forall fes, fused_traps fr fes.

(* -------------------------------------------------------------------------
   State Correspondence

   Relates composed execution state to fused state via the remap table
   and memory layout.
   ------------------------------------------------------------------------- *)

(* Helper: look up module state by source *)
Definition lookup_module_state (ces : composed_exec_state) (src : module_source)
  : option module_state :=
  match List.find (fun '(s, _) => Nat.eqb (fst s) (fst src) && Nat.eqb (snd s) (snd src))
                  (ces_module_states ces) with
  | Some (_, ms) => Some ms
  | None => None
  end.

(* Value correspondence: values are equal (no remapping needed for data) *)
Definition values_correspond (v1 v2 : wasm_value) : Prop :=
  v1 = v2.  (* Could be refined for references *)

(* Value stack correspondence *)
Definition value_stacks_correspond (vs1 vs2 : list wasm_value) : Prop :=
  length vs1 = length vs2 /\
  Forall2 values_correspond vs1 vs2.

(* Global correspondence via remap *)
Definition global_corresponds (remaps : remap_table) (src : module_source)
                              (src_idx : idx) (g_src g_fused : global_inst) : Prop :=
  values_correspond (glob_value g_src) (glob_value g_fused) /\
  glob_mut g_src = glob_mut g_fused.

(* Memory correspondence: source memory region maps to fused memory *)
Definition memory_corresponds (layout_opt : option memory_layout_table)
                             (src : module_source)
                             (mem_src : memory_inst)
                             (mem_fused : memory_inst) : Prop :=
  match layout_opt with
  | None =>
      (* Separate memories: exact equality *)
      mem_data mem_src = mem_data mem_fused
  | Some layouts =>
      (* Shared memory: source is a slice of fused, starting at base *)
      exists layout,
        In layout layouts /\
        ml_source layout = src /\
        forall offset,
          offset < length (mem_data mem_src) ->
          nth_error (mem_data mem_src) offset =
          nth_error (mem_data mem_fused) (ml_base_address layout + offset)
  end.

(* Table correspondence via remap *)
Definition table_corresponds (remaps : remap_table) (src : module_source)
                             (tab_src tab_fused : table_inst) : Prop :=
  length (tab_elem tab_src) = length (tab_elem tab_fused) /\
  tab_max tab_src = tab_max tab_fused.
  (* Full version would map function addresses via remap *)

(* State correspondence record *)
Record state_correspondence (cc : composed_component) (fr : fusion_result)
                            (ces : composed_exec_state)
                            (fes : fused_exec_state) : Prop := mkStateCorrespondence {
  (* Remap and layout from fusion result *)
  sc_remap_table : fr_remaps fr = fr_remaps fr;  (* Tautology for now *)
  sc_memory_layout : fr_memory_layout fr = fr_memory_layout fr;

  (* Value stacks correspond *)
  sc_value_stack_eq : forall src ms,
      lookup_module_state ces src = Some ms ->
      value_stacks_correspond (ms_value_stack ms)
                             (ms_value_stack (fes_module_state fes));

  (* Memory correspondence *)
  sc_memory_eq : forall src ms mem_src,
      lookup_module_state ces src = Some ms ->
      nth_error (ms_mems ms) 0 = Some mem_src ->
      exists mem_fused,
        nth_error (ms_mems (fes_module_state fes)) 0 = Some mem_fused /\
        memory_corresponds (fr_memory_layout fr) src mem_src mem_fused;

  (* Globals correspond via remap *)
  sc_globals_eq : forall src ms src_idx g_src,
      lookup_module_state ces src = Some ms ->
      nth_error (ms_globals ms) src_idx = Some g_src ->
      exists fused_idx g_fused,
        lookup_remap (fr_remaps fr) GlobalIdx src src_idx = Some fused_idx /\
        nth_error (ms_globals (fes_module_state fes)) fused_idx = Some g_fused /\
        global_corresponds (fr_remaps fr) src src_idx g_src g_fused;

  (* Tables correspond via remap *)
  sc_tables_eq : forall src ms src_idx tab_src,
      lookup_module_state ces src = Some ms ->
      nth_error (ms_tables ms) src_idx = Some tab_src ->
      exists fused_idx tab_fused,
        lookup_remap (fr_remaps fr) TableIdx src src_idx = Some fused_idx /\
        nth_error (ms_tables (fes_module_state fes)) fused_idx = Some tab_fused /\
        table_corresponds (fr_remaps fr) src tab_src tab_fused;
}.

(* -------------------------------------------------------------------------
   Semantic Equivalence via Forward Simulation

   The fused module simulates the composed component: every step in the
   composed execution is matched by corresponding step(s) in the fused
   execution, preserving state correspondence.
   ------------------------------------------------------------------------- *)

Definition forward_simulation (cc : composed_component) (fr : fusion_result) : Prop :=
  forall ces ces' fes,
    state_correspondence cc fr ces fes ->
    composed_step cc ces ces' ->
    exists fes',
      fused_step fr fes fes' /\
      state_correspondence cc fr ces' fes'.

(* Trap equivalence: both trap or neither traps *)
Definition trap_equivalence (cc : composed_component) (fr : fusion_result) : Prop :=
  forall ces fes,
    state_correspondence cc fr ces fes ->
    (composed_traps cc ces <-> fused_traps fr fes).

(* Semantic equivalence combines simulation and trap equivalence *)
Definition semantic_equivalence (cc : composed_component) (fr : fusion_result) : Prop :=
  forward_simulation cc fr /\
  trap_equivalence cc fr.

(* -------------------------------------------------------------------------
   Trap Equivalence

   Trivially provable: both composed_traps and fused_traps match all
   states (via CT_Unreachable / FT_Unreachable), so the biconditional
   holds vacuously.
   ------------------------------------------------------------------------- *)

Lemma fusion_trap_equivalence :
  forall cc config fr,
    well_formed_composition cc ->
    fusion_correct cc config fr ->
    trap_equivalence cc fr.
Proof.
  intros cc config fr _ _.
  unfold trap_equivalence. intros ces fes _.
  split.
  - intro Hc. destruct Hc; [apply FT_Unreachable | apply FT_OutOfBounds | apply FT_TypeMismatch].
  - intro Hf. destruct Hf; [apply CT_Unreachable | apply CT_OutOfBounds | apply CT_TypeMismatch].
Qed.

(* -------------------------------------------------------------------------
   Forward Simulation

   NOT PROVABLE with current stub step relations. Counterexample:
   - ces with modules A (stack=[1]) and B (stack=[1]); fes stack=[1]
   - CS_LocalOp transitions to ces' where A stack=[2], B stack=[3]
   - state_correspondence requires fes' stack to equal BOTH [2] and [3]

   The step relations need refinement before this is provable:

   1. composed_step must constrain non-active modules to preserve state
      (only the executing module's state changes per step)

   2. state_correspondence must track the active module, since in a
      composed component each module has its own stack/locals, but in
      the fused module there is one stack/locals set. Only the active
      module's stack maps to the fused stack; others are saved in frames.

   3. The fused step relation must model instruction fetch, decode, and
      execution with remapped indices, rebased memory addresses, and
      inlined cross-module calls.

   Once these are developed, forward simulation follows by induction on
   composed_step, using fusion_correct to show all index lookups succeed.
   ------------------------------------------------------------------------- *)

Lemma fusion_forward_simulation :
  forall cc config fr,
    well_formed_composition cc ->
    fusion_correct cc config fr ->
    forward_simulation cc fr.
Admitted.

(* -------------------------------------------------------------------------
   Main Semantic Preservation Theorem

   Combines trap equivalence (proved) and forward simulation (admitted,
   pending step relation refinement).
   ------------------------------------------------------------------------- *)

Theorem fusion_preserves_semantics :
  forall cc config fr,
    well_formed_composition cc ->
    fusion_correct cc config fr ->
    semantic_equivalence cc fr.
Proof.
  intros cc config fr Hwf Hcorrect.
  unfold semantic_equivalence. split.
  - exact (fusion_forward_simulation cc config fr Hwf Hcorrect).
  - exact (fusion_trap_equivalence cc config fr Hwf Hcorrect).
Qed.

(* End of fusion_spec specification *)
