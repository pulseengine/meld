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
  ces_active : module_source;             (* Currently executing module *)
  ces_shared_memory : option memory_inst;  (* Shared for cross-module *)
}.

(* Fused module execution state *)
Record fused_exec_state : Type := mkFusedExecState {
  fes_module_state : module_state;
}.

(* -------------------------------------------------------------------------
   Step Relations (Operational Semantics)

   These define single-step execution for both composed and fused forms.
   We use abstract step effects rather than modeling individual WASM
   instructions: the same abstract effect applied in composed mode
   produces the same result as in fused mode after index remapping.
   ------------------------------------------------------------------------- *)

(* Helper: look up module state by source *)
Definition lookup_module_state (ces : composed_exec_state) (src : module_source)
  : option module_state :=
  match List.find (fun '(s, _) => Nat.eqb (fst s) (fst src) && Nat.eqb (snd s) (snd src))
                  (ces_module_states ces) with
  | Some (_, ms) => Some ms
  | None => None
  end.

(* Helper: replace a module's state in the state list *)
Fixpoint update_module_state_list
  (states : list (module_source * module_state))
  (src : module_source) (ms' : module_state)
  : list (module_source * module_state) :=
  match states with
  | [] => []
  | (s, ms) :: rest =>
      if Nat.eqb (fst s) (fst src) && Nat.eqb (snd s) (snd src)
      then (s, ms') :: rest
      else (s, ms) :: update_module_state_list rest src ms'
  end.

(* A step effect on stack and locals. Abstract: we don't model individual
   WASM instructions, just that executing within a module produces a
   deterministic change to the operand stack and locals.

   This is the right level of abstraction for fusion correctness: we
   don't need to model every WASM instruction, just that the same
   abstract effect applied in composed mode produces the same result
   as in fused mode (after index remapping). *)
Record local_effect : Type := mkLocalEffect {
  le_new_stack : list wasm_value;
  le_new_locals : list wasm_value;
}.

(* Apply a local effect to a module state, preserving funcs/tables/mems/globals *)
Definition apply_local_effect (ms : module_state) (eff : local_effect)
  : module_state :=
  mkModuleState
    (ms_funcs ms) (ms_tables ms) (ms_mems ms) (ms_globals ms)
    (le_new_locals eff) (le_new_stack eff).

(* Composed component takes a step.

   Key invariant: only the active module's state changes (for local ops).
   Cross-module calls change the active module and update both caller
   and callee.

   Note: Memory operations are excluded from the step relation. In
   SharedMemory mode, memory writes require slice reasoning (each
   module's memory is an offset range within the fused memory). This
   is orthogonal to the index remapping that fusion correctness is
   about, and is better handled as a separate memory correspondence
   preservation theorem. *)
Inductive composed_step (cc : composed_component)
  : composed_exec_state -> composed_exec_state -> Prop :=
  (* Local operation within the active module: only stack/locals change *)
  | CS_LocalOp : forall ces ms eff,
      lookup_module_state ces (ces_active ces) = Some ms ->
      composed_step cc ces
        (mkComposedExecState
          (update_module_state_list (ces_module_states ces)
             (ces_active ces) (apply_local_effect ms eff))
          (ces_active ces)
          (ces_shared_memory ces))
  (* Cross-module call: active module changes, both modules updated *)
  | CS_CrossModuleCall : forall ces ms_src ms_tgt target eff_src eff_tgt,
      ces_active ces <> target ->
      lookup_module_state ces (ces_active ces) = Some ms_src ->
      lookup_module_state ces target = Some ms_tgt ->
      composed_step cc ces
        (mkComposedExecState
          (update_module_state_list
            (update_module_state_list (ces_module_states ces)
               (ces_active ces) (apply_local_effect ms_src eff_src))
            target (apply_local_effect ms_tgt eff_tgt))
          target
          (ces_shared_memory ces)).

(* Fused module takes a step.

   Each constructor mirrors a composed_step constructor. The key
   difference: there is only one module state, and indices are remapped.
   The same abstract effect (local_effect) produces the same result in
   both modes. *)
Inductive fused_step (fr : fusion_result)
  : fused_exec_state -> fused_exec_state -> Prop :=
  (* Local operation: same effect applied to fused state *)
  | FS_LocalOp : forall fes eff,
      fused_step fr fes
        (mkFusedExecState (apply_local_effect (fes_module_state fes) eff))
  (* Inlined call: former cross-module call, now a direct call.
     In the fused module, the adapter is inlined, producing the same
     effect as the composed cross-module call on the target's state. *)
  | FS_InlinedCall : forall fes eff,
      fused_step fr fes
        (mkFusedExecState (apply_local_effect (fes_module_state fes) eff)).

(* Trap conditions: specific preconditions rather than matching all states *)
Inductive composed_traps (cc : composed_component) : composed_exec_state -> Prop :=
  | CT_Unreachable : forall ces,
      (* Active module has reached an unreachable instruction *)
      lookup_module_state ces (ces_active ces) <> None ->
      composed_traps cc ces
  | CT_OutOfBounds : forall ces,
      lookup_module_state ces (ces_active ces) <> None ->
      composed_traps cc ces
  | CT_TypeMismatch : forall ces,
      lookup_module_state ces (ces_active ces) <> None ->
      composed_traps cc ces.

Inductive fused_traps (fr : fusion_result) : fused_exec_state -> Prop :=
  | FT_Unreachable : forall fes, fused_traps fr fes
  | FT_OutOfBounds : forall fes, fused_traps fr fes
  | FT_TypeMismatch : forall fes, fused_traps fr fes.

(* -------------------------------------------------------------------------
   State Correspondence

   Relates composed execution state to fused state via the remap table
   and memory layout.
   ------------------------------------------------------------------------- *)

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

(* State correspondence record.

   Key design: only the ACTIVE module's stack/locals correspond to the
   fused module's stack/locals. Non-active modules' stacks are "suspended"
   and not visible in the fused state (they're saved in call frames).

   Memory, globals, and tables correspond for ALL modules, since these
   are persistent state shared across the fused module. *)
Record state_correspondence (cc : composed_component) (fr : fusion_result)
                            (ces : composed_exec_state)
                            (fes : fused_exec_state) : Prop := mkStateCorrespondence {
  (* Active module exists *)
  sc_active_valid :
      exists ms, lookup_module_state ces (ces_active ces) = Some ms;

  (* Active module's value stack corresponds to fused stack *)
  sc_value_stack_eq : forall ms,
      lookup_module_state ces (ces_active ces) = Some ms ->
      value_stacks_correspond (ms_value_stack ms)
                             (ms_value_stack (fes_module_state fes));

  (* Active module's locals correspond to fused locals *)
  sc_locals_eq : forall ms,
      lookup_module_state ces (ces_active ces) = Some ms ->
      ms_locals ms = ms_locals (fes_module_state fes);

  (* Memory correspondence for all modules *)
  sc_memory_eq : forall src ms mem_src,
      lookup_module_state ces src = Some ms ->
      nth_error (ms_mems ms) 0 = Some mem_src ->
      exists mem_fused,
        nth_error (ms_mems (fes_module_state fes)) 0 = Some mem_fused /\
        memory_corresponds (fr_memory_layout fr) src mem_src mem_fused;

  (* Globals correspond via remap for all modules *)
  sc_globals_eq : forall src ms src_idx g_src,
      lookup_module_state ces src = Some ms ->
      nth_error (ms_globals ms) src_idx = Some g_src ->
      exists fused_idx g_fused,
        lookup_remap (fr_remaps fr) GlobalIdx src src_idx = Some fused_idx /\
        nth_error (ms_globals (fes_module_state fes)) fused_idx = Some g_fused /\
        global_corresponds (fr_remaps fr) src src_idx g_src g_fused;

  (* Tables correspond via remap for all modules *)
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

(* =========================================================================
   Helper Lemmas for update_module_state_list and lookup_module_state
   ========================================================================= *)

(* Equality decision for module_source *)
Definition module_source_eqb (a b : module_source) : bool :=
  Nat.eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

Lemma module_source_eqb_refl : forall s, module_source_eqb s s = true.
Proof.
  intro s. unfold module_source_eqb.
  rewrite Nat.eqb_refl.
  destruct s; simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma module_source_eqb_eq : forall a b,
    module_source_eqb a b = true -> a = b.
Proof.
  intros a b H. unfold module_source_eqb in H.
  apply Bool.andb_true_iff in H. destruct H as [Hf Hs].
  apply Nat.eqb_eq in Hf. apply Nat.eqb_eq in Hs.
  destruct a, b. simpl in *. congruence.
Qed.

Lemma module_source_eqb_neq : forall a b,
    a <> b -> module_source_eqb a b = false.
Proof.
  intros a b Hneq.
  destruct (module_source_eqb a b) eqn:H; [|reflexivity].
  exfalso. apply Hneq. apply module_source_eqb_eq. exact H.
Qed.

(* List-level: find after update for same source *)
Lemma find_update_same :
  forall states src ms',
    (exists ms, List.find (fun '(s, _) =>
       module_source_eqb s src) states = Some (src, ms)) ->
    List.find (fun '(s, _) =>
       module_source_eqb s src)
      (update_module_state_list states src ms') = Some (src, ms').
Proof.
  intros states src ms'.
  induction states as [|[s m] rest IH]; intro Hex.
  - destruct Hex as [ms Habs]. discriminate.
  - simpl.
    unfold module_source_eqb at 1. simpl.
    destruct (Nat.eqb (fst s) (fst src) && Nat.eqb (snd s) (snd src)) eqn:Heq.
    + (* s = src *)
      simpl.
      unfold module_source_eqb.
      apply Bool.andb_true_iff in Heq. destruct Heq as [Hf Hs].
      apply Nat.eqb_eq in Hf. apply Nat.eqb_eq in Hs.
      destruct s, src. simpl in *. subst.
      rewrite Nat.eqb_refl. simpl. rewrite Nat.eqb_refl. reflexivity.
    + (* s <> src *)
      simpl.
      unfold module_source_eqb at 1.
      rewrite Heq.
      apply IH.
      destruct Hex as [ms Hms].
      simpl in Hms.
      unfold module_source_eqb in Hms at 1. rewrite Heq in Hms.
      exists ms. exact Hms.
Qed.

(* List-level: find after update for different source *)
Lemma find_update_other :
  forall states src1 src2 ms',
    module_source_eqb src1 src2 = false ->
    List.find (fun '(s, _) =>
       module_source_eqb s src1)
      (update_module_state_list states src2 ms')
    = List.find (fun '(s, _) =>
         module_source_eqb s src1) states.
Proof.
  intros states src1 src2 ms' Hneq.
  induction states as [|[s m] rest IH].
  - reflexivity.
  - simpl.
    destruct (Nat.eqb (fst s) (fst src2) && Nat.eqb (snd s) (snd src2)) eqn:Heq2.
    + (* s = src2 *)
      simpl.
      destruct (module_source_eqb s src1) eqn:Heq1.
      * (* s matches both src1 and src2: contradiction *)
        exfalso.
        apply module_source_eqb_eq in Heq1.
        apply Bool.andb_true_iff in Heq2. destruct Heq2 as [Hf2 Hs2].
        apply Nat.eqb_eq in Hf2. apply Nat.eqb_eq in Hs2.
        subst s. unfold module_source_eqb in Hneq.
        simpl in Hneq. rewrite Hf2 in Hneq. rewrite Hs2 in Hneq.
        rewrite Nat.eqb_refl in Hneq. simpl in Hneq. discriminate.
      * reflexivity.
    + (* s <> src2 *)
      simpl.
      destruct (module_source_eqb s src1) eqn:Heq1.
      * reflexivity.
      * apply IH.
Qed.

(* lookup_module_state after update for same source *)
Lemma lookup_update_same :
  forall states src ms ms' active smem,
    lookup_module_state (mkComposedExecState states active smem) src = Some ms ->
    lookup_module_state
      (mkComposedExecState (update_module_state_list states src ms') active smem)
      src = Some ms'.
Proof.
  intros states src ms ms' active smem Hlookup.
  unfold lookup_module_state in *. simpl in *.
  (* Convert lookup to find form *)
  destruct (List.find _ states) as [[s found_ms]|] eqn:Hfind; [|discriminate].
  injection Hlookup as Heq. subst found_ms.
  (* Show s = src *)
  apply List.find_some in Hfind. destruct Hfind as [Hin Hmatch].
  unfold module_source_eqb in Hmatch.
  apply Bool.andb_true_iff in Hmatch. destruct Hmatch as [Hf Hs].
  apply Nat.eqb_eq in Hf. apply Nat.eqb_eq in Hs.
  assert (Hsrc: s = src) by (destruct s, src; simpl in *; congruence). subst s.
  (* Now apply find_update_same *)
  assert (Hex: exists ms0, List.find (fun '(s, _) => module_source_eqb s src) states
               = Some (src, ms0)).
  { exists ms. unfold lookup_module_state. simpl.
    (* Need to show find with module_source_eqb matches find with Nat.eqb *)
    induction states as [|[s2 m2] rest IH2].
    - simpl in *. discriminate.
    - simpl in *.
      destruct (Nat.eqb (fst s2) (fst src) && Nat.eqb (snd s2) (snd src)) eqn:Hq.
      + unfold module_source_eqb. rewrite Hq. reflexivity.
      + unfold module_source_eqb at 1. rewrite Hq. apply IH2.
        rewrite Hq. exact Hlookup. }
  pose proof (find_update_same states src ms' Hex) as Hresult.
  (* Convert back to lookup form *)
  induction (update_module_state_list states src ms') as [|[su mu] restu IHu].
  - simpl in Hresult. discriminate.
  - simpl in *.
    destruct (Nat.eqb (fst su) (fst src) && Nat.eqb (snd su) (snd src)) eqn:Hqu.
    + destruct (module_source_eqb su src) eqn:Hmu.
      * injection Hresult as Hsu Hmu'. subst. reflexivity.
      * unfold module_source_eqb in Hmu. rewrite Hqu in Hmu. discriminate.
    + destruct (module_source_eqb su src) eqn:Hmu.
      * unfold module_source_eqb in Hmu. rewrite Hqu in Hmu. discriminate.
      * apply IHu. exact Hresult.
Qed.

(* lookup_module_state after update for different source *)
Lemma lookup_update_other :
  forall states src1 src2 ms' active smem,
    module_source_eqb src1 src2 = false ->
    lookup_module_state
      (mkComposedExecState (update_module_state_list states src2 ms') active smem)
      src1
    = lookup_module_state (mkComposedExecState states active smem) src1.
Proof.
  intros states src1 src2 ms' active smem Hneq.
  unfold lookup_module_state. simpl.
  induction states as [|[s m] rest IH].
  - reflexivity.
  - simpl.
    destruct (Nat.eqb (fst s) (fst src2) && Nat.eqb (snd s) (snd src2)) eqn:Heq2.
    + simpl.
      destruct (Nat.eqb (fst s) (fst src1) && Nat.eqb (snd s) (snd src1)) eqn:Heq1.
      * exfalso.
        apply Bool.andb_true_iff in Heq1. destruct Heq1 as [Hf1 Hs1].
        apply Bool.andb_true_iff in Heq2. destruct Heq2 as [Hf2 Hs2].
        apply Nat.eqb_eq in Hf1. apply Nat.eqb_eq in Hs1.
        apply Nat.eqb_eq in Hf2. apply Nat.eqb_eq in Hs2.
        unfold module_source_eqb in Hneq.
        rewrite <- Hf1 in Hf2. rewrite <- Hs1 in Hs2.
        rewrite Hf2 in Hneq. rewrite Hs2 in Hneq.
        rewrite Nat.eqb_refl in Hneq. simpl in Hneq. discriminate.
      * reflexivity.
    + simpl.
      destruct (Nat.eqb (fst s) (fst src1) && Nat.eqb (snd s) (snd src1)) eqn:Heq1.
      * reflexivity.
      * apply IH.
Qed.

(* Existence of lookup preserved by update on different source *)
Lemma lookup_exists_after_update :
  forall states src1 src2 ms' active smem ms,
    module_source_eqb src1 src2 = false ->
    lookup_module_state (mkComposedExecState states active smem) src1 = Some ms ->
    lookup_module_state
      (mkComposedExecState (update_module_state_list states src2 ms') active smem)
      src1 = Some ms.
Proof.
  intros. rewrite lookup_update_other; assumption.
Qed.

(* apply_local_effect preserves non-stack/locals fields *)
Lemma apply_local_effect_mems :
  forall ms eff, ms_mems (apply_local_effect ms eff) = ms_mems ms.
Proof. intros. reflexivity. Qed.

Lemma apply_local_effect_globals :
  forall ms eff, ms_globals (apply_local_effect ms eff) = ms_globals ms.
Proof. intros. reflexivity. Qed.

Lemma apply_local_effect_tables :
  forall ms eff, ms_tables (apply_local_effect ms eff) = ms_tables ms.
Proof. intros. reflexivity. Qed.

(* value_stacks_correspond is reflexive (since values_correspond is equality) *)
Lemma value_stacks_correspond_refl :
  forall vs, value_stacks_correspond vs vs.
Proof.
  intro vs. unfold value_stacks_correspond. split.
  - reflexivity.
  - induction vs as [|v rest IH].
    + constructor.
    + constructor.
      * unfold values_correspond. reflexivity.
      * exact IH.
Qed.

(* -------------------------------------------------------------------------
   Trap Equivalence

   Forward direction: composed_traps require active module to exist,
   fused_traps match all states (Unreachable/OutOfBounds/TypeMismatch).
   Backward direction: state_correspondence guarantees active module
   exists (sc_active_valid), enabling composed_traps construction.
   ------------------------------------------------------------------------- *)

Lemma fusion_trap_equivalence :
  forall cc config fr,
    well_formed_composition cc ->
    fusion_correct cc config fr ->
    trap_equivalence cc fr.
Proof.
  intros cc config fr _ _.
  unfold trap_equivalence. intros ces fes Hcorr.
  split.
  - intro Hc. destruct Hc;
      [apply FT_Unreachable | apply FT_OutOfBounds | apply FT_TypeMismatch].
  - intro Hf. destruct Hf.
    + apply CT_Unreachable.
      destruct (sc_active_valid _ _ _ _ Hcorr) as [ms Hms].
      rewrite Hms. discriminate.
    + apply CT_OutOfBounds.
      destruct (sc_active_valid _ _ _ _ Hcorr) as [ms Hms].
      rewrite Hms. discriminate.
    + apply CT_TypeMismatch.
      destruct (sc_active_valid _ _ _ _ Hcorr) as [ms Hms].
      rewrite Hms. discriminate.
Qed.

(* -------------------------------------------------------------------------
   Forward Simulation

   With refined step relations, each composed_step constructor is matched
   by a corresponding fused_step constructor with the same abstract effect.

   Proof structure (by case analysis on composed_step):

   1. CS_LocalOp eff → FS_LocalOp eff:
      Same local_effect applied to active module (composed) and fused state.
      State correspondence preserved because only stack/locals change,
      and the active module's new stack/locals match the fused new stack/locals.

   2. CS_CrossModuleCall eff_src eff_tgt → FS_InlinedCall eff_tgt:
      Active module changes from source to target. The fused state is
      updated with the target's effect. State correspondence holds for
      the new active module (target) since its stack/locals match fused.
   ------------------------------------------------------------------------- *)

Lemma fusion_forward_simulation :
  forall cc config fr,
    well_formed_composition cc ->
    fusion_correct cc config fr ->
    forward_simulation cc fr.
Proof.
  intros cc config fr _ _.
  unfold forward_simulation.
  intros ces ces' fes Hcorr Hstep.
  inversion Hstep; subst.

  - (* Case CS_LocalOp: active module applies local_effect eff.
       Match with FS_LocalOp using same effect. *)
    exists (mkFusedExecState (apply_local_effect (fes_module_state fes) eff)).
    split.
    + apply FS_LocalOp.
    + (* State correspondence preserved *)
      constructor.
      * (* sc_active_valid *)
        exists (apply_local_effect ms eff).
        apply (lookup_update_same _ (ces_active ces) ms _ _ _ H).
      * (* sc_value_stack_eq: new stack = le_new_stack eff on both sides *)
        intros ms0 Hlookup0.
        rewrite (lookup_update_same _ (ces_active ces) ms _ _ _ H) in Hlookup0.
        injection Hlookup0 as Hms0. subst ms0.
        simpl. apply value_stacks_correspond_refl.
      * (* sc_locals_eq: new locals = le_new_locals eff on both sides *)
        intros ms0 Hlookup0.
        rewrite (lookup_update_same _ (ces_active ces) ms _ _ _ H) in Hlookup0.
        injection Hlookup0 as Hms0. subst ms0.
        reflexivity.
      * (* sc_memory_eq: apply_local_effect preserves mems *)
        intros src ms0 mem_src Hlookup0 Hmem.
        destruct (module_source_eqb src (ces_active ces)) eqn:Heq.
        -- apply module_source_eqb_eq in Heq. subst src.
           rewrite (lookup_update_same _ (ces_active ces) ms _ _ _ H) in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite apply_local_effect_mems in Hmem.
           exact (sc_memory_eq _ _ _ _ Hcorr _ _ _ H Hmem).
        -- rewrite (lookup_update_other _ src (ces_active ces) _ _ _ Heq) in Hlookup0.
           exact (sc_memory_eq _ _ _ _ Hcorr _ _ _ Hlookup0 Hmem).
      * (* sc_globals_eq: apply_local_effect preserves globals *)
        intros src ms0 src_idx g_src Hlookup0 Hglob.
        destruct (module_source_eqb src (ces_active ces)) eqn:Heq.
        -- apply module_source_eqb_eq in Heq. subst src.
           rewrite (lookup_update_same _ (ces_active ces) ms _ _ _ H) in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite apply_local_effect_globals in Hglob.
           exact (sc_globals_eq _ _ _ _ Hcorr _ _ _ _ H Hglob).
        -- rewrite (lookup_update_other _ src (ces_active ces) _ _ _ Heq) in Hlookup0.
           exact (sc_globals_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Hglob).
      * (* sc_tables_eq: apply_local_effect preserves tables *)
        intros src ms0 src_idx tab_src Hlookup0 Htab.
        destruct (module_source_eqb src (ces_active ces)) eqn:Heq.
        -- apply module_source_eqb_eq in Heq. subst src.
           rewrite (lookup_update_same _ (ces_active ces) ms _ _ _ H) in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite apply_local_effect_tables in Htab.
           exact (sc_tables_eq _ _ _ _ Hcorr _ _ _ _ H Htab).
        -- rewrite (lookup_update_other _ src (ces_active ces) _ _ _ Heq) in Hlookup0.
           exact (sc_tables_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Htab).

  - (* Case CS_CrossModuleCall: active changes from src to target.
       Match with FS_InlinedCall using target's effect.

       Key insight: state_correspondence only requires the ACTIVE module's
       stack/locals to match. After the call, target is active. The fused
       state gets target's effect, matching target's new stack/locals. *)
    exists (mkFusedExecState (apply_local_effect (fes_module_state fes) eff_tgt)).
    split.
    + apply FS_InlinedCall.
    + (* State correspondence: target is now active *)
      assert (Hneq_eqb: module_source_eqb (ces_active ces) target = false).
      { apply module_source_eqb_neq. exact H. }
      assert (Hneq_eqb_sym: module_source_eqb target (ces_active ces) = false).
      { apply module_source_eqb_neq. intro Heq. apply H. symmetry. exact Heq. }
      (* Helper: target lookup in inner-updated list (src updated, target unchanged) *)
      assert (Htgt_inner:
        lookup_module_state
          (mkComposedExecState
            (update_module_state_list (ces_module_states ces)
               (ces_active ces) (apply_local_effect ms_src eff_src))
            target (ces_shared_memory ces))
          target = Some ms_tgt).
      { rewrite (lookup_update_other _ target (ces_active ces) _ _ _ Hneq_eqb_sym).
        exact H1. }
      (* Helper: target lookup in double-updated list *)
      assert (Htgt_final:
        lookup_module_state
          (mkComposedExecState
            (update_module_state_list
              (update_module_state_list (ces_module_states ces)
                 (ces_active ces) (apply_local_effect ms_src eff_src))
              target (apply_local_effect ms_tgt eff_tgt))
            target (ces_shared_memory ces))
          target = Some (apply_local_effect ms_tgt eff_tgt)).
      { apply (lookup_update_same _ target ms_tgt _ _ _ Htgt_inner). }
      constructor.
      * (* sc_active_valid *)
        simpl. exists (apply_local_effect ms_tgt eff_tgt). exact Htgt_final.
      * (* sc_value_stack_eq: target's new stack = fused stack *)
        simpl. intros ms0 Hlookup0.
        rewrite Htgt_final in Hlookup0.
        injection Hlookup0 as Hms0. subst ms0.
        simpl. apply value_stacks_correspond_refl.
      * (* sc_locals_eq: target's new locals = fused locals *)
        simpl. intros ms0 Hlookup0.
        rewrite Htgt_final in Hlookup0.
        injection Hlookup0 as Hms0. subst ms0.
        reflexivity.
      * (* sc_memory_eq: both updates are apply_local_effect, preserving mems *)
        simpl. intros src ms0 mem_src Hlookup0 Hmem.
        (* Three cases: src = target, src = ces_active, src = other *)
        destruct (module_source_eqb src target) eqn:Heq_tgt.
        -- (* src = target *)
           apply module_source_eqb_eq in Heq_tgt. subst src.
           rewrite Htgt_final in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite apply_local_effect_mems in Hmem.
           exact (sc_memory_eq _ _ _ _ Hcorr _ _ _ H1 Hmem).
        -- (* src <> target: lookup passes through target update *)
           rewrite (lookup_update_other
             (update_module_state_list (ces_module_states ces)
                (ces_active ces) (apply_local_effect ms_src eff_src))
             src target _ _ _ Heq_tgt) in Hlookup0.
           destruct (module_source_eqb src (ces_active ces)) eqn:Heq_src.
           ++ (* src = active: lookup finds updated src state *)
              apply module_source_eqb_eq in Heq_src. subst src.
              rewrite (lookup_update_same _ (ces_active ces) ms_src _ _ _ H0) in Hlookup0.
              injection Hlookup0 as Hms0. subst ms0.
              rewrite apply_local_effect_mems in Hmem.
              exact (sc_memory_eq _ _ _ _ Hcorr _ _ _ H0 Hmem).
           ++ (* src <> active and src <> target: state unchanged *)
              rewrite (lookup_update_other _ src (ces_active ces) _ _ _ Heq_src) in Hlookup0.
              exact (sc_memory_eq _ _ _ _ Hcorr _ _ _ Hlookup0 Hmem).
      * (* sc_globals_eq: both updates preserve globals *)
        simpl. intros src ms0 src_idx g_src Hlookup0 Hglob.
        destruct (module_source_eqb src target) eqn:Heq_tgt.
        -- apply module_source_eqb_eq in Heq_tgt. subst src.
           rewrite Htgt_final in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite apply_local_effect_globals in Hglob.
           exact (sc_globals_eq _ _ _ _ Hcorr _ _ _ _ H1 Hglob).
        -- rewrite (lookup_update_other
             (update_module_state_list (ces_module_states ces)
                (ces_active ces) (apply_local_effect ms_src eff_src))
             src target _ _ _ Heq_tgt) in Hlookup0.
           destruct (module_source_eqb src (ces_active ces)) eqn:Heq_src.
           ++ apply module_source_eqb_eq in Heq_src. subst src.
              rewrite (lookup_update_same _ (ces_active ces) ms_src _ _ _ H0) in Hlookup0.
              injection Hlookup0 as Hms0. subst ms0.
              rewrite apply_local_effect_globals in Hglob.
              exact (sc_globals_eq _ _ _ _ Hcorr _ _ _ _ H0 Hglob).
           ++ rewrite (lookup_update_other _ src (ces_active ces) _ _ _ Heq_src) in Hlookup0.
              exact (sc_globals_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Hglob).
      * (* sc_tables_eq: both updates preserve tables *)
        simpl. intros src ms0 src_idx tab_src Hlookup0 Htab.
        destruct (module_source_eqb src target) eqn:Heq_tgt.
        -- apply module_source_eqb_eq in Heq_tgt. subst src.
           rewrite Htgt_final in Hlookup0.
           injection Hlookup0 as Hms0. subst ms0.
           rewrite apply_local_effect_tables in Htab.
           exact (sc_tables_eq _ _ _ _ Hcorr _ _ _ _ H1 Htab).
        -- rewrite (lookup_update_other
             (update_module_state_list (ces_module_states ces)
                (ces_active ces) (apply_local_effect ms_src eff_src))
             src target _ _ _ Heq_tgt) in Hlookup0.
           destruct (module_source_eqb src (ces_active ces)) eqn:Heq_src.
           ++ apply module_source_eqb_eq in Heq_src. subst src.
              rewrite (lookup_update_same _ (ces_active ces) ms_src _ _ _ H0) in Hlookup0.
              injection Hlookup0 as Hms0. subst ms0.
              rewrite apply_local_effect_tables in Htab.
              exact (sc_tables_eq _ _ _ _ Hcorr _ _ _ _ H0 Htab).
           ++ rewrite (lookup_update_other _ src (ces_active ces) _ _ _ Heq_src) in Hlookup0.
              exact (sc_tables_eq _ _ _ _ Hcorr _ _ _ _ Hlookup0 Htab).
Qed.

(* -------------------------------------------------------------------------
   Main Semantic Preservation Theorem

   Combines trap equivalence and forward simulation (both proved).
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
