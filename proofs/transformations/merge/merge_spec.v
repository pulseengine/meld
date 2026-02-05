(* =========================================================================
   Merge Transformation Specification

   Source: meld-core/src/merger.rs

   The merge transformation combines multiple core modules into a single
   module by:
   1. Concatenating each index space (types, funcs, tables, mems, globals)
   2. Recording the remap table for later instruction rewriting
   3. Optionally computing memory layout for address rebasing
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool.
From MeldSpec Require Import wasm_core component_model fusion_spec.
Import ListNotations.

(* -------------------------------------------------------------------------
   Merge Input: A list of modules with their sources
   ------------------------------------------------------------------------- *)

Definition merge_input := list (module_source * module).

(* -------------------------------------------------------------------------
   Index Space Offsets

   When merging, each module's indices are offset by the count of all
   preceding items in that index space.
   ------------------------------------------------------------------------- *)

(* Compute the offset for a module in an index space *)
Definition compute_offset (input : merge_input) (space : index_space)
                          (mod_idx : nat) : nat :=
  let prior := firstn mod_idx input in
  fold_left (fun acc sm =>
    let m := snd sm in
    acc + match space with
    | TypeIdx => length (mod_types m)
    | FuncIdx => count_func_imports m + length (mod_funcs m)
    | TableIdx => count_table_imports m + length (mod_tables m)
    | MemIdx => count_mem_imports m + length (mod_mems m)
    | GlobalIdx => count_global_imports m + length (mod_globals m)
    | ElemIdx => length (mod_elems m)
    | DataIdx => length (mod_datas m)
    end
  ) prior 0.

(* -------------------------------------------------------------------------
   Remap Generation

   Generate the remap table for all modules.
   ------------------------------------------------------------------------- *)

(* Generate remaps for a single index space of a single module *)
Definition gen_remaps_for_space (src : module_source) (m : module)
                                (space : index_space) (offset : nat)
                                (count : nat) : list index_remap :=
  map (fun i => mkIndexRemap space src i (offset + i)) (seq 0 count).

(* Generate all remaps for a single module *)
Definition gen_remaps_for_module (src : module_source) (m : module)
                                  (offsets : index_space -> nat) : list index_remap :=
  gen_remaps_for_space src m TypeIdx (offsets TypeIdx) (length (mod_types m)) ++
  gen_remaps_for_space src m FuncIdx (offsets FuncIdx)
                       (count_func_imports m + length (mod_funcs m)) ++
  gen_remaps_for_space src m TableIdx (offsets TableIdx)
                       (count_table_imports m + length (mod_tables m)) ++
  gen_remaps_for_space src m MemIdx (offsets MemIdx)
                       (count_mem_imports m + length (mod_mems m)) ++
  gen_remaps_for_space src m GlobalIdx (offsets GlobalIdx)
                       (count_global_imports m + length (mod_globals m)) ++
  gen_remaps_for_space src m ElemIdx (offsets ElemIdx) (length (mod_elems m)) ++
  gen_remaps_for_space src m DataIdx (offsets DataIdx) (length (mod_datas m)).

(* -------------------------------------------------------------------------
   Type Merging

   Types are merged by concatenation. Since types are structural,
   identical types from different modules remain separate (conservative).
   ------------------------------------------------------------------------- *)

Definition merge_types (input : merge_input) : list functype :=
  flat_map (fun sm => mod_types (snd sm)) input.

(* -------------------------------------------------------------------------
   Import Merging

   Imports are merged, but identical imports can be deduplicated.
   For now, we use simple concatenation.
   ------------------------------------------------------------------------- *)

Definition merge_imports (input : merge_input) : list import :=
  flat_map (fun sm => mod_imports (snd sm)) input.

(* -------------------------------------------------------------------------
   Function Merging

   Functions are concatenated. Their type indices must be remapped.
   ------------------------------------------------------------------------- *)

Definition remap_func_type (remap : idx -> idx) (f : func) : func :=
  mkFunc (remap (func_type f)) (func_locals f) (func_body f).

Definition merge_funcs (input : merge_input)
                       (type_remap : module_source -> idx -> idx) : list func :=
  flat_map (fun sm =>
    let src := fst sm in
    let m := snd sm in
    map (remap_func_type (type_remap src)) (mod_funcs m)
  ) input.

(* -------------------------------------------------------------------------
   Memory Merging

   Depends on the memory strategy:
   - SharedMemory: Combine into one memory, compute layout
   - SeparateMemory: Concatenate (multi-memory)
   ------------------------------------------------------------------------- *)

Definition merge_mems_shared (input : merge_input) : list memtype :=
  (* Single memory with combined size *)
  let total_min := fold_left (fun acc sm =>
    acc + fold_left (fun a mt => a + lim_min (mem_limits mt))
                    (mod_mems (snd sm)) 0
  ) input 0 in
  [mkMemtype (mkLimits total_min None) false].

Definition merge_mems_separate (input : merge_input) : list memtype :=
  flat_map (fun sm => mod_mems (snd sm)) input.

Definition merge_mems (input : merge_input) (strategy : memory_strategy) : list memtype :=
  match strategy with
  | SharedMemory => merge_mems_shared input
  | SeparateMemory => merge_mems_separate input
  end.

(* -------------------------------------------------------------------------
   Memory Layout Computation (for SharedMemory)
   ------------------------------------------------------------------------- *)

Definition compute_memory_layout (input : merge_input) : memory_layout_table :=
  let '(layouts, _) := fold_left (fun acc sm =>
    let '(layouts, current_addr) := acc in
    let src := fst sm in
    let m := snd sm in
    let mem_size := fold_left (fun a mt =>
      a + lim_min (mem_limits mt) * 65536 (* pages to bytes *)
    ) (mod_mems m) 0 in
    let new_layout := mkMemoryLayout src current_addr mem_size in
    (layouts ++ [new_layout], current_addr + mem_size)
  ) input ([], 0) in
  layouts.

(* -------------------------------------------------------------------------
   Global Merging

   Globals are concatenated. Init expressions may need rewriting.
   ------------------------------------------------------------------------- *)

Definition merge_globals (input : merge_input) : list global :=
  flat_map (fun sm => mod_globals (snd sm)) input.

(* -------------------------------------------------------------------------
   Table Merging

   Tables are concatenated.
   ------------------------------------------------------------------------- *)

Definition merge_tables (input : merge_input) : list tabletype :=
  flat_map (fun sm => mod_tables (snd sm)) input.

(* -------------------------------------------------------------------------
   Element Merging

   Element segments are concatenated. Indices need remapping.
   ------------------------------------------------------------------------- *)

Definition merge_elems (input : merge_input) : list elem :=
  flat_map (fun sm => mod_elems (snd sm)) input.

(* -------------------------------------------------------------------------
   Data Merging

   Data segments are concatenated. With SharedMemory, offsets are adjusted.
   ------------------------------------------------------------------------- *)

Definition merge_datas (input : merge_input) : list data :=
  flat_map (fun sm => mod_datas (snd sm)) input.

(* -------------------------------------------------------------------------
   Export Merging

   Exports from all modules are collected. Conflicts must be resolved.
   ------------------------------------------------------------------------- *)

Definition merge_exports (input : merge_input)
                         (remap : module_source -> exportdesc -> exportdesc)
                         : list export :=
  flat_map (fun sm =>
    let src := fst sm in
    let m := snd sm in
    map (fun e => mkExport (exp_name e) (remap src (exp_desc e))) (mod_exports m)
  ) input.

(* -------------------------------------------------------------------------
   Start Function Merging

   If multiple modules have start functions, they must be sequenced.
   We create a synthetic start function that calls all original starts.
   ------------------------------------------------------------------------- *)

Definition merge_start (input : merge_input)
                       (func_remap : module_source -> idx -> idx) : option idx :=
  let starts := flat_map (fun sm =>
    let src := fst sm in
    let m := snd sm in
    match mod_start m with
    | Some s => [func_remap src s]
    | None => []
    end
  ) input in
  match starts with
  | [] => None
  | [s] => Some s
  | _ => None (* TODO: Synthesize combined start function *)
  end.

(* -------------------------------------------------------------------------
   Complete Merge Operation
   ------------------------------------------------------------------------- *)

Record merge_result : Type := mkMergeResult {
  mr_module : module;
  mr_remaps : remap_table;
  mr_memory_layout : option memory_layout_table;
}.

(* -------------------------------------------------------------------------
   Merge Correctness Properties
   ------------------------------------------------------------------------- *)

(* Offset computation is monotonic *)
Lemma offset_monotonic :
  forall input space i j,
    i <= j ->
    j < length input ->
    compute_offset input space i <= compute_offset input space j.
Proof.
  (* TODO: Prove by induction on j - i *)
Admitted.

(* Remaps are complete: every source index has a remap *)
Definition remaps_complete (input : merge_input) (remaps : remap_table) : Prop :=
  forall src m space src_idx,
    In (src, m) input ->
    src_idx < match space with
              | TypeIdx => length (mod_types m)
              | FuncIdx => count_func_imports m + length (mod_funcs m)
              | TableIdx => count_table_imports m + length (mod_tables m)
              | MemIdx => count_mem_imports m + length (mod_mems m)
              | GlobalIdx => count_global_imports m + length (mod_globals m)
              | ElemIdx => length (mod_elems m)
              | DataIdx => length (mod_datas m)
              end ->
    exists fused_idx,
      lookup_remap remaps space src src_idx = Some fused_idx.

(* Remaps are injective per space *)
Definition remaps_injective (remaps : remap_table) : Prop :=
  forall r1 r2,
    In r1 remaps ->
    In r2 remaps ->
    ir_space r1 = ir_space r2 ->
    ir_fused_idx r1 = ir_fused_idx r2 ->
    ir_source r1 = ir_source r2 /\ ir_source_idx r1 = ir_source_idx r2.

(* Offset-based remapping preserves order *)
Theorem remap_preserves_order :
  forall (input : merge_input) (space : index_space)
         (src1 src2 : module_source) (i1 i2 : idx) (remaps : remap_table),
    (* If src1 comes before src2 in the input *)
    (* Then all indices from src1 come before indices from src2 *)
    True. (* TODO: Formalize and prove *)
Proof.
Admitted.

(* Memory layout is disjoint *)
Theorem memory_layout_disjoint :
  forall (input : merge_input),
    disjoint_layouts (compute_memory_layout input).
Proof.
  (* TODO: Prove that sequential allocation produces disjoint regions *)
Admitted.

(* -------------------------------------------------------------------------
   Main Merge Correctness Theorem

   If we merge modules correctly, looking up any remapped index in the
   fused module yields the same entity as in the source module.
   ------------------------------------------------------------------------- *)

Theorem merge_correctness :
  forall input remaps merged,
    (* Given a valid merge result *)
    remaps_complete input remaps ->
    remaps_injective remaps ->
    (* For any source index that maps to a fused index *)
    forall src m space src_idx fused_idx,
      In (src, m) input ->
      lookup_remap remaps space src src_idx = Some fused_idx ->
      (* The fused index is valid in the merged module *)
      match space with
      | TypeIdx => fused_idx < length (mod_types merged)
      | FuncIdx => valid_funcidx merged fused_idx
      | TableIdx => valid_tableidx merged fused_idx
      | MemIdx => valid_memidx merged fused_idx
      | GlobalIdx => valid_globalidx merged fused_idx
      | ElemIdx => fused_idx < length (mod_elems merged)
      | DataIdx => fused_idx < length (mod_datas merged)
      end.
Proof.
  (* TODO: Prove by construction of the remap table *)
Admitted.

(* End of merge_spec *)
