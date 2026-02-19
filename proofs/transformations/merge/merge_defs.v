(* =========================================================================
   Merge Transformation - Core Definitions

   Source: meld-core/src/merger.rs

   The merge transformation combines multiple core modules into a single
   module by:
   1. Concatenating each index space (types, funcs, tables, mems, globals)
   2. Recording the remap table for later instruction rewriting
   3. Optionally computing memory layout for address rebasing

   This file contains core definitions used by other merge modules.

   IMPORTANT: proof-implementation gap
   ------------------------------------
   This model assumes flat concatenation — all imports from every module
   are preserved in the merged output.  The actual Rust code (merger.rs)
   resolves cross-component imports and only keeps unresolved ones.
   See merge_resolution.v for the bridging proof, whose key insight is
   that import resolution is a refinement of flat concatenation which
   preserves the remap properties established here.
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith.
From MeldSpec Require Import wasm_core component_model fusion_types.
Import ListNotations.

(* Wasm page size: 64 KiB *)
Definition wasm_page_size : nat := 65536.

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

(* Generate remaps for MemIdx in SharedMemory mode: all map to 0.
   In SharedMemory mode (merger.rs lines 350, 932-933), all memory indices
   are remapped to 0 because all modules share a single merged memory. *)
Definition gen_remaps_for_space_zero (src : module_source) (m : module)
                                     (space : index_space) (count : nat) : list index_remap :=
  map (fun i => mkIndexRemap space src i 0) (seq 0 count).

(* Generate all remaps for a single module.
   MemIdx behaviour depends on the memory strategy:
   - SharedMemory:   gen_remaps_for_space_zero (all map to 0)
   - SeparateMemory: gen_remaps_for_space      (normal offset, like other spaces)
   All other spaces always use gen_remaps_for_space with cumulative offsets. *)
Definition gen_remaps_for_module (src : module_source) (m : module)
                                  (offsets : index_space -> nat)
                                  (strategy : memory_strategy) : list index_remap :=
  gen_remaps_for_space src m TypeIdx (offsets TypeIdx) (length (mod_types m)) ++
  gen_remaps_for_space src m FuncIdx (offsets FuncIdx)
                       (count_func_imports m + length (mod_funcs m)) ++
  gen_remaps_for_space src m TableIdx (offsets TableIdx)
                       (count_table_imports m + length (mod_tables m)) ++
  match strategy with
  | SharedMemory => gen_remaps_for_space_zero src m MemIdx
                       (count_mem_imports m + length (mod_mems m))
  | SeparateMemory => gen_remaps_for_space src m MemIdx (offsets MemIdx)
                       (count_mem_imports m + length (mod_mems m))
  end ++
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

(* Memory size calculation for a module *)
Definition module_memory_size (m : module) : nat :=
  fold_left (fun a mt =>
    a + lim_min (mem_limits mt) * wasm_page_size
  ) (mod_mems m) 0.

(* Memory layout step function *)
Definition layout_step (acc : list memory_layout * nat) (sm : module_source * module)
    : list memory_layout * nat :=
  let '(layouts, current_addr) := acc in
  let mem_size := module_memory_size (snd sm) in
  (layouts ++ [mkMemoryLayout (fst sm) current_addr mem_size],
   current_addr + mem_size).

Definition compute_memory_layout (input : merge_input) : memory_layout_table :=
  fst (fold_left layout_step input ([], 0)).

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
   Remap Correctness Properties (definitions only)
   ------------------------------------------------------------------------- *)

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

(* Count of items in a given index space for a module *)
Definition space_count (sm : module_source * module) (space : index_space) : nat :=
  let m := snd sm in
  match space with
  | TypeIdx => length (mod_types m)
  | FuncIdx => count_func_imports m + length (mod_funcs m)
  | TableIdx => count_table_imports m + length (mod_tables m)
  | MemIdx => count_mem_imports m + length (mod_mems m)
  | GlobalIdx => count_global_imports m + length (mod_globals m)
  | ElemIdx => length (mod_elems m)
  | DataIdx => length (mod_datas m)
  end.

(* layouts_sequential means each layout ends where next begins *)
Definition layouts_sequential (layouts : memory_layout_table) : Prop :=
  forall i l1 l2,
    nth_error layouts i = Some l1 ->
    nth_error layouts (S i) = Some l2 ->
    ml_base_address l1 + ml_size l1 = ml_base_address l2.

(* Helper: compute offsets for a specific module index *)
Definition offsets_for_module (input : merge_input) (mod_idx : nat)
    : index_space -> nat :=
  fun space => compute_offset input space mod_idx.

(* Generate all remaps for a merge input by folding over modules *)
Fixpoint gen_all_remaps_aux (input : merge_input) (mod_idx : nat)
    (remaining : merge_input) (strategy : memory_strategy) : remap_table :=
  match remaining with
  | [] => []
  | (src, m) :: rest =>
      gen_remaps_for_module src m (offsets_for_module input mod_idx) strategy ++
      gen_all_remaps_aux input (S mod_idx) rest strategy
  end.

Definition gen_all_remaps (input : merge_input) (strategy : memory_strategy)
    : remap_table :=
  gen_all_remaps_aux input 0 input strategy.

(* Default type remap: identity (no cross-module type references yet) *)
Definition default_type_remap (input : merge_input)
    : module_source -> idx -> idx :=
  fun src i =>
    match find (fun smp =>
      Nat.eqb (fst (fst smp)) (fst src) &&
      Nat.eqb (snd (fst smp)) (snd src)
    ) (combine (map fst input) (seq 0 (length input))) with
    | Some (_, mod_idx) => compute_offset input TypeIdx mod_idx + i
    | None => i
    end.

(* Default exportdesc remap *)
Definition default_export_remap (input : merge_input)
    : module_source -> exportdesc -> exportdesc :=
  fun src ed =>
    match find (fun smp =>
      Nat.eqb (fst (fst smp)) (fst src) &&
      Nat.eqb (snd (fst smp)) (snd src)
    ) (combine (map fst input) (seq 0 (length input))) with
    | Some (_, mod_idx) =>
        match ed with
        | ExportFunc i => ExportFunc (compute_offset input FuncIdx mod_idx + i)
        | ExportTable i => ExportTable (compute_offset input TableIdx mod_idx + i)
        | ExportMem i => ExportMem (compute_offset input MemIdx mod_idx + i)
        | ExportGlobal i => ExportGlobal (compute_offset input GlobalIdx mod_idx + i)
        end
    | None => ed
    end.

(* Default func remap *)
Definition default_func_remap (input : merge_input)
    : module_source -> idx -> idx :=
  fun src i =>
    match find (fun smp =>
      Nat.eqb (fst (fst smp)) (fst src) &&
      Nat.eqb (snd (fst smp)) (snd src)
    ) (combine (map fst input) (seq 0 (length input))) with
    | Some (_, mod_idx) => compute_offset input FuncIdx mod_idx + i
    | None => i
    end.

Definition merge_modules (input : merge_input)
    (strategy : memory_strategy) : module :=
  mkModule
    (merge_types input)
    (merge_funcs input (default_type_remap input))
    (merge_tables input)
    (merge_mems input strategy)
    (merge_globals input)
    (merge_elems input)
    (merge_datas input)
    (merge_start input (default_func_remap input))
    (merge_imports input)
    (merge_exports input (default_export_remap input)).

(* Count for a space in a module *)
Definition space_count_of_module (m : module) (space : index_space) : nat :=
  match space with
  | TypeIdx => length (mod_types m)
  | FuncIdx => count_func_imports m + length (mod_funcs m)
  | TableIdx => count_table_imports m + length (mod_tables m)
  | MemIdx => count_mem_imports m + length (mod_mems m)
  | GlobalIdx => count_global_imports m + length (mod_globals m)
  | ElemIdx => length (mod_elems m)
  | DataIdx => length (mod_datas m)
  end.

(* Total count across all modules in input *)
Definition total_space_count (input : merge_input) (space : index_space) : nat :=
  fold_left (fun acc sm => acc + space_count_of_module (snd sm) space) input 0.

(* Sources are unique: each (comp_idx, mod_idx) pair appears at most once *)
Definition unique_sources (input : merge_input) : Prop :=
  NoDup (map fst input).

(* End of merge_defs *)
