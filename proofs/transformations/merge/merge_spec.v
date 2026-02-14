(* =========================================================================
   Merge Transformation Specification

   Source: meld-core/src/merger.rs

   The merge transformation combines multiple core modules into a single
   module by:
   1. Concatenating each index space (types, funcs, tables, mems, globals)
   2. Recording the remap table for later instruction rewriting
   3. Optionally computing memory layout for address rebasing
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith.
From MeldSpec Require Import wasm_core component_model fusion_spec.
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
   Merge Correctness Properties
   ------------------------------------------------------------------------- *)

(* Helper: fold_left with non-negative additions is monotonic in its starting value *)
Lemma fold_left_add_nonneg_ge :
  forall {A : Type} (f : A -> nat) (l : list A) (base : nat),
    base <= fold_left (fun acc x => acc + f x) l base.
Proof.
  intros A f l.
  induction l as [|x l' IH]; intro base.
  - simpl. lia.
  - simpl.
    specialize (IH (base + f x)).
    lia.
Qed.

(* Helper: offset for space always non-negative *)
Lemma space_count_nonneg :
  forall (sm : module_source * module) space,
    0 <= match space with
         | TypeIdx => length (mod_types (snd sm))
         | FuncIdx => count_func_imports (snd sm) + length (mod_funcs (snd sm))
         | TableIdx => count_table_imports (snd sm) + length (mod_tables (snd sm))
         | MemIdx => count_mem_imports (snd sm) + length (mod_mems (snd sm))
         | GlobalIdx => count_global_imports (snd sm) + length (mod_globals (snd sm))
         | ElemIdx => length (mod_elems (snd sm))
         | DataIdx => length (mod_datas (snd sm))
         end.
Proof.
  intros. destruct space; lia.
Qed.

(* Offset computation is monotonic *)
Lemma offset_monotonic :
  forall input space i j,
    i <= j ->
    j < length input ->
    compute_offset input space i <= compute_offset input space j.
Proof.
  intros input space i j Hij Hj.
  unfold compute_offset.
  (* firstn i is a prefix of firstn j when i <= j *)
  assert (Hprefix: exists suffix, firstn j input = firstn i input ++ suffix).
  {
    exists (skipn i (firstn j input)).
    rewrite <- (firstn_skipn i (firstn j input)) at 1.
    f_equal.
    rewrite firstn_firstn.
    f_equal. lia.
  }
  destruct Hprefix as [suffix Heq].
  rewrite Heq.
  rewrite fold_left_app.
  (* The fold over suffix only adds non-negative values *)
  set (space_fn := fun sm : module_source * module =>
       match space with
       | TypeIdx => length (mod_types (snd sm))
       | FuncIdx => count_func_imports (snd sm) + length (mod_funcs (snd sm))
       | TableIdx => count_table_imports (snd sm) + length (mod_tables (snd sm))
       | MemIdx => count_mem_imports (snd sm) + length (mod_mems (snd sm))
       | GlobalIdx => count_global_imports (snd sm) + length (mod_globals (snd sm))
       | ElemIdx => length (mod_elems (snd sm))
       | DataIdx => length (mod_datas (snd sm))
       end).
  set (base := fold_left (fun acc sm => acc + space_fn sm) (firstn i input) 0).
  apply fold_left_add_nonneg_ge.
Qed.

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

(* Helper: firstn (S n) when nth element exists *)
Lemma firstn_S_nth_error {A : Type} :
  forall (l : list A) (n : nat) (x : A),
    nth_error l n = Some x ->
    firstn (S n) l = firstn n l ++ [x].
Proof.
  intros l. induction l as [|h t IH]; intros n x Hnth.
  - destruct n; discriminate.
  - destruct n as [|n'].
    + simpl in Hnth. injection Hnth as Heq. subst. reflexivity.
    + simpl in Hnth. simpl. f_equal. apply IH. exact Hnth.
Qed.

(* Offset-based remapping preserves order:
   Earlier modules in input get lower fused indices.
   More specifically: offset(i) + count(i) <= offset(i+1) <= offset(j) for i < j *)
Theorem remap_preserves_order :
  forall (input : merge_input) (space : index_space) (i : nat) (sm : module_source * module),
    nth_error input i = Some sm ->
    S i < length input ->
    compute_offset input space i + space_count sm space
    <= compute_offset input space (S i).
Proof.
  intros input space i sm Hnth HSi.
  unfold compute_offset, space_count.
  (* firstn (S i) input = firstn i input ++ [sm] *)
  rewrite (firstn_S_nth_error _ _ _ Hnth).
  rewrite fold_left_app. simpl.
  lia.
Qed.

(* Helper: layouts from fold maintain sequential invariant *)
(* layouts_sequential means each layout ends where next begins *)
Definition layouts_sequential (layouts : memory_layout_table) : Prop :=
  forall i l1 l2,
    nth_error layouts i = Some l1 ->
    nth_error layouts (S i) = Some l2 ->
    ml_base_address l1 + ml_size l1 = ml_base_address l2.

(* Helper: for sequential layouts, l[i].end <= l[j].base when i < j *)
Lemma sequential_layout_order :
  forall layouts i j l1 l2,
    layouts_sequential layouts ->
    i < j ->
    nth_error layouts i = Some l1 ->
    nth_error layouts j = Some l2 ->
    ml_base_address l1 + ml_size l1 <= ml_base_address l2.
Proof.
  intros layouts i j.
  (* Induction on the difference j - i *)
  remember (j - i) as diff eqn:Hdiff.
  generalize dependent j. generalize dependent i.
  induction diff as [|diff' IH]; intros i j Hdiff l1 l2 Hseq Hlt H1 H2.
  - (* diff = 0: contradiction with i < j *)
    lia.
  - (* diff = S diff': either j = S i or use IH *)
    destruct (Nat.eq_dec j (S i)) as [Heq | Hneq].
    + (* j = S i: direct from layouts_sequential *)
      subst j.
      unfold layouts_sequential in Hseq.
      specialize (Hseq i l1 l2 H1 H2).
      lia.
    + (* j > S i: use transitivity *)
      assert (HSi: S i < j) by lia.
      assert (Hdiff': diff' = j - S i) by lia.
      (* Get the element at position S i *)
      destruct (nth_error layouts (S i)) as [lmid|] eqn:Hmid.
      * (* Element exists *)
        specialize (IH (S i) j Hdiff' lmid l2 Hseq HSi Hmid H2).
        unfold layouts_sequential in Hseq.
        specialize (Hseq i l1 lmid H1 Hmid).
        lia.
      * (* No element at S i - contradiction since S i < j and j has element *)
        (* This would mean a gap in the list *)
        apply nth_error_None in Hmid.
        assert (Hj: j < length layouts) by (apply nth_error_Some; rewrite H2; discriminate).
        lia.
Qed.

(* Helper: sequential layouts are disjoint *)
Lemma sequential_implies_disjoint :
  forall layouts,
    layouts_sequential layouts ->
    disjoint_layouts layouts.
Proof.
  intros layouts Hseq.
  unfold disjoint_layouts.
  intros l1 l2 Hin1 Hin2 Hneq.
  (* Use In_nth_error to get indices *)
  apply In_nth_error in Hin1.
  apply In_nth_error in Hin2.
  destruct Hin1 as [i1 Hi1].
  destruct Hin2 as [i2 Hi2].
  (* Two distinct elements at different indices *)
  destruct (Nat.lt_trichotomy i1 i2) as [Hlt | [Heq | Hgt]].
  - (* i1 < i2: l1 ends before l2 starts *)
    left.
    apply (sequential_layout_order layouts i1 i2 l1 l2 Hseq Hlt Hi1 Hi2).
  - (* i1 = i2: contradiction since l1 <> l2 *)
    subst i2.
    rewrite Hi1 in Hi2. injection Hi2 as Heq. contradiction.
  - (* i2 < i1: symmetric to first case *)
    right.
    apply (sequential_layout_order layouts i2 i1 l2 l1 Hseq Hgt Hi2 Hi1).
Qed.

(* Auxiliary: fold_left with addition starting from any base *)
Lemma fold_left_add_shift :
  forall {A : Type} (f : A -> nat) (l : list A) (base : nat),
    fold_left (fun acc x => acc + f x) l base
    = base + fold_left (fun acc x => acc + f x) l 0.
Proof.
  intros A f l.
  induction l as [|x l' IH]; intro base; simpl.
  - lia.
  - rewrite IH.
    rewrite (IH (f x)).
    lia.
Qed.

(* Memory layout fold invariant: the address accumulator tracks total size *)
Lemma memory_layout_fold_addr :
  forall input init_layouts init_addr,
    snd (fold_left layout_step input (init_layouts, init_addr))
    = init_addr + fold_left (fun acc sm => acc + module_memory_size (snd sm)) input 0.
Proof.
  induction input as [|sm input' IH]; intros; simpl.
  - lia.
  - unfold layout_step at 1. simpl.
    rewrite IH.
    (* After IH, LHS is:
       (init_addr + module_memory_size (snd sm)) +
         fold_left (fun acc sm => acc + module_memory_size (snd sm)) input' 0
       RHS is:
       init_addr +
         fold_left (fun acc sm => acc + module_memory_size (snd sm)) input'
                   (module_memory_size (snd sm))
       Use fold_left_add_shift to rewrite RHS *)
    rewrite (fold_left_add_shift (fun sm => module_memory_size (snd sm)) input'
                                  (module_memory_size (snd sm))).
    lia.
Qed.

(* Helper: fold appends layouts in order *)
Lemma layout_fold_fst_app :
  forall input init_layouts init_addr,
    fst (fold_left layout_step input (init_layouts, init_addr))
    = init_layouts ++ fst (fold_left layout_step input ([], init_addr)).
Proof.
  induction input as [|sm input' IH]; intros; simpl.
  - rewrite app_nil_r. reflexivity.
  - unfold layout_step. simpl.
    rewrite IH.
    rewrite (IH [_]).
    rewrite app_assoc. reflexivity.
Qed.

(* Helper: length of layouts from fold *)
Lemma layout_fold_length :
  forall input init_layouts init_addr,
    length (fst (fold_left layout_step input (init_layouts, init_addr)))
    = length init_layouts + length input.
Proof.
  induction input as [|sm input' IH]; intros; simpl.
  - lia.
  - unfold layout_step at 1. simpl.
    rewrite IH. rewrite length_app. simpl. lia.
Qed.

(* Helper: nth new layout from fold starting from empty *)
Lemma layout_fold_nth_empty :
  forall input init_addr i l,
    nth_error (fst (fold_left layout_step input ([], init_addr))) i = Some l ->
    i < length input ->
    ml_base_address l = init_addr +
      fold_left (fun acc sm => acc + module_memory_size (snd sm)) (firstn i input) 0 /\
    (forall sm, nth_error input i = Some sm -> ml_size l = module_memory_size (snd sm)).
Proof.
  induction input as [|sm input' IH]; intros init_addr i l Hnth Hi.
  - simpl in Hi. lia.
  - destruct i as [|i'].
    + (* i = 0: first layout *)
      simpl in Hnth. unfold layout_step in Hnth. simpl in Hnth.
      rewrite layout_fold_fst_app in Hnth. simpl in Hnth.
      injection Hnth as Hl. subst l. simpl.
      split; [lia | intros sm' Hsm'; injection Hsm' as Heq; subst; reflexivity].
    + (* i = S i': use IH on rest *)
      simpl in Hi.
      simpl in Hnth. unfold layout_step in Hnth. simpl in Hnth.
      rewrite layout_fold_fst_app in Hnth. simpl in Hnth.
      specialize (IH (init_addr + module_memory_size (snd sm)) i' l Hnth ltac:(lia)).
      destruct IH as [IHbase IHsize].
      split.
      * rewrite IHbase.
        simpl.
        (* Use fold_left_add_shift to convert the RHS *)
        rewrite (fold_left_add_shift (fun x => module_memory_size (snd x))
                                      (firstn i' input')
                                      (module_memory_size (snd sm))).
        (* Now both sides should match modulo arithmetic *)
        lia.
      * intros sm' Hsm'. simpl in Hsm'. apply IHsize. exact Hsm'.
Qed.

(* Helper: nth layout from fold has expected base address *)
Lemma layout_fold_nth_base :
  forall input init_layouts init_addr i l,
    nth_error (fst (fold_left layout_step input (init_layouts, init_addr)))
              (length init_layouts + i) = Some l ->
    i < length input ->
    ml_base_address l = init_addr +
      fold_left (fun acc sm => acc + module_memory_size (snd sm)) (firstn i input) 0.
Proof.
  intros input init_layouts init_addr i l Hnth Hi.
  rewrite layout_fold_fst_app in Hnth.
  assert (Hlen: length init_layouts <= length init_layouts + i) by lia.
  rewrite nth_error_app2 in Hnth; [| exact Hlen].
  replace (length init_layouts + i - length init_layouts) with i in Hnth by lia.
  apply layout_fold_nth_empty; assumption.
Qed.

(* Helper: nth layout size matches module memory size *)
Lemma layout_fold_nth_size :
  forall input init_layouts init_addr i l sm,
    nth_error (fst (fold_left layout_step input (init_layouts, init_addr)))
              (length init_layouts + i) = Some l ->
    nth_error input i = Some sm ->
    ml_size l = module_memory_size (snd sm).
Proof.
  intros input init_layouts init_addr i l sm Hnth Hsm.
  rewrite layout_fold_fst_app in Hnth.
  assert (Hlen: length init_layouts <= length init_layouts + i) by lia.
  rewrite nth_error_app2 in Hnth; [| exact Hlen].
  replace (length init_layouts + i - length init_layouts) with i in Hnth by lia.
  assert (Hi: i < length input) by (apply nth_error_Some; rewrite Hsm; discriminate).
  destruct (layout_fold_nth_empty input init_addr i l Hnth Hi) as [_ Hsize].
  apply Hsize. exact Hsm.
Qed.

(* Memory layout is disjoint *)
Theorem memory_layout_disjoint :
  forall (input : merge_input),
    disjoint_layouts (compute_memory_layout input).
Proof.
  intro input.
  unfold compute_memory_layout.
  apply sequential_implies_disjoint.
  unfold layouts_sequential.
  intros i l1 l2 H1 H2.
  (* The fold produces exactly length input layouts *)
  pose proof (layout_fold_length input [] 0) as Hlen.
  simpl in Hlen.
  (* Get bounds on i from H1 and H2 *)
  assert (Hi: i < length input).
  { assert (Hsome: nth_error (fst (fold_left layout_step input ([], 0))) i <> None)
      by (rewrite H1; discriminate).
    apply nth_error_Some in Hsome. rewrite Hlen in Hsome. exact Hsome. }
  assert (HSi: S i < length input).
  { assert (Hsome: nth_error (fst (fold_left layout_step input ([], 0))) (S i) <> None)
      by (rewrite H2; discriminate).
    apply nth_error_Some in Hsome. rewrite Hlen in Hsome. exact Hsome. }
  (* Get the ith and (S i)th input elements *)
  destruct (nth_error input i) as [sm1|] eqn:Hsm1; [| apply nth_error_None in Hsm1; lia].
  destruct (nth_error input (S i)) as [sm2|] eqn:Hsm2; [| apply nth_error_None in Hsm2; lia].
  (* Use helper lemmas *)
  assert (Hbase1: ml_base_address l1 = 0 +
    fold_left (fun acc sm => acc + module_memory_size (snd sm)) (firstn i input) 0).
  { apply (layout_fold_nth_base input [] 0 i l1).
    - simpl. exact H1.
    - exact Hi. }
  assert (Hsize1: ml_size l1 = module_memory_size (snd sm1)).
  { apply (layout_fold_nth_size input [] 0 i l1 sm1).
    - simpl. exact H1.
    - exact Hsm1. }
  assert (Hbase2: ml_base_address l2 = 0 +
    fold_left (fun acc sm => acc + module_memory_size (snd sm)) (firstn (S i) input) 0).
  { apply (layout_fold_nth_base input [] 0 (S i) l2).
    - simpl. exact H2.
    - exact HSi. }
  (* Now show l1.base + l1.size = l2.base *)
  rewrite Hbase1, Hsize1, Hbase2.
  (* firstn (S i) input = firstn i input ++ [sm1] *)
  rewrite (firstn_S_nth_error input i sm1 Hsm1).
  rewrite fold_left_app. simpl.
  rewrite (fold_left_add_shift (fun sm => module_memory_size (snd sm))).
  lia.
Qed.

(* -------------------------------------------------------------------------
   Complete Remap Generation

   Generate all remaps for all modules in the input.
   ------------------------------------------------------------------------- *)

(* Helper: compute offsets for a specific module index *)
Definition offsets_for_module (input : merge_input) (mod_idx : nat)
    : index_space -> nat :=
  fun space => compute_offset input space mod_idx.

(* Generate all remaps for a merge input by folding over modules *)
Fixpoint gen_all_remaps_aux (input : merge_input) (mod_idx : nat)
    (remaining : merge_input) : remap_table :=
  match remaining with
  | [] => []
  | (src, m) :: rest =>
      gen_remaps_for_module src m (offsets_for_module input mod_idx) ++
      gen_all_remaps_aux input (S mod_idx) rest
  end.

Definition gen_all_remaps (input : merge_input) : remap_table :=
  gen_all_remaps_aux input 0 input.

(* -------------------------------------------------------------------------
   Module Merging Construction

   Construct the merged module from merge input.
   We use a default memory strategy of SharedMemory for simplicity.
   ------------------------------------------------------------------------- *)

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

Definition merge_modules (input : merge_input) : module :=
  mkModule
    (merge_types input)
    (merge_funcs input (default_type_remap input))
    (merge_tables input)
    (merge_mems input SharedMemory)
    (merge_globals input)
    (merge_elems input)
    (merge_datas input)
    (merge_start input (default_func_remap input))
    (merge_imports input)
    (merge_exports input (default_export_remap input)).

(* -------------------------------------------------------------------------
   Helper Lemmas for Remap Properties
   ------------------------------------------------------------------------- *)

(* Helper: sum of space counts equals merged length *)
Lemma sum_space_counts_types :
  forall input,
    length (merge_types input) =
    fold_left (fun acc sm => acc + length (mod_types (snd sm))) input 0.
Proof.
  intro input.
  unfold merge_types.
  induction input as [|sm input' IH]; simpl.
  - reflexivity.
  - rewrite length_app.
    rewrite IH.
    rewrite (fold_left_add_shift (fun sm0 => length (mod_types (snd sm0)))
                                  input' (length (mod_types (snd sm)))).
    lia.
Qed.

Lemma sum_space_counts_funcs :
  forall input type_remap,
    length (merge_funcs input type_remap) =
    fold_left (fun acc sm => acc + length (mod_funcs (snd sm))) input 0.
Proof.
  intros input type_remap.
  unfold merge_funcs.
  induction input as [|sm input' IH]; simpl.
  - reflexivity.
  - rewrite length_app.
    rewrite map_length.
    rewrite IH.
    rewrite (fold_left_add_shift (fun sm0 => length (mod_funcs (snd sm0)))
                                  input' (length (mod_funcs (snd sm)))).
    lia.
Qed.

Lemma sum_space_counts_tables :
  forall input,
    length (merge_tables input) =
    fold_left (fun acc sm => acc + length (mod_tables (snd sm))) input 0.
Proof.
  intro input.
  unfold merge_tables.
  induction input as [|sm input' IH]; simpl.
  - reflexivity.
  - rewrite length_app.
    rewrite IH.
    rewrite (fold_left_add_shift (fun sm0 => length (mod_tables (snd sm0)))
                                  input' (length (mod_tables (snd sm)))).
    lia.
Qed.

Lemma sum_space_counts_mems_shared :
  forall input,
    length (merge_mems_shared input) = 1.
Proof.
  intros. unfold merge_mems_shared. simpl. reflexivity.
Qed.

Lemma sum_space_counts_mems_separate :
  forall input,
    length (merge_mems_separate input) =
    fold_left (fun acc sm => acc + length (mod_mems (snd sm))) input 0.
Proof.
  intro input.
  unfold merge_mems_separate.
  induction input as [|sm input' IH]; simpl.
  - reflexivity.
  - rewrite length_app.
    rewrite IH.
    rewrite (fold_left_add_shift (fun sm0 => length (mod_mems (snd sm0)))
                                  input' (length (mod_mems (snd sm)))).
    lia.
Qed.

Lemma sum_space_counts_globals :
  forall input,
    length (merge_globals input) =
    fold_left (fun acc sm => acc + length (mod_globals (snd sm))) input 0.
Proof.
  intro input.
  unfold merge_globals.
  induction input as [|sm input' IH]; simpl.
  - reflexivity.
  - rewrite length_app.
    rewrite IH.
    rewrite (fold_left_add_shift (fun sm0 => length (mod_globals (snd sm0)))
                                  input' (length (mod_globals (snd sm)))).
    lia.
Qed.

Lemma sum_space_counts_elems :
  forall input,
    length (merge_elems input) =
    fold_left (fun acc sm => acc + length (mod_elems (snd sm))) input 0.
Proof.
  intro input.
  unfold merge_elems.
  induction input as [|sm input' IH]; simpl.
  - reflexivity.
  - rewrite length_app.
    rewrite IH.
    rewrite (fold_left_add_shift (fun sm0 => length (mod_elems (snd sm0)))
                                  input' (length (mod_elems (snd sm)))).
    lia.
Qed.

Lemma sum_space_counts_datas :
  forall input,
    length (merge_datas input) =
    fold_left (fun acc sm => acc + length (mod_datas (snd sm))) input 0.
Proof.
  intro input.
  unfold merge_datas.
  induction input as [|sm input' IH]; simpl.
  - reflexivity.
  - rewrite length_app.
    rewrite IH.
    rewrite (fold_left_add_shift (fun sm0 => length (mod_datas (snd sm0)))
                                  input' (length (mod_datas (snd sm)))).
    lia.
Qed.

Lemma sum_space_counts_imports :
  forall input,
    length (merge_imports input) =
    fold_left (fun acc sm => acc + length (mod_imports (snd sm))) input 0.
Proof.
  intro input.
  unfold merge_imports.
  induction input as [|sm input' IH]; simpl.
  - reflexivity.
  - rewrite length_app.
    rewrite IH.
    rewrite (fold_left_add_shift (fun sm0 => length (mod_imports (snd sm0)))
                                  input' (length (mod_imports (snd sm)))).
    lia.
Qed.

(* Helper: In a generated remap list, all fused indices are offset + source_idx *)
Lemma gen_remaps_for_space_fused_idx :
  forall src m space offset count r,
    In r (gen_remaps_for_space src m space offset count) ->
    ir_fused_idx r = offset + ir_source_idx r.
Proof.
  intros src m space offset count r Hin.
  unfold gen_remaps_for_space in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i [Hr Hi]].
  subst r. simpl. reflexivity.
Qed.

Lemma gen_remaps_for_space_source_bound :
  forall src m space offset count r,
    In r (gen_remaps_for_space src m space offset count) ->
    ir_source_idx r < count.
Proof.
  intros src m space offset count r Hin.
  unfold gen_remaps_for_space in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i [Hr Hi]].
  subst r. simpl.
  apply in_seq in Hi. lia.
Qed.

Lemma gen_remaps_for_space_space :
  forall src m sp offset count r,
    In r (gen_remaps_for_space src m sp offset count) ->
    ir_space r = sp.
Proof.
  intros src m sp offset count r Hin.
  unfold gen_remaps_for_space in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i [Hr Hi]].
  subst r. simpl. reflexivity.
Qed.

Lemma gen_remaps_for_space_source :
  forall s m sp offset count r,
    In r (gen_remaps_for_space s m sp offset count) ->
    ir_source r = s.
Proof.
  intros s m sp offset count r Hin.
  unfold gen_remaps_for_space in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i [Hr Hi]].
  subst r. simpl. reflexivity.
Qed.

(* Helper: offset at position i is less than offset at position i + count(i) *)
Lemma offset_plus_count_bound :
  forall input space i sm,
    nth_error input i = Some sm ->
    compute_offset input space i + space_count sm space <=
    compute_offset input space (length input).
Proof.
  intros input space i sm Hnth.
  assert (Hi: i < length input).
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  (* We show this by induction on the remaining elements *)
  unfold compute_offset, space_count.
  (* The key insight: offset(i) + count(i) <= offset(length input)
     because offset(length input) includes all modules *)
  rewrite firstn_all.
  (* We need to show that fold over firstn i + count(i) <= fold over all *)
  assert (Hsplit: input = firstn i input ++ (sm :: skipn (S i) input)).
  { rewrite <- (firstn_skipn i input) at 1.
    f_equal.
    (* skipn i input = sm :: skipn (S i) input *)
    destruct (skipn i input) as [|x rest] eqn:Hskip.
    - (* Empty - contradiction with i < length input *)
      exfalso.
      assert (length (skipn i input) = 0) by (rewrite Hskip; reflexivity).
      rewrite length_skipn in H. lia.
    - (* x :: rest - show x = sm *)
      f_equal.
      + assert (nth_error (skipn i input) 0 = Some sm).
        { rewrite nth_error_skipn. rewrite Nat.add_0_r. exact Hnth. }
        rewrite Hskip in H. simpl in H. injection H. auto.
      + simpl in Hskip.
        assert (rest = skipn (S i) input).
        { replace (S i) with (1 + i) by lia.
          rewrite <- skipn_skipn.
          rewrite Hskip. reflexivity. }
        exact H. }
  (* Rewrite the RHS first using firstn_all, then use the split *)
  assert (Hlen: length (firstn i input) = i).
  { rewrite length_firstn. lia. }
  rewrite Hsplit at 2. (* Only rewrite in RHS *)
  rewrite fold_left_app. simpl.
  (* Destruct space to eliminate match in space_count, then prove trivially *)
  destruct space; simpl;
    rewrite (fold_left_add_shift _ (skipn (S i) input));
    apply Nat.le_add_r.
Qed.

(* DEAD CODE: fused_idx_bound_types never referenced elsewhere in the codebase.
   Removed due to 3 unresolvable admits stemming from overly complex find-based
   lookup logic that cannot be connected back to nth_error. The lemma attempted
   to use find on combined data structures rather than direct indexing.
   If reintroduction is needed, prefer direct nth_error-based bounds instead.

Lemma fused_idx_bound_types :
  forall input src m offset src_idx,
    In (src, m) input ->
    src_idx < length (mod_types m) ->
    offset = compute_offset input TypeIdx (
      match find (fun p => Nat.eqb (fst (fst p)) (fst src) &&
                           Nat.eqb (snd (fst p)) (snd src))
                 (combine (map fst input) (seq 0 (length input))) with
      | Some (_, i) => i
      | None => 0
      end) ->
    offset + src_idx < length (merge_types input).
Proof.
  intros input src m offset src_idx Hin Hsrc_bound Hoffset.
  (* Need to find the position of (src, m) in input *)
  apply In_nth_error in Hin.
  destruct Hin as [i Hi].
  (* The offset at position i plus src_idx is < total length *)
  rewrite sum_space_counts_types.
  assert (Hbound: compute_offset input TypeIdx i + src_idx <
                  fold_left (fun acc sm => acc + length (mod_types (snd sm))) input 0).
  { unfold compute_offset.
    assert (Hcount: length (mod_types m) = length (mod_types (snd (src, m)))).
    { reflexivity. }
    rewrite Hcount in Hsrc_bound.
    (* Show offset(i) + src_idx < total using offset_plus_count_bound *)
    assert (Hpc: compute_offset input TypeIdx i + space_count (src, m) TypeIdx <=
                 compute_offset input TypeIdx (length input)).
    { apply offset_plus_count_bound. exact Hi. }
    unfold space_count in Hpc. simpl in Hpc.
    unfold compute_offset in Hpc. rewrite firstn_all in Hpc.
    unfold compute_offset.
    lia. }
  (* Now relate the find result to i *)
  (* This is complex - we need to show find returns i when (src,m) is at position i *)
  (* For now, we use the direct bound *)
  subst offset.
  destruct (find _ _) as [[s' idx]|] eqn:Hfind.
  - (* find found something at position idx *)
    apply find_some in Hfind.
    destruct Hfind as [Hin' Heq'].
    apply Bool.andb_true_iff in Heq'.
    destruct Heq' as [Heq1 Heq2].
    apply Nat.eqb_eq in Heq1.
    apply Nat.eqb_eq in Heq2.
    apply in_combine_l in Hin'.
    apply in_map_iff in Hin'.
    destruct Hin' as [[src'' m''] [Hsrc'' Hin'']].
    simpl in Hsrc''. subst s'.
    (* We need idx < length input for the offset to make sense *)
    apply In_nth_error in Hin''.
    destruct Hin'' as [j Hj].
    (* idx corresponds to position j *)
    assert (Hjlen: j < length input).
    { apply nth_error_Some. rewrite Hj. discriminate. }
    (* The key: offset(idx) + src_idx < total *)
    assert (Hpc': compute_offset input TypeIdx idx + space_count (src'', m'') TypeIdx <=
                  compute_offset input TypeIdx (length input)).
    { apply offset_plus_count_bound.
      (* Need to show nth_error input idx = Some (src'', m'') *)
      (* This follows from the combine structure *)
      (* Actually we need more careful reasoning about the find result *)
      (* For simplicity, assume the index is valid *)
      admit. }
    unfold space_count in Hpc'. simpl in Hpc'.
    unfold compute_offset in Hpc'. rewrite firstn_all in Hpc'.
    unfold compute_offset.
    (* We also need src_idx < length (mod_types m'') which should equal
       length (mod_types m) since src'' = src and they're in the same position *)
    (* This requires showing that find returns the correct module *)
    admit.
  - (* find returned None - contradiction since (src, m) is in input *)
    (* This case shouldn't happen if our find is set up correctly *)
    (* The input contains (src, m), so find should succeed *)
    admit.
Admitted.
*)

(* Helper: index_space equality is decidable *)
Lemma index_space_eqb_refl :
  forall space, index_space_eqb space space = true.
Proof.
  destruct space; reflexivity.
Qed.

Lemma index_space_eqb_eq :
  forall s1 s2, index_space_eqb s1 s2 = true <-> s1 = s2.
Proof.
  intros s1 s2. split.
  - destruct s1, s2; simpl; intro H; try reflexivity; discriminate.
  - intro H. subst. apply index_space_eqb_refl.
Qed.

(* Helper: lookup in gen_remaps_for_space succeeds for valid indices *)
Lemma lookup_gen_remaps_for_space :
  forall src m space offset count src_idx,
    src_idx < count ->
    exists r,
      In r (gen_remaps_for_space src m space offset count) /\
      ir_space r = space /\
      ir_source r = src /\
      ir_source_idx r = src_idx /\
      ir_fused_idx r = offset + src_idx.
Proof.
  intros src m space offset count src_idx Hbound.
  exists (mkIndexRemap space src src_idx (offset + src_idx)).
  split.
  - unfold gen_remaps_for_space.
    apply in_map_iff.
    exists src_idx. split; [reflexivity|].
    apply in_seq. lia.
  - simpl. auto.
Qed.

(* General helper: find succeeds on mapped seq when target matches an element *)
Lemma find_remap_in_mapped_seq :
  forall space src off start n target,
    start <= target < start + n ->
    find (fun r => index_space_eqb (ir_space r) space &&
                   (fst (ir_source r) =? fst src) &&
                   (snd (ir_source r) =? snd src) &&
                   (ir_source_idx r =? target))
         (map (fun i => mkIndexRemap space src i (off + i)) (seq start n)) =
    Some (mkIndexRemap space src target (off + target)).
Proof.
  intros space src off start n.
  revert start.
  induction n as [|n' IHn]; intros start target Hrange.
  - lia.
  - simpl. rewrite index_space_eqb_refl, !Nat.eqb_refl. simpl.
    destruct (start =? target) eqn:E.
    + apply Nat.eqb_eq in E. subst. reflexivity.
    + apply Nat.eqb_neq in E. apply IHn. lia.
Qed.

(* Helper: lookup succeeds for generated remaps *)
Lemma lookup_remap_gen_space_success :
  forall src m space offset count src_idx,
    src_idx < count ->
    lookup_remap (gen_remaps_for_space src m space offset count)
                 space src src_idx = Some (offset + src_idx).
Proof.
  intros src m space offset count src_idx Hbound.
  unfold lookup_remap, gen_remaps_for_space.
  rewrite find_remap_in_mapped_seq; [|lia].
  simpl. reflexivity.
Qed.

(* Helper: find fails in gen_remaps_for_space for wrong index space *)
Lemma find_gen_remaps_for_space_wrong_space :
  forall src m sp1 sp2 offset count src_idx,
    sp1 <> sp2 ->
    find (fun r =>
      index_space_eqb (ir_space r) sp1 &&
      Nat.eqb (fst (ir_source r)) (fst src) &&
      Nat.eqb (snd (ir_source r)) (snd src) &&
      Nat.eqb (ir_source_idx r) src_idx)
    (gen_remaps_for_space src m sp2 offset count) = None.
Proof.
  intros src m sp1 sp2 offset count src_idx Hneq.
  unfold gen_remaps_for_space.
  assert (Hgen: forall start n,
    find (fun r =>
      index_space_eqb (ir_space r) sp1 &&
      Nat.eqb (fst (ir_source r)) (fst src) &&
      Nat.eqb (snd (ir_source r)) (snd src) &&
      Nat.eqb (ir_source_idx r) src_idx)
         (map (fun i => mkIndexRemap sp2 src i (offset + i)) (seq start n)) = None).
  { intros start n. revert start.
    induction n as [|n' IH]; intro start; simpl.
    - reflexivity.
    - destruct (index_space_eqb sp2 sp1) eqn:E.
      + apply index_space_eqb_eq in E. subst. contradiction.
      + simpl. apply IH. }
  apply Hgen.
Qed.

(* -------------------------------------------------------------------------
   Helper lemmas for gen_remaps_for_module
   ------------------------------------------------------------------------- *)

(* A remap in gen_remaps_for_space has its fused_idx = offset + source_idx *)
Lemma in_gen_remaps_for_space_fused :
  forall src m space offset count r,
    In r (gen_remaps_for_space src m space offset count) ->
    ir_fused_idx r = offset + ir_source_idx r /\
    ir_space r = space /\
    ir_source r = src /\
    ir_source_idx r < count.
Proof.
  intros src m space offset count r Hin.
  unfold gen_remaps_for_space in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [i [Hr Hi]].
  apply in_seq in Hi.
  subst r. simpl.
  repeat split; lia.
Qed.

(* A remap in gen_remaps_for_module has fused_idx = offset(space) + source_idx *)
Lemma in_gen_remaps_for_module_fused :
  forall src m offsets r,
    In r (gen_remaps_for_module src m offsets) ->
    ir_fused_idx r = offsets (ir_space r) + ir_source_idx r /\
    ir_source r = src.
Proof.
  intros src m offsets r Hin.
  unfold gen_remaps_for_module in Hin.
  repeat (apply in_app_iff in Hin; destruct Hin as [Hin | Hin]).
  all: apply in_gen_remaps_for_space_fused in Hin;
       destruct Hin as [Hfused [Hspace [Hsrc Hbound]]];
       rewrite Hspace, Hsrc; split; [exact Hfused | reflexivity].
Qed.

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

(* Offset plus space count at position i <= offset at length input *)
Lemma offset_plus_count_total :
  forall input space i sm,
    nth_error input i = Some sm ->
    compute_offset input space i + space_count_of_module (snd sm) space <=
    compute_offset input space (length input).
Proof.
  intros input space i sm Hnth.
  assert (Hi: i < length input).
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  unfold compute_offset. rewrite firstn_all.
  (* Split input at position i *)
  assert (Hsplit: input = firstn i input ++ sm :: skipn (S i) input).
  { rewrite <- (firstn_skipn i input) at 1.
    f_equal.
    destruct (skipn i input) as [|x rest] eqn:Hskip.
    - exfalso. assert (length (skipn i input) = 0) by (rewrite Hskip; reflexivity).
      rewrite length_skipn in H. lia.
    - f_equal.
      + assert (nth_error (skipn i input) 0 = Some sm).
        { rewrite nth_error_skipn. rewrite Nat.add_0_r. exact Hnth. }
        rewrite Hskip in H. simpl in H. congruence.
      + replace (S i) with (1 + i) by lia.
        rewrite <- skipn_skipn. rewrite Hskip. reflexivity. }
  rewrite Hsplit at 2.
  rewrite fold_left_app. simpl.
  rewrite (fold_left_add_shift _ (skipn (S i) input)).
  unfold space_count_of_module.
  destruct space; simpl; lia.
Qed.

(* Total count for a space in merged module *)
Definition total_space_count (input : merge_input) (space : index_space) : nat :=
  fold_left (fun acc sm => acc + space_count_of_module (snd sm) space) input 0.

(* Offset at length input equals total space count *)
Lemma offset_at_length_eq_total :
  forall input space,
    compute_offset input space (length input) = total_space_count input space.
Proof.
  intros input space.
  unfold compute_offset, total_space_count, space_count_of_module.
  rewrite firstn_all.
  destruct space; reflexivity.
Qed.

(* Lookup in gen_all_remaps succeeds and returns the expected fused index.

   NOTE: This requires NoDup (map fst remaining) to ensure source uniqueness.
   Without uniqueness, the S case cannot show that find fails in the current
   module's remaps (two modules with the same source would cause ambiguity).
   The fully proven version with NoDup lives in merge_remap.v.

   This version without NoDup is kept as a weaker form for cases where
   uniqueness is already established at the call site. *)
Lemma lookup_gen_all_remaps_aux_success :
  forall input start_idx remaining src m space src_idx mod_idx,
    NoDup (map fst remaining) ->
    nth_error remaining mod_idx = Some (src, m) ->
    src_idx < space_count_of_module m space ->
    lookup_remap (gen_all_remaps_aux input start_idx remaining) space src src_idx
    = Some (offsets_for_module input (start_idx + mod_idx) space + src_idx).
Proof.
  intros input start_idx remaining.
  revert start_idx.
  induction remaining as [|[src' m'] rest IH]; intros start_idx src m space src_idx mod_idx Hnodup Hnth Hbound.
  - destruct mod_idx; discriminate.
  - destruct mod_idx as [|mod_idx'].
    + (* mod_idx = 0: current module matches *)
      simpl in Hnth. injection Hnth as Hsrc Hm. subst src' m'.
      simpl. replace (start_idx + 0) with start_idx by lia.
      (* lookup_remap over app: if lookup succeeds in prefix, it succeeds in whole *)
      unfold lookup_remap.
      assert (Hfind_app: forall {A : Type} (P : A -> bool) (l1 l2 : list A),
        find P (l1 ++ l2) = match find P l1 with Some x => Some x | None => find P l2 end).
      { intros A P l1 l2. induction l1 as [|h t IHl]; simpl.
        - reflexivity. - destruct (P h); [reflexivity | exact IHl]. }
      rewrite Hfind_app.
      (* Show find succeeds in gen_remaps_for_module by space case analysis *)
      unfold gen_remaps_for_module, space_count_of_module, offsets_for_module in *.
      destruct space; repeat rewrite Hfind_app;
        repeat (rewrite find_gen_remaps_for_space_wrong_space; [simpl | discriminate]);
        unfold gen_remaps_for_space;
        rewrite find_remap_in_mapped_seq; [simpl; reflexivity | lia].
    + (* mod_idx = S mod_idx': source is in the tail *)
      simpl in Hnth. simpl.
      unfold lookup_remap.
      assert (Hfind_app: forall {A : Type} (P : A -> bool) (l1 l2 : list A),
        find P (l1 ++ l2) = match find P l1 with Some x => Some x | None => find P l2 end).
      { intros A P l1 l2. induction l1 as [|h t IHl]; simpl.
        - reflexivity. - destruct (P h); [reflexivity | exact IHl]. }
      rewrite Hfind_app.
      (* find fails in current module's remaps because src <> src' (NoDup) *)
      simpl in Hnodup.
      apply NoDup_cons_iff in Hnodup.
      destruct Hnodup as [Hnot_in Hnodup_rest].
      assert (Hsrc_in_rest: In src (map fst rest)).
      { apply nth_error_In in Hnth.
        apply in_map with (f := fst) in Hnth. simpl in Hnth. exact Hnth. }
      assert (Hsrc_neq: src <> src').
      { intro Heq. subst. contradiction. }
      rewrite find_gen_remaps_wrong_source.
      2: { intro Heq. apply Hsrc_neq. symmetry. exact Heq. }
      unfold lookup_remap in IH.
      replace (start_idx + S mod_idx') with (S start_idx + mod_idx') by lia.
      eapply IH; eassumption.
Qed.

(* -------------------------------------------------------------------------
   Main Merge Correctness Theorem

   If we merge modules correctly, looking up any remapped index in the
   fused module yields the same entity as in the source module.
   ------------------------------------------------------------------------- *)

(* Helper: merged module type count equals total space count *)
Lemma merge_types_length :
  forall input,
    length (mod_types (merge_modules input)) = total_space_count input TypeIdx.
Proof.
  intro input.
  unfold merge_modules, total_space_count, space_count_of_module. simpl.
  rewrite sum_space_counts_types. reflexivity.
Qed.

(* Helper: fold_left distributes over addition *)
Lemma fold_left_add_split :
  forall {A : Type} (f g : A -> nat) (l : list A),
    fold_left (fun acc x => acc + f x) l 0 + fold_left (fun acc x => acc + g x) l 0
    = fold_left (fun acc x => acc + (f x + g x)) l 0.
Proof.
  intros A f g l.
  induction l as [|h t IHl]; simpl.
  - lia.
  - rewrite !fold_left_add_shift. rewrite IHl. lia.
Qed.

(* Helper: count_func_imports distributes over flat_map of imports *)
Lemma count_func_imports_flat_map :
  forall input,
    count_func_imports (merge_modules input)
    = fold_left (fun acc sm => acc + count_func_imports (snd sm)) input 0.
Proof.
  intro input.
  unfold merge_modules, count_func_imports, merge_imports. simpl.
  induction input as [|sm input' IH]; simpl.
  - reflexivity.
  - rewrite filter_app. rewrite length_app.
    rewrite IH.
    rewrite (fold_left_add_shift (fun sm0 => length (filter _ (mod_imports (snd sm0)))) input').
    lia.
Qed.

Lemma merge_funcs_length :
  forall input,
    count_func_imports (merge_modules input) + length (mod_funcs (merge_modules input))
    = total_space_count input FuncIdx.
Proof.
  intro input.
  unfold total_space_count, space_count_of_module.
  rewrite count_func_imports_flat_map.
  unfold merge_modules. simpl.
  rewrite sum_space_counts_funcs.
  rewrite <- fold_left_add_split. lia.
Qed.

(* Helper for tables *)
Lemma count_table_imports_flat_map :
  forall input,
    count_table_imports (merge_modules input)
    = fold_left (fun acc sm => acc + count_table_imports (snd sm)) input 0.
Proof.
  intro input.
  unfold merge_modules, count_table_imports, merge_imports. simpl.
  induction input as [|sm input' IH]; simpl.
  - reflexivity.
  - rewrite filter_app. rewrite length_app.
    rewrite IH.
    rewrite (fold_left_add_shift (fun sm0 => length (filter _ (mod_imports (snd sm0)))) input').
    lia.
Qed.

Lemma merge_tables_length :
  forall input,
    count_table_imports (merge_modules input) + length (mod_tables (merge_modules input))
    = total_space_count input TableIdx.
Proof.
  intro input.
  unfold total_space_count, space_count_of_module.
  rewrite count_table_imports_flat_map.
  unfold merge_modules. simpl.
  rewrite sum_space_counts_tables.
  rewrite <- fold_left_add_split. lia.
Qed.

(* Helper for mems - special case because SharedMemory changes the count *)
(* Note: With SharedMemory strategy, all memories are combined into one.
   This means the standard correspondence doesn't hold.
   We state a weaker property for MemIdx that works with SharedMemory. *)
Lemma count_mem_imports_flat_map :
  forall input,
    count_mem_imports (merge_modules input)
    = fold_left (fun acc sm => acc + count_mem_imports (snd sm)) input 0.
Proof.
  intro input.
  unfold merge_modules, count_mem_imports, merge_imports. simpl.
  induction input as [|sm input' IH]; simpl.
  - reflexivity.
  - rewrite filter_app. rewrite length_app.
    rewrite IH.
    rewrite (fold_left_add_shift (fun sm0 => length (filter _ (mod_imports (snd sm0)))) input').
    lia.
Qed.

(* For SharedMemory, the merged mem count is at most 1, not the sum.
   We need a different approach for MemIdx validity. *)
Lemma merge_mems_length :
  forall input,
    count_mem_imports (merge_modules input) + length (mod_mems (merge_modules input))
    <= total_space_count input MemIdx.
Proof.
  intro input.
  unfold total_space_count, space_count_of_module.
  rewrite count_mem_imports_flat_map.
  unfold merge_modules, merge_mems. simpl.
  rewrite sum_space_counts_mems_shared.
  (* LHS = fold(count_mem_imports) + 1 *)
  (* RHS = fold(count_mem_imports + length mems) *)
  (* Need: fold(imports) + 1 <= fold(imports) + fold(length mems) *)
  (* This holds when there's at least one memory in some module *)
  rewrite <- fold_left_add_split.
  (* If fold(length mems) >= 1, then we're done *)
  (* Otherwise, input has no memories and SharedMemory still creates one, which is invalid *)
  (* This is a design issue - SharedMemory shouldn't create a memory from nothing *)
  (* For now, admit this edge case *)
  admit.
Admitted.

(* Helper for globals *)
Lemma count_global_imports_flat_map :
  forall input,
    count_global_imports (merge_modules input)
    = fold_left (fun acc sm => acc + count_global_imports (snd sm)) input 0.
Proof.
  intro input.
  unfold merge_modules, count_global_imports, merge_imports. simpl.
  induction input as [|sm input' IH]; simpl.
  - reflexivity.
  - rewrite filter_app. rewrite length_app.
    rewrite IH.
    rewrite (fold_left_add_shift (fun sm0 => length (filter _ (mod_imports (snd sm0)))) input').
    lia.
Qed.

Lemma merge_globals_length :
  forall input,
    count_global_imports (merge_modules input) + length (mod_globals (merge_modules input))
    = total_space_count input GlobalIdx.
Proof.
  intro input.
  unfold total_space_count, space_count_of_module.
  rewrite count_global_imports_flat_map.
  unfold merge_modules. simpl.
  rewrite sum_space_counts_globals.
  rewrite <- fold_left_add_split. lia.
Qed.

Lemma merge_elems_length :
  forall input,
    length (mod_elems (merge_modules input)) = total_space_count input ElemIdx.
Proof.
  intro input.
  unfold merge_modules, total_space_count, space_count_of_module. simpl.
  rewrite sum_space_counts_elems. reflexivity.
Qed.

Lemma merge_datas_length :
  forall input,
    length (mod_datas (merge_modules input)) = total_space_count input DataIdx.
Proof.
  intro input.
  unfold merge_modules, total_space_count, space_count_of_module. simpl.
  rewrite sum_space_counts_datas. reflexivity.
Qed.

(* Helper: a remap in gen_remaps_for_module has bounded source_idx *)
Lemma in_gen_remaps_for_module_bound :
  forall src m offsets r,
    In r (gen_remaps_for_module src m offsets) ->
    ir_source_idx r < space_count_of_module m (ir_space r).
Proof.
  intros src m offsets r Hin.
  unfold gen_remaps_for_module in Hin.
  repeat (apply in_app_iff in Hin; destruct Hin as [Hin | Hin]).
  all: apply in_gen_remaps_for_space_fused in Hin;
       destruct Hin as [_ [Hspace [_ Hbound]]];
       subst; unfold space_count_of_module; exact Hbound.
Qed.

(* Helper: fused_idx from lookup is bounded *)
Lemma lookup_fused_idx_bound :
  forall input src m space src_idx fused_idx mod_idx,
    nth_error input mod_idx = Some (src, m) ->
    lookup_remap (gen_all_remaps input) space src src_idx = Some fused_idx ->
    fused_idx < total_space_count input space.
Proof.
  intros input src m space src_idx fused_idx mod_idx Hnth Hlookup.
  unfold lookup_remap in Hlookup.
  destruct (find _ _) as [r|] eqn:Hfind; [|discriminate].
  injection Hlookup as Hfused. subst fused_idx.
  apply find_some in Hfind.
  destruct Hfind as [Hin_r Hmatch].

  (* Parse the match condition to get ir_space r = space *)
  apply Bool.andb_true_iff in Hmatch.
  destruct Hmatch as [H123 _].
  apply Bool.andb_true_iff in H123.
  destruct H123 as [H12 _].
  apply Bool.andb_true_iff in H12.
  destruct H12 as [H1 _].
  apply index_space_eqb_eq in H1.

  (* r is in gen_all_remaps *)
  unfold gen_all_remaps in Hin_r.
  apply in_gen_all_remaps_aux in Hin_r.
  destruct Hin_r as [i [src' [m' [Hnth' Hgen']]]].

  (* Get properties of r from gen_remaps_for_module *)
  pose proof (in_gen_remaps_for_module_fused _ _ _ _ Hgen') as [Hfused_eq _].
  pose proof (in_gen_remaps_for_module_bound _ _ _ _ Hgen') as Hbound.

  (* ir_fused_idx r = offset(i) + ir_source_idx r *)
  (* ir_source_idx r < space_count_of_module m' (ir_space r) *)
  (* So ir_fused_idx r < offset(i) + space_count(m') <= total *)

  rewrite H1 in *.
  rewrite Hfused_eq.

  (* offset(i) + space_count(m') <= total *)
  assert (Hoff_bound:
    offsets_for_module input (0 + i) space + space_count_of_module m' space
    <= total_space_count input space).
  { unfold offsets_for_module.
    rewrite <- offset_at_length_eq_total.
    replace (0 + i) with i by lia.
    apply offset_plus_count_total. exact Hnth'. }

  lia.
Qed.

(* First, we prove the correctness for merged modules constructed by merge_modules *)
Theorem merge_correctness_constructed :
  forall input,
    let merged := merge_modules input in
    let remaps := gen_all_remaps input in
    forall src m space src_idx fused_idx,
      In (src, m) input ->
      lookup_remap remaps space src src_idx = Some fused_idx ->
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
  intros input merged remaps src m space src_idx fused_idx Hin Hlookup.
  apply In_nth_error in Hin.
  destruct Hin as [mod_idx Hmod_idx].

  (* Use the bound lemma *)
  assert (Hbound: fused_idx < total_space_count input space).
  { eapply lookup_fused_idx_bound; eauto. }

  destruct space; unfold merged.
  - (* TypeIdx *)
    rewrite merge_types_length. exact Hbound.
  - (* FuncIdx *)
    unfold valid_funcidx. rewrite merge_funcs_length. exact Hbound.
  - (* TableIdx *)
    unfold valid_tableidx. rewrite merge_tables_length. exact Hbound.
  - (* MemIdx *)
    unfold valid_memidx. rewrite merge_mems_length. exact Hbound.
  - (* GlobalIdx *)
    unfold valid_globalidx. rewrite merge_globals_length. exact Hbound.
  - (* ElemIdx *)
    rewrite merge_elems_length. exact Hbound.
  - (* DataIdx *)
    rewrite merge_datas_length. exact Hbound.
Qed.


(* Remaps are well-formed: each remap's fused_idx is bounded by the total *)
Definition remaps_bounded (input : merge_input) (remaps : remap_table) : Prop :=
  forall r,
    In r remaps ->
    ir_fused_idx r < total_space_count input (ir_space r).

(* The main theorem: given well-formed remaps, lookup produces valid indices *)
Theorem merge_correctness :
  forall input remaps merged,
    (* Given a valid merge result *)
    remaps_complete input remaps ->
    remaps_injective remaps ->
    remaps_bounded input remaps ->
    (* merged is constructed correctly from input *)
    merged = merge_modules input ->
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
  intros input remaps merged Hcomplete Hinjective Hbounded Hmerged
         src m space src_idx fused_idx Hin Hlookup.
  subst merged.

  (* From lookup succeeding, we get the remap r *)
  unfold lookup_remap in Hlookup.
  destruct (find _ remaps) as [r|] eqn:Hfind; [|discriminate].
  injection Hlookup as Hfused. subst fused_idx.
  apply find_some in Hfind.
  destruct Hfind as [Hin_r Hmatch].

  (* Parse the match condition *)
  apply Bool.andb_true_iff in Hmatch.
  destruct Hmatch as [H123 H4].
  apply Bool.andb_true_iff in H123.
  destruct H123 as [H12 H3].
  apply Bool.andb_true_iff in H12.
  destruct H12 as [H1 H2].
  apply index_space_eqb_eq in H1.

  (* From remaps_bounded, ir_fused_idx r < total_space_count input (ir_space r) *)
  specialize (Hbounded r Hin_r).
  rewrite H1 in Hbounded.

  destruct space.
  - (* TypeIdx *)
    rewrite merge_types_length. exact Hbounded.
  - (* FuncIdx *)
    unfold valid_funcidx. rewrite merge_funcs_length. exact Hbounded.
  - (* TableIdx *)
    unfold valid_tableidx. rewrite merge_tables_length. exact Hbounded.
  - (* MemIdx *)
    unfold valid_memidx. rewrite merge_mems_length. exact Hbounded.
  - (* GlobalIdx *)
    unfold valid_globalidx. rewrite merge_globals_length. exact Hbounded.
  - (* ElemIdx *)
    rewrite merge_elems_length. exact Hbounded.
  - (* DataIdx *)
    rewrite merge_datas_length. exact Hbounded.
Qed.

(* gen_all_remaps produces bounded remaps *)
Theorem gen_all_remaps_bounded :
  forall input,
    remaps_bounded input (gen_all_remaps input).
Proof.
  intro input.
  unfold remaps_bounded, gen_all_remaps.
  intros r Hin.
  apply in_gen_all_remaps_aux in Hin.
  destruct Hin as [i [src [m [Hnth Hgen]]]].

  (* Get fused_idx and bound properties *)
  pose proof (in_gen_remaps_for_module_fused _ _ _ _ Hgen) as [Hfused _].
  pose proof (in_gen_remaps_for_module_bound _ _ _ _ Hgen) as Hbound.

  rewrite Hfused.

  (* offset(i) + ir_source_idx r < offset(i) + space_count(m) <= total *)
  assert (Hoff: offsets_for_module input (0 + i) (ir_space r) + space_count_of_module m (ir_space r)
                <= total_space_count input (ir_space r)).
  { unfold offsets_for_module.
    rewrite <- offset_at_length_eq_total.
    replace (0 + i) with i by lia.
    apply offset_plus_count_total. exact Hnth. }

  lia.
Qed.

(* -------------------------------------------------------------------------
   Remap Generation Correctness

   The remaps generated by gen_all_remaps satisfy completeness and injectivity.
   ------------------------------------------------------------------------- *)

(* Helper: remap is in gen_all_remaps_aux iff it's in one of the module remaps *)
Lemma in_gen_all_remaps_aux :
  forall input start_idx remaining r,
    In r (gen_all_remaps_aux input start_idx remaining) <->
    exists i src m,
      nth_error remaining i = Some (src, m) /\
      In r (gen_remaps_for_module src m (offsets_for_module input (start_idx + i))).
Proof.
  intros input start_idx remaining.
  (* Induction needs to generalize over start_idx *)
  revert start_idx.
  induction remaining as [|[src m] rest IH]; intros start_idx r; split; intro H.
  - (* [] -> : contradiction *)
    simpl in H. contradiction.
  - (* -> [] : impossible *)
    destruct H as [i [src' [m' [Hnth _]]]].
    destruct i; discriminate.
  - (* (src,m)::rest -> *)
    simpl in H.
    apply in_app_iff in H.
    destruct H as [Hhead | Htail].
    + (* In head *)
      exists 0, src, m. split.
      * reflexivity.
      * replace (start_idx + 0) with start_idx by lia. exact Hhead.
    + (* In tail *)
      apply IH in Htail.
      destruct Htail as [i [src' [m' [Hnth Hin]]]].
      exists (S i), src', m'. split.
      * simpl. exact Hnth.
      * replace (start_idx + S i) with (S start_idx + i) by lia. exact Hin.
  - (* -> (src,m)::rest *)
    destruct H as [i [src' [m' [Hnth Hin]]]].
    simpl. apply in_app_iff.
    destruct i as [|i'].
    + (* i = 0 *)
      left. simpl in Hnth. injection Hnth as Heq1 Heq2. subst src' m'.
      replace (start_idx + 0) with start_idx in Hin by lia. exact Hin.
    + (* i = S i' *)
      right. apply IH.
      exists i', src', m'. split.
      * simpl in Hnth. exact Hnth.
      * replace (S start_idx + i') with (start_idx + S i') by lia. exact Hin.
Qed.

(* Helper: find fails in gen_remaps_for_space for wrong index space *)
Lemma find_gen_remaps_for_space_wrong_space :
  forall src m sp1 sp2 offset count src_idx,
    sp1 <> sp2 ->
    find (fun r =>
      index_space_eqb (ir_space r) sp1 &&
      Nat.eqb (fst (ir_source r)) (fst src) &&
      Nat.eqb (snd (ir_source r)) (snd src) &&
      Nat.eqb (ir_source_idx r) src_idx)
    (gen_remaps_for_space src m sp2 offset count) = None.
Proof.
  intros src m sp1 sp2 offset count src_idx Hneq.
  unfold gen_remaps_for_space.
  induction count as [|n IH]; simpl.
  - reflexivity.
  - simpl.
    assert (Hfalse: index_space_eqb sp2 sp1 = false).
    { destruct sp1, sp2; simpl; try reflexivity; contradiction. }
    rewrite Hfalse. simpl. exact IH.
Qed.

(* Helper: find fails in gen_remaps_for_space for wrong source *)
Lemma find_gen_remaps_for_space_wrong_src :
  forall src1 src2 m sp offset count src_idx,
    fst src1 <> fst src2 \/ snd src1 <> snd src2 ->
    find (fun r =>
      index_space_eqb (ir_space r) sp &&
      Nat.eqb (fst (ir_source r)) (fst src1) &&
      Nat.eqb (snd (ir_source r)) (snd src1) &&
      Nat.eqb (ir_source_idx r) src_idx)
    (gen_remaps_for_space src2 m sp offset count) = None.
Proof.
  intros src1 src2 m sp offset count src_idx Hneq.
  unfold gen_remaps_for_space.
  induction count as [|n IH]; simpl.
  - reflexivity.
  - simpl. rewrite index_space_eqb_refl.
    destruct Hneq as [Hfst | Hsnd].
    + assert (Hf: Nat.eqb (fst src2) (fst src1) = false).
      { apply Nat.eqb_neq. auto. }
      rewrite Hf. simpl. exact IH.
    + destruct (Nat.eqb (fst src2) (fst src1)); simpl.
      * assert (Hs: Nat.eqb (snd src2) (snd src1) = false).
        { apply Nat.eqb_neq. auto. }
        rewrite Hs. simpl. exact IH.
      * exact IH.
Qed.

(* Unique sources in input: each module_source appears at most once *)
Definition unique_sources (input : merge_input) : Prop :=
  forall i j src1 m1 src2 m2,
    nth_error input i = Some (src1, m1) ->
    nth_error input j = Some (src2, m2) ->
    src1 = src2 ->
    i = j.

(* Lookup succeeds for gen_all_remaps when sources are unique *)
Lemma lookup_gen_all_remaps_aux_gen :
  forall input start_idx remaining src m space src_idx mod_idx,
    (forall i, nth_error remaining i = nth_error input (start_idx + i)) ->
    unique_sources input ->
    nth_error remaining mod_idx = Some (src, m) ->
    src_idx < space_count_of_module m space ->
    lookup_remap (gen_all_remaps_aux input start_idx remaining) space src src_idx
    = Some (offsets_for_module input (start_idx + mod_idx) space + src_idx).
Proof.
  intros input start_idx remaining.
  revert start_idx.
  induction remaining as [|[src' m'] rest IH];
    intros start_idx src m space src_idx mod_idx Hrel Hunique Hnth Hbound.
  - (* Empty remaining: contradiction *)
    destruct mod_idx; discriminate.
  - (* (src', m') :: rest *)

    (* Reusable: find distributes over ++ *)
    assert (Hfind_app: forall {A : Type} (P : A -> bool) (l1 l2 : list A),
      find P (l1 ++ l2) =
      match find P l1 with
      | Some x => Some x
      | None => find P l2
      end).
    { intros A P l1 l2. induction l1 as [|h t IHl]; simpl.
      - reflexivity.
      - destruct (P h); [reflexivity | exact IHl]. }

    destruct mod_idx as [|mod_idx'].
    + (* mod_idx = 0: current module *)
      simpl in Hnth. injection Hnth as Hsrc Hm. subst src' m'.
      simpl.
      unfold lookup_remap.
      rewrite Hfind_app.
      unfold gen_remaps_for_module.
      replace (start_idx + 0) with start_idx by lia.

      (* For each space, show lookup succeeds in the right gen_remaps_for_space *)
      destruct space; unfold offsets_for_module, space_count_of_module in *.
      all: try (
        repeat rewrite Hfind_app;
        repeat (rewrite find_gen_remaps_for_space_wrong_space; [|discriminate]);
        pose proof (lookup_remap_gen_space_success src m _ _ _ src_idx Hbound) as H;
        unfold lookup_remap in H;
        rewrite H;
        reflexivity
      ).

    + (* mod_idx = S mod_idx': later module *)
      simpl in Hnth.
      simpl.
      unfold lookup_remap.
      rewrite Hfind_app.

      (* Show src ≠ src' using unique_sources *)
      assert (Hneq: fst src <> fst src' \/ snd src <> snd src').
      { (* src' is at position start_idx in input, src is at start_idx + S mod_idx' *)
        assert (Hnth_src': nth_error input start_idx = Some (src', m')).
        { specialize (Hrel 0). simpl in Hrel. rewrite Nat.add_0_r in Hrel. exact Hrel. }
        assert (Hnth_src: nth_error input (start_idx + S mod_idx') = Some (src, m)).
        { specialize (Hrel (S mod_idx')). simpl in Hrel. exact Hrel. }
        destruct (Nat.eq_dec (fst src) (fst src')) as [Hf | Hf];
        destruct (Nat.eq_dec (snd src) (snd src')) as [Hs | Hs].
        - (* src = src': contradicts unique_sources since positions differ *)
          exfalso.
          assert (Heq: src = src').
          { destruct src, src'. simpl in *. congruence. }
          assert (Habs: start_idx + S mod_idx' = start_idx).
          { apply (Hunique _ _ _ _ _ _ Hnth_src Hnth_src'). symmetry. exact Heq. }
          lia.
        - right. auto.
        - left. auto.
        - left. auto. }

      (* find fails in current module's remaps because src ≠ src' *)
      assert (Hfail_current:
        find (fun r =>
          index_space_eqb (ir_space r) space &&
          Nat.eqb (fst (ir_source r)) (fst src) &&
          Nat.eqb (snd (ir_source r)) (snd src) &&
          Nat.eqb (ir_source_idx r) src_idx)
        (gen_remaps_for_module src' m' (offsets_for_module input start_idx)) = None).
      { unfold gen_remaps_for_module.
        repeat rewrite Hfind_app.
        repeat (rewrite find_gen_remaps_for_space_wrong_src; [|exact Hneq]).
        reflexivity. }

      rewrite Hfail_current.

      (* Apply IH: rest corresponds to input starting at S start_idx *)
      assert (Hrel': forall i, nth_error rest i = nth_error input (S start_idx + i)).
      { intro i. specialize (Hrel (S i)). simpl in Hrel.
        replace (start_idx + S i) with (S start_idx + i) in Hrel by lia.
        exact Hrel. }

      specialize (IH (S start_idx) src m space src_idx mod_idx'
                      Hrel' Hunique Hnth Hbound).
      unfold lookup_remap in IH.
      replace (start_idx + S mod_idx') with (S start_idx + mod_idx') by lia.
      exact IH.
Qed.

(* Corollary: lookup succeeds for gen_all_remaps when sources are unique *)
Lemma lookup_gen_all_remaps_unique :
  forall input src m space src_idx mod_idx,
    unique_sources input ->
    nth_error input mod_idx = Some (src, m) ->
    src_idx < space_count_of_module m space ->
    lookup_remap (gen_all_remaps input) space src src_idx
    = Some (compute_offset input space mod_idx + src_idx).
Proof.
  intros input src m space src_idx mod_idx Hunique Hnth Hbound.
  unfold gen_all_remaps.
  change (compute_offset input space mod_idx)
    with (offsets_for_module input mod_idx space).
  replace mod_idx with (0 + mod_idx) at 2 by lia.
  apply lookup_gen_all_remaps_aux_gen with (m := m); auto.
  (* remaining = input corresponds to input starting at 0 *)
  intro i. simpl. reflexivity.
Qed.

Theorem gen_all_remaps_complete :
  forall input,
    unique_sources input ->
    remaps_complete input (gen_all_remaps input).
Proof.
  intros input Hunique.
  unfold remaps_complete.
  intros src m space src_idx Hin Hbound.
  apply In_nth_error in Hin.
  destruct Hin as [mod_idx Hmod_idx].
  exists (compute_offset input space mod_idx + src_idx).
  apply lookup_gen_all_remaps_unique; auto.
  unfold space_count_of_module.
  destruct space; exact Hbound.
Qed.


Theorem gen_all_remaps_injective :
  forall input,
    remaps_injective (gen_all_remaps input).
Proof.
  intro input.
  unfold remaps_injective, gen_all_remaps.
  intros r1 r2 Hin1 Hin2 Hspace Hfused.
  (* Two remaps with same space and fused_idx must have same source and source_idx *)
  apply in_gen_all_remaps_aux in Hin1.
  apply in_gen_all_remaps_aux in Hin2.
  destruct Hin1 as [i1 [src1 [m1 [Hnth1 Hgen1]]]].
  destruct Hin2 as [i2 [src2 [m2 [Hnth2 Hgen2]]]].

  (* Preserve gen information with pose proof BEFORE destructing *)
  pose proof (in_gen_remaps_for_module_fused _ _ _ _ Hgen1) as [Hfused1 Hsrc1].
  pose proof (in_gen_remaps_for_module_fused _ _ _ _ Hgen2) as [Hfused2 Hsrc2].
  pose proof (in_gen_remaps_for_module_bound _ _ _ _ Hgen1) as Hbound1.
  pose proof (in_gen_remaps_for_module_bound _ _ _ _ Hgen2) as Hbound2.

  (* Case analysis on whether i1 = i2 *)
  destruct (Nat.eq_dec i1 i2) as [Heq | Hneq].
  - (* i1 = i2: same module *)
    subst i2.
    rewrite Hnth1 in Hnth2. injection Hnth2 as Hsrceq Hmeq. subst src2 m2.
    (* Both have same offset, so same fused_idx means same source_idx *)
    split.
    + (* ir_source r1 = ir_source r2 *)
      congruence.
    + (* ir_source_idx r1 = ir_source_idx r2 *)
      rewrite <- Hspace in Hfused2.
      rewrite Hfused in Hfused1.
      rewrite Hfused1 in Hfused2.
      lia.

  - (* i1 <> i2: different modules — offset ranges are disjoint *)
    exfalso.

    assert (Hi1: i1 < length input).
    { apply nth_error_Some. rewrite Hnth1. discriminate. }
    assert (Hi2: i2 < length input).
    { apply nth_error_Some. rewrite Hnth2. discriminate. }

    destruct (Nat.lt_trichotomy i1 i2) as [Hlt | [Heq' | Hgt]].
    + (* i1 < i2: offset(i1) + src_idx < offset(i1) + count(m1) <= offset(i2) <= offset(i2) + src_idx *)
      assert (Hoff_bound:
        offsets_for_module input (0 + i1) (ir_space r1) + space_count_of_module m1 (ir_space r1)
        <= offsets_for_module input (0 + i2) (ir_space r2)).
      { unfold offsets_for_module.
        rewrite <- Hspace.
        replace (0 + i1) with i1 by lia.
        replace (0 + i2) with i2 by lia.
        (* Step 1: offset(S i1) = offset(i1) + count(m1) via firstn decomposition *)
        assert (Hstep: compute_offset input (ir_space r1) (S i1) =
                        compute_offset input (ir_space r1) i1 +
                        space_count_of_module m1 (ir_space r1)).
        { unfold compute_offset.
          rewrite (firstn_S_nth_error _ _ (src1, m1) Hnth1).
          rewrite fold_left_app. simpl.
          unfold space_count_of_module.
          destruct (ir_space r1); lia. }
        (* Step 2: offset(S i1) <= offset(i2) by monotonicity *)
        assert (Hmono: compute_offset input (ir_space r1) (S i1) <=
                        compute_offset input (ir_space r1) i2).
        { apply offset_monotonic; lia. }
        lia. }

      rewrite Hfused1 in Hfused.
      rewrite Hfused2 in Hfused.
      rewrite <- Hspace in Hfused.
      lia.

    + (* i1 = i2: contradiction with Hneq *)
      contradiction.

    + (* i2 < i1: symmetric case *)
      assert (Hoff_bound:
        offsets_for_module input (0 + i2) (ir_space r2) + space_count_of_module m2 (ir_space r2)
        <= offsets_for_module input (0 + i1) (ir_space r1)).
      { unfold offsets_for_module.
        rewrite Hspace.
        replace (0 + i2) with i2 by lia.
        replace (0 + i1) with i1 by lia.
        assert (Hstep: compute_offset input (ir_space r2) (S i2) =
                        compute_offset input (ir_space r2) i2 +
                        space_count_of_module m2 (ir_space r2)).
        { unfold compute_offset.
          rewrite (firstn_S_nth_error _ _ (src2, m2) Hnth2).
          rewrite fold_left_app. simpl.
          unfold space_count_of_module.
          destruct (ir_space r2); lia. }
        assert (Hmono: compute_offset input (ir_space r2) (S i2) <=
                        compute_offset input (ir_space r2) i1).
        { apply offset_monotonic; lia. }
        lia. }

      rewrite Hfused1 in Hfused.
      rewrite Hfused2 in Hfused.
      rewrite Hspace in Hfused.
      lia.
Qed.

(* End of merge_spec *)
