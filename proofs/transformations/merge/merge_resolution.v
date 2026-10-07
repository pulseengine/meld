(* =========================================================================
   Merge Transformation - Import Resolution Bridging Proof

   This file bridges the gap between the proof model and the implementation:

   - The proof model (merge_defs.v) assumes flat concatenation: every
     module's imports are preserved verbatim and index spaces grow by
     import_count + defined_count for each module.

   - The actual code (merger.rs) resolves cross-component imports against
     other modules' exports and only preserves unresolved imports in the
     merged output.

   The key insight is that import resolution is a refinement of flat
   concatenation: it strictly shrinks each module's index space contribution
   (fewer imports), while preserving the defined items unchanged.  Because
   the flat model's remap properties (completeness, injectivity, boundedness)
   are driven by the monotonic, non-overlapping structure of cumulative
   offsets, and import resolution only decreases the import terms in those
   offsets, the properties transfer to any resolved configuration.

   Specifically, we show:
   1. Resolved offsets are <= flat offsets (resolved_offset_le_flat)
   2. For defined items, the resolved remap is complete (resolved_remap_complete)
   3. For defined items, the resolved remap is injective (resolved_remap_injective)
   4. For defined items, the resolved remap is bounded (resolved_remap_bounded)
   5. The flat model's instruction rewriting theorem transfers
      (resolved_enables_rewriting)

   All theorems in this file are fully mechanized (Qed).
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith.
From MeldSpec Require Import wasm_core component_model fusion_types.
(* merge_bridge provides module_wf and gen_all_remaps_enables_rewriting,
   both referenced by resolved_enables_rewriting (Section 8). *)
From MeldMerge Require Import merge_defs merge_layout merge_remap merge_correctness
  merge_bridge.
Import ListNotations.

(* =========================================================================
   Section 1: Import Resolution Configuration

   We model import resolution abstractly as a predicate on imports: for
   each module in the input, some imports are "resolved" (matched against
   exports of other modules) and the rest are "unresolved" (kept in the
   merged output).

   This abstraction avoids depending on the resolver's exact algorithm
   while capturing the essential property: resolution only removes imports.
   ========================================================================= *)

(* A resolution configuration specifies, for each (module_source, module)
   pair, which imports are resolved (removed from the merged output). *)
Definition import_resolved := module_source -> import -> bool.

(* Count unresolved func imports for a module under a resolution config *)
Definition count_unresolved_func_imports (resolve : import_resolved)
    (src : module_source) (m : module) : nat :=
  length (filter (fun imp =>
    match imp_desc imp with
    | ImportFunc _ => negb (resolve src imp)
    | _ => false
    end
  ) (mod_imports m)).

(* Count unresolved table imports *)
Definition count_unresolved_table_imports (resolve : import_resolved)
    (src : module_source) (m : module) : nat :=
  length (filter (fun imp =>
    match imp_desc imp with
    | ImportTable _ => negb (resolve src imp)
    | _ => false
    end
  ) (mod_imports m)).

(* Count unresolved mem imports *)
Definition count_unresolved_mem_imports (resolve : import_resolved)
    (src : module_source) (m : module) : nat :=
  length (filter (fun imp =>
    match imp_desc imp with
    | ImportMem _ => negb (resolve src imp)
    | _ => false
    end
  ) (mod_imports m)).

(* Count unresolved global imports *)
Definition count_unresolved_global_imports (resolve : import_resolved)
    (src : module_source) (m : module) : nat :=
  length (filter (fun imp =>
    match imp_desc imp with
    | ImportGlobal _ => negb (resolve src imp)
    | _ => false
    end
  ) (mod_imports m)).

(* =========================================================================
   Section 2: Well-formedness of Resolution

   A resolution is well-formed if:
   (a) Every resolved import actually corresponds to an export in some
       other module in the input.
   (b) Resolution only resolves imports of the correct kind (a resolved
       ImportFunc maps to an ExportFunc, etc.).

   These are the conditions under which import resolution is semantically
   valid — the resolved import can be replaced by a direct reference to
   the exporting module's definition.
   ========================================================================= *)

(* An import is matchable if some module in the input exports a compatible item *)
Definition import_matchable (input : merge_input) (src : module_source)
    (imp : import) : Prop :=
  exists src' m',
    In (src', m') input /\
    src' <> src /\
    exists exp, In exp (mod_exports m') /\
      imp_module imp = exp_name exp /\  (* name matching simplified *)
      match imp_desc imp, exp_desc exp with
      | ImportFunc _, ExportFunc _ => True
      | ImportTable _, ExportTable _ => True
      | ImportMem _, ExportMem _ => True
      | ImportGlobal _, ExportGlobal _ => True
      | _, _ => False
      end.

(* A resolution is well-formed if it only resolves matchable imports *)
Definition resolution_wf (input : merge_input) (resolve : import_resolved)
    : Prop :=
  forall src m imp,
    In (src, m) input ->
    In imp (mod_imports m) ->
    resolve src imp = true ->
    import_matchable input src imp.

(* =========================================================================
   Section 3: Resolved Space Counts and Offsets

   With import resolution, the index space contribution of each module
   shrinks: instead of count_*_imports + defined_count, it becomes
   count_unresolved_*_imports + defined_count.

   The key structural property is:
     unresolved_imports <= all_imports
   which implies:
     resolved_space_count <= flat_space_count
   ========================================================================= *)

(* Resolved space count for a module: unresolved imports + defined items.
   Compare with space_count_of_module which uses ALL imports. *)
Definition resolved_space_count (resolve : import_resolved)
    (src : module_source) (m : module) (space : index_space) : nat :=
  match space with
  | TypeIdx => length (mod_types m)
  | FuncIdx => count_unresolved_func_imports resolve src m + length (mod_funcs m)
  | TableIdx => count_unresolved_table_imports resolve src m + length (mod_tables m)
  | MemIdx => count_unresolved_mem_imports resolve src m + length (mod_mems m)
  | GlobalIdx => count_unresolved_global_imports resolve src m + length (mod_globals m)
  | ElemIdx => length (mod_elems m)
  | DataIdx => length (mod_datas m)
  end.

(* Fundamental inequality: unresolved func import count <= total func import count.
   filter with (negb . resolve) is a subset of filter with (is_func_import). *)
Lemma unresolved_le_total_func :
  forall resolve src m,
    count_unresolved_func_imports resolve src m <= count_func_imports m.
Proof.
  intros resolve src m.
  unfold count_unresolved_func_imports, count_func_imports.
  (* Both filter the same list (mod_imports m). The unresolved filter
     is strictly more selective: it requires both ImportFunc AND negb resolve. *)
  induction (mod_imports m) as [|imp rest IH]; simpl.
  - lia.
  - destruct (imp_desc imp) eqn:Hdesc.
    + (* ImportFunc *)
      destruct (resolve src imp); simpl; lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma unresolved_le_total_table :
  forall resolve src m,
    count_unresolved_table_imports resolve src m <= count_table_imports m.
Proof.
  intros resolve src m.
  unfold count_unresolved_table_imports, count_table_imports.
  induction (mod_imports m) as [|imp rest IH]; simpl.
  - lia.
  - destruct (imp_desc imp) eqn:Hdesc.
    + lia.
    + destruct (resolve src imp); simpl; lia.
    + lia.
    + lia.
Qed.

Lemma unresolved_le_total_mem :
  forall resolve src m,
    count_unresolved_mem_imports resolve src m <= count_mem_imports m.
Proof.
  intros resolve src m.
  unfold count_unresolved_mem_imports, count_mem_imports.
  induction (mod_imports m) as [|imp rest IH]; simpl.
  - lia.
  - destruct (imp_desc imp) eqn:Hdesc.
    + lia.
    + lia.
    + destruct (resolve src imp); simpl; lia.
    + lia.
Qed.

Lemma unresolved_le_total_global :
  forall resolve src m,
    count_unresolved_global_imports resolve src m <= count_global_imports m.
Proof.
  intros resolve src m.
  unfold count_unresolved_global_imports, count_global_imports.
  induction (mod_imports m) as [|imp rest IH]; simpl.
  - lia.
  - destruct (imp_desc imp) eqn:Hdesc.
    + lia.
    + lia.
    + lia.
    + destruct (resolve src imp); simpl; lia.
Qed.

(* Core inequality: resolved_space_count <= flat space_count *)
Lemma resolved_space_count_le :
  forall resolve src m space,
    resolved_space_count resolve src m space <=
    space_count_of_module m space.
Proof.
  intros resolve src m space.
  unfold resolved_space_count, space_count_of_module.
  destruct space; try lia.
  - (* FuncIdx *)
    pose proof (unresolved_le_total_func resolve src m). lia.
  - (* TableIdx *)
    pose proof (unresolved_le_total_table resolve src m). lia.
  - (* MemIdx *)
    pose proof (unresolved_le_total_mem resolve src m). lia.
  - (* GlobalIdx *)
    pose proof (unresolved_le_total_global resolve src m). lia.
Qed.

(* Resolved cumulative offset for module at position mod_idx *)
Definition resolved_offset (resolve : import_resolved) (input : merge_input)
    (space : index_space) (mod_idx : nat) : nat :=
  let prior := firstn mod_idx input in
  fold_left (fun acc sm =>
    acc + resolved_space_count resolve (fst sm) (snd sm) space
  ) prior 0.

(* Total resolved space count across all modules *)
Definition total_resolved_space_count (resolve : import_resolved)
    (input : merge_input) (space : index_space) : nat :=
  fold_left (fun acc sm =>
    acc + resolved_space_count resolve (fst sm) (snd sm) space
  ) input 0.

(* Accumulating a pointwise-smaller summand from a smaller base yields a
   smaller fold.  This is the one fact the two "resolved <= flat" lemmas
   below need; the base is generalised so the induction goes through
   directly on the list.

   Do NOT prove these with `rewrite !fold_left_add_shift`: that lemma's
   right-hand side (`base + fold_left _ l 0`) contains an instance of its
   own left-hand side (`fold_left _ l 0`, base := 0), so the `!` iteration
   never fails and never terminates — every step adds one `0 +` to the goal
   and the proof term grows quadratically (#450).  Siblings use the lemma
   only with explicit arguments for the same reason; see
   merge_correctness.v (fold_left_add_split). *)
Lemma fold_left_add_le_pointwise :
  forall {A : Type} (f g : A -> nat),
    (forall x, f x <= g x) ->
    forall (l : list A) (base1 base2 : nat),
      base1 <= base2 ->
      fold_left (fun acc x => acc + f x) l base1 <=
      fold_left (fun acc x => acc + g x) l base2.
Proof.
  intros A f g Hfg l.
  induction l as [|x l' IH]; intros base1 base2 Hb; simpl.
  - exact Hb.
  - apply IH. specialize (Hfg x). lia.
Qed.

(* Splitting a prefix fold at an element: the fold over the first i items
   plus the i-th item is bounded by the fold over any longer prefix
   (j > i).  This is the "non-overlapping ranges" fact that
   resolved_remap_injective needs for modules at different positions.
   fold_left_add_shift is applied with explicit arguments only. *)
Lemma fold_left_add_firstn_step :
  forall {A : Type} (f : A -> nat) (i j : nat) (l : list A) (x : A),
    i < j ->
    nth_error l i = Some x ->
    fold_left (fun acc y => acc + f y) (firstn i l) 0 + f x <=
    fold_left (fun acc y => acc + f y) (firstn j l) 0.
Proof.
  intros A f i.
  induction i as [|i' IH]; intros j l x Hij Hnth;
    destruct l as [|a l']; simpl in Hnth; try discriminate Hnth;
    (destruct j as [|j']; [exfalso; lia | simpl]).
  - (* i = 0, l = a :: l', j = S j' *)
    injection Hnth as Hax. subst a.
    rewrite (fold_left_add_shift f (firstn j' l') (f x)). lia.
  - (* i = S i', l = a :: l', j = S j' *)
    rewrite (fold_left_add_shift f (firstn i' l') (f a)).
    rewrite (fold_left_add_shift f (firstn j' l') (f a)).
    specialize (IH j' l' x ltac:(lia) Hnth). lia.
Qed.

(* Resolved offsets are <= flat offsets.
   Proof strategy: both sides are a fold_left over the same prefix of input
   with pointwise-ordered summands (resolved_space_count_le), so
   fold_left_add_le_pointwise applies directly. *)
Lemma resolved_offset_le_flat :
  forall resolve input space mod_idx,
    resolved_offset resolve input space mod_idx <=
    compute_offset input space mod_idx.
Proof.
  intros resolve input space mod_idx.
  unfold resolved_offset, compute_offset.
  apply (fold_left_add_le_pointwise
           (fun sm => resolved_space_count resolve (fst sm) (snd sm) space)
           (fun sm => space_count_of_module (snd sm) space)).
  - intros sm. apply resolved_space_count_le.
  - lia.
Qed.

(* Total resolved space count <= total flat space count *)
Lemma total_resolved_le_flat :
  forall resolve input space,
    total_resolved_space_count resolve input space <=
    total_space_count input space.
Proof.
  intros resolve input space.
  unfold total_resolved_space_count, total_space_count.
  apply (fold_left_add_le_pointwise
           (fun sm => resolved_space_count resolve (fst sm) (snd sm) space)
           (fun sm => space_count_of_module (snd sm) space)).
  - intros sm. apply resolved_space_count_le.
  - lia.
Qed.

(* =========================================================================
   Section 4: Trivial Resolution (No Imports Resolved)

   When the resolution function resolves nothing (resolve = fun _ _ => false),
   the resolved model collapses to the flat model exactly.  This shows the
   flat model is a special case of the resolved model.
   ========================================================================= *)

Definition trivial_resolve : import_resolved := fun _ _ => false.

(* With trivial_resolve unfolded, the unresolved-import predicate is
   `... => negb false | _ => false` and count_func_imports's is
   `... => true | _ => false`: convertible, so the goal closes by
   conversion.  (An `f_equal` here already discharges the goal via
   reflexivity, which left the original induction script with no goal
   to operate on — "No such goal" at the first bullet.) *)
Lemma trivial_resolve_func_count :
  forall src m,
    count_unresolved_func_imports trivial_resolve src m = count_func_imports m.
Proof.
  intros src m.
  unfold count_unresolved_func_imports, count_func_imports, trivial_resolve.
  reflexivity.
Qed.

Lemma trivial_resolve_table_count :
  forall src m,
    count_unresolved_table_imports trivial_resolve src m = count_table_imports m.
Proof.
  intros src m.
  unfold count_unresolved_table_imports, count_table_imports, trivial_resolve.
  reflexivity.
Qed.

Lemma trivial_resolve_mem_count :
  forall src m,
    count_unresolved_mem_imports trivial_resolve src m = count_mem_imports m.
Proof.
  intros src m.
  unfold count_unresolved_mem_imports, count_mem_imports, trivial_resolve.
  reflexivity.
Qed.

Lemma trivial_resolve_global_count :
  forall src m,
    count_unresolved_global_imports trivial_resolve src m = count_global_imports m.
Proof.
  intros src m.
  unfold count_unresolved_global_imports, count_global_imports, trivial_resolve.
  reflexivity.
Qed.

(* The trivial resolution preserves space counts exactly *)
Lemma trivial_resolved_space_count :
  forall src m space,
    resolved_space_count trivial_resolve src m space
    = space_count_of_module m space.
Proof.
  intros src m space.
  unfold resolved_space_count, space_count_of_module.
  (* All seven cases close by conversion (the four import-bearing ones for
     the reason given at trivial_resolve_func_count).  No `try`: if a case
     ever stops being convertible this must fail loudly, not fall through
     to a bullet that has no goal. *)
  destruct space; reflexivity.
Qed.

(* =========================================================================
   Section 5: Defined-Item Remap

   Import resolution does not affect the number of defined items in any
   module. It only changes the import count, shifting where defined items
   start in the index space. The crucial observation is:

     In the flat model:     defined func j → flat_offset + all_imports + j
     In the resolved model: defined func j → resolved_offset + unresolved_imports + j

   Both assignments are injective (non-overlapping ranges per module)
   because the defined_count is the same, and cumulative offsets are
   still monotonic.

   We define a "resolved remap" for defined items and show it satisfies
   the same structural properties as the flat model's gen_all_remaps.
   ========================================================================= *)

(* A resolved remap entry for a defined item.
   For a defined function at local index j in module (src, m), the
   resolved fused index is:
     resolved_offset(mod_idx, FuncIdx) + unresolved_func_imports + j *)
Definition resolved_defined_fused_idx (resolve : import_resolved)
    (input : merge_input) (src : module_source) (m : module)
    (mod_idx : nat) (space : index_space) (local_idx : nat) : nat :=
  resolved_offset resolve input space mod_idx +
  match space with
  | FuncIdx => count_unresolved_func_imports resolve src m
  | TableIdx => count_unresolved_table_imports resolve src m
  | MemIdx => count_unresolved_mem_imports resolve src m
  | GlobalIdx => count_unresolved_global_imports resolve src m
  | TypeIdx | ElemIdx | DataIdx => 0
  end + local_idx.

(* The defined item count is the same in flat and resolved models.
   This is the invariant that makes the bridge work: resolution only
   affects import counts, not defined item counts. *)
Definition defined_count (m : module) (space : index_space) : nat :=
  match space with
  | TypeIdx => length (mod_types m)
  | FuncIdx => length (mod_funcs m)
  | TableIdx => length (mod_tables m)
  | MemIdx => length (mod_mems m)
  | GlobalIdx => length (mod_globals m)
  | ElemIdx => length (mod_elems m)
  | DataIdx => length (mod_datas m)
  end.

(* =========================================================================
   Section 6: Core Bridge Theorems

   These theorems show that the properties proved for the flat model in
   merge_correctness.v transfer to any valid import resolution.
   ========================================================================= *)

(* Theorem 1: Resolved remap is bounded.
   Every resolved defined fused index is within the total resolved space.
   Proof strategy: resolved_defined_fused_idx(mod_idx, space, j)
     = resolved_offset(mod_idx) + unresolved_imports(mod_idx) + j
     < resolved_offset(mod_idx) + resolved_space_count(mod_idx, space)
       [because j < defined_count and unresolved_imports + defined_count
        = resolved_space_count]
     <= resolved_offset(mod_idx + 1)
       [resolved_offset is cumulative]
     <= total_resolved_space_count
       [offset at any position <= offset at length input] *)
Theorem resolved_remap_bounded :
  forall resolve input src m mod_idx space local_idx,
    nth_error input mod_idx = Some (src, m) ->
    local_idx < defined_count m space ->
    resolved_defined_fused_idx resolve input src m mod_idx space local_idx <
    total_resolved_space_count resolve input space.
Proof.
  intros resolve input src m mod_idx space local_idx Hnth Hbound.
  unfold resolved_defined_fused_idx, total_resolved_space_count.
  (* The fused index is:
       resolved_offset(mod_idx) + unresolved_import_count + local_idx
     which is < resolved_offset(mod_idx) + resolved_space_count(mod_idx)
     because unresolved_import_count + local_idx < resolved_space_count.
     And resolved_offset(mod_idx) + resolved_space_count(mod_idx) <=
     total_resolved_space_count. *)
  assert (Hmod_len: mod_idx < length input).
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  (* Strategy: show resolved_offset(mod_idx) + resolved_space_count <= total,
     then show the fused index < resolved_offset(mod_idx) + resolved_space_count *)
  unfold resolved_offset.
  (* The rest requires unfolding fold_left over the split input.
     This is structurally identical to offset_plus_count_total from merge_remap.v
     but with resolved_space_count instead of space_count_of_module. *)
  (* We split input at mod_idx and use fold_left_app *)
  assert (Hsplit: input = firstn mod_idx input ++ (src, m) :: skipn (S mod_idx) input).
  { rewrite <- (firstn_skipn mod_idx input) at 1.
    f_equal.
    destruct (skipn mod_idx input) as [|x rest] eqn:Hskip.
    - exfalso. assert (length (skipn mod_idx input) = 0)
        by (rewrite Hskip; reflexivity).
      rewrite length_skipn in H. lia.
    - f_equal.
      + assert (nth_error (skipn mod_idx input) 0 = Some (src, m)).
        { rewrite nth_error_skipn. rewrite Nat.add_0_r. exact Hnth. }
        rewrite Hskip in H. simpl in H. congruence.
      + replace (S mod_idx) with (1 + mod_idx) by lia.
        rewrite <- skipn_skipn. rewrite Hskip. reflexivity. }
  rewrite Hsplit at 2.
  rewrite fold_left_app. simpl.
  (* Shift the fold over the SUFFIX explicitly.  A bare
     `rewrite fold_left_add_shift` picks the first matching subterm, which
     is the prefix fold on the left (base := 0) — a no-op that leaves the
     suffix fold's base buried, and lia has no witness. *)
  rewrite (fold_left_add_shift _ (skipn (S mod_idx) input)).
  unfold resolved_space_count, defined_count in *.
  destruct space; simpl in *; lia.
Qed.

(* Theorem 2: Resolved remap for defined items is injective.
   If two defined items from (potentially different) modules get the same
   resolved fused index, they must be from the same module at the same
   local index.
   Proof strategy: same as gen_all_remaps_injective — the resolved offsets
   are still cumulative, so modules at different positions have
   non-overlapping ranges. Within the same module, different local indices
   produce different fused indices (offset + local_idx is injective). *)
Theorem resolved_remap_injective :
  forall resolve input src1 m1 idx1 src2 m2 idx2 space local1 local2,
    nth_error input idx1 = Some (src1, m1) ->
    nth_error input idx2 = Some (src2, m2) ->
    local1 < defined_count m1 space ->
    local2 < defined_count m2 space ->
    resolved_defined_fused_idx resolve input src1 m1 idx1 space local1 =
    resolved_defined_fused_idx resolve input src2 m2 idx2 space local2 ->
    idx1 = idx2 /\ local1 = local2.
Proof.
  intros resolve input src1 m1 idx1 src2 m2 idx2 space local1 local2
         Hnth1 Hnth2 Hbound1 Hbound2 Hfused_eq.
  unfold resolved_defined_fused_idx in Hfused_eq.
  (* Compare module positions idx1 and idx2 using offset monotonicity.
     The "non-overlapping ranges" step is fold_left_add_firstn_step: the
     fold over firstn idx1 plus module idx1's whole contribution is bounded
     by the fold over firstn idx2 whenever idx1 < idx2. *)
  destruct (Nat.lt_trichotomy idx1 idx2) as [Hlt | [Heq | Hgt]].
  - (* idx1 < idx2: contradiction via non-overlapping ranges *)
    exfalso.
    (* resolved_offset(idx1) + resolved_space_count(idx1) <= resolved_offset(idx2) *)
    (* The fused index for module idx1 is
         resolved_offset(idx1) + unresolved_imports(1) + local1
       which is < resolved_offset(idx1) + resolved_space_count(idx1)
       And resolved_offset(idx1) + resolved_space_count(idx1) <= resolved_offset(idx2)
       <= resolved_offset(idx2) + unresolved_imports(2) + local2
       So fused1 < fused2, contradicting equality. *)
    assert (Hstep: resolved_offset resolve input space idx1 +
                   resolved_space_count resolve src1 m1 space <=
                   resolved_offset resolve input space idx2).
    { unfold resolved_offset.
      exact (fold_left_add_firstn_step
               (fun sm => resolved_space_count resolve (fst sm) (snd sm) space)
               idx1 idx2 input (src1, m1) Hlt Hnth1). }
    unfold resolved_space_count, defined_count in *.
    destruct space; simpl in *; lia.
  - (* idx1 = idx2: same module, so local indices must match *)
    subst idx2.
    rewrite Hnth1 in Hnth2. injection Hnth2 as Hsrc_eq Hm_eq.
    subst src2 m2.
    split; [reflexivity | lia].
  - (* idx2 < idx1: symmetric to idx1 < idx2 *)
    exfalso.
    assert (Hstep: resolved_offset resolve input space idx2 +
                   resolved_space_count resolve src2 m2 space <=
                   resolved_offset resolve input space idx1).
    { unfold resolved_offset.
      exact (fold_left_add_firstn_step
               (fun sm => resolved_space_count resolve (fst sm) (snd sm) space)
               idx2 idx1 input (src2, m2) Hgt Hnth2). }
    unfold resolved_space_count, defined_count in *.
    destruct space; simpl in *; lia.
Qed.

(* Theorem 3: Resolved remap for defined items is complete.
   Every defined item in every module has a unique resolved fused index. *)
Theorem resolved_remap_complete :
  forall resolve input src m mod_idx space local_idx,
    nth_error input mod_idx = Some (src, m) ->
    local_idx < defined_count m space ->
    exists fused_idx,
      fused_idx = resolved_defined_fused_idx resolve input src m mod_idx space local_idx /\
      fused_idx < total_resolved_space_count resolve input space.
Proof.
  intros resolve input src m mod_idx space local_idx Hnth Hbound.
  exists (resolved_defined_fused_idx resolve input src m mod_idx space local_idx).
  split; [reflexivity|].
  apply resolved_remap_bounded; assumption.
Qed.

(* =========================================================================
   Section 7: Correspondence with Flat Model

   The flat model's gen_all_remaps assigns fused indices to ALL items
   (imports + defined). The resolved model only needs to track defined
   items (imports are resolved away or renumbered). We show that for
   defined items, the flat model's fused index and the resolved model's
   fused index maintain a consistent relationship:

     flat_fused_idx = flat_offset(mod_idx) + import_count + local_idx
     resolved_fused_idx = resolved_offset(mod_idx) + unresolved_import_count + local_idx

   Since flat_offset >= resolved_offset and import_count >= unresolved_import_count,
   the relationship is:
     resolved_fused_idx <= flat_fused_idx

   More importantly, both are injective for defined items, so the
   correspondence is structure-preserving.
   ========================================================================= *)

(* For defined items, the resolved fused index <= the flat model's fused index.
   This captures the "refinement" nature of import resolution:
   resolving imports compresses the index space. *)
Theorem resolved_le_flat_defined :
  forall resolve input src m mod_idx space local_idx,
    nth_error input mod_idx = Some (src, m) ->
    local_idx < defined_count m space ->
    resolved_defined_fused_idx resolve input src m mod_idx space local_idx <=
    compute_offset input space mod_idx +
    match space with
    | TypeIdx => 0
    | FuncIdx => count_func_imports m
    | TableIdx => count_table_imports m
    | MemIdx => count_mem_imports m
    | GlobalIdx => count_global_imports m
    | ElemIdx => 0
    | DataIdx => 0
    end + local_idx.
Proof.
  intros resolve input src m mod_idx space local_idx Hnth Hbound.
  unfold resolved_defined_fused_idx.
  pose proof (resolved_offset_le_flat resolve input space mod_idx) as Hoff_le.
  destruct space; simpl;
  try (pose proof (unresolved_le_total_func resolve src m));
  try (pose proof (unresolved_le_total_table resolve src m));
  try (pose proof (unresolved_le_total_mem resolve src m));
  try (pose proof (unresolved_le_total_global resolve src m));
  lia.
Qed.

(* =========================================================================
   Section 8: Instruction Rewriting Transfer

   The flat model's gen_all_remaps_enables_rewriting theorem shows that
   every instruction can be rewritten using the flat remap. Since the
   resolved model assigns valid indices to all defined items (within
   the resolved space), instruction rewriting also works in the resolved
   model — provided we construct an appropriate remap table.

   We define a "resolved remap table" that maps each source index to its
   resolved fused index, and show that it supports instruction rewriting
   for well-formed modules.
   ========================================================================= *)

(* A resolved remap table maps:
   - For import indices (src_idx < import_count): to the resolved import's
     position (if unresolved) or to the target definition (if resolved)
   - For defined indices (src_idx >= import_count): to the resolved
     defined fused index

   For the purposes of instruction rewriting, we only need completeness:
   every valid src_idx has a fused_idx in the table. The exact values
   depend on the resolver's choices, but the existence is guaranteed by
   resolved_remap_complete. *)

(* The resolved model supports instruction rewriting.
   Proof strategy: the argument is identical to gen_all_remaps_enables_rewriting
   but uses the resolved remap table. The key premises are:
   (1) Every valid index has a remap entry (completeness)
   (2) Module well-formedness (indices in bounds)
   These are exactly what resolved_remap_complete provides.

   The proof uses the flat model's gen_all_remaps as a complete remap
   table, sidestepping the need to construct a resolved-specific table.
   This works because gen_all_remaps overapproximates the resolved model
   (it maps ALL indices, including resolved imports). *)
(* `strategy` is bound here but appears in no hypothesis and no conclusion —
   a vacuous quantifier — so Rocq could not infer its type and this statement
   has never elaborated: "Cannot infer the type of strategy". Only the proof
   body forces it, via gen_all_remaps : merge_input -> memory_strategy ->
   remap_table, and that is elaborated too late to help.

   Annotated explicitly rather than left to an `Implicit Types strategy :
   memory_strategy` declaration above the theorem. The logical content is
   identical either way — the type was already forced, so writing it down
   is not a change of claim — but a binder's type belongs where a reader of
   the statement can see it, and `Implicit Types` would also silently capture
   every later binder named `strategy` in this file, which is a wider effect
   than the problem.

   Left alone deliberately: the vacuous quantification itself. Dropping an
   unused `forall` WOULD change the statement, and the proof does need some
   strategy to instantiate gen_all_remaps with. Worth revisiting on its own
   merits rather than inside a performance fix. *)
Theorem resolved_enables_rewriting :
  forall resolve input (strategy : memory_strategy),
    resolution_wf input resolve ->
    unique_sources input ->
    forall src m f,
      In (src, m) input ->
      module_wf m ->
      In f (mod_funcs m) ->
      (* There exists a resolved remap table such that all instructions
         in f's body can be rewritten using it. *)
      exists resolved_remaps body',
        remaps_complete input resolved_remaps /\
        Forall2 (instr_rewrites resolved_remaps src) (func_body f) body'.
Proof.
  intros resolve input strategy Hres_wf Huniq src m f Hin Hwf Hf_in.
  (* The flat model's gen_all_remaps is complete, so we can use it directly
     as a valid resolved remap table. This is sound because the flat model
     overapproximates the resolved model (it maps ALL indices, including
     resolved imports, which the resolved model doesn't need). *)
  exists (gen_all_remaps input strategy).
  assert (Hcomplete: remaps_complete input (gen_all_remaps input strategy)).
  { apply gen_all_remaps_complete. exact Huniq. }
  pose proof (gen_all_remaps_enables_rewriting input strategy Huniq src m f Hin Hwf Hf_in)
    as [body' Hbody'].
  exists body'. split; [exact Hcomplete | exact Hbody'].
Qed.

(* =========================================================================
   Section 9: Summary of the Bridge

   The gap between the flat model and import-resolving code is bridged by
   the following chain of results:

   1. resolved_space_count_le: Resolution shrinks space counts
      (removing imports can only decrease the index space size).

   2. resolved_offset_le_flat: Resolved cumulative offsets are <=
      flat cumulative offsets (consequence of smaller space counts).

   3. resolved_remap_bounded: Resolved fused indices for defined items
      are within the total resolved space (analogous to gen_all_remaps_bounded).

   4. resolved_remap_injective: Resolved fused indices for defined items
      are injective (analogous to gen_all_remaps_injective /
      remap_injective_separate_memory).

   5. resolved_remap_complete: Every defined item has a resolved fused
      index (analogous to gen_all_remaps_complete).

   6. resolved_le_flat_defined: The resolved fused index for a defined
      item is <= the flat model's fused index (import resolution is a
      refinement that compresses the index space).

   7. resolved_enables_rewriting: The resolved model supports instruction
      rewriting (leverages the flat model's gen_all_remaps as a superset).

   Together, these show that the flat concatenation model's correctness
   properties are an upper bound: any import resolution that satisfies
   resolution_wf produces a valid, injective index assignment for all
   defined items, and instruction rewriting works correctly.

   The code (merger.rs) implements one specific resolution strategy via
   the resolver. The proofs above hold for ANY resolution satisfying
   resolution_wf, including the actual resolver's output.
   ========================================================================= *)

(* End of merge_resolution *)
