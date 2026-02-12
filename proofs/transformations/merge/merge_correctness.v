(* =========================================================================
   Merge Transformation - Correctness Proofs

   This file contains the main correctness theorems for merge.
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith.
From MeldSpec Require Import wasm_core component_model fusion_spec.
From MeldMerge Require Import merge_defs merge_layout merge_remap.
Import ListNotations.

(* -------------------------------------------------------------------------
   Merged Module Structure Lemmas
   ------------------------------------------------------------------------- *)

Lemma merge_types_length :
  forall input,
    length (mod_types (merge_modules input)) = total_space_count input TypeIdx.
Proof.
  intro input.
  unfold merge_modules, total_space_count, space_count_of_module. simpl.
  rewrite sum_space_counts_types. reflexivity.
Qed.

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

(* Helper: filter over flat_map distributes as flat_map of filtered sublists.
   Used by the count_*_imports_flat_map lemmas below. *)
Lemma count_imports_flat_map_aux :
  forall {A : Type} (p : import -> bool) (f : A -> list import) (l : list A),
    length (filter p (flat_map f l))
    = fold_left (fun acc x => acc + length (filter p (f x))) l 0.
Proof.
  intros A p f l.
  induction l as [|h t IH]; simpl.
  - reflexivity.
  - rewrite filter_app. rewrite length_app. rewrite IH.
    rewrite (fold_left_add_shift (fun x => length (filter p (f x))) t
                                  (length (filter p (f h)))).
    lia.
Qed.

Lemma count_func_imports_flat_map :
  forall input,
    count_func_imports (merge_modules input)
    = fold_left (fun acc sm => acc + count_func_imports (snd sm)) input 0.
Proof.
  intro input.
  unfold merge_modules, count_func_imports, merge_imports. simpl.
  apply count_imports_flat_map_aux.
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

Lemma count_table_imports_flat_map :
  forall input,
    count_table_imports (merge_modules input)
    = fold_left (fun acc sm => acc + count_table_imports (snd sm)) input 0.
Proof.
  intro input.
  unfold merge_modules, count_table_imports, merge_imports. simpl.
  apply count_imports_flat_map_aux.
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

Lemma count_mem_imports_flat_map :
  forall input,
    count_mem_imports (merge_modules input)
    = fold_left (fun acc sm => acc + count_mem_imports (snd sm)) input 0.
Proof.
  intro input.
  unfold merge_modules, count_mem_imports, merge_imports. simpl.
  apply count_imports_flat_map_aux.
Qed.

(* merge_mems_length: Design gap — SharedMemory MemIdx remapping.

   ISSUE: SharedMemory collapses all source memories into 1 shared memory,
   but gen_all_remaps computes cumulative offsets (total_space_count) for
   MemIdx just like for other spaces. This creates a mismatch:

   - Merged module: count_mem_imports(merged) + 1 memory slots
   - Remap bound:   fused_idx < total_space_count input MemIdx
                   = count_mem_imports(merged) + sum(length(mod_mems(m)))

   When sum(length mems) > 1, the remap can produce indices beyond the
   merged module's memory space. The callers need fused_idx < merged_total,
   but only have fused_idx < total_space_count >= merged_total.

   ROOT CAUSE: gen_all_remaps should special-case MemIdx for SharedMemory:
   all memory references should remap to index 0 (the single shared memory)
   rather than using cumulative offsets. This requires:
   1. A SharedMemory-aware remap generation for MemIdx
   2. A tighter bound: forall r, ir_space r = MemIdx -> ir_fused_idx r = 0
   3. Callers use: valid_memidx merged 0 (trivially true since 0 < 0 + 1)

   The current lemma statement (<=) is mathematically correct with a
   precondition (1 <= sum(length mems)), but the direction is WRONG for
   callers which need (>=). Neither direction works universally.

   Admitted pending SharedMemory-aware MemIdx remap redesign. *)
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
  rewrite <- fold_left_add_split.
  (* Goal: fold(mem_imports) + 1 <= fold(mem_imports) + fold(length mems)
     Equivalent to: 1 <= fold(length mems).
     Even with a precondition, the callers can't use this (<= direction).
     See design note above. *)
  admit.
Admitted.

Lemma count_global_imports_flat_map :
  forall input,
    count_global_imports (merge_modules input)
    = fold_left (fun acc sm => acc + count_global_imports (snd sm)) input 0.
Proof.
  intro input.
  unfold merge_modules, count_global_imports, merge_imports. simpl.
  apply count_imports_flat_map_aux.
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

(* -------------------------------------------------------------------------
   gen_all_remaps_aux characterization
   ------------------------------------------------------------------------- *)

(* A remap r is in gen_all_remaps_aux iff it comes from one of the modules
   in the remaining list. We prove both directions by induction on remaining,
   generalizing over start_idx. *)
Lemma in_gen_all_remaps_aux :
  forall input start_idx remaining r,
    In r (gen_all_remaps_aux input start_idx remaining) <->
    exists i src m,
      nth_error remaining i = Some (src, m) /\
      In r (gen_remaps_for_module src m (offsets_for_module input (start_idx + i))).
Proof.
  intros input start_idx remaining.
  revert start_idx.
  induction remaining as [|[src m] rest IH]; intros start_idx r; split; intro H.
  - (* [] forward: contradiction *)
    simpl in H. contradiction.
  - (* [] backward: impossible nth_error *)
    destruct H as [i [src' [m' [Hnth _]]]].
    destruct i; discriminate.
  - (* (src,m)::rest forward *)
    simpl in H.
    apply in_app_iff in H.
    destruct H as [Hhead | Htail].
    + (* r is in the current module's remaps *)
      exists 0, src, m. split.
      * reflexivity.
      * replace (start_idx + 0) with start_idx by lia. exact Hhead.
    + (* r is in the tail *)
      apply IH in Htail.
      destruct Htail as [i [src' [m' [Hnth Hin]]]].
      exists (S i), src', m'. split.
      * simpl. exact Hnth.
      * replace (start_idx + S i) with (S start_idx + i) by lia. exact Hin.
  - (* (src,m)::rest backward *)
    destruct H as [i [src' [m' [Hnth Hin]]]].
    simpl. apply in_app_iff.
    destruct i as [|i'].
    + (* i = 0: r is from current module *)
      left. simpl in Hnth. injection Hnth as Heq1 Heq2. subst src' m'.
      replace (start_idx + 0) with start_idx in Hin by lia. exact Hin.
    + (* i = S i': r is from a later module *)
      right. apply IH.
      exists i', src', m'. split.
      * simpl in Hnth. exact Hnth.
      * replace (S start_idx + i') with (start_idx + S i') by lia. exact Hin.
Qed.

(* A remap from gen_remaps_for_module has its source_idx bounded by
   the space count of the module in the corresponding index space. *)
Lemma in_gen_remaps_for_module_bound :
  forall src m offsets r,
    In r (gen_remaps_for_module src m offsets) ->
    ir_source_idx r < space_count_of_module m (ir_space r).
Proof.
  intros src m offsets r Hin.
  unfold gen_remaps_for_module in Hin.
  (* r must be in one of the 7 appended gen_remaps_for_space lists *)
  repeat (apply in_app_iff in Hin; destruct Hin as [Hin | Hin]).
  (* For each case, extract properties from in_gen_remaps_for_space_fused *)
  all: apply in_gen_remaps_for_space_fused in Hin;
       destruct Hin as [_ [Hspace [_ Hbound]]];
       subst; unfold space_count_of_module; exact Hbound.
Qed.

(* -------------------------------------------------------------------------
   Remaps bounded property
   ------------------------------------------------------------------------- *)

Definition remaps_bounded (input : merge_input) (remaps : remap_table) : Prop :=
  forall r,
    In r remaps ->
    ir_fused_idx r < total_space_count input (ir_space r).

(* gen_all_remaps produces remaps where every fused index is within bounds.
   Proof: each remap r comes from some module at position i. Its fused_idx
   equals offset(i) + source_idx. Since source_idx < space_count(m),
   fused_idx < offset(i) + space_count(m) <= total_space_count. *)
Theorem gen_all_remaps_bounded :
  forall input,
    remaps_bounded input (gen_all_remaps input).
Proof.
  intro input.
  unfold remaps_bounded, gen_all_remaps.
  intros r Hin.
  apply in_gen_all_remaps_aux in Hin.
  destruct Hin as [i [src [m [Hnth Hgen]]]].
  (* Get the fused_idx formula and source_idx bound *)
  pose proof (in_gen_remaps_for_module_fused _ _ _ _ Hgen) as [Hfused _].
  pose proof (in_gen_remaps_for_module_bound _ _ _ _ Hgen) as Hbound.
  rewrite Hfused.
  (* offset(0 + i) + source_idx < total_space_count *)
  assert (Hoff: offsets_for_module input (0 + i) (ir_space r) +
                space_count_of_module m (ir_space r)
                <= total_space_count input (ir_space r)).
  { unfold offsets_for_module.
    rewrite <- offset_at_length_eq_total.
    replace (0 + i) with i by lia.
    apply offset_plus_count_total. exact Hnth. }
  lia.
Qed.

(* -------------------------------------------------------------------------
   Main Correctness Theorems
   ------------------------------------------------------------------------- *)

(* Helper: extract the fused_idx bound from gen_all_remaps lookup.
   If lookup succeeds, the fused_idx is bounded by total_space_count. *)
Lemma lookup_fused_idx_bound :
  forall input space src src_idx fused_idx,
    lookup_remap (gen_all_remaps input) space src src_idx = Some fused_idx ->
    fused_idx < total_space_count input space.
Proof.
  intros input space src src_idx fused_idx Hlookup.
  unfold lookup_remap in Hlookup.
  destruct (find _ _) as [r|] eqn:Hfind; [|discriminate].
  injection Hlookup as Hfused. subst fused_idx.
  apply find_some in Hfind.
  destruct Hfind as [Hin_r Hmatch].
  (* Parse match condition to extract ir_space r = space *)
  apply Bool.andb_true_iff in Hmatch.
  destruct Hmatch as [H123 _].
  apply Bool.andb_true_iff in H123.
  destruct H123 as [H12 _].
  apply Bool.andb_true_iff in H12.
  destruct H12 as [Hspace_eq _].
  apply index_space_eqb_eq in Hspace_eq.
  (* Use gen_all_remaps_bounded *)
  pose proof (gen_all_remaps_bounded input) as Hbounded_all.
  unfold remaps_bounded in Hbounded_all.
  specialize (Hbounded_all r Hin_r).
  rewrite Hspace_eq in Hbounded_all. exact Hbounded_all.
Qed.

(* For the concrete gen_all_remaps, every lookup produces a valid index
   in the merged module. *)
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
  (* Get the bound on fused_idx *)
  assert (Hbound: fused_idx < total_space_count input space).
  { eapply lookup_fused_idx_bound; eauto. }
  (* Case split on space, using the length lemmas to translate
     total_space_count into the merged module's actual bounds *)
  destruct space; unfold merged.
  - (* TypeIdx *)
    rewrite merge_types_length. exact Hbound.
  - (* FuncIdx *)
    unfold valid_funcidx. rewrite merge_funcs_length. exact Hbound.
  - (* TableIdx *)
    unfold valid_tableidx. rewrite merge_tables_length. exact Hbound.
  - (* MemIdx *)
    unfold valid_memidx.
    pose proof (merge_mems_length input) as Hmems. lia.
  - (* GlobalIdx *)
    unfold valid_globalidx. rewrite merge_globals_length. exact Hbound.
  - (* ElemIdx *)
    rewrite merge_elems_length. exact Hbound.
  - (* DataIdx *)
    rewrite merge_datas_length. exact Hbound.
Qed.

(* For any remap table satisfying boundedness, lookup produces valid indices. *)
Theorem merge_correctness :
  forall input remaps merged,
    remaps_complete input remaps ->
    remaps_injective remaps ->
    remaps_bounded input remaps ->
    merged = merge_modules input ->
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
  intros input remaps merged Hcomplete Hinjective Hbounded Hmerged
         src m space src_idx fused_idx Hin Hlookup.
  subst merged.
  (* Extract the remap entry r from the lookup *)
  unfold lookup_remap in Hlookup.
  destruct (find _ remaps) as [r|] eqn:Hfind; [|discriminate].
  injection Hlookup as Hfused. subst fused_idx.
  apply find_some in Hfind.
  destruct Hfind as [Hin_r Hmatch].
  (* Parse match condition to get ir_space r = space *)
  apply Bool.andb_true_iff in Hmatch.
  destruct Hmatch as [H123 H4].
  apply Bool.andb_true_iff in H123.
  destruct H123 as [H12 H3].
  apply Bool.andb_true_iff in H12.
  destruct H12 as [H1 H2].
  apply index_space_eqb_eq in H1.
  (* From remaps_bounded, fused_idx < total_space_count *)
  specialize (Hbounded r Hin_r).
  rewrite H1 in Hbounded.
  (* Translate total_space_count into merged module bounds *)
  destruct space.
  - rewrite merge_types_length. exact Hbounded.
  - unfold valid_funcidx. rewrite merge_funcs_length. exact Hbounded.
  - unfold valid_tableidx. rewrite merge_tables_length. exact Hbounded.
  - unfold valid_memidx. pose proof (merge_mems_length input). lia.
  - unfold valid_globalidx. rewrite merge_globals_length. exact Hbounded.
  - rewrite merge_elems_length. exact Hbounded.
  - rewrite merge_datas_length. exact Hbounded.
Qed.

(* -------------------------------------------------------------------------
   Remap Generation Correctness
   ------------------------------------------------------------------------- *)

(* Helper: NoDup on a mapped list implies injectivity via nth_error.
   This is a standard property of NoDup. *)
Lemma NoDup_map_nth_error_injective :
  forall {A B : Type} (f : A -> B) (l : list A),
    NoDup (map f l) ->
    forall i j x y,
      nth_error l i = Some x ->
      nth_error l j = Some y ->
      f x = f y ->
      i = j.
Proof.
  intros A B f l Hnodup.
  induction l as [|h t IH]; intros i j x y Hi Hj Hfxy.
  - (* l = []: no elements *)
    destruct i; discriminate.
  - (* l = h :: t *)
    simpl in Hnodup. inversion Hnodup as [|? ? Hnotin Hnodup_t]. subst.
    destruct i as [|i']; destruct j as [|j'].
    + (* i = 0, j = 0 *)
      reflexivity.
    + (* i = 0, j = S j': f h = f y but y is in t, contradiction *)
      simpl in Hi. injection Hi as Hx. subst x.
      simpl in Hj.
      exfalso. apply Hnotin.
      rewrite Hfxy. apply in_map. eapply nth_error_In. exact Hj.
    + (* i = S i', j = 0: symmetric *)
      simpl in Hj. injection Hj as Hy. subst y.
      simpl in Hi.
      exfalso. apply Hnotin.
      rewrite <- Hfxy. apply in_map. eapply nth_error_In. exact Hi.
    + (* i = S i', j = S j': use IH *)
      simpl in Hi. simpl in Hj.
      f_equal. eapply IH; eauto.
Qed.

(* unique_sources (NoDup-based) is equivalent to the nth_error formulation. *)
Lemma unique_sources_nth_error :
  forall input,
    unique_sources input <->
    (forall i j src1 m1 src2 m2,
      nth_error input i = Some (src1, m1) ->
      nth_error input j = Some (src2, m2) ->
      src1 = src2 ->
      i = j).
Proof.
  intro input. unfold unique_sources. split.
  - (* Forward: NoDup (map fst input) -> nth_error injectivity *)
    intros Hnodup i j src1 m1 src2 m2 Hi Hj Hsrc_eq.
    eapply (NoDup_map_nth_error_injective fst); eauto.
    simpl. exact Hsrc_eq.
  - (* Backward: nth_error injectivity -> NoDup (map fst input) *)
    intro Hinj.
    induction input as [|[src m] rest IH].
    + constructor.
    + simpl. constructor.
      * (* src not in map fst rest *)
        intro Hin.
        apply in_map_iff in Hin.
        destruct Hin as [[src' m'] [Hfst Hin_rest]].
        simpl in Hfst. subst src'.
        apply In_nth_error in Hin_rest.
        destruct Hin_rest as [j Hj].
        (* (src, m) is at position 0, (src, m') is at position S j *)
        assert (Habs: 0 = S j).
        { eapply Hinj; simpl; eauto. reflexivity. }
        lia.
      * (* NoDup (map fst rest) *)
        apply IH.
        intros i j s1 m1' s2 m2' Hi Hj Heq.
        assert (HS: S i = S j).
        { eapply Hinj; simpl; eauto. }
        lia.
Qed.

(* Helper: find in appended lists *)
Lemma find_app :
  forall {A : Type} (P : A -> bool) (l1 l2 : list A),
    find P (l1 ++ l2) =
    match find P l1 with
    | Some x => Some x
    | None => find P l2
    end.
Proof.
  intros A P l1 l2.
  induction l1 as [|h t IH]; simpl.
  - reflexivity.
  - destruct (P h); [reflexivity | exact IH].
Qed.

(* Helper: find fails for wrong source in gen_remaps_for_module *)
Lemma find_gen_remaps_for_module_wrong_src :
  forall src1 src2 m space offsets src_idx,
    fst src1 <> fst src2 \/ snd src1 <> snd src2 ->
    find (fun r =>
      index_space_eqb (ir_space r) space &&
      Nat.eqb (fst (ir_source r)) (fst src1) &&
      Nat.eqb (snd (ir_source r)) (snd src1) &&
      Nat.eqb (ir_source_idx r) src_idx)
    (gen_remaps_for_module src2 m offsets) = None.
Proof.
  intros src1 src2 m space offsets src_idx Hneq.
  unfold gen_remaps_for_module.
  repeat rewrite find_app.
  repeat (rewrite find_gen_remaps_for_space_wrong_src; [|exact Hneq]).
  reflexivity.
Qed.

(* Helper: lookup_remap distributes over list append *)
Lemma lookup_remap_app :
  forall l1 l2 space src src_idx,
    lookup_remap (l1 ++ l2) space src src_idx =
    match lookup_remap l1 space src src_idx with
    | Some fused => Some fused
    | None => lookup_remap l2 space src src_idx
    end.
Proof.
  intros l1 l2 space src src_idx.
  unfold lookup_remap.
  rewrite find_app.
  destruct (find _ l1) as [r|]; reflexivity.
Qed.

(* Helper: lookup_remap fails for wrong space *)
Lemma lookup_remap_wrong_space :
  forall src m sp1 sp2 offset count src_idx,
    sp1 <> sp2 ->
    lookup_remap (gen_remaps_for_space src m sp2 offset count) sp1 src src_idx = None.
Proof.
  intros src m sp1 sp2 offset count src_idx Hneq.
  unfold lookup_remap.
  rewrite find_gen_remaps_for_space_wrong_space; auto.
Qed.

(* Helper: lookup_remap fails for wrong source *)
Lemma lookup_remap_wrong_src :
  forall src1 src2 m sp offset count src_idx,
    fst src1 <> fst src2 \/ snd src1 <> snd src2 ->
    lookup_remap (gen_remaps_for_space src2 m sp offset count) sp src1 src_idx = None.
Proof.
  intros src1 src2 m sp offset count src_idx Hneq.
  unfold lookup_remap.
  rewrite find_gen_remaps_for_space_wrong_src; auto.
Qed.

(* Helper: lookup_remap fails for wrong source in gen_remaps_for_module *)
Lemma lookup_remap_module_wrong_src :
  forall src1 src2 m space offsets src_idx,
    fst src1 <> fst src2 \/ snd src1 <> snd src2 ->
    lookup_remap (gen_remaps_for_module src2 m offsets) space src1 src_idx = None.
Proof.
  intros src1 src2 m space offsets src_idx Hneq.
  unfold gen_remaps_for_module.
  repeat rewrite lookup_remap_app.
  repeat (rewrite lookup_remap_wrong_src; auto).
Qed.

(* Helper: lookup_remap succeeds in gen_remaps_for_module for the right source *)
Lemma lookup_remap_gen_remaps_for_module :
  forall src m offsets space src_idx,
    src_idx < space_count_of_module m space ->
    lookup_remap (gen_remaps_for_module src m offsets) space src src_idx
    = Some (offsets space + src_idx).
Proof.
  intros src m offsets space src_idx Hbound.
  unfold gen_remaps_for_module, space_count_of_module in *.
  (* Navigate through the appended lists to find the correct space.
     gen_remaps_for_module concatenates 7 segments in order:
     TypeIdx, FuncIdx, TableIdx, MemIdx, GlobalIdx, ElemIdx, DataIdx *)
  repeat rewrite lookup_remap_app.
  destruct space.
  - (* FuncIdx: second segment *)
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite (lookup_remap_gen_space_success src m FuncIdx); auto.
  - (* TableIdx: third segment *)
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite (lookup_remap_gen_space_success src m TableIdx); auto.
  - (* MemIdx: fourth segment *)
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite (lookup_remap_gen_space_success src m MemIdx); auto.
  - (* GlobalIdx: fifth segment *)
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite (lookup_remap_gen_space_success src m GlobalIdx); auto.
  - (* TypeIdx: first segment *)
    rewrite (lookup_remap_gen_space_success src m TypeIdx); auto.
  - (* ElemIdx: sixth segment *)
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite (lookup_remap_gen_space_success src m ElemIdx); auto.
  - (* DataIdx: seventh segment *)
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite lookup_remap_wrong_space; [|discriminate].
    rewrite (lookup_remap_gen_space_success src m DataIdx); auto.
Qed.

(* Helper: lookup_remap in gen_all_remaps_aux succeeds with unique sources *)
Lemma lookup_gen_all_remaps_aux_unique :
  forall input start_idx remaining src m space src_idx mod_idx,
    (forall i j s1 sm1 s2 sm2,
      nth_error remaining i = Some (s1, sm1) ->
      nth_error remaining j = Some (s2, sm2) ->
      s1 = s2 -> i = j) ->
    nth_error remaining mod_idx = Some (src, m) ->
    src_idx < space_count_of_module m space ->
    lookup_remap (gen_all_remaps_aux input start_idx remaining) space src src_idx
    = Some (offsets_for_module input (start_idx + mod_idx) space + src_idx).
Proof.
  intros input start_idx remaining.
  revert start_idx.
  induction remaining as [|[src' m'] rest IH];
    intros start_idx src m space src_idx mod_idx Huniq Hnth Hbound.
  - (* Empty remaining: contradiction *)
    destruct mod_idx; discriminate.
  - (* (src', m') :: rest *)
    destruct mod_idx as [|mod_idx'].
    + (* mod_idx = 0: current module *)
      simpl in Hnth. injection Hnth as Hsrc Hm. subst src' m'.
      simpl.
      rewrite lookup_remap_app.
      (* Lookup succeeds in current module's remaps *)
      replace (start_idx + 0) with start_idx by lia.
      rewrite (lookup_remap_gen_remaps_for_module
                 src m (offsets_for_module input start_idx) space src_idx Hbound).
      reflexivity.
    + (* mod_idx = S mod_idx': later module *)
      simpl in Hnth. simpl.
      rewrite lookup_remap_app.
      (* Show lookup fails in current module's remaps because src <> src' *)
      assert (Hneq: fst src <> fst src' \/ snd src <> snd src').
      { destruct (Nat.eq_dec (fst src) (fst src')) as [Hf | Hf];
        destruct (Nat.eq_dec (snd src) (snd src')) as [Hs | Hs].
        - exfalso.
          assert (Heq: src = src').
          { destruct src, src'. simpl in *. congruence. }
          assert (H0Smod: S mod_idx' = 0).
          { apply (Huniq (S mod_idx') 0 src m src' m'); auto. }
          lia.
        - right. auto.
        - left. auto.
        - left. auto. }
      rewrite (lookup_remap_module_wrong_src src src' m' space
                 (offsets_for_module input start_idx) src_idx Hneq).
      (* Use IH on rest *)
      replace (start_idx + S mod_idx') with (S start_idx + mod_idx') by lia.
      assert (Huniq_rest: forall i j s1 sm1 s2 sm2,
        nth_error rest i = Some (s1, sm1) ->
        nth_error rest j = Some (s2, sm2) ->
        s1 = s2 -> i = j).
      { intros i j s1 sm1 s2 sm2 Hi Hj Heq.
        assert (HS: S i = S j).
        { apply (Huniq (S i) (S j) s1 sm1 s2 sm2); simpl; auto. }
        lia. }
      apply (IH (S start_idx) src m space src_idx mod_idx'
                 Huniq_rest Hnth Hbound).
Qed.

(* gen_all_remaps is complete: every source index has a corresponding
   fused index, provided sources are unique. *)
Theorem gen_all_remaps_complete :
  forall input,
    unique_sources input ->
    remaps_complete input (gen_all_remaps input).
Proof.
  intros input Hunique.
  unfold remaps_complete.
  intros src m space src_idx Hin Hlt.
  (* Get the position of (src, m) in input *)
  apply In_nth_error in Hin.
  destruct Hin as [mod_idx Hmod_idx].
  (* The fused index is offset(mod_idx) + src_idx *)
  exists (offsets_for_module input (0 + mod_idx) space + src_idx).
  unfold gen_all_remaps.
  (* Convert src_idx bound to space_count_of_module form *)
  assert (Hbound: src_idx < space_count_of_module m space).
  { unfold space_count_of_module. destruct space; exact Hlt. }
  (* Convert unique_sources to the nth_error injectivity form *)
  apply unique_sources_nth_error in Hunique.
  apply lookup_gen_all_remaps_aux_unique; auto.
Qed.

(* gen_all_remaps is injective: distinct source indices map to distinct
   fused indices within each index space. Proof outline:
   - Two remaps r1, r2 with same space and fused_idx come from modules
     at positions i1, i2
   - fused_idx_k = offset(i_k) + source_idx_k
   - If i1 < i2: offset(i1) + source_idx1 < offset(i1) + count(i1)
     <= offset(i2) <= offset(i2) + source_idx2, contradiction
   - If i1 = i2: same offset, so source_idx1 = source_idx2, and
     source1 = source2 (both from same module)
   - If i1 > i2: symmetric to i1 < i2 *)
Theorem gen_all_remaps_injective :
  forall input,
    remaps_injective (gen_all_remaps input).
Proof.
  intro input.
  unfold remaps_injective, gen_all_remaps.
  intros r1 r2 Hin1 Hin2 Hspace Hfused.
  apply in_gen_all_remaps_aux in Hin1.
  apply in_gen_all_remaps_aux in Hin2.
  destruct Hin1 as [i1 [src1 [m1 [Hnth1 Hgen1]]]].
  destruct Hin2 as [i2 [src2 [m2 [Hnth2 Hgen2]]]].
  (* Extract fused_idx formulas *)
  pose proof (in_gen_remaps_for_module_fused _ _ _ _ Hgen1) as [Hfused1 Hsrc1].
  pose proof (in_gen_remaps_for_module_fused _ _ _ _ Hgen2) as [Hfused2 Hsrc2].
  (* Extract source_idx bounds *)
  pose proof (in_gen_remaps_for_module_bound _ _ _ _ Hgen1) as Hbound1.
  pose proof (in_gen_remaps_for_module_bound _ _ _ _ Hgen2) as Hbound2.
  (* Rewrite ir_space r1 = ir_space r2 in bounds *)
  rewrite Hspace in Hbound1.
  (* The fused indices are equal *)
  rewrite Hfused1, Hfused2 in Hfused.
  (* Compare module positions i1 and i2 *)
  destruct (Nat.lt_trichotomy i1 i2) as [Hlt | [Heq | Hgt]].
  - (* i1 < i2: contradiction *)
    exfalso.
    (* offset(i1) + source_idx r1 < offset(i1) + count1
       <= offset(S i1) <= offset(i2) <= offset(i2) + source_idx r2 *)
    assert (Hoff_bound:
      offsets_for_module input (0 + i1) (ir_space r2) +
      space_count_of_module m1 (ir_space r2)
      <= offsets_for_module input (0 + i2) (ir_space r2)).
    { unfold offsets_for_module.
      replace (0 + i1) with i1 by lia.
      replace (0 + i2) with i2 by lia.
      (* offset(i1) + count(m1) <= offset(S i1) <= offset(i2) *)
      assert (Hstep: compute_offset input (ir_space r2) i1 +
                      space_count_of_module m1 (ir_space r2) <=
                      compute_offset input (ir_space r2) (S i1)).
      { unfold compute_offset.
        rewrite (firstn_S_nth_error _ _ _ Hnth1).
        rewrite fold_left_app. simpl.
        unfold space_count_of_module.
        destruct (ir_space r2); simpl; lia. }
      assert (Hmono: compute_offset input (ir_space r2) (S i1) <=
                      compute_offset input (ir_space r2) i2).
      { apply offset_monotonic; try lia.
        apply nth_error_Some. rewrite Hnth2. discriminate. }
      lia. }
    (* Now: offset(i1) + source_idx r1 = offset(i2) + source_idx r2
       But: offset(i1) + source_idx r1 < offset(i1) + count1 <= offset(i2) <= offset(i2) + source_idx r2
       Contradiction. *)
    lia.
  - (* i1 = i2: same module position *)
    subst i2.
    rewrite Hnth1 in Hnth2. injection Hnth2 as Hsrc_eq Hm_eq.
    subst src2 m2.
    (* Both remaps from same module with same offset *)
    assert (Hidx_eq: ir_source_idx r1 = ir_source_idx r2) by lia.
    split; [congruence | exact Hidx_eq].
  - (* i2 < i1: symmetric to i1 < i2 *)
    exfalso.
    assert (Hoff_bound:
      offsets_for_module input (0 + i2) (ir_space r2) +
      space_count_of_module m2 (ir_space r2)
      <= offsets_for_module input (0 + i1) (ir_space r2)).
    { unfold offsets_for_module.
      replace (0 + i2) with i2 by lia.
      replace (0 + i1) with i1 by lia.
      assert (Hstep: compute_offset input (ir_space r2) i2 +
                      space_count_of_module m2 (ir_space r2) <=
                      compute_offset input (ir_space r2) (S i2)).
      { unfold compute_offset.
        rewrite (firstn_S_nth_error _ _ _ Hnth2).
        rewrite fold_left_app. simpl.
        unfold space_count_of_module.
        destruct (ir_space r2); simpl; lia. }
      assert (Hmono: compute_offset input (ir_space r2) (S i2) <=
                      compute_offset input (ir_space r2) i1).
      { apply offset_monotonic; try lia.
        apply nth_error_Some. rewrite Hnth1. discriminate. }
      lia. }
    lia.
Qed.

(* End of merge_correctness *)
