(* =========================================================================
   Merge Transformation - Remap Generation Proofs

   This file contains proofs about remap table generation:
   - Space count lemmas
   - Remap lookup lemmas
   - gen_remaps_for_space/module properties
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith.
From MeldSpec Require Import wasm_core component_model fusion_spec.
From MeldMerge Require Import merge_defs merge_layout.
Import ListNotations.

(* -------------------------------------------------------------------------
   Sum of Space Counts Lemmas
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
    rewrite length_map.
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

(* -------------------------------------------------------------------------
   gen_remaps_for_space Properties
   ------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------
   Offset Bound Lemmas
   ------------------------------------------------------------------------- *)

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
  unfold compute_offset, space_count.
  rewrite firstn_all.
  assert (Hsplit: input = firstn i input ++ (sm :: skipn (S i) input)).
  { rewrite <- (firstn_skipn i input) at 1.
    f_equal.
    destruct (skipn i input) as [|x rest] eqn:Hskip.
    - exfalso.
      assert (length (skipn i input) = 0) by (rewrite Hskip; reflexivity).
      rewrite length_skipn in H. lia.
    - f_equal.
      + assert (nth_error (skipn i input) 0 = Some sm).
        { rewrite nth_error_skipn. rewrite Nat.add_0_r. exact Hnth. }
        rewrite Hskip in H. simpl in H. injection H. auto.
      + simpl in Hskip.
        assert (rest = skipn (S i) input).
        { replace (S i) with (1 + i) by lia.
          rewrite <- skipn_skipn.
          rewrite Hskip. reflexivity. }
        exact H. }
  assert (Hlen: length (firstn i input) = i).
  { rewrite length_firstn. lia. }
  rewrite Hsplit at 2.
  rewrite fold_left_app. simpl.
  destruct space; simpl;
    rewrite (fold_left_add_shift _ (skipn (S i) input));
    apply Nat.le_add_r.
Qed.

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

(* -------------------------------------------------------------------------
   Index Space Equality Lemmas
   ------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------
   Lookup Lemmas for gen_remaps_for_space
   ------------------------------------------------------------------------- *)

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
   gen_remaps_for_module Properties
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

(* -------------------------------------------------------------------------
   Lookup in gen_all_remaps
   ------------------------------------------------------------------------- *)

(* Helper: find over appended lists *)
Lemma find_app_remap {A : Type} :
  forall (P : A -> bool) (l1 l2 : list A),
    find P (l1 ++ l2) =
    match find P l1 with
    | Some x => Some x
    | None => find P l2
    end.
Proof.
  intros P l1 l2. induction l1 as [|h t IHl]; simpl.
  - reflexivity.
  - destruct (P h); [reflexivity | exact IHl].
Qed.

(* Every remap in gen_remaps_for_module has ir_source = src *)
Lemma gen_remaps_source :
  forall src m offsets r,
    In r (gen_remaps_for_module src m offsets) ->
    ir_source r = src.
Proof.
  intros src m offsets r Hin.
  apply in_gen_remaps_for_module_fused in Hin.
  destruct Hin as [_ Hsrc]. exact Hsrc.
Qed.

(* If all remaps have source src' and src <> src', find matching src returns None *)
Lemma find_wrong_source :
  forall remaps space src src_idx,
    (forall r, In r remaps -> ir_source r <> src) ->
    find (fun r =>
      index_space_eqb (ir_space r) space &&
      Nat.eqb (fst (ir_source r)) (fst src) &&
      Nat.eqb (snd (ir_source r)) (snd src) &&
      Nat.eqb (ir_source_idx r) src_idx)
    remaps = None.
Proof.
  induction remaps as [|r remaps' IH]; intros space src src_idx Hwrong.
  - reflexivity.
  - simpl.
    assert (Hr: ir_source r <> src) by (apply Hwrong; left; reflexivity).
    (* The source mismatch makes the boolean predicate false *)
    assert (Hmismatch: fst (ir_source r) <> fst src \/ snd (ir_source r) <> snd src).
    { destruct (Nat.eq_dec (fst (ir_source r)) (fst src)) as [Hf|Hf];
      destruct (Nat.eq_dec (snd (ir_source r)) (snd src)) as [Hs|Hs].
      - exfalso. apply Hr. destruct (ir_source r), src. simpl in *. congruence.
      - right. exact Hs.
      - left. exact Hf.
      - left. exact Hf. }
    destruct Hmismatch as [Hf | Hs].
    + rewrite (proj2 (Nat.eqb_neq _ _) Hf).
      destruct (index_space_eqb _ _); simpl;
        apply IH; intros r' Hin'; apply Hwrong; right; exact Hin'.
    + destruct (index_space_eqb _ _); simpl;
      destruct (Nat.eqb (fst (ir_source r)) (fst src)); simpl;
      try (rewrite (proj2 (Nat.eqb_neq _ _) Hs); simpl;
           apply IH; intros r' Hin'; apply Hwrong; right; exact Hin').
      all: apply IH; intros r' Hin'; apply Hwrong; right; exact Hin'.
Qed.

(* Corollary: find fails in gen_remaps_for_module when sources differ *)
Lemma find_gen_remaps_wrong_source :
  forall src' m' offsets space src src_idx,
    src <> src' ->
    find (fun r =>
      index_space_eqb (ir_space r) space &&
      Nat.eqb (fst (ir_source r)) (fst src) &&
      Nat.eqb (snd (ir_source r)) (snd src) &&
      Nat.eqb (ir_source_idx r) src_idx)
    (gen_remaps_for_module src' m' offsets) = None.
Proof.
  intros src' m' offsets space src src_idx Hneq.
  apply find_wrong_source.
  intros r Hin.
  pose proof (gen_remaps_source src' m' offsets r Hin) as Hsrc.
  rewrite Hsrc. intro Heq. apply Hneq. symmetry. exact Heq.
Qed.

(* Helper: lookup_remap over an appended list succeeds if it succeeds in the prefix *)
Lemma lookup_remap_app :
  forall l1 l2 space src src_idx result,
    lookup_remap l1 space src src_idx = Some result ->
    lookup_remap (l1 ++ l2) space src src_idx = Some result.
Proof.
  intros l1 l2 space src src_idx result H.
  unfold lookup_remap in *.
  rewrite find_app_remap.
  destruct (find _ l1) eqn:Hfind.
  - exact H.
  - discriminate.
Qed.

(* Helper: lookup_remap in gen_remaps_for_module succeeds for valid indices.
   Navigates the 7-space concatenation (Type, Func, Table, Mem, Global, Elem, Data)
   by case-splitting on the target space and eliminating wrong-space chunks. *)
Lemma lookup_remap_gen_remaps_for_module :
  forall src m offsets space src_idx,
    src_idx < space_count_of_module m space ->
    lookup_remap (gen_remaps_for_module src m offsets) space src src_idx
    = Some (offsets space + src_idx).
Proof.
  intros src m offsets space src_idx Hbound.
  unfold lookup_remap, gen_remaps_for_module, space_count_of_module in *.
  destruct space; repeat rewrite find_app_remap.
  all: repeat (rewrite find_gen_remaps_for_space_wrong_space; [simpl | discriminate]).
  all: unfold gen_remaps_for_space;
       rewrite find_remap_in_mapped_seq; [simpl; reflexivity | lia].
Qed.

(* Lookup in gen_all_remaps succeeds when sources are unique.
   The NoDup hypothesis ensures find correctly partitions across modules. *)
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
      simpl.
      replace (start_idx + 0) with start_idx by lia.
      apply lookup_remap_app.
      apply lookup_remap_gen_remaps_for_module.
      exact Hbound.
    + (* mod_idx = S mod_idx': source is in the tail *)
      simpl in Hnth.
      simpl.
      unfold lookup_remap.
      rewrite find_app_remap.
      (* Show find fails in current module's remaps because src <> src'.
         From NoDup: src' not in map fst rest.
         From nth_error: src is in map fst rest.
         Therefore src <> src'. *)
      simpl in Hnodup.
      apply NoDup_cons_iff in Hnodup.
      destruct Hnodup as [Hnot_in Hnodup_rest].
      assert (Hsrc_in_rest: In src (map fst rest)).
      { apply nth_error_In in Hnth.
        apply in_map with (f := fst) in Hnth. simpl in Hnth. exact Hnth. }
      assert (Hsrc_neq: src <> src').
      { intro Heq. subst. contradiction. }
      rewrite find_gen_remaps_wrong_source; [| exact Hsrc_neq].
      (* Now the find falls through to gen_all_remaps_aux for the rest *)
      unfold lookup_remap in IH.
      replace (start_idx + S mod_idx') with (S start_idx + mod_idx') by lia.
      eapply IH; eassumption.
Qed.

(* End of merge_remap *)
