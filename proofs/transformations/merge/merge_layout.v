(* =========================================================================
   Merge Transformation - Memory Layout Proofs

   This file contains proofs about memory layout computation:
   - Offset monotonicity
   - Layout sequential property
   - Layout disjointness theorem
   ========================================================================= *)

From Stdlib Require Import List ZArith Lia Bool Arith.
From MeldSpec Require Import wasm_core component_model fusion_spec.
From MeldMerge Require Import merge_defs.
Import ListNotations.

(* -------------------------------------------------------------------------
   Basic Helper Lemmas
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

(* -------------------------------------------------------------------------
   Offset Monotonicity
   ------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------
   Sequential Layout Properties
   ------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------
   Memory Layout Fold Invariants
   ------------------------------------------------------------------------- *)

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
        rewrite (fold_left_add_shift (fun x => module_memory_size (snd x))
                                      (firstn i' input')
                                      (module_memory_size (snd sm))).
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

(* -------------------------------------------------------------------------
   Main Layout Disjointness Theorem
   ------------------------------------------------------------------------- *)

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

(* End of merge_layout *)
