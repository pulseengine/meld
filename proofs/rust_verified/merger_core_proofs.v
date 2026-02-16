(*
  Implementation proofs for merger_core.rs

  This file establishes the connection between the Rust implementation
  (translated via rocq-of-rust) and the merge specification.

  The translated Rust code provides:
  - SpaceOffsets.advance (offset accumulation)
  - compute_offsets (offset calculation for all prior modules)
  - compute_memory_layout (memory layout computation)

  The spec (split across merge_defs.v, merge_layout.v, merge_remap.v,
  merge_correctness.v) provides:
  - compute_offset (per-space offset calculation) — merge_defs.v
  - layout_step / compute_memory_layout (memory layout) — merge_layout.v
  - Correctness properties (monotonicity, disjointness) — merge_correctness.v
*)

From Stdlib Require Import List ZArith Lia Arith.
Import ListNotations.

(* -------------------------------------------------------------------------
   Pure-Model Definitions

   These mirror the Rust implementation in a way that's easier to reason
   about before connecting to the translated code.
   ------------------------------------------------------------------------- *)

(* Wasm page size: 64 KiB *)
Definition wasm_page_size : nat := 65536.

(* Space counts for a module *)
Record space_counts : Type := mkSpaceCounts {
  sc_types : nat;
  sc_funcs : nat;
  sc_tables : nat;
  sc_mems : nat;
  sc_globals : nat;
}.

(* Running offsets during merge *)
Record space_offsets : Type := mkSpaceOffsets {
  so_types : nat;
  so_funcs : nat;
  so_tables : nat;
  so_mems : nat;
  so_globals : nat;
}.

(* Zero offsets *)
Definition space_offsets_zero : space_offsets :=
  mkSpaceOffsets 0 0 0 0 0.

(* Advance offsets by adding counts *)
Definition advance_offsets (off : space_offsets) (cnt : space_counts) : space_offsets :=
  mkSpaceOffsets
    (so_types off + sc_types cnt)
    (so_funcs off + sc_funcs cnt)
    (so_tables off + sc_tables cnt)
    (so_mems off + sc_mems cnt)
    (so_globals off + sc_globals cnt).

(* Compute offsets from a list of prior counts *)
Definition compute_offsets (prior : list space_counts) : space_offsets :=
  fold_left advance_offsets prior space_offsets_zero.

(* Memory layout for a single module *)
Record memory_layout : Type := mkMemoryLayout {
  ml_base : nat;
  ml_size : nat;
}.

(* Layout step function - accumulates layouts and base address *)
Definition layout_step (acc : list memory_layout * nat) (pages : nat)
    : list memory_layout * nat :=
  let '(layouts, current_base) := acc in
  let size := pages * wasm_page_size in
  (layouts ++ [mkMemoryLayout current_base size], current_base + size).

(* Compute memory layout from page sizes *)
Definition compute_memory_layout_spec (page_sizes : list nat) : list memory_layout :=
  fst (fold_left layout_step page_sizes ([], 0)).

(* -------------------------------------------------------------------------
   Offset Computation Properties
   ------------------------------------------------------------------------- *)

(* Advance preserves ordering: if we advance, each field increases or stays same *)
Lemma advance_increases_types :
  forall off cnt,
    so_types off <= so_types (advance_offsets off cnt).
Proof.
  intros. unfold advance_offsets. simpl. lia.
Qed.

Lemma advance_increases_funcs :
  forall off cnt,
    so_funcs off <= so_funcs (advance_offsets off cnt).
Proof.
  intros. unfold advance_offsets. simpl. lia.
Qed.

(* Helper: fold_left with advance_offsets increases types *)
Lemma fold_left_advance_types_ge :
  forall l init,
    so_types init <= so_types (fold_left advance_offsets l init).
Proof.
  induction l as [|c l' IH]; intro init.
  - simpl. lia.
  - simpl.
    assert (Hadv: so_types init <= so_types (advance_offsets init c))
      by apply advance_increases_types.
    specialize (IH (advance_offsets init c)).
    lia.
Qed.

(* Offset computation is monotonic in list length *)
Lemma compute_offsets_types_monotonic :
  forall l1 l2,
    so_types (compute_offsets l1) <= so_types (compute_offsets (l1 ++ l2)).
Proof.
  intros l1 l2.
  unfold compute_offsets.
  rewrite fold_left_app.
  apply fold_left_advance_types_ge.
Qed.

(* Helper lemma for fold_left shift *)
Lemma fold_left_add_shift :
  forall (f : space_counts -> nat) (l : list space_counts) (base : nat),
    fold_left (fun acc x => acc + f x) l base =
    base + fold_left (fun acc x => acc + f x) l 0.
Proof.
  intros f l. induction l as [|x l' IH]; intro base.
  - simpl. lia.
  - simpl. rewrite IH. rewrite (IH (f x)). lia.
Qed.

(* Offset for type space equals sum of all prior type counts *)
Lemma compute_offsets_types_sum :
  forall prior,
    so_types (compute_offsets prior) =
    fold_left (fun acc cnt => acc + sc_types cnt) prior 0.
Proof.
  intro prior.
  unfold compute_offsets.
  assert (H: forall init,
    so_types (fold_left advance_offsets prior init) =
    so_types init + fold_left (fun acc cnt => acc + sc_types cnt) prior 0).
  {
    induction prior as [|cnt prior' IH]; intro init.
    - simpl. lia.
    - simpl. rewrite IH.
      unfold advance_offsets. simpl.
      rewrite (fold_left_add_shift sc_types prior' (sc_types cnt)).
      lia.
  }
  rewrite H. simpl. lia.
Qed.

(* Similar lemma for funcs *)
Lemma compute_offsets_funcs_sum :
  forall prior,
    so_funcs (compute_offsets prior) =
    fold_left (fun acc cnt => acc + sc_funcs cnt) prior 0.
Proof.
  intro prior.
  unfold compute_offsets.
  assert (H: forall init,
    so_funcs (fold_left advance_offsets prior init) =
    so_funcs init + fold_left (fun acc cnt => acc + sc_funcs cnt) prior 0).
  {
    induction prior as [|cnt prior' IH]; intro init.
    - simpl. lia.
    - simpl. rewrite IH.
      unfold advance_offsets. simpl.
      rewrite (fold_left_add_shift sc_funcs prior' (sc_funcs cnt)).
      lia.
  }
  rewrite H. simpl. lia.
Qed.

(* -------------------------------------------------------------------------
   Memory Layout Properties
   ------------------------------------------------------------------------- *)

(* Layouts are sequential: each ends where next begins *)
Definition layouts_sequential (layouts : list memory_layout) : Prop :=
  forall i l1 l2,
    nth_error layouts i = Some l1 ->
    nth_error layouts (S i) = Some l2 ->
    ml_base l1 + ml_size l1 = ml_base l2.

(* Helper: for sequential layouts, layout[i].end <= layout[j].base when i < j *)
Lemma sequential_layout_order :
  forall layouts i j l1 l2,
    layouts_sequential layouts ->
    i < j ->
    nth_error layouts i = Some l1 ->
    nth_error layouts j = Some l2 ->
    ml_base l1 + ml_size l1 <= ml_base l2.
Proof.
  intros layouts i j.
  (* Induction on the difference j - i *)
  remember (j - i) as diff eqn:Hdiff.
  generalize dependent j. generalize dependent i.
  induction diff as [|diff' IH]; intros i j Hdiff l1 l2 Hseq Hlt Hl1 Hl2.
  - (* diff = 0: contradiction with i < j *)
    lia.
  - (* diff = S diff': either j = S i (direct) or use transitivity *)
    destruct (Nat.eq_dec j (S i)) as [Heq | Hneq].
    + (* j = S i: direct from layouts_sequential *)
      subst j.
      specialize (Hseq i l1 l2 Hl1 Hl2). lia.
    + (* j > S i: transitivity via element at S i *)
      assert (HSi_lt_j: S i < j) by lia.
      assert (Hdiff': diff' = j - S i) by lia.
      destruct (nth_error layouts (S i)) as [lmid|] eqn:Hmid.
      * assert (Hstep: ml_base l1 + ml_size l1 = ml_base lmid)
          by (apply Hseq; assumption).
        assert (Hrest: ml_base lmid + ml_size lmid <= ml_base l2)
          by (apply (IH (S i) j Hdiff' lmid l2 Hseq HSi_lt_j Hmid Hl2)).
        lia.
      * (* No element at S i: contradiction since S i < j and j has element *)
        apply nth_error_None in Hmid.
        assert (Hj_bound: j < length layouts)
          by (apply nth_error_Some; rewrite Hl2; discriminate).
        lia.
Qed.

(* Sequential layouts are disjoint *)
Theorem sequential_disjoint :
  forall layouts,
    layouts_sequential layouts ->
    forall l1 l2,
      In l1 layouts ->
      In l2 layouts ->
      l1 <> l2 ->
      ml_base l1 + ml_size l1 <= ml_base l2 \/
      ml_base l2 + ml_size l2 <= ml_base l1.
Proof.
  intros layouts Hseq l1 l2 Hin1 Hin2 Hneq.
  apply In_nth_error in Hin1.
  apply In_nth_error in Hin2.
  destruct Hin1 as [i1 Hi1].
  destruct Hin2 as [i2 Hi2].
  destruct (Nat.lt_trichotomy i1 i2) as [Hlt | [Heq | Hgt]].
  - (* i1 < i2: l1 ends before l2 starts *)
    left.
    apply (sequential_layout_order layouts i1 i2 l1 l2 Hseq Hlt Hi1 Hi2).
  - (* i1 = i2: contradiction *)
    subst. rewrite Hi1 in Hi2. injection Hi2 as Heq. contradiction.
  - (* i2 < i1: symmetric *)
    right.
    apply (sequential_layout_order layouts i2 i1 l2 l1 Hseq Hgt Hi2 Hi1).
Qed.

(* ---- Helper lemmas for compute_memory_layout_sequential ---- *)

(* Generic fold_left shift lemma for nat lists *)
Lemma fold_left_add_shift_nat :
  forall (f : nat -> nat) (l : list nat) (base : nat),
    fold_left (fun acc x => acc + f x) l base =
    base + fold_left (fun acc x => acc + f x) l 0.
Proof.
  intros f l. induction l as [|x l' IH]; intro base.
  - simpl. lia.
  - simpl. rewrite IH. rewrite (IH (f x)). lia.
Qed.

(* The fold distributes: output layouts = init ++ layouts from empty start *)
Lemma layout_fold_fst_app :
  forall l init_layouts init_addr,
    fst (fold_left layout_step l (init_layouts, init_addr))
    = init_layouts ++ fst (fold_left layout_step l ([], init_addr)).
Proof.
  induction l as [|p l' IH]; intros; simpl.
  - rewrite app_nil_r. reflexivity.
  - unfold layout_step. simpl.
    rewrite IH. rewrite (IH [_]).
    rewrite app_assoc. reflexivity.
Qed.

(* Number of output layouts = initial count + input length *)
Lemma layout_fold_length :
  forall l init_layouts init_addr,
    length (fst (fold_left layout_step l (init_layouts, init_addr)))
    = length init_layouts + length l.
Proof.
  induction l as [|p l' IH]; intros; simpl.
  - lia.
  - unfold layout_step at 1. simpl.
    rewrite IH. rewrite length_app. simpl. lia.
Qed.

(* Helper: firstn (S n) splits into firstn n ++ [nth element] *)
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

(* The nth layout from empty initial list has predictable base and size *)
Lemma layout_fold_nth_props :
  forall l init_addr i lay,
    nth_error (fst (fold_left layout_step l ([], init_addr))) i = Some lay ->
    i < length l ->
    ml_base lay = init_addr +
      fold_left (fun acc p => acc + p * wasm_page_size) (firstn i l) 0 /\
    (forall p, nth_error l i = Some p -> ml_size lay = p * wasm_page_size).
Proof.
  induction l as [|p l' IH]; intros init_addr i lay Hnth Hi.
  - simpl in Hi. lia.
  - destruct i as [|i'].
    + (* i = 0: the first layout has base = init_addr *)
      simpl in Hnth. unfold layout_step in Hnth. simpl in Hnth.
      rewrite layout_fold_fst_app in Hnth. simpl in Hnth.
      injection Hnth as Hlay. subst lay. simpl.
      split; [lia | intros p' Hp'; injection Hp' as Heq; subst; reflexivity].
    + (* i = S i': use IH on the tail *)
      simpl in Hi.
      simpl in Hnth. unfold layout_step in Hnth. simpl in Hnth.
      rewrite layout_fold_fst_app in Hnth. simpl in Hnth.
      specialize (IH (init_addr + p * wasm_page_size) i' lay Hnth ltac:(lia)).
      destruct IH as [IHbase IHsize].
      split.
      * rewrite IHbase. simpl.
        rewrite (fold_left_add_shift_nat
                   (fun x => x * wasm_page_size) (firstn i' l')
                   (p * wasm_page_size)).
        lia.
      * intros p' Hp'. simpl in Hp'. apply IHsize. exact Hp'.
Qed.

(* The memory layout we compute is sequential *)
Theorem compute_memory_layout_sequential :
  forall page_sizes,
    layouts_sequential (compute_memory_layout_spec page_sizes).
Proof.
  intro page_sizes.
  unfold layouts_sequential, compute_memory_layout_spec.
  intros i l1 l2 Hl1 Hl2.
  (* Determine bounds on i from the nth_error hypotheses *)
  pose proof (layout_fold_length page_sizes [] 0) as Hlen.
  simpl in Hlen.
  assert (Hi: i < length page_sizes).
  { assert (Hsome: nth_error (fst (fold_left layout_step page_sizes ([], 0))) i <> None)
      by (rewrite Hl1; discriminate).
    apply nth_error_Some in Hsome. rewrite Hlen in Hsome. exact Hsome. }
  assert (HSi: S i < length page_sizes).
  { assert (Hsome: nth_error (fst (fold_left layout_step page_sizes ([], 0))) (S i) <> None)
      by (rewrite Hl2; discriminate).
    apply nth_error_Some in Hsome. rewrite Hlen in Hsome. exact Hsome. }
  (* Get the page sizes at positions i and S i *)
  destruct (nth_error page_sizes i) as [p1|] eqn:Hp1;
    [| apply nth_error_None in Hp1; lia].
  destruct (nth_error page_sizes (S i)) as [p2|] eqn:Hp2;
    [| apply nth_error_None in Hp2; lia].
  (* Extract properties of l1 and l2 from the fold *)
  destruct (layout_fold_nth_props page_sizes 0 i l1 Hl1 Hi) as [Hbase1 Hsize1].
  destruct (layout_fold_nth_props page_sizes 0 (S i) l2 Hl2 HSi) as [Hbase2 _].
  (* l1.base + l1.size = l2.base *)
  rewrite Hbase1, (Hsize1 p1 Hp1), Hbase2.
  rewrite (firstn_S_nth_error page_sizes i p1 Hp1).
  rewrite fold_left_app. simpl.
  rewrite (fold_left_add_shift_nat
             (fun x => x * wasm_page_size) (firstn i page_sizes)
             (p1 * wasm_page_size)).
  lia.
Qed.

(* Main disjointness theorem *)
Theorem compute_memory_layout_disjoint :
  forall page_sizes,
    forall l1 l2,
      In l1 (compute_memory_layout_spec page_sizes) ->
      In l2 (compute_memory_layout_spec page_sizes) ->
      l1 <> l2 ->
      ml_base l1 + ml_size l1 <= ml_base l2 \/
      ml_base l2 + ml_size l2 <= ml_base l1.
Proof.
  intros page_sizes l1 l2 Hin1 Hin2 Hneq.
  apply (sequential_disjoint (compute_memory_layout_spec page_sizes)).
  - apply compute_memory_layout_sequential.
  - exact Hin1.
  - exact Hin2.
  - exact Hneq.
Qed.

(* -------------------------------------------------------------------------
   Connection to Translated Rust (placeholder)

   Once the Rust code is translated, we will add lemmas of the form:

   Lemma rust_compute_offsets_correct :
     forall prior,
       MergerCore.compute_offsets prior = compute_offsets (convert prior).

   This bridges the gap between the translated Rust and our pure model.
   ------------------------------------------------------------------------- *)

(* End of merger_core_proofs *)
